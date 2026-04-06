from __future__ import annotations

"""
Discord platform adapter.

Uses discord.py library for:
- Receiving messages from servers and DMs
- Sending responses back
- Handling threads and channels
"""

import asyncio
import json
import logging
import os
import struct
import subprocess
import tempfile
import threading
import time
from collections import defaultdict
from pathlib import Path
from typing import Callable, Dict, Optional, Any

logger = logging.getLogger(__name__)

VALID_THREAD_AUTO_ARCHIVE_MINUTES = {60, 1440, 4320, 10080}

try:
    import discord
    from discord import Message as DiscordMessage, Intents
    from discord.ext import commands
    DISCORD_AVAILABLE = True
except ImportError:
    DISCORD_AVAILABLE = False
    discord = None
    DiscordMessage = Any
    Intents = Any
    commands = None

import sys
from pathlib import Path as _Path
sys.path.insert(0, str(_Path(__file__).resolve().parents[2]))

from gateway.config import Platform, PlatformConfig
import re

from gateway.platforms.base import (
    BasePlatformAdapter,
    MessageEvent,
    MessageType,
    SendResult,
    cache_image_from_url,
    cache_audio_from_url,
    cache_document_from_bytes,
    SUPPORTED_DOCUMENT_TYPES,
)


def _clean_discord_id(entry: str) -> str:
    """Strip common prefixes from a Discord user ID or username entry.

    Users sometimes paste IDs with prefixes like ``user:123``, ``<@123>``,
    or ``<@!123>`` from Discord's UI or other tools.  This normalises the
    entry to just the bare ID or username.
    """
    entry = entry.strip()
    # Strip Discord mention syntax: <@123> or <@!123>
    if entry.startswith("<@") and entry.endswith(">"):
        entry = entry.lstrip("<@!").rstrip(">")
    # Strip "user:" prefix (seen in some Discord tools / onboarding pastes)
    if entry.lower().startswith("user:"):
        entry = entry[5:]
    return entry.strip()


def check_discord_requirements() -> bool:
    """Check if Discord dependencies are available."""
    return DISCORD_AVAILABLE


class VoiceReceiver:
    """Captures and decodes voice audio from a Discord voice channel.

    Attaches to a VoiceClient's socket listener, decrypts RTP packets
    (NaCl transport + DAVE E2EE), decodes Opus to PCM, and buffers
    per-user audio.  A polling loop detects silence and delivers
    completed utterances via a callback.
    """

    SILENCE_THRESHOLD = 1.5    # seconds of silence → end of utterance
    MIN_SPEECH_DURATION = 0.5  # minimum seconds to process (skip noise)
    SAMPLE_RATE = 48000        # Discord native rate
    CHANNELS = 2               # Discord sends stereo

    def __init__(self, voice_client, allowed_user_ids: set = None):
        self._vc = voice_client
        self._allowed_user_ids = allowed_user_ids or set()
        self._running = False

        # Decryption
        self._secret_key: Optional[bytes] = None
        self._dave_session = None
        self._bot_ssrc: int = 0

        # SSRC -> user_id mapping (populated from SPEAKING events)
        self._ssrc_to_user: Dict[int, int] = {}
        self._lock = threading.Lock()

        # Per-user audio buffers
        self._buffers: Dict[int, bytearray] = defaultdict(bytearray)
        self._last_packet_time: Dict[int, float] = {}

        # Opus decoder per SSRC (each user needs own decoder state)
        self._decoders: Dict[int, object] = {}

        # Pause flag: don't capture while bot is playing TTS
        self._paused = False

        # Debug logging counter (instance-level to avoid cross-instance races)
        self._packet_debug_count = 0

    # ------------------------------------------------------------------
    # Lifecycle
    # ------------------------------------------------------------------

    def start(self):
        """Start listening for voice packets."""
        conn = self._vc._connection
        self._secret_key = bytes(conn.secret_key)
        self._dave_session = conn.dave_session
        self._bot_ssrc = conn.ssrc

        self._install_speaking_hook(conn)
        conn.add_socket_listener(self._on_packet)
        self._running = True
        logger.info("VoiceReceiver started (bot_ssrc=%d)", self._bot_ssrc)

    def stop(self):
        """Stop listening and clean up."""
        self._running = False
        try:
            self._vc._connection.remove_socket_listener(self._on_packet)
        except Exception:
            pass
        with self._lock:
            self._buffers.clear()
            self._last_packet_time.clear()
            self._decoders.clear()
            self._ssrc_to_user.clear()
        logger.info("VoiceReceiver stopped")

    def pause(self):
        self._paused = True

    def resume(self):
        self._paused = False

    # ------------------------------------------------------------------
    # SSRC -> user_id mapping via SPEAKING opcode hook
    # ------------------------------------------------------------------

    def map_ssrc(self, ssrc: int, user_id: int):
        with self._lock:
            self._ssrc_to_user[ssrc] = user_id

    def _install_speaking_hook(self, conn):
        """Wrap the voice websocket hook to capture SPEAKING events (op 5).

        VoiceConnectionState stores the hook as ``conn.hook`` (public attr).
        It is passed to DiscordVoiceWebSocket on each (re)connect, so we
        must wrap it on the VoiceConnectionState level AND on the current
        live websocket instance.
        """
        original_hook = conn.hook
        receiver_self = self

        async def wrapped_hook(ws, msg):
            if isinstance(msg, dict) and msg.get("op") == 5:
                data = msg.get("d", {})
                ssrc = data.get("ssrc")
                user_id = data.get("user_id")
                if ssrc and user_id:
                    logger.info("SPEAKING event: ssrc=%d -> user=%s", ssrc, user_id)
                    receiver_self.map_ssrc(int(ssrc), int(user_id))
            if original_hook:
                await original_hook(ws, msg)

        # Set on connection state (for future reconnects)
        conn.hook = wrapped_hook
        # Set on the current live websocket (for immediate effect)
        try:
            from discord.utils import MISSING
            if hasattr(conn, 'ws') and conn.ws is not MISSING:
                conn.ws._hook = wrapped_hook
                logger.info("Speaking hook installed on live websocket")
        except Exception as e:
            logger.warning("Could not install hook on live ws: %s", e)

    # ------------------------------------------------------------------
    # Packet handler (called from SocketReader thread)
    # ------------------------------------------------------------------

    def _on_packet(self, data: bytes):
        if not self._running or self._paused:
            return

        # Log first few raw packets for debugging
        self._packet_debug_count += 1
        if self._packet_debug_count <= 5:
            logger.debug(
                "Raw UDP packet: len=%d, first_bytes=%s",
                len(data), data[:4].hex() if len(data) >= 4 else "short",
            )

        if len(data) < 16:
            return

        # RTP version check: top 2 bits must be 10 (version 2).
        # Lower bits may vary (padding, extension, CSRC count).
        # Payload type (byte 1 lower 7 bits) = 0x78 (120) for voice.
        if (data[0] >> 6) != 2 or (data[1] & 0x7F) != 0x78:
            if self._packet_debug_count <= 5:
                logger.debug("Skipped non-RTP: byte0=0x%02x byte1=0x%02x", data[0], data[1])
            return

        first_byte = data[0]
        _, _, seq, timestamp, ssrc = struct.unpack_from(">BBHII", data, 0)

        # Skip bot's own audio
        if ssrc == self._bot_ssrc:
            return

        # Calculate dynamic RTP header size (RFC 9335 / rtpsize mode)
        cc = first_byte & 0x0F  # CSRC count
        has_extension = bool(first_byte & 0x10)  # extension bit
        header_size = 12 + (4 * cc) + (4 if has_extension else 0)

        if len(data) < header_size + 4:  # need at least header + nonce
            return

        # Read extension length from preamble (for skipping after decrypt)
        ext_data_len = 0
        if has_extension:
            ext_preamble_offset = 12 + (4 * cc)
            ext_words = struct.unpack_from(">H", data, ext_preamble_offset + 2)[0]
            ext_data_len = ext_words * 4

        if self._packet_debug_count <= 10:
            with self._lock:
                known_user = self._ssrc_to_user.get(ssrc, "unknown")
            logger.debug(
                "RTP packet: ssrc=%d, seq=%d, user=%s, hdr=%d, ext_data=%d",
                ssrc, seq, known_user, header_size, ext_data_len,
            )

        header = bytes(data[:header_size])
        payload_with_nonce = data[header_size:]

        # --- NaCl transport decrypt (aead_xchacha20_poly1305_rtpsize) ---
        if len(payload_with_nonce) < 4:
            return
        nonce = bytearray(24)
        nonce[:4] = payload_with_nonce[-4:]
        encrypted = bytes(payload_with_nonce[:-4])

        try:
            import nacl.secret  # noqa: delayed import – only in voice path
            box = nacl.secret.Aead(self._secret_key)
            decrypted = box.decrypt(encrypted, header, bytes(nonce))
        except Exception as e:
            if self._packet_debug_count <= 10:
                logger.warning("NaCl decrypt failed: %s (hdr=%d, enc=%d)", e, header_size, len(encrypted))
            return

        # Skip encrypted extension data to get the actual opus payload
        if ext_data_len and len(decrypted) > ext_data_len:
            decrypted = decrypted[ext_data_len:]

        # --- DAVE E2EE decrypt ---
        if self._dave_session:
            with self._lock:
                user_id = self._ssrc_to_user.get(ssrc, 0)
            if user_id:
                try:
                    import davey
                    decrypted = self._dave_session.decrypt(
                        user_id, davey.MediaType.audio, decrypted
                    )
                except Exception as e:
                    # Unencrypted passthrough — use NaCl-decrypted data as-is
                    if "Unencrypted" not in str(e):
                        if self._packet_debug_count <= 10:
                            logger.warning("DAVE decrypt failed for ssrc=%d: %s", ssrc, e)
                        return
            # If SSRC unknown (no SPEAKING event yet), skip DAVE and try
            # Opus decode directly — audio may be in passthrough mode.
            # Buffer will get a user_id when SPEAKING event arrives later.

        # --- Opus decode -> PCM ---
        try:
            if ssrc not in self._decoders:
                self._decoders[ssrc] = discord.opus.Decoder()
            pcm = self._decoders[ssrc].decode(decrypted)
            with self._lock:
                self._buffers[ssrc].extend(pcm)
                self._last_packet_time[ssrc] = time.monotonic()
        except Exception as e:
            logger.debug("Opus decode error for SSRC %s: %s", ssrc, e)
            return

    # ------------------------------------------------------------------
    # Silence detection
    # ------------------------------------------------------------------

    def _infer_user_for_ssrc(self, ssrc: int) -> int:
        """Try to infer user_id for an unmapped SSRC.

        When the bot rejoins a voice channel, Discord may not resend
        SPEAKING events for users already speaking.  If exactly one
        allowed user is in the channel, map the SSRC to them.
        """
        try:
            channel = self._vc.channel
            if not channel:
                return 0
            bot_id = self._vc.user.id if self._vc.user else 0
            allowed = self._allowed_user_ids
            candidates = [
                m.id for m in channel.members
                if m.id != bot_id and (not allowed or str(m.id) in allowed)
            ]
            if len(candidates) == 1:
                uid = candidates[0]
                self._ssrc_to_user[ssrc] = uid
                logger.info("Auto-mapped ssrc=%d -> user=%d (sole allowed member)", ssrc, uid)
                return uid
        except Exception:
            pass
        return 0

    def check_silence(self) -> list:
        """Return list of (user_id, pcm_bytes) for completed utterances."""
        now = time.monotonic()
        completed = []

        with self._lock:
            ssrc_user_map = dict(self._ssrc_to_user)
            ssrc_list = list(self._buffers.keys())

            for ssrc in ssrc_list:
                last_time = self._last_packet_time.get(ssrc, now)
                silence_duration = now - last_time
                buf = self._buffers[ssrc]
                # 48kHz, 16-bit, stereo = 192000 bytes/sec
                buf_duration = len(buf) / (self.SAMPLE_RATE * self.CHANNELS * 2)

                if silence_duration >= self.SILENCE_THRESHOLD and buf_duration >= self.MIN_SPEECH_DURATION:
                    user_id = ssrc_user_map.get(ssrc, 0)
                    if not user_id:
                        # SSRC not mapped (SPEAKING event missing after bot rejoin).
                        # Infer from allowed users in the voice channel.
                        user_id = self._infer_user_for_ssrc(ssrc)
                    if user_id:
                        completed.append((user_id, bytes(buf)))
                    self._buffers[ssrc] = bytearray()
                    self._last_packet_time.pop(ssrc, None)
                elif silence_duration >= self.SILENCE_THRESHOLD * 2:
                    # Stale buffer with no valid user — discard
                    self._buffers.pop(ssrc, None)
                    self._last_packet_time.pop(ssrc, None)

        return completed

    # ------------------------------------------------------------------
    # PCM -> WAV conversion (for Whisper STT)
    # ------------------------------------------------------------------

    @staticmethod
    def pcm_to_wav(pcm_data: bytes, output_path: str,
                   src_rate: int = 48000, src_channels: int = 2):
        """Convert raw PCM to 16kHz mono WAV via ffmpeg."""
        with tempfile.NamedTemporaryFile(suffix=".pcm", delete=False) as f:
            f.write(pcm_data)
            pcm_path = f.name
        try:
            subprocess.run(
                [
                    "ffmpeg", "-y", "-loglevel", "error",
                    "-f", "s16le",
                    "-ar", str(src_rate),
                    "-ac", str(src_channels),
                    "-i", pcm_path,
                    "-ar", "16000",
                    "-ac", "1",
                    output_path,
                ],
                check=True,
                timeout=10,
            )
        finally:
            try:
                os.unlink(pcm_path)
            except OSError:
                pass


class DiscordAdapter(BasePlatformAdapter):
    """
    Discord bot adapter.

    Handles:
    - Receiving messages from servers and DMs
    - Sending responses with Discord markdown
    - Thread support
    - Native slash commands (/ask, /reset, /status, /stop)
    - Button-based exec approvals
    - Auto-threading for long conversations
    - Reaction-based feedback
    """

    # Discord message limits
    MAX_MESSAGE_LENGTH = 2000

    # Auto-disconnect from voice channel after this many seconds of inactivity
    VOICE_TIMEOUT = 300

    def __init__(self, config: PlatformConfig):
        super().__init__(config, Platform.DISCORD)
        self._client: Optional[commands.Bot] = None
        self._ready_event = asyncio.Event()
        self._allowed_user_ids: set = set()  # For button approval authorization
        # Voice channel state (per-guild)
        self._voice_clients: Dict[int, Any] = {}  # guild_id -> VoiceClient
        self._voice_text_channels: Dict[int, int] = {}  # guild_id -> text_channel_id
        self._voice_timeout_tasks: Dict[int, asyncio.Task] = {}  # guild_id -> timeout task
        # Phase 2: voice listening
        self._voice_receivers: Dict[int, VoiceReceiver] = {}  # guild_id -> VoiceReceiver
        self._voice_listen_tasks: Dict[int, asyncio.Task] = {}  # guild_id -> listen loop
        self._voice_input_callback: Optional[Callable] = None  # set by run.py
        self._on_voice_disconnect: Optional[Callable] = None  # set by run.py
        # Track threads where the bot has participated so follow-up messages
        # in those threads don't require @mention.  Persisted to disk so the
        # set survives gateway restarts.
        self._bot_participated_threads: set = self._load_participated_threads()
        # Persistent typing indicator loops per channel (DMs don't reliably
        # show the standard typing gateway event for bots)
        self._typing_tasks: Dict[str, asyncio.Task] = {}
        self._bot_task: Optional[asyncio.Task] = None
        # Cap to prevent unbounded growth (Discord threads get archived).
        self._MAX_TRACKED_THREADS = 500
        # Dedup cache: message_id → timestamp.  Prevents duplicate bot
        # responses when Discord RESUME replays events after reconnects.
        self._seen_messages: Dict[str, float] = {}
        self._SEEN_TTL = 300   # 5 minutes
        self._SEEN_MAX = 2000  # prune threshold

    async def connect(self) -> bool:
        """Connect to Discord and start receiving events."""
        if not DISCORD_AVAILABLE:
            logger.error("[%s] discord.py not installed. Run: pip install discord.py", self.name)
            return False

        # Load opus codec for voice channel support
        if not discord.opus.is_loaded():
            import ctypes.util
            opus_path = ctypes.util.find_library("opus")
            # ctypes.util.find_library fails on macOS with Homebrew-installed libs,
            # so fall back to known Homebrew paths if needed.
            if not opus_path:
                import sys
                _homebrew_paths = (
                    "/opt/homebrew/lib/libopus.dylib",  # Apple Silicon
                    "/usr/local/lib/libopus.dylib",     # Intel Mac
                )
                if sys.platform == "darwin":
                    for _hp in _homebrew_paths:
                        if os.path.isfile(_hp):
                            opus_path = _hp
                            break
            if opus_path:
                try:
                    discord.opus.load_opus(opus_path)
                except Exception:
                    logger.warning("Opus codec found at %s but failed to load", opus_path)
            if not discord.opus.is_loaded():
                logger.warning("Opus codec not found — voice channel playback disabled")

        if not self.config.token:
            logger.error("[%s] No bot token configured", self.name)
            return False

        try:
            # Acquire scoped lock to prevent duplicate bot token usage
            from gateway.status import acquire_scoped_lock
            self._token_lock_identity = self.config.token
            acquired, existing = acquire_scoped_lock('discord-bot-token', self._token_lock_identity, metadata={'platform': 'discord'})
            if not acquired:
                owner_pid = existing.get('pid') if isinstance(existing, dict) else None
                message = f'Discord bot token already in use' + (f' (PID {owner_pid})' if owner_pid else '') + '. Stop the other gateway first.'
                logger.error('[%s] %s', self.name, message)
                self._set_fatal_error('discord_token_lock', message, retryable=False)
                return False


            # Parse allowed user entries (may contain usernames or IDs)
            allowed_env = os.getenv("DISCORD_ALLOWED_USERS", "")
            if allowed_env:
                self._allowed_user_ids = {
                    _clean_discord_id(uid) for uid in allowed_env.split(",")
                    if uid.strip()
                }

            # Set up intents.
            # Message Content is required for normal text replies.
            # Server Members is only needed when the allowlist contains usernames
            # that must be resolved to numeric IDs. Requesting privileged intents
            # that aren't enabled in the Discord Developer Portal can prevent the
            # bot from coming online at all, so avoid requesting members intent
            # unless it is actually necessary.
            intents = Intents.default()
            intents.message_content = True
            intents.dm_messages = True
            intents.guild_messages = True
            intents.members = any(not entry.isdigit() for entry in self._allowed_user_ids)
            intents.voice_states = True

            # Create bot
            self._client = commands.Bot(
                command_prefix="!",  # Not really used, we handle raw messages
                intents=intents,
            )
            adapter_self = self  # capture for closure

            # Register event handlers
            @self._client.event
            async def on_ready():
                logger.info("[%s] Connected as %s", adapter_self.name, adapter_self._client.user)

                # Resolve any usernames in the allowed list to numeric IDs
                await adapter_self._resolve_allowed_usernames()

                # Sync slash commands with Discord
                try:
                    # Sync globally first (enables DM commands)
                    try:
                        global_synced = await adapter_self._client.tree.sync()
                        logger.info("[%s] Synced %d global slash command(s)", adapter_self.name, len(global_synced))
                    except Exception as ge:
                        logger.warning("[%s] Global slash command sync failed: %s", adapter_self.name, ge)
                    # Then sync to each guild for instant availability
                    for guild in adapter_self._client.guilds:
                        try:
                            adapter_self._client.tree.copy_global_to(guild=guild)
                            guild_synced = await adapter_self._client.tree.sync(guild=guild)
                            logger.info("[%s] Synced %d slash command(s) to guild %s", adapter_self.name, len(guild_synced), guild.name)
                        except Exception as ge:
                            logger.warning("[%s] Guild sync failed for %s: %s", adapter_self.name, guild.name, ge)
                except Exception as e:  # pragma: no cover - defensive logging
                    logger.warning("[%s] Slash command sync failed: %s", adapter_self.name, e, exc_info=True)
                adapter_self._ready_event.set()

                # Send startup message to status channel
                _status_ch_id = os.getenv("DISCORD_STATUS_CHANNEL")
                if _status_ch_id:
                    try:
                        from datetime import datetime
                        _ch = adapter_self._client.get_channel(int(_status_ch_id))
                        if not _ch:
                            _ch = await adapter_self._client.fetch_channel(int(_status_ch_id))
                        if _ch:
                            await _ch.send(f"Health Bot online — {datetime.now().strftime('%Y-%m-%d %H:%M')}")
                    except Exception as _e:
                        logger.warning("Failed to send startup status: %s", _e)

            @self._client.event
            async def on_message(message: DiscordMessage):
                # Dedup: Discord RESUME replays events after reconnects (#4777)
                msg_id = str(message.id)
                now = time.time()
                if msg_id in adapter_self._seen_messages:
                    return
                adapter_self._seen_messages[msg_id] = now
                if len(adapter_self._seen_messages) > adapter_self._SEEN_MAX:
                    cutoff = now - adapter_self._SEEN_TTL
                    adapter_self._seen_messages = {
                        k: v for k, v in adapter_self._seen_messages.items()
                        if v > cutoff
                    }

                # Always ignore our own messages
                if message.author == self._client.user:
                    return

                # Ignore Discord system messages (thread renames, pins, member joins, etc.)
                # Allow both default and reply types — replies have a distinct MessageType.
                if message.type not in (discord.MessageType.default, discord.MessageType.reply):
                    return

                # Check if the message author is in the allowed user list
                if not self._is_allowed_user(str(message.author.id)):
                    return

                # Bot message filtering (DISCORD_ALLOW_BOTS):
                #   "none"     — ignore all other bots (default)
                #   "mentions" — accept bot messages only when they @mention us
                #   "all"      — accept all bot messages
                if getattr(message.author, "bot", False):
                    allow_bots = os.getenv("DISCORD_ALLOW_BOTS", "none").lower().strip()
                    if allow_bots == "none":
                        return
                    elif allow_bots == "mentions":
                        if not self._client.user or self._client.user not in message.mentions:
                            return
                    # "all" falls through to handle_message

                # If the message @mentions other users but NOT the bot, the
                # sender is talking to someone else — stay silent.  Only
                # applies in server channels; in DMs the user is always
                # talking to the bot (mentions are just references).
                # Controlled by DISCORD_IGNORE_NO_MENTION (default: true).
                _ignore_no_mention = os.getenv(
                    "DISCORD_IGNORE_NO_MENTION", "true"
                ).lower() in ("true", "1", "yes")
                if _ignore_no_mention and message.mentions and not isinstance(message.channel, discord.DMChannel):
                    _bot_mentioned = (
                        self._client.user is not None
                        and self._client.user in message.mentions
                    )
                    if not _bot_mentioned:
                        return  # Talking to someone else, don't interrupt

                await self._handle_message(message)

            @self._client.event
            async def on_voice_state_update(member, before, after):
                """Track voice channel join/leave events."""
                # Only track channels where the bot is connected
                bot_guild_ids = set(adapter_self._voice_clients.keys())
                if not bot_guild_ids:
                    return
                guild_id = member.guild.id
                if guild_id not in bot_guild_ids:
                    return
                # Ignore the bot itself
                if member == adapter_self._client.user:
                    return

                joined = before.channel is None and after.channel is not None
                left = before.channel is not None and after.channel is None
                switched = (
                    before.channel is not None
                    and after.channel is not None
                    and before.channel != after.channel
                )

                if joined or left or switched:
                    logger.info(
                        "Voice state: %s (%d) %s (guild %d)",
                        member.display_name,
                        member.id,
                        "joined " + after.channel.name if joined
                        else "left " + before.channel.name if left
                        else f"moved {before.channel.name} -> {after.channel.name}",
                        guild_id,
                    )

            # Register slash commands
            self._register_slash_commands()

            # Start the bot in background
            self._bot_task = asyncio.create_task(self._client.start(self.config.token))

            # Wait for ready
            await asyncio.wait_for(self._ready_event.wait(), timeout=120)

            self._running = True
            return True

        except asyncio.TimeoutError:
            logger.error("[%s] Timeout waiting for connection to Discord", self.name, exc_info=True)
            try:
                from gateway.status import release_scoped_lock
                if getattr(self, '_token_lock_identity', None):
                    release_scoped_lock('discord-bot-token', self._token_lock_identity)
                    self._token_lock_identity = None
            except Exception:
                pass
            return False
        except Exception as e:  # pragma: no cover - defensive logging
            logger.error("[%s] Failed to connect to Discord: %s", self.name, e, exc_info=True)
            try:
                from gateway.status import release_scoped_lock
                if getattr(self, '_token_lock_identity', None):
                    release_scoped_lock('discord-bot-token', self._token_lock_identity)
                    self._token_lock_identity = None
            except Exception:
                pass
            return False

    async def disconnect(self) -> None:
        """Disconnect from Discord."""
        # Send shutdown message to status channel
        _status_ch_id = os.getenv("DISCORD_STATUS_CHANNEL")
        if _status_ch_id and self._client and not self._client.is_closed():
            try:
                from datetime import datetime
                _ch = self._client.get_channel(int(_status_ch_id))
                if _ch:
                    await _ch.send(f"Health Bot going offline — {datetime.now().strftime('%Y-%m-%d %H:%M')}")
            except Exception:
                pass
        # Clean up all active voice connections before closing the client
        for guild_id in list(self._voice_clients.keys()):
            try:
                await self.leave_voice_channel(guild_id)
            except Exception as e:  # pragma: no cover - defensive logging
                logger.debug("[%s] Error leaving voice channel %s: %s", self.name, guild_id, e)

        if self._client:
            try:
                await self._client.close()
            except Exception as e:  # pragma: no cover - defensive logging
                logger.warning("[%s] Error during disconnect: %s", self.name, e, exc_info=True)

        self._running = False
        self._client = None
        self._ready_event.clear()

        # Release the token lock
        try:
            from gateway.status import release_scoped_lock
            if getattr(self, '_token_lock_identity', None):
                release_scoped_lock('discord-bot-token', self._token_lock_identity)
                self._token_lock_identity = None
        except Exception:
            pass

        logger.info("[%s] Disconnected", self.name)

    async def _add_reaction(self, message: Any, emoji: str) -> bool:
        """Add an emoji reaction to a Discord message."""
        if not message or not hasattr(message, "add_reaction"):
            return False
        try:
            await message.add_reaction(emoji)
            return True
        except Exception as e:
            logger.debug("[%s] add_reaction failed (%s): %s", self.name, emoji, e)
            return False

    async def _remove_reaction(self, message: Any, emoji: str) -> bool:
        """Remove the bot's own emoji reaction from a Discord message."""
        if not message or not hasattr(message, "remove_reaction") or not self._client or not self._client.user:
            return False
        try:
            await message.remove_reaction(emoji, self._client.user)
            return True
        except Exception as e:
            logger.debug("[%s] remove_reaction failed (%s): %s", self.name, emoji, e)
            return False

    def _reactions_enabled(self) -> bool:
        """Check if message reactions are enabled via config/env."""
        return os.getenv("DISCORD_REACTIONS", "true").lower() not in ("false", "0", "no")

    async def on_processing_start(self, event: MessageEvent) -> None:
        """Add an in-progress reaction for normal Discord message events."""
        if not self._reactions_enabled():
            return
        message = event.raw_message
        if hasattr(message, "add_reaction"):
            await self._add_reaction(message, "👀")

    async def on_processing_complete(self, event: MessageEvent, success: bool) -> None:
        """Swap the in-progress reaction for a final success/failure reaction."""
        if not self._reactions_enabled():
            return
        message = event.raw_message
        if hasattr(message, "add_reaction"):
            await self._remove_reaction(message, "👀")
            await self._add_reaction(message, "✅" if success else "❌")

    async def send(
        self,
        chat_id: str,
        content: str,
        reply_to: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None
    ) -> SendResult:
        """Send a message to a Discord channel."""
        if not self._client:
            return SendResult(success=False, error="Not connected")

        try:
            # Get the channel
            channel = self._client.get_channel(int(chat_id))
            if not channel:
                channel = await self._client.fetch_channel(int(chat_id))

            if not channel:
                return SendResult(success=False, error=f"Channel {chat_id} not found")

            # Format and split message if needed
            formatted = self.format_message(content)

            # If response exceeds line threshold, send as file attachment
            _file_line_threshold = int(os.getenv("DISCORD_FILE_LINE_THRESHOLD", "0"))
            if _file_line_threshold > 0 and formatted.count("\n") >= _file_line_threshold:
                import tempfile
                import textwrap
                with tempfile.NamedTemporaryFile(mode="w", suffix=".md", prefix="response_", delete=False) as tmp:
                    wrapped = "\n".join(
                        "\n".join(textwrap.wrap(line, width=60, break_long_words=False, break_on_hyphens=False)) if line.strip() else line
                        for line in formatted.split("\n")
                    )
                    tmp.write(wrapped)
                    tmp_path = tmp.name
                try:
                    preview = "\n".join(formatted.split("\n")[:3])
                    if len(preview) > 200:
                        preview = preview[:200] + "..."
                    ref = None
                    if reply_to:
                        try:
                            ref = await channel.fetch_message(int(reply_to))
                        except Exception:
                            pass
                    msg = await channel.send(
                        content=preview,
                        file=discord.File(tmp_path, filename="response.md"),
                        reference=ref,
                    )
                    return SendResult(success=True, message_id=str(msg.id))
                finally:
                    os.unlink(tmp_path)

            chunks = self.truncate_message(formatted, self.MAX_MESSAGE_LENGTH)

            message_ids = []
            reference = None

            if reply_to:
                try:
                    ref_msg = await channel.fetch_message(int(reply_to))
                    reference = ref_msg
                except Exception as e:
                    logger.debug("Could not fetch reply-to message: %s", e)

            for i, chunk in enumerate(chunks):
                chunk_reference = reference if i == 0 else None
                try:
                    msg = await channel.send(
                        content=chunk,
                        reference=chunk_reference,
                    )
                except Exception as e:
                    err_text = str(e)
                    if (
                        chunk_reference is not None
                        and "error code: 50035" in err_text
                        and "Cannot reply to a system message" in err_text
                    ):
                        logger.warning(
                            "[%s] Reply target %s is a Discord system message; retrying send without reply reference",
                            self.name,
                            reply_to,
                        )
                        msg = await channel.send(
                            content=chunk,
                            reference=None,
                        )
                    else:
                        raise
                message_ids.append(str(msg.id))

            return SendResult(
                success=True,
                message_id=message_ids[0] if message_ids else None,
                raw_response={"message_ids": message_ids}
            )

        except Exception as e:  # pragma: no cover - defensive logging
            logger.error("[%s] Failed to send Discord message: %s", self.name, e, exc_info=True)
            return SendResult(success=False, error=str(e))

    async def edit_message(
        self,
        chat_id: str,
        message_id: str,
        content: str,
    ) -> SendResult:
        """Edit a previously sent Discord message."""
        if not self._client:
            return SendResult(success=False, error="Not connected")
        try:
            channel = self._client.get_channel(int(chat_id))
            if not channel:
                channel = await self._client.fetch_channel(int(chat_id))
            msg = await channel.fetch_message(int(message_id))
            formatted = self.format_message(content)
            if len(formatted) > self.MAX_MESSAGE_LENGTH:
                formatted = formatted[:self.MAX_MESSAGE_LENGTH - 3] + "..."
            await msg.edit(content=formatted)
            return SendResult(success=True, message_id=message_id)
        except Exception as e:  # pragma: no cover - defensive logging
            logger.error("[%s] Failed to edit Discord message %s: %s", self.name, message_id, e, exc_info=True)
            return SendResult(success=False, error=str(e))

    async def _send_file_attachment(
        self,
        chat_id: str,
        file_path: str,
        caption: Optional[str] = None,
        file_name: Optional[str] = None,
    ) -> SendResult:
        """Send a local file as a Discord attachment."""
        if not self._client:
            return SendResult(success=False, error="Not connected")

        channel = self._client.get_channel(int(chat_id))
        if not channel:
            channel = await self._client.fetch_channel(int(chat_id))
        if not channel:
            return SendResult(success=False, error=f"Channel {chat_id} not found")

        filename = file_name or os.path.basename(file_path)
        with open(file_path, "rb") as fh:
            file = discord.File(fh, filename=filename)
            msg = await channel.send(content=caption if caption else None, file=file)
        return SendResult(success=True, message_id=str(msg.id))

    async def play_tts(
        self,
        chat_id: str,
        audio_path: str,
        **kwargs,
    ) -> SendResult:
        """Play auto-TTS audio.

        When the bot is in a voice channel for this chat's guild, play
        directly in the VC instead of sending as a file attachment.
        """
        for gid, text_ch_id in self._voice_text_channels.items():
            if str(text_ch_id) == str(chat_id) and self.is_in_voice_channel(gid):
                logger.info("[%s] Playing TTS in voice channel (guild=%d)", self.name, gid)
                success = await self.play_in_voice_channel(gid, audio_path)
                return SendResult(success=success)
        return await self.send_voice(chat_id=chat_id, audio_path=audio_path, **kwargs)

    async def send_voice(
        self,
        chat_id: str,
        audio_path: str,
        caption: Optional[str] = None,
        reply_to: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
        **kwargs,
    ) -> SendResult:
        """Send audio as a Discord file attachment."""
        try:
            import io

            channel = self._client.get_channel(int(chat_id))
            if not channel:
                channel = await self._client.fetch_channel(int(chat_id))
            if not channel:
                return SendResult(success=False, error=f"Channel {chat_id} not found")

            if not os.path.exists(audio_path):
                return SendResult(success=False, error=f"Audio file not found: {audio_path}")

            filename = os.path.basename(audio_path)

            with open(audio_path, "rb") as f:
                file_data = f.read()

            # Try sending as a native voice message via raw API (flags=8192).
            try:
                import base64

                duration_secs = 5.0
                try:
                    from mutagen.oggopus import OggOpus
                    info = OggOpus(audio_path)
                    duration_secs = info.info.length
                except Exception:
                    duration_secs = max(1.0, len(file_data) / 2000.0)

                waveform_bytes = bytes([128] * 256)
                waveform_b64 = base64.b64encode(waveform_bytes).decode()

                import json as _json
                payload = _json.dumps({
                    "flags": 8192,
                    "attachments": [{
                        "id": "0",
                        "filename": "voice-message.ogg",
                        "duration_secs": round(duration_secs, 2),
                        "waveform": waveform_b64,
                    }],
                })
                form = [
                    {"name": "payload_json", "value": payload},
                    {
                        "name": "files[0]",
                        "value": file_data,
                        "filename": "voice-message.ogg",
                        "content_type": "audio/ogg",
                    },
                ]
                msg_data = await self._client.http.request(
                    discord.http.Route("POST", "/channels/{channel_id}/messages", channel_id=channel.id),
                    form=form,
                )
                return SendResult(success=True, message_id=str(msg_data["id"]))
            except Exception as voice_err:
                logger.debug("Voice message flag failed, falling back to file: %s", voice_err)
                file = discord.File(io.BytesIO(file_data), filename=filename)
                msg = await channel.send(file=file)
                return SendResult(success=True, message_id=str(msg.id))
        except Exception as e:  # pragma: no cover - defensive logging
            logger.error("[%s] Failed to send audio, falling back to base adapter: %s", self.name, e, exc_info=True)
            return await super().send_voice(chat_id, audio_path, caption, reply_to, metadata=metadata)

    # ------------------------------------------------------------------
    # Voice channel methods (join / leave / play)
    # ------------------------------------------------------------------

    async def join_voice_channel(self, channel) -> bool:
        """Join a Discord voice channel. Returns True on success."""
        if not self._client or not DISCORD_AVAILABLE:
            return False
        guild_id = channel.guild.id

        # Already connected in this guild?
        existing = self._voice_clients.get(guild_id)
        if existing and existing.is_connected():
            if existing.channel.id == channel.id:
                self._reset_voice_timeout(guild_id)
                return True
            await existing.move_to(channel)
            self._reset_voice_timeout(guild_id)
            return True

        vc = await channel.connect()
        self._voice_clients[guild_id] = vc
        self._reset_voice_timeout(guild_id)

        # Start voice receiver (Phase 2: listen to users)
        try:
            receiver = VoiceReceiver(vc, allowed_user_ids=self._allowed_user_ids)
            receiver.start()
            self._voice_receivers[guild_id] = receiver
            self._voice_listen_tasks[guild_id] = asyncio.ensure_future(
                self._voice_listen_loop(guild_id)
            )
        except Exception as e:
            logger.warning("Voice receiver failed to start: %s", e)

        return True

    async def leave_voice_channel(self, guild_id: int) -> None:
        """Disconnect from the voice channel in a guild."""
        # Stop voice receiver first
        receiver = self._voice_receivers.pop(guild_id, None)
        if receiver:
            receiver.stop()
        listen_task = self._voice_listen_tasks.pop(guild_id, None)
        if listen_task:
            listen_task.cancel()

        vc = self._voice_clients.pop(guild_id, None)
        if vc and vc.is_connected():
            await vc.disconnect()
        task = self._voice_timeout_tasks.pop(guild_id, None)
        if task:
            task.cancel()
        self._voice_text_channels.pop(guild_id, None)

    # Maximum seconds to wait for voice playback before giving up
    PLAYBACK_TIMEOUT = 120

    async def play_in_voice_channel(self, guild_id: int, audio_path: str) -> bool:
        """Play an audio file in the connected voice channel."""
        vc = self._voice_clients.get(guild_id)
        if not vc or not vc.is_connected():
            return False

        # Pause voice receiver while playing (echo prevention)
        receiver = self._voice_receivers.get(guild_id)
        if receiver:
            receiver.pause()

        try:
            # Wait for current playback to finish (with timeout)
            wait_start = time.monotonic()
            while vc.is_playing():
                if time.monotonic() - wait_start > self.PLAYBACK_TIMEOUT:
                    logger.warning("Timed out waiting for previous playback to finish")
                    vc.stop()
                    break
                await asyncio.sleep(0.1)

            done = asyncio.Event()
            loop = asyncio.get_running_loop()

            def _after(error):
                if error:
                    logger.error("Voice playback error: %s", error)
                loop.call_soon_threadsafe(done.set)

            source = discord.FFmpegPCMAudio(audio_path)
            source = discord.PCMVolumeTransformer(source, volume=1.0)
            vc.play(source, after=_after)
            try:
                await asyncio.wait_for(done.wait(), timeout=self.PLAYBACK_TIMEOUT)
            except asyncio.TimeoutError:
                logger.warning("Voice playback timed out after %ds", self.PLAYBACK_TIMEOUT)
                vc.stop()
            self._reset_voice_timeout(guild_id)
            return True
        finally:
            if receiver:
                receiver.resume()

    async def get_user_voice_channel(self, guild_id: int, user_id: str):
        """Return the voice channel the user is currently in, or None."""
        if not self._client:
            return None
        guild = self._client.get_guild(guild_id)
        if not guild:
            return None
        member = guild.get_member(int(user_id))
        if not member or not member.voice:
            return None
        return member.voice.channel

    def _reset_voice_timeout(self, guild_id: int) -> None:
        """Reset the auto-disconnect inactivity timer."""
        task = self._voice_timeout_tasks.pop(guild_id, None)
        if task:
            task.cancel()
        self._voice_timeout_tasks[guild_id] = asyncio.ensure_future(
            self._voice_timeout_handler(guild_id)
        )

    async def _voice_timeout_handler(self, guild_id: int) -> None:
        """Auto-disconnect after VOICE_TIMEOUT seconds of inactivity."""
        try:
            await asyncio.sleep(self.VOICE_TIMEOUT)
        except asyncio.CancelledError:
            return
        text_ch_id = self._voice_text_channels.get(guild_id)
        await self.leave_voice_channel(guild_id)
        # Notify the runner so it can clean up voice_mode state
        if self._on_voice_disconnect and text_ch_id:
            try:
                self._on_voice_disconnect(str(text_ch_id))
            except Exception:
                pass
        if text_ch_id and self._client:
            ch = self._client.get_channel(text_ch_id)
            if ch:
                try:
                    await ch.send("Left voice channel (inactivity timeout).")
                except Exception:
                    pass

    def is_in_voice_channel(self, guild_id: int) -> bool:
        """Check if the bot is connected to a voice channel in this guild."""
        vc = self._voice_clients.get(guild_id)
        return vc is not None and vc.is_connected()

    def get_voice_channel_info(self, guild_id: int) -> Optional[Dict[str, Any]]:
        """Return voice channel awareness info for the given guild.

        Returns None if the bot is not in a voice channel.  Otherwise
        returns a dict with channel name, member list, count, and
        currently-speaking user IDs (from SSRC mapping).
        """
        vc = self._voice_clients.get(guild_id)
        if not vc or not vc.is_connected():
            return None

        channel = vc.channel
        if not channel:
            return None

        # Members currently in the voice channel (includes bot)
        members_info = []
        bot_user = self._client.user if self._client else None
        for m in channel.members:
            if bot_user and m.id == bot_user.id:
                continue  # skip the bot itself
            members_info.append({
                "user_id": m.id,
                "display_name": m.display_name,
                "is_bot": m.bot,
            })

        # Currently speaking users (from SSRC mapping + active buffers)
        speaking_user_ids: set = set()
        receiver = self._voice_receivers.get(guild_id)
        if receiver:
            import time as _time
            now = _time.monotonic()
            with receiver._lock:
                for ssrc, last_t in receiver._last_packet_time.items():
                    # Consider "speaking" if audio received within last 2 seconds
                    if now - last_t < 2.0:
                        uid = receiver._ssrc_to_user.get(ssrc)
                        if uid:
                            speaking_user_ids.add(uid)

        # Tag speaking status on members
        for info in members_info:
            info["is_speaking"] = info["user_id"] in speaking_user_ids

        return {
            "channel_name": channel.name,
            "member_count": len(members_info),
            "members": members_info,
            "speaking_count": len(speaking_user_ids),
        }

    def get_voice_channel_context(self, guild_id: int) -> str:
        """Return a human-readable voice channel context string.

        Suitable for injection into the system/ephemeral prompt so the
        agent is always aware of voice channel state.
        """
        info = self.get_voice_channel_info(guild_id)
        if not info:
            return ""

        parts = [f"[Voice channel: #{info['channel_name']} — {info['member_count']} participant(s)]"]
        for m in info["members"]:
            status = " (speaking)" if m["is_speaking"] else ""
            parts.append(f"  - {m['display_name']}{status}")

        return "\n".join(parts)

    # ------------------------------------------------------------------
    # Voice listening (Phase 2)
    # ------------------------------------------------------------------

    # UDP keepalive interval in seconds — prevents Discord from dropping
    # the UDP route after ~60s of silence.
    _KEEPALIVE_INTERVAL = 15

    async def _voice_listen_loop(self, guild_id: int):
        """Periodically check for completed utterances and process them."""
        receiver = self._voice_receivers.get(guild_id)
        if not receiver:
            return
        last_keepalive = time.monotonic()
        try:
            while receiver._running:
                await asyncio.sleep(0.2)

                # Send periodic UDP keepalive to prevent Discord from
                # dropping the UDP session after ~60s of silence.
                now = time.monotonic()
                if now - last_keepalive >= self._KEEPALIVE_INTERVAL:
                    last_keepalive = now
                    try:
                        vc = self._voice_clients.get(guild_id)
                        if vc and vc.is_connected():
                            vc._connection.send_packet(b'\xf8\xff\xfe')
                    except Exception:
                        pass

                completed = receiver.check_silence()
                for user_id, pcm_data in completed:
                    if not self._is_allowed_user(str(user_id)):
                        continue
                    await self._process_voice_input(guild_id, user_id, pcm_data)
        except asyncio.CancelledError:
            pass
        except Exception as e:
            logger.error("Voice listen loop error: %s", e, exc_info=True)

    async def _process_voice_input(self, guild_id: int, user_id: int, pcm_data: bytes):
        """Convert PCM -> WAV -> STT -> callback."""
        from tools.voice_mode import is_whisper_hallucination

        tmp_f = tempfile.NamedTemporaryFile(suffix=".wav", prefix="vc_listen_", delete=False)
        wav_path = tmp_f.name
        tmp_f.close()
        try:
            await asyncio.to_thread(VoiceReceiver.pcm_to_wav, pcm_data, wav_path)

            from tools.transcription_tools import transcribe_audio, get_stt_model_from_config
            stt_model = get_stt_model_from_config()
            result = await asyncio.to_thread(transcribe_audio, wav_path, model=stt_model)

            if not result.get("success"):
                return
            transcript = result.get("transcript", "").strip()
            if not transcript or is_whisper_hallucination(transcript):
                return

            logger.info("Voice input from user %d: %s", user_id, transcript[:100])

            if self._voice_input_callback:
                await self._voice_input_callback(
                    guild_id=guild_id,
                    user_id=user_id,
                    transcript=transcript,
                )
        except Exception as e:
            logger.warning("Voice input processing failed: %s", e, exc_info=True)
        finally:
            try:
                os.unlink(wav_path)
            except OSError:
                pass

    def _is_allowed_user(self, user_id: str) -> bool:
        """Check if user is in DISCORD_ALLOWED_USERS."""
        if not self._allowed_user_ids:
            return True
        return user_id in self._allowed_user_ids

    async def send_image_file(
        self,
        chat_id: str,
        image_path: str,
        caption: Optional[str] = None,
        reply_to: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> SendResult:
        """Send a local image file natively as a Discord file attachment."""
        try:
            return await self._send_file_attachment(chat_id, image_path, caption)
        except FileNotFoundError:
            return SendResult(success=False, error=f"Image file not found: {image_path}")
        except Exception as e:  # pragma: no cover - defensive logging
            logger.error("[%s] Failed to send local image, falling back to base adapter: %s", self.name, e, exc_info=True)
            return await super().send_image_file(chat_id, image_path, caption, reply_to, metadata=metadata)

    async def send_image(
        self,
        chat_id: str,
        image_url: str,
        caption: Optional[str] = None,
        reply_to: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> SendResult:
        """Send an image natively as a Discord file attachment."""
        if not self._client:
            return SendResult(success=False, error="Not connected")

        try:
            import aiohttp

            channel = self._client.get_channel(int(chat_id))
            if not channel:
                channel = await self._client.fetch_channel(int(chat_id))
            if not channel:
                return SendResult(success=False, error=f"Channel {chat_id} not found")

            # Download the image and send as a Discord file attachment
            # (Discord renders attachments inline, unlike plain URLs)
            async with aiohttp.ClientSession() as session:
                async with session.get(image_url, timeout=aiohttp.ClientTimeout(total=30)) as resp:
                    if resp.status != 200:
                        raise Exception(f"Failed to download image: HTTP {resp.status}")

                    image_data = await resp.read()

                    # Determine filename from URL or content type
                    content_type = resp.headers.get("content-type", "image/png")
                    ext = "png"
                    if "jpeg" in content_type or "jpg" in content_type:
                        ext = "jpg"
                    elif "gif" in content_type:
                        ext = "gif"
                    elif "webp" in content_type:
                        ext = "webp"

                    import io
                    file = discord.File(io.BytesIO(image_data), filename=f"image.{ext}")

                    msg = await channel.send(
                        content=caption if caption else None,
                        file=file,
                    )
                    return SendResult(success=True, message_id=str(msg.id))

        except ImportError:
            logger.warning(
                "[%s] aiohttp not installed, falling back to URL. Run: pip install aiohttp",
                self.name,
                exc_info=True,
            )
            return await super().send_image(chat_id, image_url, caption, reply_to)
        except Exception as e:  # pragma: no cover - defensive logging
            logger.error(
                "[%s] Failed to send image attachment, falling back to URL: %s",
                self.name,
                e,
                exc_info=True,
            )
            return await super().send_image(chat_id, image_url, caption, reply_to)

    async def send_video(
        self,
        chat_id: str,
        video_path: str,
        caption: Optional[str] = None,
        reply_to: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> SendResult:
        """Send a local video file natively as a Discord attachment."""
        try:
            return await self._send_file_attachment(chat_id, video_path, caption)
        except FileNotFoundError:
            return SendResult(success=False, error=f"Video file not found: {video_path}")
        except Exception as e:  # pragma: no cover - defensive logging
            logger.error("[%s] Failed to send local video, falling back to base adapter: %s", self.name, e, exc_info=True)
            return await super().send_video(chat_id, video_path, caption, reply_to, metadata=metadata)

    async def send_document(
        self,
        chat_id: str,
        file_path: str,
        caption: Optional[str] = None,
        file_name: Optional[str] = None,
        reply_to: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> SendResult:
        """Send an arbitrary file natively as a Discord attachment."""
        try:
            return await self._send_file_attachment(chat_id, file_path, caption, file_name=file_name)
        except FileNotFoundError:
            return SendResult(success=False, error=f"File not found: {file_path}")
        except Exception as e:  # pragma: no cover - defensive logging
            logger.error("[%s] Failed to send document, falling back to base adapter: %s", self.name, e, exc_info=True)
            return await super().send_document(chat_id, file_path, caption, file_name, reply_to, metadata=metadata)

    async def send_typing(self, chat_id: str, metadata=None) -> None:
        """Start a persistent typing indicator for a channel.

        Discord's TYPING_START gateway event is unreliable in DMs for bots.
        Instead, start a background loop that hits the typing endpoint every
        8 seconds (typing indicator lasts ~10s).  The loop is cancelled when
        stop_typing() is called (after the response is sent).
        """
        if not self._client:
            return
        # Don't start a duplicate loop
        if chat_id in self._typing_tasks:
            return

        async def _typing_loop() -> None:
            try:
                while True:
                    try:
                        route = discord.http.Route(
                            "POST", "/channels/{channel_id}/typing",
                            channel_id=chat_id,
                        )
                        await self._client.http.request(route)
                    except asyncio.CancelledError:
                        return
                    except Exception as e:
                        logger.debug("Discord typing indicator failed for %s: %s", chat_id, e)
                        return
                    await asyncio.sleep(8)
            except asyncio.CancelledError:
                pass

        self._typing_tasks[chat_id] = asyncio.create_task(_typing_loop())

    async def stop_typing(self, chat_id: str) -> None:
        """Stop the persistent typing indicator for a channel."""
        task = self._typing_tasks.pop(chat_id, None)
        if task:
            task.cancel()
            try:
                await task
            except (asyncio.CancelledError, Exception):
                pass

    async def get_chat_info(self, chat_id: str) -> Dict[str, Any]:
        """Get information about a Discord channel."""
        if not self._client:
            return {"name": "Unknown", "type": "dm"}

        try:
            channel = self._client.get_channel(int(chat_id))
            if not channel:
                channel = await self._client.fetch_channel(int(chat_id))

            if not channel:
                return {"name": str(chat_id), "type": "dm"}

            # Determine channel type
            if isinstance(channel, discord.DMChannel):
                chat_type = "dm"
                name = channel.recipient.name if channel.recipient else str(chat_id)
            elif isinstance(channel, discord.Thread):
                chat_type = "thread"
                name = channel.name
            elif isinstance(channel, discord.TextChannel):
                chat_type = "channel"
                name = f"#{channel.name}"
                if channel.guild:
                    name = f"{channel.guild.name} / {name}"
            else:
                chat_type = "channel"
                name = getattr(channel, "name", str(chat_id))

            return {
                "name": name,
                "type": chat_type,
                "guild_id": str(channel.guild.id) if hasattr(channel, "guild") and channel.guild else None,
                "guild_name": channel.guild.name if hasattr(channel, "guild") and channel.guild else None,
            }
        except Exception as e:  # pragma: no cover - defensive logging
            logger.error("[%s] Failed to get chat info for %s: %s", self.name, chat_id, e, exc_info=True)
            return {"name": str(chat_id), "type": "dm", "error": str(e)}

    async def _resolve_allowed_usernames(self) -> None:
        """
        Resolve non-numeric entries in DISCORD_ALLOWED_USERS to Discord user IDs.

        Users can specify usernames (e.g. "teknium") or display names instead of
        raw numeric IDs.  After resolution, the env var and internal set are updated
        so authorization checks work with IDs only.
        """
        if not self._allowed_user_ids or not self._client:
            return

        numeric_ids = set()
        to_resolve = set()

        for entry in self._allowed_user_ids:
            if entry.isdigit():
                numeric_ids.add(entry)
            else:
                to_resolve.add(entry.lower())

        if not to_resolve:
            return

        print(f"[{self.name}] Resolving {len(to_resolve)} username(s): {', '.join(to_resolve)}")
        resolved_count = 0

        for guild in self._client.guilds:
            # Fetch full member list (requires members intent)
            try:
                members = guild.members
                if len(members) < guild.member_count:
                    members = [m async for m in guild.fetch_members(limit=None)]
            except Exception as e:
                logger.warning("Failed to fetch members for guild %s: %s", guild.name, e)
                continue

            for member in members:
                name_lower = member.name.lower()
                display_lower = member.display_name.lower()
                global_lower = (member.global_name or "").lower()

                matched = name_lower in to_resolve or display_lower in to_resolve or global_lower in to_resolve
                if matched:
                    uid = str(member.id)
                    numeric_ids.add(uid)
                    resolved_count += 1
                    matched_name = name_lower if name_lower in to_resolve else (
                        display_lower if display_lower in to_resolve else global_lower
                    )
                    to_resolve.discard(matched_name)
                    print(f"[{self.name}] Resolved '{matched_name}' -> {uid} ({member.name}#{member.discriminator})")

            if not to_resolve:
                break

        if to_resolve:
            print(f"[{self.name}] Could not resolve usernames: {', '.join(to_resolve)}")

        # Update internal set and env var so gateway auth checks use IDs
        self._allowed_user_ids = numeric_ids
        os.environ["DISCORD_ALLOWED_USERS"] = ",".join(sorted(numeric_ids))
        if resolved_count:
            print(f"[{self.name}] Updated DISCORD_ALLOWED_USERS with {resolved_count} resolved ID(s)")

    def format_message(self, content: str) -> str:
        """
        Format message for Discord.

        Discord uses its own markdown variant.
        """
        # Discord markdown is fairly standard, no special escaping needed
        return content

    async def _run_simple_slash(
        self,
        interaction: discord.Interaction,
        command_text: str,
        followup_msg: str | None = None,
    ) -> None:
        """Common handler for simple slash commands that dispatch a command string.

        Defers the interaction (shows "thinking..."), dispatches the command,
        then cleans up the deferred response.  If *followup_msg* is provided
        the "thinking..." indicator is replaced with that text; otherwise it
        is deleted so the channel isn't cluttered.
        """
        await interaction.response.defer(ephemeral=True)
        event = self._build_slash_event(interaction, command_text)
        await self.handle_message(event)
        try:
            if followup_msg:
                await interaction.edit_original_response(content=followup_msg)
            else:
                await interaction.delete_original_response()
        except Exception as e:
            logger.debug("Discord interaction cleanup failed: %s", e)

    def _register_slash_commands(self) -> None:
        """Register Discord slash commands on the command tree."""
        if not self._client:
            return

        tree = self._client.tree

        @tree.command(name="new", description="Start a new conversation")
        async def slash_new(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/reset", "New conversation started~")

        @tree.command(name="reset", description="Reset your Hermes session")
        async def slash_reset(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/reset", "Session reset~")

        @tree.command(name="model", description="Show or change the model")
        @discord.app_commands.describe(name="Model name (e.g. anthropic/claude-sonnet-4). Leave empty to see current.")
        async def slash_model(interaction: discord.Interaction, name: str = ""):
            await self._run_simple_slash(interaction, f"/model {name}".strip())

        @tree.command(name="reasoning", description="Show or change reasoning effort")
        @discord.app_commands.describe(effort="Reasoning effort: xhigh, high, medium, low, minimal, or none.")
        async def slash_reasoning(interaction: discord.Interaction, effort: str = ""):
            await self._run_simple_slash(interaction, f"/reasoning {effort}".strip())

        @tree.command(name="personality", description="Set a personality")
        @discord.app_commands.describe(name="Personality name. Leave empty to list available.")
        async def slash_personality(interaction: discord.Interaction, name: str = ""):
            await self._run_simple_slash(interaction, f"/personality {name}".strip())

        @tree.command(name="retry", description="Retry your last message")
        async def slash_retry(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/retry", "Retrying~")

        @tree.command(name="undo", description="Remove the last exchange")
        async def slash_undo(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/undo")

        @tree.command(name="status", description="Show Hermes session status")
        async def slash_status(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/status", "Status sent~")

        @tree.command(name="sethome", description="Set this chat as the home channel")
        async def slash_sethome(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/sethome")

        @tree.command(name="stop", description="Stop the running Hermes agent")
        async def slash_stop(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/stop", "Stop requested~")

        @tree.command(name="compress", description="Compress conversation context")
        async def slash_compress(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/compress")

        @tree.command(name="title", description="Set or show the session title")
        @discord.app_commands.describe(name="Session title. Leave empty to show current.")
        async def slash_title(interaction: discord.Interaction, name: str = ""):
            await self._run_simple_slash(interaction, f"/title {name}".strip())

        @tree.command(name="resume", description="Resume a previously-named session")
        @discord.app_commands.describe(name="Session name to resume. Leave empty to list sessions.")
        async def slash_resume(interaction: discord.Interaction, name: str = ""):
            await self._run_simple_slash(interaction, f"/resume {name}".strip())

        @tree.command(name="usage", description="Show token usage for this session")
        async def slash_usage(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/usage")

        @tree.command(name="provider", description="Show available providers")
        async def slash_provider(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/provider")

        @tree.command(name="help", description="Show available commands")
        async def slash_help(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/help")

        @tree.command(name="insights", description="Show usage insights and analytics")
        @discord.app_commands.describe(days="Number of days to analyze (default: 7)")
        async def slash_insights(interaction: discord.Interaction, days: int = 7):
            await self._run_simple_slash(interaction, f"/insights {days}")

        @tree.command(name="reload-mcp", description="Reload MCP servers from config")
        async def slash_reload_mcp(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/reload-mcp")

        @tree.command(name="voice", description="Toggle voice reply mode")
        @discord.app_commands.describe(mode="Voice mode: on, off, tts, channel, leave, or status")
        @discord.app_commands.choices(mode=[
            discord.app_commands.Choice(name="channel — join your voice channel", value="channel"),
            discord.app_commands.Choice(name="leave — leave voice channel", value="leave"),
            discord.app_commands.Choice(name="on — voice reply to voice messages", value="on"),
            discord.app_commands.Choice(name="tts — voice reply to all messages", value="tts"),
            discord.app_commands.Choice(name="off — text only", value="off"),
            discord.app_commands.Choice(name="status — show current mode", value="status"),
        ])
        async def slash_voice(interaction: discord.Interaction, mode: str = ""):
            await self._run_simple_slash(interaction, f"/voice {mode}".strip())

        @tree.command(name="update", description="Update Hermes Agent to the latest version")
        async def slash_update(interaction: discord.Interaction):
            await self._run_simple_slash(interaction, "/update", "Update initiated~")

        @tree.command(name="approve", description="Approve a pending dangerous command")
        @discord.app_commands.describe(scope="Optional: 'all', 'session', 'always', 'all session', 'all always'")
        async def slash_approve(interaction: discord.Interaction, scope: str = ""):
            await self._run_simple_slash(interaction, f"/approve {scope}".strip())

        @tree.command(name="deny", description="Deny a pending dangerous command")
        @discord.app_commands.describe(scope="Optional: 'all' to deny all pending commands")
        async def slash_deny(interaction: discord.Interaction, scope: str = ""):
            await self._run_simple_slash(interaction, f"/deny {scope}".strip())

        @tree.command(name="thread", description="Create a new thread and start a Hermes session in it")
        @discord.app_commands.describe(
            name="Thread name",
            message="Optional first message to send to Hermes in the thread",
            auto_archive_duration="Auto-archive in minutes (60, 1440, 4320, 10080)",
        )
        async def slash_thread(
            interaction: discord.Interaction,
            name: str,
            message: str = "",
            auto_archive_duration: int = 1440,
        ):
            await interaction.response.defer(ephemeral=True)
            await self._handle_thread_create_slash(interaction, name, message, auto_archive_duration)


        @tree.command(name="file", description="Show a file from the server")
        @discord.app_commands.describe(path="File path on the server (e.g. ~/pump-labs-vault/TODO.md)")
        async def slash_file(interaction: discord.Interaction, path: str):
            import os
            await interaction.response.defer()
            expanded = os.path.expanduser(path)
            if not os.path.isfile(expanded):
                await interaction.followup.send(f"File not found: {path}")
                return
            try:
                size = os.path.getsize(expanded)
                if size > 1_900:
                    # Send as attachment if too large for a message
                    await interaction.followup.send(file=discord.File(expanded))
                else:
                    with open(expanded, "r") as f:
                        text = f.read()
                    ext = os.path.splitext(expanded)[1].lstrip(".") or "txt"
                    lang = {"py": "python", "js": "javascript", "ts": "typescript", "sh": "bash", "yml": "yaml", "md": "markdown"}.get(ext, ext)
                    triple = chr(96)*3
                    await interaction.followup.send(f"**{os.path.basename(expanded)}**\n{triple}{lang}\n{text}\n{triple}")
            except Exception as e:
                await interaction.followup.send(f"Error reading file: {e}")


        @tree.command(name="ingest", description="Ingest a URL into the knowledge vault")
        @discord.app_commands.describe(
            url="URL to article, paper, or resource",
            category="Vault category (e.g. hormones, conditions, materia-medica, ray-peat, patterns, research)"
        )
        async def slash_ingest(interaction: discord.Interaction, url: str, category: str = "research"):
            import os, re, subprocess, json, sys
            await interaction.response.defer()
            vault = os.path.expanduser(os.getenv("OBSIDIAN_VAULT_PATH", "~/east-west-synthesis"))
            helper = os.path.expanduser("~/.hermes/profiles/healthbot/ingest_helper.py")
            valid_categories = ["hormones", "conditions", "materia-medica", "ray-peat", "patterns", "research", "atlas", "mappings", "references"]
            if category not in valid_categories:
                sep = ", "
                await interaction.followup.send(f"Invalid category. Choose from: {sep.join(valid_categories)}")
                return
            try:
                fetch_result = subprocess.run(
                    [sys.executable, helper, "fetch", url],
                    capture_output=True, text=True, timeout=30
                )
                if fetch_result.returncode != 0:
                    await interaction.followup.send(f"Failed to fetch URL: {fetch_result.stderr[:300]}")
                    return
                fetched = json.loads(fetch_result.stdout)
                title = fetched["title"]
                body = fetched["body"]

                api_key = os.getenv("ANTHROPIC_API_KEY", "")
                if not api_key:
                    await interaction.followup.send("No ANTHROPIC_API_KEY configured")
                    return

                prompt = f"Extract the key health/science information from this article and create an Obsidian-compatible markdown note.\n\nTitle: {title}\nURL: {url}\nContent: {body[:6000]}\n\nCreate a structured note with:\n1. YAML frontmatter (title, date, source, url, tags)\n2. Summary (2-3 sentences)\n3. Key findings or claims\n4. Mechanisms discussed\n5. Relevant compounds, hormones, or nutrients mentioned\n6. Cross-references to related concepts using [[wikilinks]]\n\nKeep it concise and factual."

                llm_result = subprocess.run(
                    [sys.executable, helper, "llm"],
                    input=prompt,
                    capture_output=True, text=True, timeout=90,
                    env={**os.environ, "ANTHROPIC_API_KEY": api_key}
                )
                if llm_result.returncode != 0:
                    await interaction.followup.send(f"LLM processing failed: {llm_result.stderr[:300]}")
                    return

                note_content = llm_result.stdout.strip()
                slug = re.sub(r'[^a-z0-9]+', '-', title.lower().strip())[:60].strip('-')
                filename = f"{slug}.md"
                filepath = os.path.join(vault, category, filename)
                os.makedirs(os.path.dirname(filepath), exist_ok=True)

                import textwrap as _tw
                wrapped_note = "\n".join(
                    "\n".join(_tw.wrap(line, width=60, break_long_words=False, break_on_hyphens=False)) if line.strip() else line
                    for line in note_content.split("\n")
                )
                with open(filepath, "w") as f:
                    f.write(note_content)

                import tempfile as _tf
                with _tf.NamedTemporaryFile(mode="w", suffix=".md", prefix="ingested_", delete=False) as tmp:
                    tmp.write(wrapped_note)
                    tmp_path = tmp.name
                try:
                    await interaction.followup.send(
                        f"Ingested into vault: `{category}/{filename}`",
                        file=discord.File(tmp_path, filename=filename),
                    )
                finally:
                    os.unlink(tmp_path)
            except Exception as e:
                await interaction.followup.send(f"Ingest failed: {str(e)[:300]}")

        # ── /tokens — per-user token usage tracking ──
        @tree.command(name="tokens", description="Check your token usage this month")
        @discord.app_commands.describe(target="Admin only: @user, 'top', or 'cost'")
        async def slash_tokens(interaction: discord.Interaction, target: str = ""):
            import sqlite3 as _sql
            from datetime import datetime as _dt, timedelta as _td
            from pathlib import Path as _P

            _DB = _P(os.environ.get("HERMES_HOME", os.path.expanduser("~/.hermes"))) / "token_usage.db"
            _ADMINS = set(os.environ.get("TOKEN_ADMIN_USERS", "").split(","))
            _LIMITS = {"Admin": 0, "Mod": 0, "Premium": 500_000, "Basic Access": 100_000}
            _DEFAULT = 50_000
            _IN_COST, _OUT_COST = 3.0, 15.0

            def _mo(): return _dt.utcnow().strftime("%Y-%m")
            def _rst():
                n = _dt.utcnow()
                return int((n.replace(day=28) + _td(days=4)).replace(day=1, hour=0, minute=0, second=0).timestamp())
            def _bar(p):
                f = int(min(p, 100) / 10)
                return "\u2588" * f + "\u2591" * (10 - f)

            uid = str(interaction.user.id)
            is_admin = uid in _ADMINS

            if not _DB.exists():
                await interaction.response.send_message("No usage data yet.", ephemeral=True)
                return

            db = _sql.connect(str(_DB))

            if not target or (not is_admin and target in ("top", "cost")):
                row = db.execute("SELECT input_tokens, output_tokens FROM token_usage WHERE user_id=? AND month=?", (uid, _mo())).fetchone()
                inp, out = (row[0], row[1]) if row else (0, 0)
                total = inp + out
                _limit = 0 if is_admin else _DEFAULT
                if _limit == 0:
                    msg = f"**Token Usage \u2014 {_mo()}**\n**{total:,}** tokens used\nTier: **Unlimited**"
                else:
                    pct = min(total / _limit * 100, 100)
                    msg = f"**Token Usage \u2014 {_mo()}**\n`[{_bar(pct)}]` {pct:.0f}%\n**{total:,}** / {_limit:,} tokens\nResets <t:{_rst()}:R>"
                if target and not is_admin:
                    msg += "\n\n*Admin access required.*"

            elif target == "top" and is_admin:
                rows = db.execute("SELECT user_id, input_tokens + output_tokens as t FROM token_usage WHERE month=? ORDER BY t DESC LIMIT 10", (_mo(),)).fetchall()
                if not rows:
                    msg = "No usage this month."
                else:
                    lines = [f"**Top Users \u2014 {_mo()}**"]
                    for i, (u, t) in enumerate(rows, 1):
                        lines.append(f"{i}. <@{u}> \u2014 **{t:,}** tokens")
                    msg = "\n".join(lines)

            elif target == "cost" and is_admin:
                row = db.execute("SELECT SUM(input_tokens), SUM(output_tokens), COUNT(DISTINCT user_id) FROM token_usage WHERE month=?", (_mo(),)).fetchone()
                inp, out, uc = (row[0] or 0, row[1] or 0, row[2] or 0)
                cost = (inp / 1e6 * _IN_COST) + (out / 1e6 * _OUT_COST)
                msg = (f"**API Cost \u2014 {_mo()}**\n"
                       f"Input: **{inp:,}** (${inp/1e6*_IN_COST:.2f})\n"
                       f"Output: **{out:,}** (${out/1e6*_OUT_COST:.2f})\n"
                       f"**Total: ${cost:.2f}** \u2014 {uc} users\n"
                       f"Resets <t:{_rst()}:R>")

            elif target.startswith("<@") and is_admin:
                tid = target.replace("<@", "").replace(">", "").replace("!", "")
                row = db.execute("SELECT input_tokens, output_tokens FROM token_usage WHERE user_id=? AND month=?", (tid, _mo())).fetchone()
                inp, out = (row[0], row[1]) if row else (0, 0)
                total = inp + out
                pct = min(total / _DEFAULT * 100, 100) if _DEFAULT > 0 else 0
                msg = (f"**Token Usage for <@{tid}> \u2014 {_mo()}**\n"
                       f"`[{_bar(pct)}]` {pct:.0f}%\n"
                       f"**{total:,}** / {_DEFAULT:,} tokens")
            else:
                msg = _format_user_usage(uid) if not target else "Unknown command. Try: `/tokens`, `/tokens top`, `/tokens cost`, `/tokens @user`"

            db.close()
            await interaction.response.send_message(msg, ephemeral=True)


        # ── /suggest — generate supplement protocol from vault knowledge ──
        @tree.command(name="suggest", description="Get a supplement regimen suggestion from the knowledge base")
        @discord.app_commands.describe(topic="What you want the regimen for (e.g. knee pain, thyroid, sleep)")
        async def slash_suggest(interaction: discord.Interaction, topic: str):
            import json as _json
            import subprocess as _sp
            import hashlib as _hl
            from pathlib import Path as _Path

            await interaction.response.defer(ephemeral=False)

            _VAULT = _Path("/knowledge-base")
            _SUPA_URL = (os.environ.get("SUPABASE_URL", "") or "https://itdtludfrlwjmjxtpvwl.supabase.co")
            _SUPA_KEY = os.environ.get("SUPABASE_SERVICE_KEY", "")
            _API_KEY = os.environ.get("ANTHROPIC_API_KEY", "")

            if not _SUPA_URL or not _SUPA_KEY or not _API_KEY:
                await interaction.followup.send("Missing configuration. Contact an admin.")
                return

            # Gather vault context — search for relevant files
            _relevant = []
            _search_dirs = ["conditions", "materia-medica", "hormones", "patterns", "mappings", "atlas"]
            _topic_lower = topic.lower()
            for _sd in _search_dirs:
                _dir = _VAULT / _sd
                if not _dir.exists():
                    continue
                for _f in _dir.rglob("*.md"):
                    _content = _f.read_text(encoding="utf-8", errors="ignore")
                    if _topic_lower in _content.lower() or _topic_lower in _f.stem.lower():
                        _relevant.append(f"## {_f.stem}\n{_content[:1500]}")
                        if len(_relevant) >= 8:
                            break

            _vault_context = "\n\n".join(_relevant) if _relevant else "No specific vault entries found for this topic."

            # Call Claude to build protocol
            import urllib.request as _req
            _body = _json.dumps({
                "model": "claude-sonnet-4-6",
                "max_tokens": 2000,
                "messages": [{"role": "user", "content": f"""You are a supplement protocol designer with access to a curated health knowledge base.

Based on the following vault research, create a supplement regimen for: {topic}

VAULT CONTEXT:
{_vault_context}

Return ONLY valid JSON in this exact format (no markdown, no explanation before or after):
{{
  "version": 1,
  "name": "<Protocol Name>",
  "source": "healthbot",
  "reasoning": "<2-3 sentences explaining why these supplements were chosen>",
  "groups": [
    {{
      "name": "<Group Name (e.g. Morning Stack)>",
      "schedule_type": "ed",
      "schedule_days": ["sun","mon","tue","wed","thu","fri","sat"],
      "time_of_day": ["morning"],
      "color": "#00d4aa",
      "medications": [
        {{"name": "Supplement Name", "dose": "100", "unit": "mg"}}
      ]
    }}
  ]
}}

Rules:
- Use evidence from the vault context when available
- Include 3-8 supplements total across groups
- Group by time of day (morning/evening) or purpose
- Use standard doses from established research
- Include the reasoning field explaining your choices"""}]
            }).encode()

            _headers = {
                "Content-Type": "application/json",
                "x-api-key": _API_KEY,
                "anthropic-version": "2023-06-01"
            }

            try:
                _rq = _req.Request("https://api.anthropic.com/v1/messages", data=_body, headers=_headers, method="POST")
                with _req.urlopen(_rq, timeout=30) as _resp:
                    _result = _json.loads(_resp.read().decode())
                _text = _result["content"][0]["text"]
            except Exception as _e:
                await interaction.followup.send(f"Failed to generate protocol: {_e}")
                return

            # Parse JSON from response
            try:
                _start = _text.index("{")
                _end = _text.rindex("}") + 1
                _proto = _json.loads(_text[_start:_end])
            except (ValueError, _json.JSONDecodeError) as _e:
                await interaction.followup.send(f"Failed to parse protocol. Try again or rephrase your request.")
                return

            # Generate code
            _code = f"pl-{_hl.md5(topic.encode()).hexdigest()[:6]}-{int(__import__('time').time()) % 10000}"

            # Save to pending_protocols
            try:
                _save_body = _json.dumps({
                    "code": _code,
                    "protocol": _proto,
                    "created_by_discord_id": str(interaction.user.id)
                }).encode()
                _save_headers = {
                    "Content-Type": "application/json",
                    "apikey": _SUPA_KEY,
                    "Authorization": f"Bearer {_SUPA_KEY}",
                    "Prefer": "return=minimal"
                }
                _save_rq = _req.Request(f"{_SUPA_URL}/rest/v1/pending_protocols", data=_save_body, headers=_save_headers, method="POST")
                _req.urlopen(_save_rq, timeout=10)
            except Exception as _e:
                await interaction.followup.send(f"Protocol generated but failed to save: {_e}")
                return

            # Format response
            _reasoning = _proto.get("reasoning", "")
            _groups_text = []
            for _g in _proto.get("groups", []):
                _meds = "\n".join(f"  • {m['name']} {m.get('dose','')} {m.get('unit','')}" for m in _g.get("medications", []))
                _groups_text.append(f"**{_g['name']}**\n{_meds}")

            _msg = (
                f"**{_proto.get('name', 'Supplement Protocol')}** — for *{topic}*\n\n"
                + "\n\n".join(_groups_text)
                + f"\n\n*{_reasoning}*"
                + f"\n_Expires in 24 hours. Code: `{_code}`_"
            )

            # Import button — one tap, no copy-paste
            import discord.ui as _dui
            _view = _dui.View(timeout=86400)

            class _ImportButton(_dui.Button):
                def __init__(self):
                    super().__init__(label="Import to Sup Tracker", style=discord.ButtonStyle.green, custom_id=f"import:{_code}")

                async def callback(self, btn_interaction: discord.Interaction):
                    _btn_uid = str(btn_interaction.user.id)
                    await btn_interaction.response.defer(ephemeral=False)
                    _btn_headers = {"apikey": _SUPA_KEY, "Authorization": f"Bearer {_SUPA_KEY}", "Content-Type": "application/json"}

                    # Look up linked account
                    try:
                        _link_rq = _req.Request(f"{_SUPA_URL}/rest/v1/linked_accounts?provider=eq.discord&provider_user_id=eq.{_btn_uid}&select=user_id", headers=_btn_headers)
                        with _req.urlopen(_link_rq, timeout=10) as _r:
                            _links = _json.loads(_r.read().decode())
                    except Exception:
                        _links = []

                    if not _links:
                        await btn_interaction.followup.send("Your Discord isn't linked. Run `/link email:your@email.com` first.", ephemeral=True)
                        return

                    _uid = _links[0]["user_id"]
                    _p_code = self.custom_id.split(":", 1)[1]

                    # Get pending protocol
                    try:
                        _p_rq = _req.Request(f"{_SUPA_URL}/rest/v1/pending_protocols?code=eq.{_p_code}&select=protocol", headers=_btn_headers)
                        with _req.urlopen(_p_rq, timeout=10) as _r:
                            _pend = _json.loads(_r.read().decode())
                    except Exception:
                        _pend = []

                    if not _pend:
                        await btn_interaction.followup.send("Protocol expired or already imported.", ephemeral=True)
                        return

                    _pp = _pend[0]["protocol"]
                    _gc, _mc = 0, 0

                    for _ig in _pp.get("groups", []):
                        try:
                            _gb = _json.dumps({"user_id": _uid, "name": (_ig.get("name") or "Imported")[:100], "schedule_type": _ig.get("schedule_type", "ed"), "schedule_days": _ig.get("schedule_days", []), "time_of_day": _ig.get("time_of_day", ["morning"]), "color": _ig.get("color", "#00d4aa"), "active": True, "sort_order": 0}).encode()
                            _grq = _req.Request(f"{_SUPA_URL}/rest/v1/groups", data=_gb, headers={**_btn_headers, "Prefer": "return=representation"}, method="POST")
                            with _req.urlopen(_grq, timeout=10) as _r:
                                _ng = _json.loads(_r.read().decode())[0]
                            _gc += 1
                        except Exception:
                            continue
                        for _mi, _im in enumerate(_ig.get("medications", [])):
                            _mn = str(_im.get("name", ""))[:100]
                            if not _mn: continue
                            try:
                                _nb = _json.dumps({"input_name": _mn}).encode()
                                _nrq = _req.Request(f"{_SUPA_URL}/rest/v1/rpc/normalize_supplement_name", data=_nb, headers=_btn_headers, method="POST")
                                with _req.urlopen(_nrq, timeout=10) as _r:
                                    _nd = _json.loads(_r.read().decode())
                                if _nd and _nd[0].get("canonical_name"): _mn = _nd[0]["canonical_name"]
                            except Exception: pass
                            try:
                                _mb = _json.dumps({"group_id": _ng["id"], "name": _mn, "dose": str(_im.get("dose", ""))[:50], "unit": str(_im.get("unit", ""))[:20], "sort_order": _mi, "schedule_type": _im.get("schedule_type"), "schedule_days": _im.get("schedule_days"), "time_of_day": _im.get("time_of_day"), "frequency_days": _im.get("frequency_days")}).encode()
                                _mrq = _req.Request(f"{_SUPA_URL}/rest/v1/medications", data=_mb, headers={**_btn_headers, "Prefer": "return=minimal"}, method="POST")
                                _req.urlopen(_mrq, timeout=10)
                                _mc += 1
                            except Exception: pass

                    # Delete pending + disable button
                    try:
                        _drq = _req.Request(f"{_SUPA_URL}/rest/v1/pending_protocols?code=eq.{_p_code}", headers=_btn_headers, method="DELETE")
                        _req.urlopen(_drq, timeout=10)
                    except Exception: pass
                    self.disabled = True
                    self.label = "Imported"
                    try: await btn_interaction.message.edit(view=_view)
                    except Exception: pass
                    await btn_interaction.followup.send(f"Imported **{_pp.get('name', 'Protocol')}** — {_gc} group{'s' if _gc != 1 else ''}, {_mc} supplement{'s' if _mc != 1 else ''}. Open Sup Tracker to see it.")

            _view.add_item(_ImportButton())
            await interaction.followup.send(_msg, view=_view)


        # ── /link — link Discord to Sup Tracker ──
        @tree.command(name="link", description="Link your Discord account to Sup Tracker")
        @discord.app_commands.describe(email="Your Sup Tracker email address")
        async def slash_link(interaction: discord.Interaction, email: str = ""):
            import json as _json
            import urllib.request as _req

            _SUPA_URL = (os.environ.get("SUPABASE_URL", "") or "https://itdtludfrlwjmjxtpvwl.supabase.co")
            _SUPA_KEY = os.environ.get("SUPABASE_SERVICE_KEY", "")
            if not _SUPA_URL or not _SUPA_KEY:
                await interaction.response.send_message("Missing configuration.", ephemeral=True)
                return

            _headers = {"apikey": _SUPA_KEY, "Authorization": f"Bearer {_SUPA_KEY}", "Content-Type": "application/json"}
            uid = str(interaction.user.id)

            # Check if already linked
            try:
                _rq = _req.Request(f"{_SUPA_URL}/rest/v1/linked_accounts?provider=eq.discord&provider_user_id=eq.{uid}&select=user_id", headers=_headers)
                with _req.urlopen(_rq, timeout=10) as _resp:
                    existing = _json.loads(_resp.read().decode())
                if existing:
                    await interaction.response.send_message("Your Discord is already linked to Sup Tracker.", ephemeral=True)
                    return
            except Exception:
                pass

            if not email:
                await interaction.response.send_message(
                    "To link your Discord to Sup Tracker:\n"
                    "1. Sign up at **sups.pumplabs.dev** (Google or email)\n"
                    "2. Run `/link email:your@email.com`",
                    ephemeral=True
                )
                return

            # Look up profile by email
            try:
                _clean = email.lower().strip()
                _rq = _req.Request(f"{_SUPA_URL}/rest/v1/profiles?email=eq.{_clean}&select=id,email,display_name", headers=_headers)
                with _req.urlopen(_rq, timeout=10) as _resp:
                    profiles = _json.loads(_resp.read().decode())
            except Exception as _e:
                await interaction.response.send_message(f"Error looking up account: {_e}", ephemeral=True)
                return

            if not profiles:
                await interaction.response.send_message(f"No Sup Tracker account found for `{email}`. Sign up first at **sups.pumplabs.dev**.", ephemeral=True)
                return

            profile = profiles[0]

            # Create the link
            try:
                _body = _json.dumps({
                    "user_id": profile["id"],
                    "provider": "discord",
                    "provider_user_id": uid,
                    "provider_username": interaction.user.name,
                }).encode()
                _save_headers = {**_headers, "Prefer": "return=minimal"}
                _rq = _req.Request(f"{_SUPA_URL}/rest/v1/linked_accounts", data=_body, headers=_save_headers, method="POST")
                _req.urlopen(_rq, timeout=10)
            except Exception as _e:
                await interaction.response.send_message(f"Failed to link: {_e}", ephemeral=True)
                return

            await interaction.response.send_message(
                f"Linked! Your Discord is now connected to Sup Tracker ({profile.get('display_name') or profile.get('email')}).",
                ephemeral=True
            )

        # ── /import — import a pending protocol to Sup Tracker ──
        @tree.command(name="import-regimen", description="Import a supplement protocol to your Sup Tracker")
        @discord.app_commands.describe(code="Protocol code from /suggest")
        async def slash_import(interaction: discord.Interaction, code: str):
            import json as _json
            import urllib.request as _req

            _SUPA_URL = (os.environ.get("SUPABASE_URL", "") or "https://itdtludfrlwjmjxtpvwl.supabase.co")
            _SUPA_KEY = os.environ.get("SUPABASE_SERVICE_KEY", "")
            if not _SUPA_URL or not _SUPA_KEY:
                await interaction.response.send_message("Missing configuration.", ephemeral=True)
                return

            _headers = {"apikey": _SUPA_KEY, "Authorization": f"Bearer {_SUPA_KEY}", "Content-Type": "application/json"}
            uid = str(interaction.user.id)

            await interaction.response.defer(ephemeral=False)

            # Look up linked account
            try:
                _rq = _req.Request(f"{_SUPA_URL}/rest/v1/linked_accounts?provider=eq.discord&provider_user_id=eq.{uid}&select=user_id", headers=_headers)
                with _req.urlopen(_rq, timeout=10) as _resp:
                    links = _json.loads(_resp.read().decode())
            except Exception:
                links = []

            if not links:
                await interaction.followup.send("Your Discord isn't linked to Sup Tracker. Run `/link email:your@email.com` first.")
                return

            user_id = links[0]["user_id"]

            # Look up pending protocol
            try:
                _rq = _req.Request(f"{_SUPA_URL}/rest/v1/pending_protocols?code=eq.{code}&select=protocol", headers=_headers)
                with _req.urlopen(_rq, timeout=10) as _resp:
                    pending = _json.loads(_resp.read().decode())
            except Exception:
                pending = []

            if not pending:
                await interaction.followup.send("Protocol not found or expired. Check the code.")
                return

            proto = pending[0]["protocol"]
            groups_created = 0
            meds_created = 0

            for group in proto.get("groups", []):
                # Create group
                try:
                    _body = _json.dumps({
                        "user_id": user_id,
                        "name": (group.get("name") or "Imported")[:100],
                        "schedule_type": group.get("schedule_type", "ed"),
                        "schedule_days": group.get("schedule_days", []),
                        "time_of_day": group.get("time_of_day", ["morning"]),
                        "color": group.get("color", "#00d4aa"),
                        "active": True,
                        "sort_order": 0,
                    }).encode()
                    _save_headers = {**_headers, "Prefer": "return=representation"}
                    _rq = _req.Request(f"{_SUPA_URL}/rest/v1/groups", data=_body, headers=_save_headers, method="POST")
                    with _req.urlopen(_rq, timeout=10) as _resp:
                        new_group = _json.loads(_resp.read().decode())[0]
                except Exception as _e:
                    continue

                groups_created += 1

                for i, med in enumerate(group.get("medications", [])):
                    med_name = str(med.get("name", ""))[:100]
                    if not med_name:
                        continue

                    # Normalize
                    try:
                        _norm_body = _json.dumps({"input_name": med_name}).encode()
                        _rq = _req.Request(f"{_SUPA_URL}/rest/v1/rpc/normalize_supplement_name", data=_norm_body, headers=_headers, method="POST")
                        with _req.urlopen(_rq, timeout=10) as _resp:
                            norm = _json.loads(_resp.read().decode())
                        if norm and norm[0].get("canonical_name"):
                            med_name = norm[0]["canonical_name"]
                    except Exception:
                        pass

                    try:
                        _med_body = _json.dumps({
                            "group_id": new_group["id"],
                            "name": med_name,
                            "dose": str(med.get("dose", ""))[:50],
                            "unit": str(med.get("unit", ""))[:20],
                            "sort_order": i,
                            "schedule_type": med.get("schedule_type"),
                            "schedule_days": med.get("schedule_days"),
                            "time_of_day": med.get("time_of_day"),
                            "frequency_days": med.get("frequency_days"),
                        }).encode()
                        _save_headers = {**_headers, "Prefer": "return=minimal"}
                        _rq = _req.Request(f"{_SUPA_URL}/rest/v1/medications", data=_med_body, headers=_save_headers, method="POST")
                        _req.urlopen(_rq, timeout=10)
                        meds_created += 1
                    except Exception:
                        pass

            # Delete pending protocol
            try:
                _rq = _req.Request(f"{_SUPA_URL}/rest/v1/pending_protocols?code=eq.{code}", headers=_headers, method="DELETE")
                _req.urlopen(_rq, timeout=10)
            except Exception:
                pass

            await interaction.followup.send(
                f"Imported **{proto.get('name', 'Protocol')}** — {groups_created} group{'s' if groups_created != 1 else ''}, "
                f"{meds_created} supplement{'s' if meds_created != 1 else ''}. Open Sup Tracker to start tracking."
            )


        # ── Supplement Stack Builder (DM only) ──────────────────────
        _sups_sessions = {}

        @tree.command(name="start-sups", description="Start building a supplement stack (DM only)")
        async def slash_start_sups(interaction: discord.Interaction):
            if not isinstance(interaction.channel, discord.DMChannel):
                await interaction.response.send_message("This command only works in DMs. Message me directly to build a stack.", ephemeral=True)
                return
            uid = str(interaction.user.id)
            _sups_sessions[uid] = {"items": [], "started": True}
            await interaction.response.send_message(
                "**Stack builder started.** Add supplements with:\n"
                "`/sup name:<name> dose:<amount> unit:<mg/IU/mcg> schedule:<ed/eod/MWF/etc>`\n\n"
                "When done, run `/end-sups name:<stack name>` to finalize."
            )

        @tree.command(name="sup", description="Add a supplement to your stack (DM only)")
        @discord.app_commands.describe(
            name="Supplement name (type to search)", dose="Dose amount (e.g. 200)",
            unit="Unit (mg, IU, mcg, ml, g)", schedule="Schedule (ed, eod, MWF, mon/thu, weekly)",
            time_of_day="Time of day (morning, afternoon, evening, bedtime)",
        )
        async def slash_sup(interaction: discord.Interaction, name: str, dose: str = "", unit: str = "mg", schedule: str = "ed", time_of_day: str = "morning"):
            import json as _json
            import urllib.request as _req
            if not isinstance(interaction.channel, discord.DMChannel):
                await interaction.response.send_message("This command only works in DMs. Message me directly to build a stack.", ephemeral=True)
                return
            uid = str(interaction.user.id)
            session = _sups_sessions.get(uid)
            if not session or not session.get("started"):
                await interaction.response.send_message("No active stack session. Run `/start-sups` first.", ephemeral=True)
                return
            _SUPA_URL = (os.environ.get("SUPABASE_URL", "") or "https://itdtludfrlwjmjxtpvwl.supabase.co")
            _SUPA_KEY = os.environ.get("SUPABASE_SERVICE_KEY", "")
            _headers = {"apikey": _SUPA_KEY, "Authorization": f"Bearer {_SUPA_KEY}", "Content-Type": "application/json"}
            canonical = name
            if _SUPA_URL and _SUPA_KEY:
                try:
                    _body = _json.dumps({"input_name": name}).encode()
                    _rq = _req.Request(f"{_SUPA_URL}/rest/v1/rpc/normalize_supplement_name", data=_body, headers=_headers, method="POST")
                    with _req.urlopen(_rq, timeout=10) as _resp:
                        _norm = _json.loads(_resp.read().decode())
                    if _norm and _norm[0].get("canonical_name"):
                        canonical = _norm[0]["canonical_name"]
                except Exception:
                    pass
            _s = schedule.lower().strip().replace(" / ", "/").replace(" /", "/").replace("/ ", "/").replace(", ", "/")
            _day_names = {"mon","tue","wed","thu","fri","sat","sun","monday","tuesday","wednesday","thursday","friday","saturday","sunday"}
            # If input contains space-separated day names, convert spaces to slashes
            _parts = _s.split()
            if len(_parts) > 1 and all(p in _day_names for p in _parts):
                _s = "/".join(_parts)
            _presets = {"ed": ("ed", ["sun","mon","tue","wed","thu","fri","sat"]), "daily": ("ed", ["sun","mon","tue","wed","thu","fri","sat"]),
                "eod": ("eod", []), "mwf": ("custom", ["mon","wed","fri"]), "mon/thu": ("custom", ["mon","thu"]),
                "mon/wed/fri": ("custom", ["mon","wed","fri"]), "tue/thu": ("custom", ["tue","thu"]),
                "tue/thu/sat": ("custom", ["tue","thu","sat"]), "weekly": ("weekly", [])}
            _stype, _sdays = _presets.get(_s, ("ed", ["sun","mon","tue","wed","thu","fri","sat"]))
            if "/" in _s and _s not in _presets:
                _abbr = {"mon":"mon","monday":"mon","tue":"tue","tuesday":"tue","wed":"wed","wednesday":"wed","thu":"thu","thursday":"thu","fri":"fri","friday":"fri","sat":"sat","saturday":"sat","sun":"sun","sunday":"sun"}
                _stype, _sdays = "custom", [_abbr.get(d.strip(), d.strip()) for d in _s.split("/")]
            _valid_times = ["morning", "afternoon", "evening", "bedtime", "pre-workout", "post-workout", "with meals", "night"]
            _time_input = time_of_day.lower().strip().replace("night", "bedtime")
            _times = [t.strip() for t in _time_input.replace(",", " ").split() if t.strip() in _valid_times]
            if not _times:
                _times = ["morning"]
            item = {"name": canonical, "dose": dose, "unit": unit, "schedule_type": _stype, "schedule_days": _sdays, "time_of_day": _times, "frequency_days": 2 if _stype == "eod" else None}
            session["items"].append(item)
            count = len(session["items"])
            matched = f" (matched: **{canonical}**)" if canonical != name else ""
            if _stype == "custom" and _sdays: sched_label = "/".join(d.capitalize() for d in _sdays)
            elif _stype == "eod": sched_label = "Every other day"
            elif _stype == "weekly": sched_label = "Weekly"
            else: sched_label = "Daily"
            await interaction.response.send_message(f"Added #{count}: **{canonical}** {dose} {unit} \u2014 {sched_label} ({_time}){matched}\nAdd more with `/sup` or finalize with `/end-sups name:<stack name>`")





        # Cache supplement names in memory for instant autocomplete
        _sup_name_cache = []

        async def _load_sup_cache():
            import json as _json, urllib.request as _req, urllib.parse as _parse
            try:
                _SU = (os.environ.get("SUPABASE_URL", "") or "https://itdtludfrlwjmjxtpvwl.supabase.co")
                _SK = os.environ.get("SUPABASE_SERVICE_KEY", "")
                if not _SU or not _SK:
                    return
                _h = {"apikey": _SK, "Authorization": f"Bearer {_SK}"}
                _params = _parse.urlencode({"select": "name,aliases", "limit": "500"})
                _rq = _req.Request(f"{_SU}/rest/v1/supplement_database?{_params}", headers=_h)
                with _req.urlopen(_rq, timeout=10) as _resp:
                    results = _json.loads(_resp.read().decode())
                _sup_name_cache.clear()
                for r in results:
                    _sup_name_cache.append(r["name"])
                logger.info("[sups-builder] Cached %d supplement names", len(_sup_name_cache))
            except Exception as _e:
                logger.error("[sups-builder] Failed to cache supplements: %s", _e)

        # Load cache on startup
        asyncio.get_event_loop().call_soon(lambda: asyncio.ensure_future(_load_sup_cache()))

        @slash_sup.autocomplete("name")
        async def _sup_name_ac(interaction: discord.Interaction, current: str):
            if not current or len(current) < 2:
                return []
            _term = current.lower()
            matches = [n for n in _sup_name_cache if _term in n.lower()]
            return [discord.app_commands.Choice(name=m[:100], value=m[:100]) for m in matches[:15]]

        @slash_sup.autocomplete("unit")
        async def _sup_unit_ac(interaction: discord.Interaction, current: str):
            units = ["mg", "mcg", "IU", "ml", "g", "drops", "capsules", "tablets"]
            if not current:
                return [discord.app_commands.Choice(name=u, value=u) for u in units]
            return [discord.app_commands.Choice(name=u, value=u) for u in units if current.lower() in u.lower()]

        @slash_sup.autocomplete("schedule")
        async def _sup_sched_ac(interaction: discord.Interaction, current: str):
            scheds = [
                ("Daily", "ed"), ("Every other day", "eod"), ("Mon/Wed/Fri", "MWF"),
                ("Mon/Thu", "mon/thu"), ("Tue/Thu", "tue/thu"), ("Tue/Thu/Sat", "tue/thu/sat"),
                ("Weekly", "weekly"), ("Sunday", "sun"), ("Monday", "mon"), ("Tuesday", "tue"),
                ("Wednesday", "wed"), ("Thursday", "thu"), ("Friday", "fri"), ("Saturday", "sat"),
            ]
            if not current:
                return [discord.app_commands.Choice(name=l, value=v) for l, v in scheds[:10]]
            return [discord.app_commands.Choice(name=l, value=v) for l, v in scheds if current.lower() in l.lower() or current.lower() in v.lower()][:10]

        @slash_sup.autocomplete("time_of_day")
        async def _sup_time_ac(interaction: discord.Interaction, current: str):
            times = [("Morning", "morning"), ("Afternoon", "afternoon"), ("Evening", "evening"), ("Bedtime", "bedtime"),
                     ("With meals", "with meals"), ("Before bed", "bedtime"), ("Pre-workout", "pre-workout"), ("Post-workout", "post-workout")]
            if not current:
                return [discord.app_commands.Choice(name=l, value=v) for l, v in times]
            return [discord.app_commands.Choice(name=l, value=v) for l, v in times if current.lower() in l.lower()][:10]

        @tree.command(name="end-sups", description="Finalize your supplement stack (DM only)")
        @discord.app_commands.describe(name="Name for this stack (e.g. TRT Protocol, Morning Stack)")
        async def slash_end_sups(interaction: discord.Interaction, name: str = "My Stack"):
            import json as _json, hashlib as _hl, urllib.request as _req
            # Defer IMMEDIATELY to avoid 3-second timeout
            is_dm = isinstance(interaction.channel, discord.DMChannel)
            if not is_dm:
                await interaction.response.send_message("This command only works in DMs. Message me directly to build a stack.", ephemeral=True)
                return
            await interaction.response.defer()
            uid = str(interaction.user.id)
            session = _sups_sessions.get(uid)
            if not session or not session.get("started") or not session.get("items"):
                await interaction.followup.send("No active stack or no supplements added. Run `/start-sups` then `/sup` first.")
                return
            items = session["items"]
            _SUPA_URL = (os.environ.get("SUPABASE_URL", "") or "https://itdtludfrlwjmjxtpvwl.supabase.co") or "https://itdtludfrlwjmjxtpvwl.supabase.co"
            _SUPA_KEY = os.environ.get("SUPABASE_SERVICE_KEY", "")
            if not _SUPA_KEY:
                # Try loading from profile .env
                _env_path = os.path.join(os.environ.get("HERMES_HOME", "/profile"), ".env")
                if os.path.exists(_env_path):
                    with open(_env_path) as _ef:
                        for _el in _ef:
                            if _el.startswith("SUPABASE_SERVICE_KEY="):
                                _SUPA_KEY = _el.strip().split("=", 1)[1].strip()
            _headers = {"apikey": _SUPA_KEY, "Authorization": f"Bearer {_SUPA_KEY}", "Content-Type": "application/json"}
            logger.info("[sups-builder] end-sups: URL=%s KEY=%s...", _SUPA_URL, _SUPA_KEY[:20] if _SUPA_KEY else "NONE")
            medications = []
            for item in items:
                med = {"name": item["name"], "dose": item["dose"], "unit": item["unit"]}
                for k in ("schedule_type", "schedule_days", "time_of_day", "frequency_days"):
                    if item.get(k): med[k] = item[k]
                medications.append(med)
            protocol = {"version": 1, "name": name, "source": "sups-builder",
                "groups": [{"name": name, "schedule_type": "ed", "schedule_days": ["sun","mon","tue","wed","thu","fri","sat"],
                    "time_of_day": ["morning"], "color": "#00d4aa", "medications": medications}]}
            _slug = name.lower().replace(" ", "-")[:20]
            _hash = _hl.md5(f"{uid}{_slug}{len(items)}".encode()).hexdigest()[:6]
            code = f"pl-{_slug}-{_hash}"
            try:
                _body = _json.dumps({"code": code, "protocol": protocol}).encode()
                _rq = _req.Request(f"{_SUPA_URL}/rest/v1/pending_protocols", data=_body, headers={**_headers, "Prefer": "return=minimal"}, method="POST")
                _req.urlopen(_rq, timeout=10)
            except Exception as _e:
                await interaction.followup.send(f"Failed to save protocol: {_e}")
                return
            summary_lines = [f"**{name}** \u2014 {len(items)} supplement{'s' if len(items) != 1 else ''}\n"]
            for i, item in enumerate(items, 1):
                st, sd, td = item.get("schedule_type","ed"), item.get("schedule_days",[]), item.get("time_of_day",["morning"])
                if st == "custom" and sd: ss = "/".join(d.capitalize() for d in sd)
                elif st == "eod": ss = "Every other day"
                elif st == "weekly": ss = "Weekly"
                else: ss = "Daily"
                summary_lines.append(f"{i}. **{item['name']}** {item['dose']} {item['unit']} \u2014 {ss} ({', '.join(td)})")
            del _sups_sessions[uid]
            await interaction.followup.send("\n".join(summary_lines) + f"\n\nTo import to Sup Tracker, run:\n`/import-regimen code:{code}`\n\nCode expires in 24 hours.")



    def _build_slash_event(self, interaction: discord.Interaction, text: str) -> MessageEvent:
        """Build a MessageEvent from a Discord slash command interaction."""
        is_dm = isinstance(interaction.channel, discord.DMChannel)
        is_thread = isinstance(interaction.channel, discord.Thread)
        thread_id = None

        if is_dm:
            chat_type = "dm"
        elif is_thread:
            chat_type = "thread"
            thread_id = str(interaction.channel_id)
        else:
            chat_type = "group"

        chat_name = ""
        if not is_dm and hasattr(interaction.channel, "name"):
            chat_name = interaction.channel.name
            if hasattr(interaction.channel, "guild") and interaction.channel.guild:
                chat_name = f"{interaction.channel.guild.name} / #{chat_name}"

        # Get channel topic (if available)
        chat_topic = getattr(interaction.channel, "topic", None)

        source = self.build_source(
            chat_id=str(interaction.channel_id),
            chat_name=chat_name,
            chat_type=chat_type,
            user_id=str(interaction.user.id),
            user_name=interaction.user.display_name,
            thread_id=thread_id,
            chat_topic=chat_topic,
        )

        msg_type = MessageType.COMMAND if text.startswith("/") else MessageType.TEXT
        return MessageEvent(
            text=text,
            message_type=msg_type,
            source=source,
            raw_message=interaction,
        )

    # ------------------------------------------------------------------
    # Thread creation helpers
    # ------------------------------------------------------------------

    async def _handle_thread_create_slash(
        self,
        interaction: discord.Interaction,
        name: str,
        message: str = "",
        auto_archive_duration: int = 1440,
    ) -> None:
        """Create a Discord thread from a slash command and start a session in it."""
        result = await self._create_thread(
            interaction,
            name=name,
            message=message,
            auto_archive_duration=auto_archive_duration,
        )

        if not result.get("success"):
            error = result.get("error", "unknown error")
            await interaction.followup.send(f"Failed to create thread: {error}", ephemeral=True)
            return

        thread_id = result.get("thread_id")
        thread_name = result.get("thread_name") or name

        # Tell the user where the thread is
        link = f"<#{thread_id}>" if thread_id else f"**{thread_name}**"
        await interaction.followup.send(f"Created thread {link}", ephemeral=True)

        # Track thread participation so follow-ups don't require @mention
        if thread_id:
            self._track_thread(thread_id)

        # If a message was provided, kick off a new Hermes session in the thread
        starter = (message or "").strip()
        if starter and thread_id:
            await self._dispatch_thread_session(interaction, thread_id, thread_name, starter)

    async def _dispatch_thread_session(
        self,
        interaction: discord.Interaction,
        thread_id: str,
        thread_name: str,
        text: str,
    ) -> None:
        """Build a MessageEvent pointing at a thread and send it through handle_message."""
        guild_name = ""
        if hasattr(interaction, "guild") and interaction.guild:
            guild_name = interaction.guild.name

        chat_name = f"{guild_name} / {thread_name}" if guild_name else thread_name

        source = self.build_source(
            chat_id=thread_id,
            chat_name=chat_name,
            chat_type="thread",
            user_id=str(interaction.user.id),
            user_name=interaction.user.display_name,
            thread_id=thread_id,
        )

        event = MessageEvent(
            text=text,
            message_type=MessageType.TEXT,
            source=source,
            raw_message=interaction,
        )
        await self.handle_message(event)

    def _thread_parent_channel(self, channel: Any) -> Any:
        """Return the parent text channel when invoked from a thread."""
        return getattr(channel, "parent", None) or channel

    async def _resolve_interaction_channel(self, interaction: discord.Interaction) -> Optional[Any]:
        """Return the interaction channel, fetching it if the payload is partial."""
        channel = getattr(interaction, "channel", None)
        if channel is not None:
            return channel
        if not self._client:
            return None
        channel_id = getattr(interaction, "channel_id", None)
        if channel_id is None:
            return None
        channel = self._client.get_channel(int(channel_id))
        if channel is not None:
            return channel
        try:
            return await self._client.fetch_channel(int(channel_id))
        except Exception:
            return None

    async def _create_thread(
        self,
        interaction: discord.Interaction,
        *,
        name: str,
        message: str = "",
        auto_archive_duration: int = 1440,
    ) -> Dict[str, Any]:
        """Create a thread in the current Discord channel.

        Tries ``parent_channel.create_thread()`` first.  If Discord rejects
        that (e.g. permission issues), falls back to sending a seed message
        and creating the thread from it.
        """
        name = (name or "").strip()
        if not name:
            return {"error": "Thread name is required."}

        if auto_archive_duration not in VALID_THREAD_AUTO_ARCHIVE_MINUTES:
            allowed = ", ".join(str(v) for v in sorted(VALID_THREAD_AUTO_ARCHIVE_MINUTES))
            return {"error": f"auto_archive_duration must be one of: {allowed}."}

        channel = await self._resolve_interaction_channel(interaction)
        if channel is None:
            return {"error": "Could not resolve the current Discord channel."}
        if isinstance(channel, discord.DMChannel):
            return {"error": "Discord threads can only be created inside server text channels, not DMs."}

        parent_channel = self._thread_parent_channel(channel)
        if parent_channel is None:
            return {"error": "Could not determine a parent text channel for the new thread."}

        display_name = getattr(getattr(interaction, "user", None), "display_name", None) or "unknown user"
        reason = f"Requested by {display_name} via /thread"
        starter_message = (message or "").strip()

        try:
            thread = await parent_channel.create_thread(
                name=name,
                auto_archive_duration=auto_archive_duration,
                reason=reason,
            )
            if starter_message:
                await thread.send(starter_message)
            return {
                "success": True,
                "thread_id": str(thread.id),
                "thread_name": getattr(thread, "name", None) or name,
            }
        except Exception as direct_error:
            try:
                seed_content = starter_message or f"\U0001f9f5 Thread created by Hermes: **{name}**"
                seed_msg = await parent_channel.send(seed_content)
                thread = await seed_msg.create_thread(
                    name=name,
                    auto_archive_duration=auto_archive_duration,
                    reason=reason,
                )
                return {
                    "success": True,
                    "thread_id": str(thread.id),
                    "thread_name": getattr(thread, "name", None) or name,
                }
            except Exception as fallback_error:
                return {
                    "error": (
                        "Discord rejected direct thread creation and the fallback also failed. "
                        f"Direct error: {direct_error}. Fallback error: {fallback_error}"
                    )
                }

    # ------------------------------------------------------------------
    # Auto-thread helpers
    # ------------------------------------------------------------------

    async def _auto_create_thread(self, message: 'DiscordMessage') -> Optional[Any]:
        """Create a thread from a user message for auto-threading.

        Returns the created thread object, or ``None`` on failure.
        """
        # Build a short thread name from the message
        content = (message.content or "").strip()
        thread_name = content[:80] if content else "Hermes"
        if len(content) > 80:
            thread_name = thread_name[:77] + "..."

        try:
            thread = await message.create_thread(name=thread_name, auto_archive_duration=1440)
            return thread
        except Exception as e:
            logger.warning("[%s] Auto-thread creation failed: %s", self.name, e)
            return None

    async def send_exec_approval(
        self, chat_id: str, command: str, session_key: str,
        description: str = "dangerous command",
        metadata: Optional[dict] = None,
    ) -> SendResult:
        """
        Send a button-based exec approval prompt for a dangerous command.

        The buttons call ``resolve_gateway_approval()`` to unblock the waiting
        agent thread — this replaces the text-based ``/approve`` flow on Discord.
        """
        if not self._client or not DISCORD_AVAILABLE:
            return SendResult(success=False, error="Not connected")

        try:
            # Resolve channel — use thread_id from metadata if present
            target_id = chat_id
            if metadata and metadata.get("thread_id"):
                target_id = metadata["thread_id"]

            channel = self._client.get_channel(int(target_id))
            if not channel:
                channel = await self._client.fetch_channel(int(target_id))

            # Discord embed description limit is 4096; show full command up to that
            max_desc = 4088
            cmd_display = command if len(command) <= max_desc else command[: max_desc - 3] + "..."
            embed = discord.Embed(
                title="⚠️ Command Approval Required",
                description=f"```\n{cmd_display}\n```",
                color=discord.Color.orange(),
            )
            embed.add_field(name="Reason", value=description, inline=False)

            view = ExecApprovalView(
                session_key=session_key,
                allowed_user_ids=self._allowed_user_ids,
            )

            msg = await channel.send(embed=embed, view=view)
            return SendResult(success=True, message_id=str(msg.id))

        except Exception as e:
            return SendResult(success=False, error=str(e))

    async def send_update_prompt(
        self, chat_id: str, prompt: str, default: str = "",
        session_key: str = "",
    ) -> SendResult:
        """Send an interactive button-based update prompt (Yes / No).

        Used by the gateway ``/update`` watcher when ``hermes update --gateway``
        needs user input (stash restore, config migration).
        """
        if not self._client or not DISCORD_AVAILABLE:
            return SendResult(success=False, error="Not connected")
        try:
            channel = self._client.get_channel(int(chat_id))
            if not channel:
                channel = await self._client.fetch_channel(int(chat_id))

            default_hint = f" (default: {default})" if default else ""
            embed = discord.Embed(
                title="⚕ Update Needs Your Input",
                description=f"{prompt}{default_hint}",
                color=discord.Color.gold(),
            )
            view = UpdatePromptView(
                session_key=session_key,
                allowed_user_ids=self._allowed_user_ids,
            )
            msg = await channel.send(embed=embed, view=view)
            return SendResult(success=True, message_id=str(msg.id))
        except Exception as e:
            return SendResult(success=False, error=str(e))

    def _get_parent_channel_id(self, channel: Any) -> Optional[str]:
        """Return the parent channel ID for a Discord thread-like channel, if present."""
        parent = getattr(channel, "parent", None)
        if parent is not None and getattr(parent, "id", None) is not None:
            return str(parent.id)
        parent_id = getattr(channel, "parent_id", None)
        if parent_id is not None:
            return str(parent_id)
        return None

    def _is_forum_parent(self, channel: Any) -> bool:
        """Best-effort check for whether a Discord channel is a forum channel."""
        if channel is None:
            return False
        forum_cls = getattr(discord, "ForumChannel", None)
        if forum_cls and isinstance(channel, forum_cls):
            return True
        channel_type = getattr(channel, "type", None)
        if channel_type is not None:
            type_value = getattr(channel_type, "value", channel_type)
            if type_value == 15:
                return True
        return False

    def _format_thread_chat_name(self, thread: Any) -> str:
        """Build a readable chat name for thread-like Discord channels, including forum context when available."""
        thread_name = getattr(thread, "name", None) or str(getattr(thread, "id", "thread"))
        parent = getattr(thread, "parent", None)
        guild = getattr(thread, "guild", None) or getattr(parent, "guild", None)
        guild_name = getattr(guild, "name", None)
        parent_name = getattr(parent, "name", None)

        if self._is_forum_parent(parent) and guild_name and parent_name:
            return f"{guild_name} / {parent_name} / {thread_name}"
        if parent_name and guild_name:
            return f"{guild_name} / #{parent_name} / {thread_name}"
        if parent_name:
            return f"{parent_name} / {thread_name}"
        return thread_name

    # ------------------------------------------------------------------
    # Thread participation persistence
    # ------------------------------------------------------------------

    @staticmethod
    def _thread_state_path() -> Path:
        """Path to the persisted thread participation set."""
        from hermes_cli.config import get_hermes_home
        return get_hermes_home() / "discord_threads.json"

    @classmethod
    def _load_participated_threads(cls) -> set:
        """Load persisted thread IDs from disk."""
        path = cls._thread_state_path()
        try:
            if path.exists():
                data = json.loads(path.read_text(encoding="utf-8"))
                if isinstance(data, list):
                    return set(data)
        except Exception as e:
            logger.debug("Could not load discord thread state: %s", e)
        return set()

    def _save_participated_threads(self) -> None:
        """Persist the current thread set to disk (best-effort)."""
        path = self._thread_state_path()
        try:
            # Trim to most recent entries if over cap
            thread_list = list(self._bot_participated_threads)
            if len(thread_list) > self._MAX_TRACKED_THREADS:
                thread_list = thread_list[-self._MAX_TRACKED_THREADS:]
                self._bot_participated_threads = set(thread_list)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(thread_list), encoding="utf-8")
        except Exception as e:
            logger.debug("Could not save discord thread state: %s", e)

    def _track_thread(self, thread_id: str) -> None:
        """Add a thread to the participation set and persist."""
        if thread_id not in self._bot_participated_threads:
            self._bot_participated_threads.add(thread_id)
            self._save_participated_threads()

    async def _handle_message(self, message: DiscordMessage) -> None:
        """Handle incoming Discord messages."""
        # In server channels (not DMs), require the bot to be @mentioned
        # UNLESS the channel is in the free-response list or the message is
        # in a thread where the bot has already participated.
        #
        # Config (all settable via discord.* in config.yaml):
        #   discord.require_mention: Require @mention in server channels (default: true)
        #   discord.free_response_channels: Channel IDs where bot responds without mention
        #   discord.auto_thread: Auto-create thread on @mention in channels (default: true)

        thread_id = None
        parent_channel_id = None
        is_thread = isinstance(message.channel, discord.Thread)
        if is_thread:
            thread_id = str(message.channel.id)
            parent_channel_id = self._get_parent_channel_id(message.channel)

        if not isinstance(message.channel, discord.DMChannel):
            free_channels_raw = os.getenv("DISCORD_FREE_RESPONSE_CHANNELS", "")
            free_channels = {ch.strip() for ch in free_channels_raw.split(",") if ch.strip()}
            channel_ids = {str(message.channel.id)}
            if parent_channel_id:
                channel_ids.add(parent_channel_id)

            require_mention = os.getenv("DISCORD_REQUIRE_MENTION", "true").lower() not in ("false", "0", "no")
            is_free_channel = bool(channel_ids & free_channels)

            # Skip the mention check if the message is in a thread where
            # the bot has previously participated (auto-created or replied in).
            in_bot_thread = is_thread and thread_id in self._bot_participated_threads

            if require_mention and not is_free_channel and not in_bot_thread:
                if self._client.user not in message.mentions:
                    return

            if self._client.user and self._client.user in message.mentions:
                message.content = message.content.replace(f"<@{self._client.user.id}>", "").strip()
                message.content = message.content.replace(f"<@!{self._client.user.id}>", "").strip()

        # Auto-thread: when enabled, automatically create a thread for every
        # @mention in a text channel so each conversation is isolated (like Slack).
        # Messages already inside threads or DMs are unaffected.
        auto_threaded_channel = None
        if not is_thread and not isinstance(message.channel, discord.DMChannel):
            auto_thread = os.getenv("DISCORD_AUTO_THREAD", "true").lower() in ("true", "1", "yes")
            if auto_thread:
                thread = await self._auto_create_thread(message)
                if thread:
                    is_thread = True
                    thread_id = str(thread.id)
                    auto_threaded_channel = thread
                    self._track_thread(thread_id)

        # Determine message type
        msg_type = MessageType.TEXT
        if message.content.startswith("/"):
            msg_type = MessageType.COMMAND
        elif message.attachments:
            # Check attachment types
            for att in message.attachments:
                if att.content_type:
                    if att.content_type.startswith("image/"):
                        msg_type = MessageType.PHOTO
                    elif att.content_type.startswith("video/"):
                        msg_type = MessageType.VIDEO
                    elif att.content_type.startswith("audio/"):
                        msg_type = MessageType.AUDIO
                    else:
                        doc_ext = ""
                        if att.filename:
                            _, doc_ext = os.path.splitext(att.filename)
                            doc_ext = doc_ext.lower()
                        if doc_ext in SUPPORTED_DOCUMENT_TYPES:
                            msg_type = MessageType.DOCUMENT
                    break

        # When auto-threading kicked in, route responses to the new thread
        effective_channel = auto_threaded_channel or message.channel

        # Determine chat type
        if isinstance(message.channel, discord.DMChannel):
            chat_type = "dm"
            chat_name = message.author.name
        elif is_thread:
            chat_type = "thread"
            chat_name = self._format_thread_chat_name(effective_channel)
        else:
            chat_type = "group"
            chat_name = getattr(message.channel, "name", str(message.channel.id))
            if hasattr(message.channel, "guild") and message.channel.guild:
                chat_name = f"{message.channel.guild.name} / #{chat_name}"

        # Get channel topic (if available - TextChannels have topics, DMs/threads don't)
        chat_topic = getattr(message.channel, "topic", None)

        # Build source
        source = self.build_source(
            chat_id=str(effective_channel.id),
            chat_name=chat_name,
            chat_type=chat_type,
            user_id=str(message.author.id),
            user_name=message.author.display_name,
            thread_id=thread_id,
            chat_topic=chat_topic,
        )

        # Build media URLs -- download image attachments to local cache so the
        # vision tool can access them reliably (Discord CDN URLs can expire).
        media_urls = []
        media_types = []
        pending_text_injection: Optional[str] = None
        for att in message.attachments:
            content_type = att.content_type or "unknown"
            if content_type.startswith("image/"):
                try:
                    # Determine extension from content type (image/png -> .png)
                    ext = "." + content_type.split("/")[-1].split(";")[0]
                    if ext not in (".jpg", ".jpeg", ".png", ".gif", ".webp"):
                        ext = ".jpg"
                    cached_path = await cache_image_from_url(att.url, ext=ext)
                    media_urls.append(cached_path)
                    media_types.append(content_type)
                    print(f"[Discord] Cached user image: {cached_path}", flush=True)
                except Exception as e:
                    print(f"[Discord] Failed to cache image attachment: {e}", flush=True)
                    # Fall back to the CDN URL if caching fails
                    media_urls.append(att.url)
                    media_types.append(content_type)
            elif content_type.startswith("audio/"):
                try:
                    ext = "." + content_type.split("/")[-1].split(";")[0]
                    if ext not in (".ogg", ".mp3", ".wav", ".webm", ".m4a"):
                        ext = ".ogg"
                    cached_path = await cache_audio_from_url(att.url, ext=ext)
                    media_urls.append(cached_path)
                    media_types.append(content_type)
                    print(f"[Discord] Cached user audio: {cached_path}", flush=True)
                except Exception as e:
                    print(f"[Discord] Failed to cache audio attachment: {e}", flush=True)
                    media_urls.append(att.url)
                    media_types.append(content_type)
            else:
                # Document attachments: download, cache, and optionally inject text
                ext = ""
                if att.filename:
                    _, ext = os.path.splitext(att.filename)
                    ext = ext.lower()
                if not ext and content_type:
                    mime_to_ext = {v: k for k, v in SUPPORTED_DOCUMENT_TYPES.items()}
                    ext = mime_to_ext.get(content_type, "")
                if ext not in SUPPORTED_DOCUMENT_TYPES:
                    logger.warning(
                        "[Discord] Unsupported document type '%s' (%s), skipping",
                        ext or "unknown", content_type,
                    )
                else:
                    MAX_DOC_BYTES = 20 * 1024 * 1024
                    if att.size and att.size > MAX_DOC_BYTES:
                        logger.warning(
                            "[Discord] Document too large (%s bytes), skipping: %s",
                            att.size, att.filename,
                        )
                    else:
                        try:
                            import aiohttp
                            async with aiohttp.ClientSession() as session:
                                async with session.get(
                                    att.url,
                                    timeout=aiohttp.ClientTimeout(total=30),
                                ) as resp:
                                    if resp.status != 200:
                                        raise Exception(f"HTTP {resp.status}")
                                    raw_bytes = await resp.read()
                            cached_path = cache_document_from_bytes(
                                raw_bytes, att.filename or f"document{ext}"
                            )
                            doc_mime = SUPPORTED_DOCUMENT_TYPES[ext]
                            media_urls.append(cached_path)
                            media_types.append(doc_mime)
                            logger.info("[Discord] Cached user document: %s", cached_path)
                            # Inject text content for .txt/.md files (capped at 100 KB)
                            MAX_TEXT_INJECT_BYTES = 100 * 1024
                            if ext in (".md", ".txt") and len(raw_bytes) <= MAX_TEXT_INJECT_BYTES:
                                try:
                                    text_content = raw_bytes.decode("utf-8")
                                    display_name = att.filename or f"document{ext}"
                                    display_name = re.sub(r'[^\w.\- ]', '_', display_name)
                                    injection = f"[Content of {display_name}]:\n{text_content}"
                                    if pending_text_injection:
                                        pending_text_injection = f"{pending_text_injection}\n\n{injection}"
                                    else:
                                        pending_text_injection = injection
                                except UnicodeDecodeError:
                                    pass
                        except Exception as e:
                            logger.warning(
                                "[Discord] Failed to cache document %s: %s",
                                att.filename, e, exc_info=True,
                            )

        event_text = message.content
        if pending_text_injection:
            event_text = f"{pending_text_injection}\n\n{event_text}" if event_text else pending_text_injection

        # Defense-in-depth: prevent empty user messages from entering session
        # (can happen when user sends @mention-only with no other text)
        if not event_text or not event_text.strip():
            event_text = "(The user sent a message with no text content)"

        event = MessageEvent(
            text=event_text,
            message_type=msg_type,
            source=source,
            raw_message=message,
            message_id=str(message.id),
            media_urls=media_urls,
            media_types=media_types,
            reply_to_message_id=str(message.reference.message_id) if message.reference else None,
            timestamp=message.created_at,
        )

        # Track thread participation so the bot won't require @mention for
        # follow-up messages in threads it has already engaged in.
        if thread_id:
            self._track_thread(thread_id)

        await self.handle_message(event)


# ---------------------------------------------------------------------------
# Discord UI Components (outside the adapter class)
# ---------------------------------------------------------------------------

if DISCORD_AVAILABLE:

    class ExecApprovalView(discord.ui.View):
        """
        Interactive button view for exec approval of dangerous commands.

        Shows four buttons: Allow Once, Allow Session, Always Allow, Deny.
        Clicking a button calls ``resolve_gateway_approval()`` to unblock the
        waiting agent thread — the same mechanism as the text ``/approve`` flow.
        Only users in the allowed list can click.  Times out after 5 minutes.
        """

        def __init__(self, session_key: str, allowed_user_ids: set):
            super().__init__(timeout=300)  # 5-minute timeout
            self.session_key = session_key
            self.allowed_user_ids = allowed_user_ids
            self.resolved = False

        def _check_auth(self, interaction: discord.Interaction) -> bool:
            """Verify the user clicking is authorized."""
            if not self.allowed_user_ids:
                return True  # No allowlist = anyone can approve
            return str(interaction.user.id) in self.allowed_user_ids

        async def _resolve(
            self, interaction: discord.Interaction, choice: str,
            color: discord.Color, label: str,
        ):
            """Resolve the approval via the gateway approval queue and update the embed."""
            if self.resolved:
                await interaction.response.send_message(
                    "This approval has already been resolved~", ephemeral=True
                )
                return

            if not self._check_auth(interaction):
                await interaction.response.send_message(
                    "You're not authorized to approve commands~", ephemeral=True
                )
                return

            self.resolved = True

            # Update the embed with the decision
            embed = interaction.message.embeds[0] if interaction.message.embeds else None
            if embed:
                embed.color = color
                embed.set_footer(text=f"{label} by {interaction.user.display_name}")

            # Disable all buttons
            for child in self.children:
                child.disabled = True

            await interaction.response.edit_message(embed=embed, view=self)

            # Unblock the waiting agent thread via the gateway approval queue
            try:
                from tools.approval import resolve_gateway_approval
                count = resolve_gateway_approval(self.session_key, choice)
                logger.info(
                    "Discord button resolved %d approval(s) for session %s (choice=%s, user=%s)",
                    count, self.session_key, choice, interaction.user.display_name,
                )
            except Exception as exc:
                logger.error("Failed to resolve gateway approval from button: %s", exc)

        @discord.ui.button(label="Allow Once", style=discord.ButtonStyle.green)
        async def allow_once(
            self, interaction: discord.Interaction, button: discord.ui.Button
        ):
            await self._resolve(interaction, "once", discord.Color.green(), "Approved once")

        @discord.ui.button(label="Allow Session", style=discord.ButtonStyle.grey)
        async def allow_session(
            self, interaction: discord.Interaction, button: discord.ui.Button
        ):
            await self._resolve(interaction, "session", discord.Color.blue(), "Approved for session")

        @discord.ui.button(label="Always Allow", style=discord.ButtonStyle.blurple)
        async def allow_always(
            self, interaction: discord.Interaction, button: discord.ui.Button
        ):
            await self._resolve(interaction, "always", discord.Color.purple(), "Approved permanently")

        @discord.ui.button(label="Deny", style=discord.ButtonStyle.red)
        async def deny(
            self, interaction: discord.Interaction, button: discord.ui.Button
        ):
            await self._resolve(interaction, "deny", discord.Color.red(), "Denied")

        async def on_timeout(self):
            """Handle view timeout -- disable buttons and mark as expired."""
            self.resolved = True
            for child in self.children:
                child.disabled = True

    class UpdatePromptView(discord.ui.View):
        """Interactive Yes/No buttons for ``hermes update`` prompts.

        Clicking a button writes the answer to ``.update_response`` so the
        detached update process can pick it up.  Only authorized users can
        click.  Times out after 5 minutes (the update process also has a
        5-minute timeout on its side).
        """

        def __init__(self, session_key: str, allowed_user_ids: set):
            super().__init__(timeout=300)
            self.session_key = session_key
            self.allowed_user_ids = allowed_user_ids
            self.resolved = False

        def _check_auth(self, interaction: discord.Interaction) -> bool:
            if not self.allowed_user_ids:
                return True
            return str(interaction.user.id) in self.allowed_user_ids

        async def _respond(
            self, interaction: discord.Interaction, answer: str,
            color: discord.Color, label: str,
        ):
            if self.resolved:
                await interaction.response.send_message(
                    "Already answered~", ephemeral=True
                )
                return
            if not self._check_auth(interaction):
                await interaction.response.send_message(
                    "You're not authorized~", ephemeral=True
                )
                return

            self.resolved = True

            # Update embed
            embed = interaction.message.embeds[0] if interaction.message.embeds else None
            if embed:
                embed.color = color
                embed.set_footer(text=f"{label} by {interaction.user.display_name}")

            for child in self.children:
                child.disabled = True
            await interaction.response.edit_message(embed=embed, view=self)

            # Write response file
            try:
                from hermes_constants import get_hermes_home
                home = get_hermes_home()
                response_path = home / ".update_response"
                tmp = response_path.with_suffix(".tmp")
                tmp.write_text(answer)
                tmp.replace(response_path)
                logger.info(
                    "Discord update prompt answered '%s' by %s",
                    answer, interaction.user.display_name,
                )
            except Exception as exc:
                logger.error("Failed to write update response: %s", exc)

        @discord.ui.button(label="Yes", style=discord.ButtonStyle.green, emoji="✓")
        async def yes_btn(
            self, interaction: discord.Interaction, button: discord.ui.Button
        ):
            await self._respond(interaction, "y", discord.Color.green(), "Yes")

        @discord.ui.button(label="No", style=discord.ButtonStyle.red, emoji="✗")
        async def no_btn(
            self, interaction: discord.Interaction, button: discord.ui.Button
        ):
            await self._respond(interaction, "n", discord.Color.red(), "No")

        async def on_timeout(self):
            self.resolved = True
            for child in self.children:
                child.disabled = True
