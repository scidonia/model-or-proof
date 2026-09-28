"""Observe writes outside the working copy while a file-mode session runs (plan D26, item 5).

D26 asks that the prover's shell be its working copy only. **Enforcing** that needs a sandbox, and the
sandbox is not available on this host: `unshare -r --mount` fails with

    unshare: write failed /proc/self/uid_map: Operation not permitted

i.e. unprivileged user namespaces are disabled, so bind-mounting the package read-only with the working copy
writable is out, and bubblewrap (which needs the same) would fail identically. That is recorded here so a
future reader does not re-litigate it: with no kernel boundary available, D26's "reported, never silently
prevented" is the operative half, and the boundary is **observed**.

Observation has to be event-based. A before/after digest sweep of the tree is defeated by a write followed
by a restore, which is precisely the trick this exists to catch — and a candidate with a shell can perform
it. `inotifywait` reports the events themselves, including its own queue overflows, which a hand-rolled
`ctypes` watcher would drop silently — and silent dropping is a false "nothing was written outside", the
one failure mode worse than not watching at all.

Every way this can go blind is a refusal rather than silence, on the same principle as the rest of the
harness:

* a queue overflow, or any line the parser cannot read, means the event stream has a gap: `blind`;
* the watcher dying before we stop it means the tail of the run was unobserved: `blind`;
* a directory *created* outside the working copy is itself a write — recursive watches do not follow new
  directories, so treating the creation as the event closes the gap conservatively.

A run whose watcher reports either blindness or an outside event is not a closure, whatever its file says.
"""

from __future__ import annotations

import pathlib
import re
import shutil
import subprocess
import threading

#: The binary the flake declares. Absent means we cannot observe, which is `blind`, not "nothing happened".
WATCH_BINARY = "inotifywait"

#: Events worth watching: the ones that mean the tree changed. `CREATE,ISDIR` is included by `create`.
WATCHED_EVENTS = ("create", "modify", "delete", "move", "attrib")

#: How long to wait for the watches to be established before calling the observation blind.
READY_TIMEOUT_S = 10.0

_EVENT_LINE = re.compile(r"^(?P<events>[A-Z_,]+)\s+(?P<path>.+)$")


class OutsideWatch:
    """A recursive, event-based watch of a tree, with the working copy as the only allowed path."""

    def __init__(self, root: pathlib.Path, allowed: pathlib.Path, *, binary: str = WATCH_BINARY) -> None:
        self.root = pathlib.Path(root)
        self.allowed = pathlib.Path(allowed)
        self.binary = binary
        self.events: list[str] = []
        self.blind: str | None = None
        self._process: subprocess.Popen | None = None
        self._thread: threading.Thread | None = None
        # Set when `inotifywait` reports its watches established: until then the tree is unobserved.
        self._ready = threading.Event()

    # -- lifecycle ---------------------------------------------------------------------------------
    def start(self) -> None:
        """Begin watching, and wait until the watches are actually in place before returning.

        `inotifywait` prints `Setting up watches.` / `Watches established.` on its output, and until that
        second line the tree is unobserved — a session that acts immediately would write outside its copy
        into a gap. So the handshake is not optional: `start` blocks on it and treats a failure to arrive as
        blindness.
        """
        binary = shutil.which(self.binary)
        if binary is None:
            self.blind = f"{self.binary} is not on PATH: the working-copy-only boundary cannot be observed"
            return
        args = [binary, "-m", "-r", "--format", "%e %w%f"]
        for event in WATCHED_EVENTS:
            args += ["-e", event]
        args.append(str(self.root))
        try:
            self._process = subprocess.Popen(
                args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True
            )
        except OSError as error:  # pragma: no cover - a real host failure, reported rather than fatal
            self.blind = f"{self.binary} could not be started: {error}"
            return
        self._thread = threading.Thread(target=self._read, daemon=True)
        self._thread.start()
        if not self._ready.wait(timeout=READY_TIMEOUT_S):
            self.blind = self.blind or (
                f"{self.binary} did not report its watches established within {READY_TIMEOUT_S:g}s"
            )

    def _read(self) -> None:
        assert self._process is not None and self._process.stdout is not None
        for line in self._process.stdout:
            line = line.strip()
            if not line:
                continue
            if "Watches established" in line:
                # The handshake, not an event: from here the tree is observed.
                self._ready.set()
                continue
            if line.startswith("Setting up watches"):
                continue
            if self._ready.is_set() is False and ("Watches" in line or "Setting up" in line):
                continue
            if line.startswith("Watching new directory "):
                # An announcement, not an event. `-r` reports each watch it *adds*, so creating a
                # subdirectory of the tree prints `Watching new directory <path>` immediately before the
                # matching `CREATE,ISDIR <path>`: the tree is more observed than a moment before, not
                # less. A writer that organises its scratch into a subdirectory of the one path it may
                # write is the one most likely to print it, so reading it as a fault withholds the
                # verdict of the most compliant run.
                continue
            match = _EVENT_LINE.match(line)
            if match is None or "OVERFLOW" in line.upper():
                # A queue overflow or anything unparseable: the stream has a gap, so the observation is
                # worthless rather than clean.
                self.blind = self.blind or f"the event stream is not readable: {line!r}"
                continue
            path = pathlib.Path(match.group("path"))
            events = match.group("events")
            if not self._allowed(path):
                self.events.append(f"{events} {path}")

    def _allowed(self, path: pathlib.Path) -> bool:
        try:
            path.relative_to(self.allowed)
            return True
        except ValueError:
            return False

    def stop(self) -> tuple[list[str], str | None]:
        """Stop watching and report what was seen outside the working copy, and any blindness."""
        if self._process is not None:
            if self._process.poll() is None:
                self._process.terminate()
                try:
                    self._process.wait(timeout=5)
                except subprocess.TimeoutExpired:  # pragma: no cover - the watcher ignores SIGTERM
                    self._process.kill()
                    self._process.wait(timeout=5)
            elif self._thread is not None and self._thread.is_alive():
                # It exited on its own while we were running: the tail of the run was unobserved.
                self.blind = self.blind or f"{self.binary} exited before the run ended"
        elif self.blind is None:
            self.blind = "the watcher was never started"
        if self._thread is not None:
            self._thread.join(timeout=5)
        return list(self.events), self.blind
