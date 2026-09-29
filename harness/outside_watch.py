"""Observe writes outside the working copy while a file-mode session runs (plan D26, item 5).

D26 asks that the prover's shell be its working copy only. **Enforcing** that needs a boundary, and the one
this file's first version gave up on is not the only one this host has. Unprivileged user namespaces are
indeed unavailable — `unshare -r --mount` fails with

    unshare: write failed /proc/self/uid_map: Operation not permitted

so bubblewrap (which is not installed here, and would need the same) fails identically, and bare `chroot` is
out as well. But **a container boundary is available**, and it is a real one: `Docker 28.5.1` is installed
and usable by this user (in the `docker` group; the socket is `root:docker`). Measured —
`docker run --rm --read-only -v <package>:/work -w /work alpine` — the repository does not resolve inside
that container: no relative walk, no guessed absolute path, and no route through the `.lake` symlink, because
none of them are there; mounting the repository read-only as well makes all of them resolve again, which is
the control. So D26's "reported, never silently prevented" is the operative half **for the runner as it
stands** (uncontainerised), and a containerised runner would put this watch where it belongs — the second
layer rather than the only one. `tests/isolation-escape-contract.md` Scenario 5 carries the measurement and
its control.

Observation has to be event-based. A before/after digest sweep of the tree is defeated by a write followed
by a restore, which is precisely the trick this exists to catch — and a candidate with a shell can perform
it. `inotifywait` reports the events themselves; a hand-rolled `ctypes` watcher would drop its queue
silently, and silent dropping is a false "nothing was written outside", the one failure mode worse than not
watching at all. (The instrument drops a queue overflow itself, so a flood gets events lost with neither an
event nor a blindness: a real, accepted gap, recorded in `tests/outside-watch-contract.md` rather than
papered over here.)

The instrument is run as `inotifywait -q -c -m -r -e … <root>` (the shape
`tests/outside-watch-contract.md` contracts). `-c` makes each event exactly one CSV record,
`<watched dir>,<EVENTS>,<filename>`, quoting any newline, comma or quote inside a field, so a record is read
with `csv.reader` rather than by splitting physical lines. `-q` suppresses the tool's own commentary, so no
message has to be classified and **there are no exemptions**: a record the grammar cannot recognise blinds
the observation instead of being blessed by name. A named exemption is how an earlier revision turned a
write outside the allowed prefix into a certified-clean run.

The read is the layer this module is careful about, because it is silent when it goes wrong:

* the pipe is decoded with `errors="surrogateescape"` and `newline=""`, so an undecodable byte in a name is
  a **path**, not a dead reader, and a `\\r\\n` inside a name is not rewritten;
* the whole read loop is wrapped so that **any** exception sets `blind` — a reader that dies must never
  leave `blind` as `None`, which is the value meaning "observed";
* `stop()` checks the reader's liveness independently of the process's state, and treats a watcher that
  exited before the run ended as blindness.

Every way this can go blind is a refusal rather than silence, on the same principle as the rest of the
harness:

* any record the grammar cannot read as an event — wrong field count, an unrecognised event name, a parse
  error, a stream ending mid-record — means the event stream has a gap: `blind`;
* the watcher dying before we stop it, or its reader dying at all, means the tail of the run was
  unobserved: `blind`;
* a directory *created* outside the working copy is itself a write — recursive watches do not follow new
  directories, so treating the creation as the event closes the gap conservatively.

A run whose watcher reports either blindness or an outside event is not a closure, whatever its file says,
and the two are reported separately because their remedies have nothing in common.
"""

from __future__ import annotations

import csv
import io
import os
import pathlib
import secrets
import shutil
import subprocess
import threading
import time
from typing import IO, Iterator

#: The binary the flake declares. Absent means we cannot observe, which is `blind`, not "nothing happened".
WATCH_BINARY = "inotifywait"

#: Events worth watching: the ones that mean the tree changed. `CREATE,ISDIR` is included by `create`.
WATCHED_EVENTS = ("create", "modify", "delete", "move", "attrib")

#: Every event name `inotifywait` puts in the event field of a CSV record. A record's event field is a
#: comma-separated list drawn from this set, and anything else is not an event: **three fields is not
#: sufficient**, because a filename may itself contain commas, and accepting shape alone would promote a
#: truncated fragment to a whole path. Deliberately no overflow name: the tool consumes and drops
#: `IN_Q_OVERFLOW` rather than emitting it, so a clause recognising it would guard a line that never comes.
KNOWN_EVENTS = frozenset(
    {
        "ACCESS",
        "ATTRIB",
        "CLOSE",
        "CLOSE_NOWRITE",
        "CLOSE_WRITE",
        "CREATE",
        "DELETE",
        "DELETE_SELF",
        "IGNORED",
        "ISDIR",
        "MODIFY",
        "MOVE",
        "MOVE_SELF",
        "MOVED_FROM",
        "MOVED_TO",
        "OPEN",
        "UNMOUNT",
    }
)

#: How long to wait for the sentinel's own event before calling the observation blind.
READY_TIMEOUT_S = 10.0

#: The dedicated hidden subdirectory of `allowed` that holds the handshake sentinel.
PROBE_DIRNAME = ".watch-probe"

#: Sentinel filename prefix; a random nonce is appended so the path cannot pre-exist or be guessed.
SENTINEL_PREFIX = "probe-"

#: How long one sentinel attempt waits for its own event before a fresh nonce is tried. A sentinel written
#: while the recursive setup is still walking the tree is never seen, so the handshake repeats inside the
#: `READY_TIMEOUT_S` budget rather than calling that startup window blindness.
SENTINEL_RETRY_S = 0.5


def _decoded(pipe: IO[bytes] | IO[str]) -> IO[str]:
    """A text view of `pipe` that never raises on an undecodable byte and never translates newlines.

    `errors="surrogateescape"` turns an invalid byte into a surrogate-escaped path instead of an exception,
    and `newline=""` leaves a quoted `\\r\\n` inside a name byte-identical. A stream handed over already
    decoded (a text stream with no binary buffer) is used as-is: it has no decode layer to go wrong.
    """
    if isinstance(pipe, io.TextIOBase):
        buffer = getattr(pipe, "buffer", None)
        if buffer is None:
            return pipe
        pipe = buffer
    return io.TextIOWrapper(pipe, encoding="utf-8", errors="surrogateescape", newline="")


def _under(path: pathlib.Path, prefix: pathlib.Path) -> bool:
    """Whether `path` is lexically inside `prefix` — no symlink resolution, deliberately (Scenario 5)."""
    try:
        path.relative_to(prefix)
        return True
    except ValueError:
        return False


class OutsideWatch:
    """A recursive, event-based watch of a tree, with the working copy's prefixes as the allowed paths."""

    def __init__(
        self,
        root: pathlib.Path,
        allowed: pathlib.Path | Sequence[pathlib.Path],
        *,
        denied: Sequence[pathlib.Path] = (),
        binary: str = WATCH_BINARY,
    ) -> None:
        self.root = pathlib.Path(root)
        # One prefix or several. The working copy needs its own directory and the toolchain's local state
        # under `.lake` — `build/` and `config/`, both of which `lake build` writes inside the package.
        # `.lake/packages` is **not** allowed but denied explicitly: it is a symlink to the cache every
        # attempt shares, and containment here is lexical, so a write reached through it still names a path
        # under the package. Only the denial keeps that cache watched (contract Scenario 5).
        if isinstance(allowed, (str, pathlib.Path)):
            allowed = (allowed,)
        self.allowed = tuple(pathlib.Path(prefix) for prefix in allowed)
        self.denied = tuple(pathlib.Path(prefix) for prefix in denied)
        # The handshake sentinels are written inside the *working copy* — the first prefix — because the
        # probe's job is to show that a write the model could make is observed, and the build output is not
        # somewhere the model writes by hand.
        self.probe_root = self.allowed[0] if self.allowed else pathlib.Path(root)
        self.binary = binary
        self.events: list[str] = []
        self.blind: str | None = None
        self._process: subprocess.Popen | None = None
        self._thread: threading.Thread | None = None
        # Set when the watch shows an event for one of our own sentinels: until then the tree is unobserved.
        self._ready = threading.Event()
        # Every nonce sentinel issued, matched by exact assembled path. A set, because a late record for an
        # earlier attempt's sentinel is just as much proof that the watch works.
        self._sentinels: set[pathlib.Path] = set()
        # The hidden probe directory inside `allowed`, once it exists: ours to clean up.
        self._probe_dir: pathlib.Path | None = None

    # -- lifecycle ---------------------------------------------------------------------------------
    def start(self) -> None:
        """Begin watching, and wait until the watch is demonstrated to work before returning.

        `-q` suppresses `Watches established.`, so the handshake cannot be a message; waiting for a message
        would only prove the tool can print. Instead nonce sentinels are written inside `allowed` and
        `start` blocks until it observes its own event for one, because waiting for your own event proves
        the watch works. The sentinel proves that subtree is watched; it does **not** prove the whole `-r`
        tree was established, which the text handshake did — a weaker axis the contract accepts explicitly,
        traded for observing behaviour instead of a claim.
        """
        binary = shutil.which(self.binary)
        if binary is None:
            self.blind = f"{self.binary} is not on PATH: the working-copy-only boundary cannot be observed"
            return
        probe_dir = self.probe_root / PROBE_DIRNAME
        try:
            # Created *before* the watcher starts, so the recursive setup includes it and a sentinel's own
            # event has a watch to arrive on.
            probe_dir.mkdir(parents=True, exist_ok=True)
        except OSError as error:  # pragma: no cover - a real host failure, reported rather than fatal
            self.blind = f"the watch probe directory {probe_dir} could not be created: {error}"
            return
        self._probe_dir = probe_dir
        args = [binary, "-q", "-c", "-m", "-r"]
        for event in WATCHED_EVENTS:
            args += ["-e", event]
        args.append(str(self.root))
        try:
            self._process = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        except OSError as error:  # pragma: no cover - a real host failure, reported rather than fatal
            self.blind = f"{self.binary} could not be started: {error}"
            return
        self._thread = threading.Thread(target=self._read, daemon=True)
        self._thread.start()
        self._handshake(probe_dir)

    def _handshake(self, probe_dir: pathlib.Path) -> None:
        """Write nonce sentinels in the probe directory until one's own event is observed.

        One attempt is not enough: a sentinel written while the recursive setup is still walking the tree is
        silently missed, and that startup window is not blindness. Each attempt is a fresh nonce, matched on
        its exact assembled path.
        """
        deadline = time.monotonic() + READY_TIMEOUT_S
        while not self._ready.is_set() and time.monotonic() < deadline:
            if not self._probe_once(probe_dir):
                return
            self._ready.wait(timeout=min(SENTINEL_RETRY_S, max(0.0, deadline - time.monotonic())))
        if not self._ready.is_set():
            self.blind = self.blind or (
                f"{self.binary} did not show an event for any of its own watch sentinels within "
                f"{READY_TIMEOUT_S:g}s: the watch is not established"
            )

    def _probe_once(self, probe_dir: pathlib.Path) -> bool:
        """Create and delete one nonce sentinel; `False` (with `blind` set) if it cannot be written.

        It is created `O_CREAT|O_EXCL` so a collision is `blind` rather than a crash, and deleted
        immediately — a DELETE inside `allowed` is benign by definition.
        """
        sentinel = probe_dir / f"{SENTINEL_PREFIX}{secrets.token_hex(16)}"
        try:
            descriptor = os.open(sentinel, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
            os.close(descriptor)
        except FileExistsError:
            self.blind = f"the watch sentinel {sentinel} already exists"
            return False
        except OSError as error:  # pragma: no cover - a real host failure, reported rather than fatal
            self.blind = f"the watch sentinel {sentinel} could not be written: {error}"
            return False
        self._sentinels.add(sentinel)
        try:
            os.unlink(sentinel)
        except OSError as error:  # pragma: no cover - a real host failure, reported rather than fatal
            self.blind = f"the watch sentinel {sentinel} could not be removed: {error}"
            return False
        return True

    def _read(self) -> None:
        """Read the instrument's records to the end of the stream; **any** failure is blindness.

        The whole loop is wrapped: a reader that dies for any reason must set `blind`, because `None` is
        the value meaning "observed" and a dead reader left at `None` certifies a boundary nobody watched.
        """
        try:
            self._consume()
        except BaseException as error:  # noqa: BLE001 - a dead reader must never look like silence
            self.blind = self.blind or f"the event stream could not be read: {error!r}"

    def _consume(self) -> None:
        pipe = None if self._process is None else self._process.stdout
        if pipe is None:
            self.blind = self.blind or f"{self.binary} produced no event stream"
            return
        stream = _decoded(pipe)
        consumed: list[str] = []

        def lines() -> Iterator[str]:
            # Record the physical line each record is built from: a CSV parse error has no record to
            # report, and the offender has to be named for the blindness to be actionable.
            for line in stream:
                consumed.append(line)
                yield line

        reader = csv.reader(lines())
        start = 0
        final_raw = ""
        try:
            for record in reader:
                # The raw text this record was built from: `csv.reader` yields a record only once its
                # last physical line has been pulled, so `consumed[start:]` is exactly that record.
                final_raw = "".join(consumed[start:])
                start = len(consumed)
                self._record(record)
        except csv.Error as error:
            offending = consumed[-1] if consumed else ""
            self.blind = self.blind or f"the event stream is not readable ({error}): {offending!r}"
            return
        # `-c` terminates every record, so the last record must end at a terminator, outside every quote.
        # `csv.reader` accepts an unterminated quoted field at end of stream without complaint, so the
        # check is made here. It is *adequate for this instrument*, not a termination proof: an even quote
        # count alone has a passing counterexample (`/root"x/,CREATE,"abc` is accepted though it ends
        # mid-quote). What rules that out is the instrument's own quoting — every `"` inside a field is
        # doubled, so a raw odd quote cannot appear — together with the only other thing on the raw stream,
        # `Couldn't watch <path>: <strerror>`, whose second field always carries `': '` and so can never
        # equal a bare event name. A future reader should not lean on the count as an invariant; the
        # reachability argument is why it holds here.
        if final_raw and (not final_raw.endswith(("\n", "\r")) or final_raw.count('"') % 2):
            self.blind = self.blind or f"the event stream ended mid-record: {final_raw!r}"

    def _record(self, record: list[str]) -> None:
        """Classify one CSV record: a recognised event, or blindness naming the offending input."""
        text = ",".join(record)
        if len(record) != 3:
            self.blind = self.blind or f"the event stream is not readable: {text!r}"
            return
        directory, names, filename = record
        if not names or not all(name in KNOWN_EVENTS for name in names.split(",")):
            self.blind = self.blind or f"the event stream is not readable: {text!r}"
            return
        path = pathlib.Path(directory) / filename
        if path in self._sentinels:
            # Our own handshake: the watch is demonstrated to work, and the event is inside `allowed`.
            self._ready.set()
            return
        if not self._allowed(path):
            self.events.append(f"{names} {path}")

    def _allowed(self, path: pathlib.Path) -> bool:
        """Inside an allowed prefix, and not inside a denied one.

        The denial is what keeps the shared dependency cache watched while `.lake` is allowed: containment
        is lexical, so a write reached through the `.lake/packages` symlink still *names* a path under the
        package, and only an explicit denial keeps that cache out of the allowed set (Scenario 5).
        """
        if not any(_under(path, prefix) for prefix in self.allowed):
            return False
        return not any(_under(path, prefix) for prefix in self.denied)

    def stop(self) -> tuple[list[str], str | None]:
        """Stop watching and report what was seen outside the working copy, and any blindness."""
        if self._process is None:
            if self.blind is None:
                self.blind = "the watcher was never started"
            return list(self.events), self.blind
        # The reader's liveness is checked independently of the process's state: a reader that died while
        # the watcher was still running is blindness, not silence.
        if self._thread is not None and not self._thread.is_alive() and self._process.poll() is None:
            self.blind = self.blind or (
                f"the {self.binary} event stream reader stopped while the watcher was still running"
            )
        if self._process.poll() is not None:
            # It exited on its own while we were running: the tail of the run was unobserved.
            self.blind = self.blind or f"{self.binary} exited before the run ended"
        else:
            self._process.terminate()
            try:
                self._process.wait(timeout=5)
            except subprocess.TimeoutExpired:  # pragma: no cover - the watcher ignores SIGTERM
                self._process.kill()
                self._process.wait(timeout=5)
        if self._thread is not None:
            self._thread.join(timeout=5)
            if self._thread.is_alive():  # pragma: no cover - a wedged reader, reported rather than waited on
                self.blind = self.blind or f"the {self.binary} event stream reader did not finish"
        if self._probe_dir is not None:
            # The sentinels are already gone; the probe directory is ours, inside `allowed`, and a removal
            # there is benign by definition.
            shutil.rmtree(self._probe_dir, ignore_errors=True)
        return list(self.events), self.blind
