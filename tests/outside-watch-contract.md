# Contract: the working-copy-only boundary watch

Owner: planner. Subject: `harness/outside_watch.py` — the recursive event watch that reports whether a
run wrote outside its working copy, and whose `blind` field reports whether it could observe at all. The
boundary *rule* it enforces (a write outside the attempt's allowed prefix withholds the verdict) is
stated in `tests/paxos-attempt-isolation-contract.md`; this contract covers the instrument.

**One requirement, two ways to fail it.** The watch must never certify a boundary it did not observe, and
it must never call an observed run blind. Every revision below came from a measured counterexample in one
of those directions, and the failures have been in this order:

1. **The instrument's own reassurance was read as blindness.** `inotifywait -m -r` prints `Watching new
   directory <path>` on stdout when it *adds* a watch, so a run organising scratch into a subdirectory of
   the one path it may write — the most compliant thing it can do — declared itself unobserved and
   forfeited its verdict.
2. **Naming that line benign turned a fail-closed answer into a silent one.** With `--format`, a path
   containing a newline splits one record across two physical lines: the first fragment truncates to the
   allowed directory and is classified *inside*; the second is a bare fragment that the exemption matched
   and skipped. Measured: `blind: None`, `events: []` — **a write outside the allowed prefix certified
   clean**. Naming one message benign bought a false certification to cure a false withholding, which is
   the wrong trade.
3. **The decode layer is silent, and it is the live defect now.** A filename containing one invalid-UTF-8
   byte (`b"bad\xff.lean"`) written outside `allowed` is emitted raw by the instrument; the reader is
   created with `Popen(text=True)`, so decoding raises `UnicodeDecodeError`, **the reader thread dies**,
   and `stop()` returns `blind=None`. Measured against the real harness: `thread_alive: False |
   blind: None | events: []` — a boundary certified that was never observed. Surrogate-encoded bytes
   (`0xED 0xA0 0x80`) behave the same way. A third gap sits beside it: `stop()` only consults
   `is_alive()` on the branch where the process has *already exited*, so **a dead reader with a live
   process is never noticed at all**. This defect predates every change in this sequence — the original
   parser had it too — and it is why the requirements below are about the *read*, not the *grammar*.

**Contracted interface.** `OutsideWatch(root, allowed, *, binary=WATCH_BINARY)`; `start()` blocks until
the watch is demonstrated to work; `stop()` returns `(events, blind)`. `blind` is a string saying why the
observation is worthless, and `None` when the tree was observed for the whole run; `events` lists every
event whose path is outside `allowed`, formatted `<EVENTS> <path>`.

## The invocation and the read

**Invocation:** `inotifywait -q -c -m -r -e create -e modify -e delete -e move -e attrib <root>`.

- **`-c`** makes each event one CSV record, `<watched dir>,<EVENTS>,<filename>`, quoting any newline,
  comma or quote inside a field rather than emitting it raw. Measured: a newline in a filename **and** in
  the directory component of `%w` is quoted, a `,` is quoted, and a `"` is doubled — each yielding exactly
  one record with the path intact. `--format '%e %w%f\0'` does **not** work: the format prints a literal
  `\0` and the record still splits.
- **`-q`** suppresses the instrument's commentary, including `Setting up watches.` and `Watches
  established.`, so there is no announcement to classify and nothing is blessed by name. Errors are *not*
  suppressed, which is correct: a `Couldn't watch …` line reaching the stream is blindness.

**Reading.** The pipe is read **without universal-newline translation and without strict decoding**:
`io.TextIOWrapper(pipe, encoding="utf-8", errors="surrogateescape", newline="")`, or the bytes are read
directly. An invalid byte then becomes a **path**, not an exception — surrogate-escaped, comparably
prefix-checked, and reportable. Records are then taken with **`csv.reader` over that wrapper**, not by
splitting physical lines, because one record may legitimately span several. The whole read loop is wrapped
so that **any** exception sets `blind`: a reader that dies must never leave `blind` as `None`, whatever
killed it, because `None` is the value that means "observed". `stop()` checks the reader's liveness
**independently of the process's state**, so a dead reader with a live watcher is blindness rather than
silence.

**Grammar.** Every record must be a three-field CSV event record whose event field is a **recognised
event name** — three fields is not sufficient — and the event path is the watched directory joined with
the filename. Anything else is **blindness**: a different field count, an unrecognised event name, a
record that cannot be parsed, a stream that ends mid-record, a line the instrument never promised. There
are **no exemptions**: no message is benign, so there is no list to keep correct and no future message
can be silently treated as serving.

**The recognised set is measured, not guessed, because a name missing from it is a false withholding.**
Provoking every subscribed operation against the real instrument on a temporary tree — directory create,
file create, modify, attrib, rename within the tree, delete file, delete directory, move out of the tree
and back in — emits exactly `CREATE`, `CREATE,ISDIR`, `MODIFY`, `ATTRIB`, `MOVED_FROM`, `MOVED_TO`,
`DELETE` and `DELETE,ISDIR`, and **every one is in the set**. `DELETE_SELF`, `MOVE_SELF` and `IGNORED`
arise only when the watched root itself is removed or the watch is dropped, and are in the set too. The
set also names events unreachable under this `-e` subscription (`ACCESS`, `OPEN`, `CLOSE*`, `UNMOUNT`),
which is inert in this direction: an unrecognised **token** blinds, conservatively, whereas a blessed
**message** goes silent — and a superset of event names is exactly the inverse of the exemption that had
to be retired, where naming one message benign is what turned a refusal into a pass.

## The handshake is a sentinel, and it is weaker than what it replaces — deliberately

`-q` costs the `Watches established.` line, and waiting for a *message* only proves the tool can print.
`start()` therefore writes a sentinel **inside `allowed`** and waits until it observes its own event for
it, because waiting for your own event proves the watch works.

- The sentinel is created `O_CREAT|O_EXCL` with a **random nonce** in its name, and matched on the
  **exact assembled path**; a name collision is `blind`, never a crash.
- **One sentinel is not enough, and that is measured rather than cautious.** A sentinel written while the
  recursive setup is still walking the tree is **silently missed** — observed against the real instrument,
  where a single sentinel blinded a healthy watch. The handshake therefore retries with a **fresh nonce**
  within the ready budget and reports blindness only when no sentinel's event arrives at all. A handshake
  is a new way to trip, and this is its own false-withholding mode.
- `allowed` is `.runs`, which is the run's own output directory, so the sentinel belongs in a dedicated
  hidden subdirectory of it (for example `.runs/.watch-probe/`) and is deleted immediately — a DELETE
  inside `allowed` is benign by definition.
- **The trade, stated so it is made rather than inherited:** a sentinel inside `allowed` proves that
  subtree is watched. It does **not** prove the whole `-r` tree is established, which the text handshake
  did establish. The sentinel is strictly weaker on that axis and stronger on the one that matters
  (it observes behaviour instead of a claim), and this contract accepts the weaker half explicitly.

**No overflow record exists, so no clause may claim one.** Measured three ways: the kernel delivers
`IN_Q_OVERFLOW` (a ctypes `inotify_init1` with `IN_ALL_EVENTS` and 30,000 creates produced 16,385 raw
events, exactly one with `mask & 0x4000`), while `inotifywait` **consumes and drops it** in every
configuration tried (`-q -c`: 16,384 event lines, `overflow_lines=0`; the harness's own un-quoted format
without `-q`: none either). The man page is explicit — *"It is assumed the inotify event queue will never
overflow."* An earlier revision of this contract required an overflow record to be blindness; **that
clause is removed, because it tested a line the instrument never emits**, and a test asserting it would
pin behaviour that cannot occur.

The limitation it leaves is recorded rather than papered over: **a candidate that floods the tree gets
events dropped with neither an event nor blindness** — a silent gap, pre-existing and not fixable by
parsing, because the instrument discards the one signal that would announce it. Detecting it would need a
different instrument or a self-observed probe of known density; neither is in scope here, and the contract
says so rather than implying the loop is airtight.

## What the boundaries are, measured

- **Quoted, one record:** a newline in a filename; a newline in the `%w` directory component; a comma; a
  doubled quote.
- **A lone CR (`0x0D`) is not quoted, and where it sits decides what happens.** *Inside* a name the record
  splits, and the fragment cannot be read as an event, so it is **blindness** — a false withholding, the
  safe direction. *Trailing* a name it arrives as `…,CREATE,trail\r\n`, which `newline=""` reads as one
  CRLF line ending, so `csv` strips the CR: the event **is** reported, without that one byte. Both cases
  leave the directory field — the one that decides allowed-ness — intact, so neither hides an outside
  write, and the trailing case is **unfixable at the parse layer** because the byte sequence is genuinely
  ambiguous between a name ending in CR and a record ended by CRLF. This clause previously claimed that a
  lone CR "degrades to blindness" and labelled the reasoning `[INFERENCE]`; measurement retired it, and the
  one-byte path truncation is recorded as the known cost rather than as a refusal.
- **Quoted but mangled by universal newlines:** a `\r\n` inside a name survives `-c` quoting and is then
  rewritten to `\n` by `text=True`'s newline translation, corrupting the path
  (`'f\r\ncrnl.lean'` → `'f\ncrnl.lean'`). Which is why the read specifies `newline=""`.
- **`attempt-005`'s exact shape is gone** under `-q -c`: a writer creating `.runs/probe/` yields only
  `CREATE,ISDIR` inside `allowed` — no event, no blindness, no forfeited verdict. The residual class is
  **control characters and undecodable bytes**, not the ordinary subdirectory case.

## Scenario 1 — an undecodable filename is a path, not a dead watcher

- **Actor**: a run whose shell writes outside its working copy under a name containing an invalid UTF-8
  byte — a name the instrument emits raw.
- **Boundary**: the read layer of `OutsideWatch` and the `blind`/`events` it reports.
- **Given**: a pipe carrying a real event record whose filename field is `b"outside\xff.lean"`, plus a
  well-formed record after it.
- **When**: the stream is read to its end.
- **Then**: the record is reported as an **event** with a surrogate-escaped path, the following record is
  also reported, `blind` is `None`, and the reader is still alive — the undecodable byte is a path, not a
  failure. If the reader dies for any reason, `blind` is set: an unobserved run is never reported as
  observed.
- **Why**: this is defect 3 above. Today the reader is created with `text=True`, the decode raises into
  the thread, the thread dies, and `stop()` returns `blind=None` with no events — a boundary certified
  that was never observed. It is the same silence as the exemption, reached from a different direction,
  and it is the defect the next change has to close.
- **Expected first failure before correction**: reading the stream raises `UnicodeDecodeError` out of the
  reader (the test observes the exception or a dead thread with `blind is None`), and no event is
  reported. The contract does not require the *exception* to be caught so much as the loss to be
  impossible: an unreadable run must be blind and an undecodable name must be an event.

## Scenario 2 — a control character degrades to blindness, never to certification

- **Actor**: the same writer, using a lone CR in a name.
- **Boundary**: the same read layer.
- **Given**: the two physical lines a lone CR produces — the truncated record and the fragment.
- **When**: the stream is read.
- **Then**: `blind` is set and names the offending input; nothing is certified and nothing is silently
  dropped.
- **Why**: this is the residual class after the newline fix. It is the safe direction — a false
  withholding rather than a false certification — and the contract requires that direction explicitly
  rather than leaving it to whichever way the fragment happens to parse.
- **Expected first failure before correction**: none required. The behaviour is asserted so that a future
  change which made fragments *events* would be caught, not because today's code fails it.

## Scenario 3 — the quoted forms do not split a record

- **Actor**: a writer whose names contain the characters `-c` is supposed to quote.
- **Boundary**: the same read layer.
- **Given**: one stream carrying records for a newline in a filename, a newline in the watched directory
  component of `%w`, a comma in a name, a doubled quote in a name, and a `\r\n` in a name.
- **When**: the stream is read.
- **Then**: each is exactly one event, with its path intact and **byte-identical** to what the writer
  used — including the `\r\n`, which is why the read disables newline translation; `blind` is `None`.
- **Why**: quoting is what makes the stream unambiguous, and the two ways it can still go wrong are a
  reader that translates newlines (corrupting `\r\n`) and a parser that splits physical lines instead of
  records.
- **Expected first failure before correction**: the current parser matches physical lines with a regular
  expression, so the quoted multi-line records do not parse; the `\r\n` variant would additionally be
  corrupted by `text=True`.

## Scenario 4 — a record that is not a recognised event is blindness

- **Actor**: the same writer, on a run whose boundary may genuinely be unobserved.
- **Boundary**: the same read layer.
- **Given**: in turn, a line the grammar cannot classify; a **three-field** record whose event field is
  not a recognised event name; and a record truncated by the end of the stream.
- **When**: each stream is read.
- **Then**: `blind` is set and names the offending input.
- **Why**: three fields is not evidence of an event. Without the event-name check a fragment that happens
  to contain two commas — a filename can — would be read as an event, which is how a truncated path gets
  promoted to a whole one. This is the tightening that keeps the grammar from being satisfied by shape
  alone.
- **Expected pre-correction behaviour**: the unclassifiable line already blinds and must keep doing so.
  The three-field-with-an-unknown-event case cannot be a red against today's parser, because that parser
  rejects the whole CSV record as unreadable — so it passes today and is a **guard-rail**, not a red. It
  guards the *new* grammar: once records are taken with `csv.reader`, a fragment that happens to contain
  two commas would be read as an event unless the event name is checked against a known set.

## What this contract is not

The scenarios drive the read layer with a stream rather than spawning `inotifywait`: the defects are in
how the stream is read and classified, a real invocation would be neither deterministic nor fast, and the
record shapes are the ones measured from the real tool. What the scenarios cannot show is that the
instrument emits nothing else under `-q -c` — and by design that does not matter, because there are no
exemptions: an unrecognised record is blindness, so an unknown message degrades to a refusal rather than
to a silent pass. The two things this contract explicitly does **not** claim are that the sentinel proves
the whole `-r` tree is watched, and that a flooded queue is detectable; both are stated above as accepted
limits.

The instrument's own failure is its own verdict class: `watch_blind` and `outside_events` are separate
fields and must stay separate in every report. A run whose boundary was never observed is not a run that
breached it and not a run that failed to prove anything — three classes, three opposite responses — so a
single count of "non-closures" merges findings whose remedies have nothing in common.
