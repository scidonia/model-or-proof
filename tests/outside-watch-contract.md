# Contract: the working-copy-only boundary watch

Owner: planner. Subject: `harness/outside_watch.py` — the recursive event watch that reports whether a
run wrote outside its working copy, and whose `blind` field reports whether it could observe at all. The
boundary *rule* it enforces (a write outside the attempt's allowed prefix withholds the verdict) is
stated in `tests/paxos-attempt-isolation-contract.md`; this contract covers the instrument.

**The design, after a real defect made the earlier one unsound.** The watch must never certify a boundary
it did not observe, and it must never call an observed run blind. An earlier version of this contract
solved the second half by *naming* `inotifywait`'s informational lines as benign, and an independent
review produced a counterexample to it (recorded below) in which naming a line as benign converted a
fail-closed response into a silent one. The design that replaces it has **no exemptions at all**: the
instrument is asked for a machine-readable stream, so there is no announcement to classify, and every
record that is not an event is blindness.

**Contracted interface.** `OutsideWatch(root, allowed, *, binary=WATCH_BINARY)`; `start()` blocks until
the watch is demonstrated to work; `stop()` returns `(events, blind)`. `blind` is a string saying why the
observation is worthless, and `None` when the tree was observed for the whole run; `events` lists every
event whose path is outside `allowed`.

**The invocation.** `inotifywait -q -c -m -r -e create -e modify -e delete -e move -e attrib <root>`:

- **`-c`** makes each event one CSV record, `<watched dir>,<EVENTS>,<filename>`, with any newline,
  comma or quote inside a field escaped rather than emitted raw. This is what makes the stream
  unambiguous, and it is not optional: see the counterexample.
- **`-q`** suppresses the instrument's own commentary, including `Setting up watches.` and
  `Watches established.` — so the announcement this contract used to name does not appear at all, and
  nothing has to be classified as benign.

**The handshake is a sentinel, not a message.** `-q` costs the "Watches established" line, and replacing
it with a *message* would only prove the tool said something. `start()` instead writes a probe file
**inside `allowed`** and waits until it observes its own event for it. Waiting for your own event proves
the watch *works*; waiting for a line proves the tool can print. A probe that is not observed within the
ready timeout is `blind`.

**The parser has no exemptions.** Every record must be a three-field event record; the event path is the
watched directory joined with the filename. An event outside `allowed` is reported as `<EVENTS> <path>`,
which is the format the rows already use. A record with any other shape, a field count that is not three,
a stream that ends mid-record, or anything else — **including a queue overflow and a failure to add a
watch** — is `blindness`. Fail-closed is uniform, so there is no list of blessed messages to keep correct,
and no future instrument message can silently be treated as serving.

**Contingency, recorded so it is not re-derived.** If `-q` turns out to suppress the queue-overflow
report as well as the commentary, then `-q` is disqualified outright — a suppressed overflow is a silent
gap, which is the one failure this instrument exists to prevent — and the design becomes `-c` **without**
`-q`: the two fixed handshake strings stay the only non-records (they are constants the tool prints, not
paths it derived, so naming them carries none of the risk that naming the new-directory announcement did),
every other non-record is blindness, and the newline case stays solved by `-c`. Which of the two applies is
decided by measurement, not by preference.

## Why: the counterexample that retired the earlier design

A model in this harness has a shell, which is the threat model the module already states. A path
containing a **newline** splits one record into two physical lines. Writing a sibling of `.runs` named
`.runs\nWatching new directory xyz`, with the un-quoted `--format %e %w%f` invocation and the earlier
parser:

- fragment one, `CREATE,ISDIR <root>/pkg/.runs`, is a **truncated** path that equals `allowed`, so it is
  classified inside and is not an event;
- fragment two, `Watching new directory xyz`, is a **bare fragment**, not an announcement — but it
  matched the exemption's prefix and was **skipped**.

Measured result: `blind: None`, `events: []` — a write outside the allowed prefix **certified clean**.
Pre-correction, fragment two failed the event grammar and set `blind`; the exemption is what replaced
that fail-closed answer with silence. That is precisely the trade the earlier contract named and got
wrong in the other direction: a parser loosened until nothing is blind trades a false withholding for a
false certification, which is the worse error.

Two instrument facts were measured, not assumed, because the replacement is worthless if either is false:

- `--format '%e %w%f\0'` does **not** delimit: `inotifywait` prints a literal `\0`, and the record still
  splits across physical lines.
- `-c` escapes the newline inside a quoted field, and `csv.reader` over the stream yields **exactly one**
  record with the path intact — so the parser must read the **stream** with a CSV reader, not physical
  lines, since one record may legitimately span several.

**A path containing a newline is the adversarial case, not an exotic regression.** An actor with a shell
chooses its filenames, so a newline in one is the shape it reaches for when the instrument's record
format is the thing being evaded. It is therefore Scenario 1 rather than a footnote.

## Scenario 1 — a newline in a path does not split a record

- **Actor**: a run whose shell writes outside its working copy under a name chosen to contain a newline.
- **Boundary**: `OutsideWatch._read`, which turns the instrument's stream into events or blindness.
- **Given**: a stream carrying the CSV record `<root>/pkg/,CREATE,".runs\nWatching new directory xyz"` —
  one record whose filename field contains a newline, spanning two physical lines — followed by
  `<root>/pkg/,CREATE,outside.lean`, with `<root>/pkg/.runs` the allowed path.
- **When**: the stream is read to its end.
- **Then**: **both** creates are reported as events, the first with its full path including the newline;
  `blind` is `None`; and the run's boundary is not certified clean by a fragment.
- **Why**: this is the counterexample above. Before the correction the newline path was split, its first
  fragment was classified inside and its second was silently skipped — a write outside the prefix that no
  reader would ever see.
- **Expected first failure before correction**: the parser matches records with a regular expression over
  physical lines, so the quoted multi-line record does not parse: the fragment `Watching new directory
  xyz"` is skipped by the exemption and the record is truncated, and the first event's path assertion
  fails.

## Scenario 2 — a bare fragment is not a record

- **Actor**: the same writer, with an instrument invocation that does not delimit (a regression to
  `--format`, or a future option that reintroduces raw newlines).
- **Boundary**: the same parser.
- **Given**: the two physical lines that the un-quoted format produces for that path — the truncated
  record and the fragment — followed by a well-formed three-field record.
- **When**: the stream is read.
- **Then**: `blind` is set and names the offending input, because a fragment is not a record and the
  stream therefore has a gap; the run's boundary is **not** certified.
- **Why**: this is what makes the exemption's *absence* load-bearing. With the exemption present the
  fragment was skipped and the stream was declared clean; with a uniform grammar the same bytes are
  blindness, so a delimiter regression degrades into an honest refusal instead of a silent pass.
- **Expected first failure before correction**: the fragment is skipped by the exemption, `blind` stays
  `None`, and the assertion fails.

## Scenario 3 — an unreadable record is still blindness

- **Actor**: the same writer, on a run whose boundary may genuinely be unobserved.
- **Boundary**: the same parser.
- **Given**: a well-formed handshake, then either a line the grammar cannot classify, or a
  queue-overflow record, each followed by a real event.
- **When**: each stream is read.
- **Then**: `blind` is set and names the offending input.
- **Why**: the correction for the counterexample is a **uniform grammar with no exemptions**, not a
  general tolerance. A parser that ignored what it could not read would report a clean boundary for a run
  it never observed — the failure the instrument exists to prevent.
- **Expected pre-correction behaviour**: these cases already pass and must keep passing; they are the
  guard against any future "fix" that loosens the grammar.

## What this contract is not

The scenarios drive the parser with a stream rather than spawning `inotifywait`: the defect is the
classification of that stream, a real invocation would be neither deterministic nor fast, and the record
shapes above are the ones measured from the real tool (`-c` quoting an embedded newline; `-q` suppressing
the handshake). What the scenarios cannot show is that `inotifywait` emits nothing else under `-q -c` — so
a future line that trips the parser is **blindness by construction**, which needs no exemption and no
scenario; that property is the point of removing them.

The instrument's own failure is its own verdict class: `watch_blind` and `outside_events` are already
separate fields and must stay separate in every report. A run whose boundary was never observed is not a
run that breached it and not a run that failed to prove anything — three classes, three opposite
responses — so a single count of "non-closures" merges findings whose remedies have nothing in common.
