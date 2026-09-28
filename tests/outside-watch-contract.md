# Contract: the working-copy-only boundary watch

Owner: planner. Subject: `harness/outside_watch.py` — the recursive event watch that reports whether a
run wrote outside its working copy, and whose `blind` field reports whether it could observe at all. The
boundary *rule* it enforces (a write outside the attempt's allowed prefix withholds the verdict) is
stated in `tests/paxos-attempt-isolation-contract.md`; this contract covers the instrument itself,
because the instrument has had no contract of its own and the defect below is a classification failure
inside it rather than a wrong rule.

Why the parser is contractual. `inotifywait` multiplexes its own announcements with its event records on
one stream, and the two failure directions cost different things: calling an observed run *blind* throws
away a valid closure, while trusting a stream with a gap certifies a boundary nobody watched. The
announcements are indistinguishable from faults unless the contract names them, so it names them.

**Contracted interface.** `OutsideWatch(root, allowed, *, binary=WATCH_BINARY)`; `start()` blocks until
the instrument reports its watches established; `stop()` returns `(events, blind)`. `blind` is a string
describing why the observation is worthless, and `None` when the tree was observed for the whole run;
`events` lists every event whose path is outside `allowed`.

**What is an announcement, what is an event, and what is blindness.**

- `inotifywait -m -r` prints `Setting up watches.` and `Watches established.` before any event. The
  second is the handshake `start()` waits on; neither is an event.
- It also prints **`Watching new directory <path>` on stdout whenever it adds a watch for a newly created
  subdirectory** — a reassurance that the tree is *more* observed than before, not less. It is an
  announcement: neither blindness nor an event.
- Every other line must parse as `<EVENTS> <path>`, where `<EVENTS>` is an upper-case event list. A line
  that does not, **including a queue overflow and a failure to add a watch**, is **blindness** — because a
  stream with a gap in it is worthless rather than clean.

Fail-closed is right for the unknown and wrong for the known-good; the whole content of this contract is
which lines are which.

## Scenario 1 — the watch reads its instrument's announcements as serving, not as blindness

- **Actor**: a file-mode attempt that organises its scratch into a subdirectory of its working copy — the
  most compliant behaviour available to it, since the working copy is the only path it may write.
- **Boundary**: `OutsideWatch._read`, which classifies the instrument's stream.
- **Given**: a stream carrying the two handshake lines, then `Watching new directory <root>/pkg/probe/`,
  then the matching `CREATE,ISDIR <root>/pkg/probe`, then `CREATE <root>/pkg/probe/scratch.lean`, with
  `<root>/pkg/.runs` as the allowed path.
- **When**: the stream is read to its end.
- **Then**: `blind` is `None` — the run was observed; the two `probe/` records are reported as **events**,
  because they lie outside the allowed path; and the announcement contributes **no event of its own**,
  since a reassurance is not a write.
- **Why**: this is the shape that withheld a real closure in the fresh theorem cell. The model created
  `.runs/probe/`, `inotifywait` announced the watch it added, the parser called the stream unreadable, and
  a closure that elaborates within the permitted axioms forfeited its verdict. Reproduced by hand:
  `inotifywait -m -r --format "%e %w%f" -e create -e modify -e delete -e attrib <root>` prints
  `Watching new directory <path>/` immediately **before** the matching `CREATE,ISDIR`.
- **Expected pre-correction failure**: `Watching new directory …` matches neither the handshake nor the
  event grammar, so the parser sets `blind` to `the event stream is not readable: …` and the `blind is
  None` assertion fails. Nothing else in the scenario fails, so the red is that assertion alone.

## Scenario 2 — an unreadable line is still blindness

- **Actor**: the same writer, on a run whose boundary may genuinely be unobserved.
- **Boundary**: the same parser.
- **Given**: the handshake, then either a diagnostic line the grammar does not classify, or a
  queue-overflow record, each followed by a real event.
- **When**: each stream is read.
- **Then**: `blind` is set and names the offending line, and the run's boundary is not certified — the
  event that follows a gap is not treated as the whole truth.
- **Why**: the correction for Scenario 1 is a **named exemption**, not a general tolerance. A parser that
  ignored whatever it could not read would report a clean boundary for a run it never observed, which is
  the failure this instrument exists to prevent.
- **Expected pre-correction behaviour**: these cases already pass and must keep passing; they are the
  guard against fixing Scenario 1 by making the parser permissive.

## The instrument's own failure is its own verdict class

`watch_blind` and `outside_events` are already separate fields, and they must stay separate **in every
report** too: a run whose boundary was never observed is not a run that breached it, and it is not a run
that failed to prove anything. The three call for opposite responses — a breach is the guard working,
blindness is the instrument failing, a proof failure is the route failing — so any table that reports a
single count of "non-closures" merges findings whose remedies have nothing in common. That is why
attempt-005 had to be read from its transcript before its arithmetic meant anything: `3 of 5` reads as
"two failures to prove" and was in fact one write-location accident and one instrument failure with a
clean transcript.

The rule this contract takes from that, stated here rather than left as a comment at the parser: **an
instrument that fails closed on input it does not recognise punishes the actor it cannot model, and the
more disciplined the actor, the likelier it trips.** Attempt-005 is the proof — its only offence was
creating a subdirectory inside the one path it was allowed to write — and the consequence for the fix is
that the exemption must be **named** (this announcement, observed from the instrument) and never general
(ignore what cannot be parsed). A parser loosened until nothing is blind trades a false withholding for a
false certification, which is the worse error by a distance.

## What this contract is not

The scenarios drive the parser with a line stream rather than spawning `inotifywait`: the defect is a
classification of that stream, a real invocation would be neither deterministic nor fast, and the real
line order was demonstrated once by hand and is the stream above. What the scenarios cannot show is that
`inotifywait` prints nothing *else* benign — so a future line that trips the parser should be added to
Scenario 1's stream by the planner, with its observation recorded, rather than tolerated by a looser rule.
