"""Audit a file-mode cell's per-attempt transcripts for prior-proof reuse.

The operational-independence gate (``tests/paxos-attempt-isolation-contract.md``, the section after
the scenarios; ``docs/protocol.md`` §4.7) says a cell's median is an independent-cost operand **only**
if every attempt's complete tool-call transcript has been inspected and shows no read or copy of an
earlier same-tier proof. This script is that inspection, made executable so a reader can re-run it and
a reviewer can check it rather than trusting a narrative.

Run it against the cell's **session root** — the directory whose children are the per-attempt OMP
session directories, e.g. ``--sessions results/paxos-calibration/omp``::

    python -m scripts.audit_attempts --sessions results/paxos-calibration/omp
    python -m scripts.audit_attempts --sessions <root> --json > <cell>/audit.json

What is scanned
---------------
**Every** tool call in every ``*.jsonl`` under each attempt directory — not a search for path-shaped
strings. Each call's full command text (and, for non-shell tools, its path-like arguments) is split
into shell segments and every token that names an artifact file is examined, including bare relative
filenames, tokens inside dynamically generated shell loops, and tokens inside heredoc bodies. Failed
calls are scanned too: an attempted read is evidence about the attempt even when it errored, and in
this repository a *failed* redirect still created a file at the wrong path, which is exactly the event
a path-shaped scan and a success-only scan would each have missed.

Each token is classified **lexically, by name and location rather than by path prefix**, and the
``cwd`` recorded for a call — when the caller supplied one — is reported beside each hit. A
name-shaped rule cannot be defeated by reaching the same prior proof through a different directory,
and it treats a bare relative filename exactly like an absolute path, which is the lesson from the
published-cell audit whose first pass missed the decisive commands by matching on path shapes. The
recorded ``cwd`` is context for the reader, not an input to the classification:

``seed``            the registered pristine seed, its ``Mutant`` sibling, or anything under ``baseline/`` — a legitimate input.
``own-copy``        ``<stem>-r<k>`` where ``k`` is this attempt's repetition — the attempt's own working file.
``prior-copy``      ``<stem>-r<j>`` with ``j < k`` — an earlier attempt's working file.
``later-copy``      ``<stem>-r<j>`` with ``j > k`` — a later attempt's file.
``promoted-proof``  a ``*Proved*`` file or a closure copy under ``closures/``.
``other-transcript`` a ``.jsonl`` that is not this attempt's own transcript.
``other``           anything else the name does not identify.

The *effect* of a token in its segment is what the leading verb does to it: ``cat``/``head``/``sed``/
``grep``/``diff``/``cmp``/``sha256sum`` read or compare; ``cp``/``mv`` copy their sources and write
their last argument; ``rm`` deletes; ``ls``/``find``/``stat``/``wc`` merely enumerate. An unrecognised
verb is reported as a read, deliberately: this instrument fails loud, because a missed read is the
failure that matters and an over-reported one costs a human a glance.

Verdicts and exit status
------------------------
An attempt is **contaminated** when a token classified ``prior-copy``, ``promoted-proof`` or
``other-transcript`` is read, copied or compared — the rule the contract states. An attempt with no
readable transcript is **unaudited**. Everything else is **clean**, and enumeration hits are reported
without invalidating the attempt: seeing a predecessor's filename in an ``ls`` is not opening it.

Exit status **0** means every attempt is clean, **1** means at least one is contaminated, and **2**
means at least one is unaudited or the invocation itself is unusable — 2 taking precedence, so that a
missing audit can never be read as a clean cell. That distinction is the same one the preparer's
refusal path enforces: "could not establish" and "established clean" are different answers.

This script reads transcripts and writes nothing; it never runs a model, TLC or Lean.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Every attempt directory is named by `harness.route_b.run_session_dir`: `<stem>-<stamp>-r<k>`.
ATTEMPT_DIR = re.compile(r"^(?P<stem>.+?)-(?P<stamp>\d{8}T\d{6})-r(?P<repetition>\d+)$")
# A work copy: `<stem>-r<k>.lean` (or the mutant's). Matched against the attempt's own stem.
WORK_COPY = re.compile(r"^(?P<stem>.+?)-r(?P<repetition>\d+)(?P<suffix>\.\w+)$")

# Artifact tokens: a path-like run ending in a proof or transcript suffix, or any `closures/` path.
TOKEN = re.compile(
    r"[A-Za-z0-9_./$~@{}+\-]*\.(?:lean|jsonl)"
    r"|[A-Za-z0-9_./$~@{}+\-]*closures/[A-Za-z0-9_./$~@{}+\-]+"
)
SEGMENT = re.compile(r"&&|\|\||;|\||\n")
REDIRECT = re.compile(r">>?")

ENUMERATE = {"ls", "find", "stat", "file", "wc", "du", "readlink", "realpath", "test", "command", "which"}
COMPARE = {"diff", "cmp", "sha256sum", "md5sum", "sha1sum", "sha512sum"}
COPY = {"cp", "mv", "install", "rsync"}
DELETE = {"rm", "rmdir", "shred"}
READ = {
    "cat", "head", "tail", "less", "more", "nl", "sed", "grep", "egrep", "fgrep", "rg", "awk",
    "strings", "xxd", "od", "tac", "sort", "uniq", "cut", "tr", "split", "tee",
}
# A command that runs a tool over a named proof file reads it; python and lake both count.
RUNS = {"python", "python3", "lean", "lake", "elan", "bash", "sh", "nix", "timeout"}

INVALIDATING_CLASSES = {"prior-copy", "promoted-proof", "other-transcript"}
INVALIDATING_EFFECTS = {"read", "compare", "copy"}


def classify(token: str, stem: str, repetition: int, own_transcript: Path) -> str:
    """The token's class, by name and location. Lexical on purpose: a name-shaped rule cannot be
    defeated by choosing a different directory, which is what a path-prefix rule can."""
    name = Path(token).name
    if "baseline/" in token or name in (f"{stem}.lean", f"{stem}Mutant.lean"):
        return "seed"
    if name.endswith(".jsonl"):
        return "own-transcript" if Path(token).name == own_transcript.name else "other-transcript"
    if "Proved" in name or "closures/" in token:
        return "promoted-proof"
    work = WORK_COPY.match(name)
    if work and work["stem"] == stem:
        found = int(work["repetition"])
        if found == repetition:
            return "own-copy"
        return "prior-copy" if found < repetition else "later-copy"
    return "other"


def segment_effects(segment: str) -> list[tuple[str, str, int]]:
    """(verb, effect, token-position) for each artifact token in one shell segment.

    Position distinguishes a copy's sources from its destination, and a redirect's target from the
    text before it — the difference between `cp prior own` (a copy of a prior proof) and `cp own tmp`
    (housekeeping).
    """
    words = segment.split()
    verb = next((w for w in words if not w.startswith("-") and "=" not in w), "")
    verb = Path(verb).name
    tokens = [m.group(0) for m in TOKEN.finditer(segment)]
    redirect_at = REDIRECT.search(segment)
    found = []
    for index, token in enumerate(tokens):
        last = index == len(tokens) - 1
        if redirect_at and segment.find(token) > redirect_at.start() and last:
            effect = "write"  # a redirect target is created even when the command then fails
        elif verb in ENUMERATE:
            effect = "mention"
        elif verb in COPY:
            effect = "write" if last else "copy"
        elif verb in DELETE:
            effect = "delete"
        elif verb in COMPARE:
            effect = "compare"
        elif verb in READ or verb in RUNS:
            effect = "read"
        else:
            effect = "read"  # fail loud on an unknown verb rather than assume harmlessness
        found.append((verb or "<none>", effect, index, token))
    return found


def scan_transcript(path: Path, stem: str, repetition: int) -> list[dict]:
    """Every artifact-touching tool call in one transcript, with its class and effect."""
    hits = []
    with path.open() as handle:
        for lineno, line in enumerate(handle, 1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                hits.append({"line": lineno, "kind": "unparseable-record", "detail": path.name})
                continue
            if record.get("type") != "message":
                continue
            for block in record["message"].get("content") or []:
                if not isinstance(block, dict) or block.get("type") != "toolCall":
                    continue
                arguments = block.get("arguments") or {}
                # Any path-like argument counts, so a non-shell tool is covered too.
                text = arguments.get("command") or " ".join(
                    str(value) for key, value in sorted(arguments.items()) if key != "i"
                )
                cwd = arguments.get("cwd")
                for segment in SEGMENT.split(text):
                    for verb, effect, _, token in segment_effects(segment):
                        if token.startswith("/dev/null") or token in {".", ".."}:
                            continue
                        klass = classify(token, stem, repetition, path)
                        if klass in {"other"} and token.endswith(".jsonl"):
                            klass = "other-transcript"
                        hits.append(
                            {
                                "line": lineno,
                                "tool": block.get("name"),
                                "verb": verb,
                                "effect": effect,
                                "class": klass,
                                "token": token,
                                "cwd": cwd,
                            }
                        )
    return hits


def audit_attempt(directory: Path) -> dict:
    """One attempt's verdict and evidence. An unreadable or unidentifiable attempt is `unaudited`,
    which is deliberately not the same answer as `clean`."""
    match = ATTEMPT_DIR.match(directory.name)
    transcripts = sorted(directory.rglob("*.jsonl"))
    if not match:
        return {
            "attempt": directory.name,
            "session": str(directory),
            "verdict": "unaudited",
            "reason": "directory name is not <stem>-<stamp>-r<k>, so own-copies cannot be told from prior ones",
            "transcripts": [str(path) for path in transcripts],
            "calls": 0,
            "hits": [],
        }
    if not transcripts:
        return {
            "attempt": directory.name,
            "session": str(directory),
            "verdict": "unaudited",
            "reason": "no transcript jsonl under the session directory",
            "transcripts": [],
            "calls": 0,
            "hits": [],
        }
    stem, repetition = match["stem"], int(match["repetition"])
    hits = [hit for path in transcripts for hit in scan_transcript(path, stem, repetition)]
    calls = sum(
        1
        for path in transcripts
        for line in path.read_text().splitlines()
        if line.strip()
        for record in [json.loads(line)]
        if record.get("type") == "message"
        for block in (record["message"].get("content") or [])
        if isinstance(block, dict) and block.get("type") == "toolCall"
    )
    offenders = [
        hit
        for hit in hits
        if hit.get("class") in INVALIDATING_CLASSES and hit.get("effect") in INVALIDATING_EFFECTS
    ]
    return {
        "attempt": directory.name,
        "session": str(directory),
        "stem": stem,
        "repetition": repetition,
        "transcripts": [str(path) for path in transcripts],
        "calls": calls,
        "verdict": "contaminated" if offenders else "clean",
        "offenders": offenders,
        "hits": hits,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="scripts.audit_attempts",
        description="Scan every per-attempt tool call for prior-proof reads or copies.",
    )
    parser.add_argument("--sessions", required=True, help="cell session root: one directory per attempt")
    parser.add_argument("--json", action="store_true", help="emit the full machine-readable report")
    args = parser.parse_args(argv)

    root = Path(args.sessions)
    directories = sorted(path for path in root.iterdir() if path.is_dir()) if root.is_dir() else []
    if not directories:
        print(f"error: no attempt directories under {root}", file=sys.stderr)
        return 2

    reports = [audit_attempt(directory) for directory in directories]
    if args.json:
        print(json.dumps(reports, indent=2))
    else:
        for report in reports:
            print(
                f"{report['verdict']:<12} {report['attempt']:<32} calls={report['calls']:<4} "
                f"hits={len(report['hits'])}"
                + (f"  reason={report['reason']}" if report.get("reason") else "")
            )
            for hit in report["hits"]:
                print(
                    f"    {hit.get('class', hit.get('kind', '?')):<16} {hit.get('effect', '-'):<8} "
                    f"{hit.get('verb', ''):<6} {hit.get('token', hit.get('detail', ''))}  "
                    f"(line {hit['line']}, cwd {hit.get('cwd')})"
                )

    if any(report["verdict"] == "unaudited" for report in reports):
        return 2
    if any(report["verdict"] == "contaminated" for report in reports):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
