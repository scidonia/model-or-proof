"""Behavior scenarios for the published human-proof baseline (tests/human-baseline-contract.md)."""

import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
HUMAN = REPO / "results" / "human.jsonl"

MEASURED_KEYS = {
    "route", "tool", "wall_clock_s", "startup_s", "peak_rss_mb", "cost_usd",
    "tlc", "proof", "outcome", "repetition", "tier", "states_reached",
    "cost_basis", "negative_control",
}

EXPECTED_IDS = ["ewd998", "ijcar2010-peterson", "ijcar2010-bakery", "ijcar2010-paxos"]
NON_POOLABLE = ["route_a_measured", "route_b_measured"]


def records():
    text = HUMAN.read_text()  # FileNotFoundError before the data is written (the expected red run).
    return [json.loads(line) for line in text.splitlines() if line.strip()]


def by_id(recs, record_id):
    matches = [r for r in recs if r.get("record_id") == record_id]
    assert len(matches) == 1, f"expected exactly one record {record_id!r}, got {len(matches)}"
    return matches[0]


def test_every_record_is_a_labelled_prior_art_record():
    """Scenario 1: exactly four labelled, non-poolable prior-art records, no extras."""
    recs = records()
    ids = [r.get("record_id") for r in recs]
    assert sorted(ids) == sorted(EXPECTED_IDS), f"inventory must be exactly {EXPECTED_IDS}, got {ids}"
    for row in recs:
        assert row["kind"] == "human_prior_art", row
        assert row["machine_checked"] is False, row
        source = row["source"]
        for key in ("repo", "commit", "upstream_path", "license"):
            assert source.get(key), f"missing/empty source.{key}: {source}"
        figures = row["figures"]
        assert figures, row
        for fig in figures:
            assert fig.get("kind"), fig
            assert "value" in fig, fig
            assert fig.get("quote"), fig
        assert row["artifact_size"], row
        assert row["never_pooled_with"] == NON_POOLABLE, row
        overlap = MEASURED_KEYS & set(row)
        assert not overlap, f"prior-art record carries measured keys {sorted(overlap)}"


def test_artifact_sizes_match_committed_files():
    """Scenario 2: each recorded artifact size matches the committed file."""
    for row in records():
        for entry in row["artifact_size"]:
            path = REPO / entry["path"]
            assert path.exists(), f"artifact not committed: {entry['path']}"
            assert entry["bytes"] == len(path.read_bytes()), entry
            assert entry["lines"] == len(path.read_text().splitlines()), entry


def test_line_count_disagreement_is_preserved():
    """Scenario 3: the published-vs-artifact line-count disagreement is preserved."""
    recs = records()
    bakery = by_id(recs, "ijcar2010-bakery")
    bakery_lines = {f["kind"]: f["value"] for f in bakery["figures"]}
    assert bakery_lines["proof_lines"] == 800, bakery_lines
    assert bakery["artifact_size"][0]["path"].endswith("Bakery.tla"), bakery["artifact_size"]
    assert bakery["artifact_size"][0]["lines"] == 383, bakery["artifact_size"]
    assert bakery.get("line_count_disagreement"), "missing disagreement note on bakery"

    peterson = by_id(recs, "ijcar2010-peterson")
    peterson_lines = {f["kind"]: f["value"] for f in peterson["figures"]}
    assert peterson_lines["proof_lines"] == 130, peterson_lines
    assert peterson["artifact_size"][0]["path"].endswith("Peterson.tla"), peterson["artifact_size"]
    assert peterson["artifact_size"][0]["lines"] == 199, peterson["artifact_size"]
    assert peterson.get("line_count_disagreement"), "missing disagreement note on peterson"


def test_person_days_only_for_ewd998_and_tlc_anchor_cited():
    """Scenario 4: person-days only for EWD998, and the TLC anchor is cited."""
    recs = records()
    ewd = by_id(recs, "ewd998")
    kinds = {f["kind"] for f in ewd["figures"]}
    assert "person_days" in kinds, kinds
    tlc_anchor = [f for f in ewd["figures"] if f["kind"] == "tlc_distinct_states"]
    assert tlc_anchor and tlc_anchor[0]["value"] == 1300000, tlc_anchor

    for record_id in ("ijcar2010-peterson", "ijcar2010-bakery", "ijcar2010-paxos"):
        row = by_id(recs, record_id)
        assert row["effort"]["unit"] == "lines_only", (record_id, row["effort"])
        assert not any(f["kind"] == "person_days" for f in row["figures"]), record_id

    paxos = by_id(recs, "ijcar2010-paxos")
    second = [f for f in paxos["figures"] if f.get("proof") == "second_refinement"]
    assert second and second[0].get("partial") is True, second


def test_ewd998_tlc_figures_reproduced_at_paper_era_and_drifted_at_pin():
    """Scenario 5: published TLC figures reproduced at the paper-era revision, drifted at the pin."""
    ewd = by_id(records(), "ewd998")
    c = ewd["calibration"]
    assert c["published"]["distinct"] == 1300000, c
    paper = c["paper_era"]["distinct"]
    assert isinstance(paper, int) and paper > 0, c
    assert 1170000 <= paper <= 1430000, c  # reproduces the published "1.3 million" within rounding
    head = c["branch_head"]["distinct"]
    assert isinstance(head, int) and head >= paper, c  # the widening can only enlarge the set
    # The drift cause is carried structurally and machine-checked by equality, so a
    # contradictory prose sentence cannot satisfy it (no prose is parsed).
    cause = c["cause"]
    assert cause["commit"] == "dafe1e5c8a742c0515d9477f982815adeae04580", cause
    assert cause["date"] == "2023-07-28", cause
    assert cause["change"] == {"field": "token.pos", "before": "{0}", "after": "Node"}, cause
    # The human-readable root_cause prose is documentation only: required present, not asserted for meaning.
    assert isinstance(c["root_cause"], str) and c["root_cause"], c
