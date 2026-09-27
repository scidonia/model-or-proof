"""Structural conformance checks for tests/paxos-projection-contract.md.

The measured TLC curve and mutant trace are real-run acceptance gates, not a fast suite fixture.
"""

import json
import re
from pathlib import Path

from harness.tlc_run import read_cfg

REPO = Path(__file__).resolve().parents[1]
MANIFEST = REPO / "tasks" / "paxos.json"


def cfg_constants(text: str) -> dict[str, int]:
    return {
        key: int(value)
        for key, value in re.findall(r"(?m)^CONSTANT\s+(N|B)\s*=\s*(\d+)\s*$", text)
    }


def test_paxos_instance_sweep_fixes_ballots_while_varying_acceptors():
    manifest = json.loads(MANIFEST.read_text())
    assert manifest["name"] == "paxos"
    assert manifest["spec"] == "specs/tla/paxos/PaxosFinite.tla"
    assert manifest["property"]["name"] == "Consistency"
    assert manifest["budgets"]["wall_clock_s"] == 7200
    instances = [item["param_N"] for item in manifest["instances"]]
    assert instances == list(range(2, max(instances) + 1)) and max(instances) >= 8
    assert manifest["calibration"]["ballot_bound"] == 1
    assert "log-nearest" in manifest["calibration"]["n0_rule"]
    witness_manifest = json.loads((REPO / "tasks" / "paxos-witness.json").read_text())
    assert witness_manifest["name"] == "paxos-witness"
    assert witness_manifest["spec"] == manifest["spec"]
    assert witness_manifest["budgets"]["wall_clock_s"] == 7200
    assert [item["param_N"] for item in witness_manifest["instances"]] == instances

    for instance in manifest["instances"]:
        n = instance["param_N"]
        assert instance["config"] == f"specs/tla/paxos/PaxosN{n}.cfg"
        config = REPO / instance["config"]
        text = config.read_text()
        assert "SPECIFICATION Spec" in text
        assert read_cfg(config) == {"param_N": n, "property": "Consistency"}
        assert cfg_constants(text) == {"N": n, "B": 1}
        witness = REPO / f"specs/tla/paxos/PaxosN{n}Witness.cfg"
        witness_text = witness.read_text()
        assert "SPECIFICATION Spec" in witness_text
        assert cfg_constants(witness_text) == {"N": n, "B": 1}
        assert read_cfg(witness) == {"param_N": n, "property": "NoChoice"}
        witness_instance = witness_manifest["instances"][n - 2]
        assert witness_instance["config"] == f"specs/tla/paxos/PaxosN{n}Witness.cfg"


def test_paxos_mutant_changes_one_phase2a_quorum_guard_only():
    manifest = json.loads(MANIFEST.read_text())
    assert manifest["mutant"]["spec"] == "specs/tla/paxos/PaxosFiniteMutant.tla"
    assert manifest["mutant"]["config"] == "specs/tla/paxos/PaxosMutant.cfg"
    config = REPO / manifest["mutant"]["config"]
    assert cfg_constants(config.read_text()) == {"N": 3, "B": 1}
    assert read_cfg(config)["property"] == "Consistency"

    source = (REPO / manifest["spec"]).read_text()
    mutant = (REPO / manifest["mutant"]["spec"]).read_text()
    guard = "\\E Q \\in Quorums :"
    weak_guard = "\\E Q \\in (SUBSET Acceptors) \\ {{}} :"
    # Remove module headers and compare every remaining byte after the one guarded
    # substitution. The parser/real TLC run verifies the actual TLA+ syntax.
    source = re.sub(r"(?m)^-+ MODULE PaxosFinite -+$", "", source, count=1)
    mutant = re.sub(r"(?m)^-+ MODULE PaxosFiniteMutant -+$", "", mutant, count=1)
    phase2a = source.split("Phase2a(b) ==", 1)[1].split("Phase2b(a) ==", 1)[0]
    assert phase2a.count(guard) == 1
    assert source.count(guard) >= 2  # Phase2a and ChosenIn retain distinct uses.
    assert mutant == source.replace(guard, weak_guard, 1)
