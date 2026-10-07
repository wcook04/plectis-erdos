#!/usr/bin/env python3
"""Check the public split between human mathematical prose and agent machinery."""

import json
import re
from pathlib import Path

from check_release import contributor_gate_posture_errors, has_release_status_boundary


ROOT = Path(__file__).resolve().parents[1]


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def release_status_boundary() -> str:
    claims = json.loads(read("docs/claims.json"))
    boundary = claims["external_verification_packet"].get("boundary")
    require(isinstance(boundary, str) and boundary.strip(),
            "docs/claims.json lacks the release status boundary")
    return boundary


def main() -> None:
    contributing = " ".join(read("CONTRIBUTING.md").split())
    require(not contributor_gate_posture_errors(contributing),
            "current contributor prose must preserve the release-gate policy")
    for old, new in (
        ("deliberately broken statements or links are detected",
         "deliberately broken statements or links are not tested"),
        ("A failure blocks the release gate", "A failure does not block a release"),
    ):
        require(old in contributing, f"contributor-policy fixture missing: {old}")
        require(bool(contributor_gate_posture_errors(contributing.replace(old, new, 1))),
                f"contributor guidance understated validation without rejection: {new}")
    legacy = ("combined baseline-plus-adversarial release-gate check. "
              "A failure therefore blocks the release gate.")
    require(not contributor_gate_posture_errors(legacy),
            "the equivalent earlier gate description must remain accepted")
    require(bool(contributor_gate_posture_errors(contributing + " diagnostic (not a gate)")),
            "contradictory diagnostic-only wording must be rejected")
    claims = json.loads(read("docs/claims.json"))
    boundary = release_status_boundary()
    require(has_release_status_boundary(boundary.replace(". ", ".\n"), claims),
            "release boundary check must tolerate line wrapping")
    for missing in ("", "All eight problems remain open.",
                    "The degree-seven example refutes Erdős #1041."):
        require(not has_release_status_boundary(missing, claims),
                "release boundary check accepted missing formulation or review limits")
    for path in ("README.md", "docs/METHODOLOGY.md"):
        require(has_release_status_boundary(read(path), claims),
                f"{path} differs from the current claim-owner boundary")
    human = read("docs/README.md")
    require("```" not in human, "HUMAN_ENTRY must not make readers begin with commands")
    first_heading = human.find("## Choose a way in")
    require(first_heading > 0 and "\n|" not in human[:first_heading],
            "human entry must explain the mathematics before a guide table")
    require(human.count("\n\n") >= 10, "HUMAN_ENTRY has lost its prose structure")
    # Boundaries are matched across line wrapping, so reflowing a paragraph
    # cannot hide or fake one.
    prose = " ".join(human.split())
    require("[Results and limits](RESULTS.md)" in human,
            "human entry lost its current status route")
    require(has_release_status_boundary(read("docs/RESULTS.md"), claims),
            "human status route lost the exact authority-owned boundary")
    for boundary in ("A finite computation covers its tested range",
                     "it is not peer review", "does not establish"):
        require(boundary in prose, f"human entry lost evidence limit: {boundary}")

    # Current systems manuscripts are also public entry points. Their examples
    # may be historical, but their descriptions of the present corpus must not
    # restore the superseded blanket status split. "Eight open Erdős problems"
    # is the same claim in adjective form: the systems paper printed it on its
    # first page three lines above "The other seven targets remain open".
    eight_open = re.compile(
        r"\beight\s+open\s+(?:Erd(?:ő|\\H\{o\}|o)s\s+)?(?:problems|programmes|targets)\b",
        re.IGNORECASE,
    )
    for path in (ROOT / "paper/systems").glob("*.tex"):
        manuscript = " ".join(path.read_text(encoding="utf-8").split())
        for stale in (
            "all eight problems remain open",
            "All eight problems remain open",
            "all eight endpoint problems remain open",
            "are the two principal reviewed programmes",
        ):
            require(stale not in manuscript, f"{path.name} repeats obsolete corpus status: {stale}")
        hit = eight_open.search(manuscript)
        require(hit is None, f"{path.name} repeats obsolete corpus status: {hit.group(0) if hit else ''}")
    for sample in (
        r"\textbf{Instance.} Eight open Erd\H{o}s problems in one Lean repository",
        "maintains eight open Erdős problems this way",
    ):
        require(eight_open.search(sample) is not None, "eight-open status guard lost a known specimen")

    # The public site refuses "one person built this" framing: the work is read
    # as if a department produced it, and the site deploy scans every rendered
    # paper for it. The systems paper merged two such sentences that only the
    # deploy caught, so the manuscripts are checked here, before merge. The
    # strategy paper's two clauses about overlapping contributor roles are the
    # only known exceptions.
    founder = re.compile(r"\b(?:one[- ]person|single[- ]person)\b", re.IGNORECASE)
    role_clauses = (
        "one person may perform several, and several people may perform one",
        "one person may perform both roles",
    )
    for path in sorted((ROOT / "paper").rglob("*.tex")):
        manuscript = " ".join(path.read_text(encoding="utf-8").split())
        for clause in role_clauses:
            manuscript = re.sub(re.escape(clause), "", manuscript, flags=re.IGNORECASE)
        hit = founder.search(manuscript)
        require(hit is None, f"{path.relative_to(ROOT)} uses one-person framing: {hit.group(0) if hit else ''}")
    require(founder.search("One person has built the environment") is not None,
            "one-person framing guard lost its specimen")

    # The same blanket split must not survive on the pages a contributor or an
    # outside model reads first. The guard above covered only the manuscripts,
    # so CONTRIBUTING.md and the related-problem map kept the obsolete sentence
    # after the #1041 status changed. The pattern is loose on purpose: it
    # matches the claim, whatever words surround "eight".
    blanket = re.compile(
        r"\b(?:all|none of the)\s+eight\b[^.]{0,80}?"
        r"(?:remain(?:s)? open|(?:is|are) (?:solved|resolved|unsolved)|problems? is solved)",
        re.IGNORECASE,
    )
    first_contact = [
        ROOT / ".github/START_HERE_ISSUE.md",
        ROOT / "README.md",
        ROOT / "docs/README.md",
        ROOT / "docs/README.md",
        ROOT / "docs/METHODOLOGY.md",
        ROOT / "docs/RESULTS.md",
        ROOT / "CONTRIBUTING.md",
        ROOT / "AGENTS.md",
        ROOT / "docs/reference/RELATED_PROBLEMS.md",
        ROOT / "docs/agents/FRONTIER_RELAY.md",
        ROOT / "docs/agents/README.md",
        ROOT / "docs/reading-edition/INTRODUCTION.md",
        *sorted((ROOT / "skills").glob("*/SKILL.md")),
    ]
    for path in first_contact:
        text = " ".join(path.read_text(encoding="utf-8").split())
        hit = blanket.search(text) or eight_open.search(text)
        require(hit is None, f"{path.relative_to(ROOT)} repeats obsolete corpus status: {hit.group(0) if hit else ''}")
    for sample in (
        "all eight headline Erdős problems remain open unless something happens",
        "None of the eight open problems is solved here.",
    ):
        require(blanket.search(sample) is not None, "blanket-status guard lost a known specimen")

    # Retired audit infrastructure must not return as a live public capability.
    # These markers came from a two-problem historical sample, not the current
    # integrated claim, semantic-relation, and residual-evaluation owners.
    retired_paths = (
        "docs/reformulation_productivity.json",
        "scripts/measure_reformulation_productivity.py",
        "docs/reference/TRUTH_AUDIT.md",
    )
    for path in retired_paths:
        require(not (ROOT / path).exists(), f"retired public audit surface returned: {path}")

    drift_surfaces = (
        "README.md",
        "docs/README.md",
        "docs/README.md",
        "docs/METHODOLOGY.md",
        "docs/ARCHITECTURE.md",
        "docs/RESULTS.md",
        "docs/agents/AGENT_GUIDE.md",
        "docs/reference/README.md",
        "docs/reference/RESIDUAL_PROGRESS.md",
        "docs/expert_review_protocol.json",
        "docs/semantic/frontier.json",
        "docs/semantic/zones/Z18.json",
    )
    retired_markers = (
        "17 of 23",
        "23 hypotheses",
        "23 are substantial",
        "Seventeen of the 23",
        "101 distinct closed",
        "every claim has a Lean address",
        "reformulation_productivity.json",
        "measure_reformulation_productivity.py",
        "TRUTH_AUDIT.md",
    )
    for path in drift_surfaces:
        surface = read(path)
        for marker in retired_markers:
            require(marker not in surface, f"{path} restored retired audit language: {marker}")

    current_1041_surfaces = (
        "lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean",
        "scripts/query_expert_handoffs.py",
        "docs/research-commons/source-attributions.json",
        "docs/research-commons/SOURCE_ATTRIBUTIONS.md",
    )
    stale_1041_markers = (
        "Erdős #1041 remains open",
        "external claim awaiting source assessment",
        "Do not change #1041 status until source/proof assessment",
    )
    for path in current_1041_surfaces:
        surface = read(path)
        for marker in stale_1041_markers:
            require(marker not in surface, f"{path} restored stale #1041 status: {marker}")

    public_builder_surfaces = (
        ".github/workflows/lean.yml",
        "docs/papers/check_paper_corpus.py",
        "docs/papers/build_publication_taxonomy.py",
        "scripts/build_problem_index.py",
    )
    private_builder_markers = (
        "generated from the private system repository",
        "canonical corpus builder lives in the private system repository",
    )
    for path in public_builder_surfaces:
        surface = read(path)
        for marker in private_builder_markers:
            require(marker not in surface, f"{path} restored a private paper-corpus owner: {marker}")

    frontier = json.loads(read("docs/semantic/frontier.json"))
    require(
        "demand_lattice" not in frontier,
        "semantic frontier restored the retired aggregate DemandLedger census",
    )
    z18 = json.loads(read("docs/semantic/zones/Z18.json"))
    z18_nodes = {row["id"] for row in z18["statement_nodes"]}
    require(
        "demand_ledger_extraction" not in z18_nodes,
        "semantic zone restored the retired binder-extraction census node",
    )
    protocol = json.loads(read("docs/expert_review_protocol.json"))
    systems_template = protocol["questions"][0]["input_template"]
    for retired_field in ("equivalent_antecedents", "substantial_antecedents"):
        require(
            retired_field not in systems_template,
            f"expert protocol restored retired audit field: {retired_field}",
        )

    readme = read("README.md")
    human_link = readme.find("docs/README.md")
    first_table = readme.find("\n|")
    first_fence = readme.find("```")
    require(human_link >= 0, "README no longer links the human entry")
    require(first_table < 0 or human_link < first_table, "README presents a table before its human entry")
    require(first_fence < 0 or human_link < first_fence, "README presents commands before its human entry")

    contributing = read("CONTRIBUTING.md").split("## For agents and maintainers", 1)[0]
    require("```" not in contributing, "human contribution guidance contains a command block")
    require("python3 " not in contributing, "human contribution guidance exposes commands")

    skill_path = "skills/public-mathematical-writing/SKILL.md"
    skill = read(skill_path)
    require("ai_workflow" not in skill and "/Users/" not in skill, "public writing skill has a private dependency")
    require(skill_path in read("AGENTS.md"), "AGENTS.md does not route to the public writing skill")
    require(skill_path in read("docs/agents/AGENT_GUIDE.md"), "docs/agents/AGENT_GUIDE.md does not route to the public writing skill")
    require(
        "public-mathematical-writing/SKILL.md" in read("skills/README.md"),
        "skills/README.md does not list the public writing skill",
    )

    print("test_public_writing_contract: human prose and agent machinery remain separated")


if __name__ == "__main__":
    main()
