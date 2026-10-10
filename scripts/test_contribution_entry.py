#!/usr/bin/env python3
"""Check the public human-to-agent contribution and credit route."""

from __future__ import annotations

import json
import re
from pathlib import Path
from urllib.parse import parse_qs, urljoin, urlparse

import repository_identity

from agent_entry import entry_packet
from agent_skill_catalog import load_catalog


ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def local_markdown_links(path: str) -> list[Path]:
    source = ROOT / path
    links: list[Path] = []
    for target in re.findall(r"\[[^]]+\]\(([^)]+)\)", source.read_text(encoding="utf-8")):
        target = target.split("#", 1)[0]
        if not target or "://" in target:
            continue
        links.append((source.parent / target).resolve())
    return links


def check_issue_form_link(form: str, target: str) -> None:
    """Resolve links where GitHub renders the form, not beside the YAML file."""
    origin = repository_identity.load_identity()["current"]["origin"]
    resolved = urlparse(urljoin(f"{origin}/issues/new?template={form}", target))
    file_prefix = urlparse(origin).path + "/blob/main/"
    if resolved.scheme == "https" and resolved.netloc == "github.com":
        if resolved.path.startswith(file_prefix):
            path = resolved.path.removeprefix(file_prefix)
            require((ROOT / path).is_file(), f"{form}: hosted link has no public file: {target}")
            return
        if resolved.path == urlparse(origin).path + "/issues/new":
            templates = parse_qs(resolved.query).get("template", [])
            require(len(templates) == 1 and Path(templates[0]).name == templates[0],
                    f"{form}: hosted link has no exact form selector: {target}")
            require((ROOT / ".github/ISSUE_TEMPLATE" / templates[0]).is_file(),
                    f"{form}: hosted link names a missing form: {target}")
            return
    raise AssertionError(f"{form}: hosted link leaves the public contribution routes: {target}")


def check_discrepancy_intake() -> None:
    # Exercise the tracked GitHub form's required-field boundary. The report
    # identifies a statement and mismatch; a reader need not clone or know a tag.
    form = text(".github/ISSUE_TEMPLATE/math_discrepancy.yml")
    fields = {}
    for block in re.split(r"(?m)^  - type: ", form)[1:]:
        field_id = re.search(r"(?m)^    id: ([a-z_]+)$", block)
        require(field_id is not None, "discrepancy form has an unidentified field")
        fields[field_id.group(1)] = block
    require({"claim", "discrepancy", "release"} <= fields.keys(),
            "discrepancy form lost its statement, mismatch or source identity field")
    required_fields = {
        name for name, block in fields.items()
        if re.search(r"(?m)^      required: true$", block)
    }
    require(required_fields == {"claim", "discrepancy"},
            f"discrepancy intake requires more than a statement and mismatch: {required_fields}")
    source = fields["release"]
    require(source.startswith("input\n"),
            "source identity must accept a free-text tag, edition, commit or link")
    for term in ("edition", "commit", "link", "known"):
        require(term in source.lower(), f"source identity guidance omits {term}")
    require("v0.10.0" in source, "source identity guidance lost the known release tag example")
    require(not re.search(r"(?m)^      value:", source),
            "discrepancy form invents a source identity for the reporter")

    statement = {
        "claim": "README statement",
        "discrepancy": "The stated assumptions differ from the referenced source.",
    }
    for identity in (
        "",  # A correction read without a clone, edition or tag.
        "v0.10.0",  # Existing historical edition remains a valid answer.
        "https://github.com/wcook04/plectis-erdos/blob/main/README.md",
        # Public main observed when this intake regression was captured.
        "bdcce7f85835b8d6a18c22a3bc90eeaf0064ddb6",
    ):
        answers = {**statement, "release": identity}
        missing = {name for name in required_fields if not answers.get(name, "").strip()}
        require(not missing, f"valid discrepancy report blocked for identity {identity!r}: {missing}")
    for absent in ("claim", "discrepancy"):
        answers = {**statement, absent: "", "release": "v0.10.0"}
        missing = {name for name in required_fields if not answers.get(name, "").strip()}
        require(missing == {absent}, f"source identity bypasses required {absent}")


def check_erdos269_bridge_frontier() -> None:
    """Do not offer the closed actual-series bridge as contributor research."""
    bridge = text("lean/ErdosProblems/Erdos269/RationalityCarryBridge.lean")
    require("theorem exists_reducedCarry_of_value_eq_rat" in bridge,
            "retired #269 task lost its formal bridge evidence")
    require("(hescape : ActualCofinalLocalWindowEscape)" in bridge,
            "#269 conditional consumer lost its actual escape hypothesis")
    for owner in ("docs/problem_index_source.json", "docs/problems.json"):
        problem = next(row for row in json.loads(text(owner))["problems"] if row["erdos_number"] == 269)
        obligations = {row["id"] for row in problem["open_obligations"]}
        require("actual_rational_carry_instantiation" not in obligations,
                f"{owner} offers the formally closed #269 bridge as open research")
        require("actual_local_window_residue_escape" in obligations,
                f"{owner} lost the unresolved actual #269 escape producer")
        require(problem["status"] == "open", f"{owner} promotes the #269 endpoint")
    for guide in ("docs/CONTRIBUTE_BY_PAPER.md", "docs/SOURCE_MAP.md"):
        require("actual_rational_carry_instantiation" not in text(guide),
                f"{guide} still advertises the retired #269 task")
    claims = json.loads(text("docs/claims.json"))
    escape = next(row for row in claims["remaining_open_propositions"]
                  if row["id"] == "remaining_open.erdos_269_cofinal_local_window_escape")
    require(escape["status"] == "open", "#269 escape was silently closed")


def check_erdos251_tail_frontier() -> None:
    """Keep completed analytic bridges separate from the prime-specific supply."""
    source = text("lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean")
    for declaration in (
        "summable_primeDyadicTerm", "summable_primeGapDyadicTerm",
        "cast_rationalPrimeGapTailState_eq_scaled_tsum_nat_add",
        "exists_rationalPrimeGapTailState_representation_of_not_irrational",
        "rationalPrimeGapTailState_recurrence",
        "cast_rationalPrimeGapTailShift_eq_scaled_tsum_sub",
    ):
        require(f"theorem {declaration}" in source, f"retired #251 task lost {declaration}")
    for owner in ("docs/problem_index_source.json", "docs/problems.json"):
        problem = next(row for row in json.loads(text(owner))["problems"] if row["erdos_number"] == 251)
        obligations = {row["id"] for row in problem["open_obligations"]}
        require("actual_prime_gap_tail_formal_bridge" not in obligations,
                f"{owner} offers the completed #251 analytic bridge as open research")
        require({"prime_gap_cofinal_shift_escape", "cofinal_adjacent_small_mismatch"} <= obligations,
                f"{owner} lost an unresolved actual-prime-gap supplier")
        require(problem["status"] == "open", f"{owner} promotes the #251 endpoint")
    for guide in ("docs/CONTRIBUTE_BY_PAPER.md", "docs/SOURCE_MAP.md"):
        require("actual_prime_gap_tail_formal_bridge" not in text(guide),
                f"{guide} still advertises the retired #251 task")


def main() -> int:
    check_discrepancy_intake()
    check_erdos269_bridge_frontier()
    check_erdos251_tail_frontier()
    # Both source-relative variants looked valid locally but GitHub rendered
    # them as /wcook04/CONTRIBUTING.md and /issues/research_progress.yml.
    for target in ("../../CONTRIBUTING.md", "research_progress.yml"):
        try:
            check_issue_form_link("research_return.yml", target)
        except AssertionError:
            pass
        else:
            raise AssertionError(f"incorrect hosted form route was accepted: {target}")
    for source in sorted((ROOT / ".github/ISSUE_TEMPLATE").glob("*.yml")):
        for target in re.findall(r"\[[^]]+\]\(([^)]+)\)", source.read_text(encoding="utf-8")):
            check_issue_form_link(source.name, target)
    catalog = load_catalog()
    for task, lane in (
        ("I want to work on problem 257 using the existing papers and Lean sources", "bounded_research"),
        ("I want to improve the infrastructure for executable construction mining", "repository_architecture"),
        ("Refine contributor journeys starting from our papers", "repository_architecture"),
        ("Develop a reusable method from the corpus", "explore_corpus"),
    ):
        packet = entry_packet(catalog, task)
        require(packet["primary_lane"]["id"] == lane, f"contributor journey misrouted: {task}: {packet['primary_lane']}")
    # Every programme remains a first-class entry; one representative example
    # must not silently replace the full research environment.
    for number in (68, 243, 249, 251, 257, 269, 1041, 1049):
        task = f"Work on problem {number} using its short and long papers and Lean source"
        packet = entry_packet(catalog, task, purpose="research", scope=f"problem:{number}")
        require(packet["primary_lane"]["id"] == "bounded_research", f"problem {number} research entry misrouted")
        require(packet["scope"] == f"problem:{number}" and packet["task"] == task,
                f"problem {number} identity or original request lost")
    packet = entry_packet(catalog, "Refine the proof paper", purpose="infrastructure", scope="problem:257")
    require(packet["primary_lane"]["id"] == "repository_architecture" and packet["scope"] == "problem:257", "explicit purpose or scope lost")
    require(packet["task"] == "Refine the proof paper", "original request lost")
    guide = text("docs/CONTRIBUTE_BY_PAPER.md")
    for row in json.loads(text("docs/problems.json"))["problems"]:
        number = row["erdos_number"]
        require(f"## Problem {number}" in guide, f"missing paper entry {number}")
        section = guide.split(f"## Problem {number}\n", 1)[1].split("\n## Problem ", 1)[0]
        for label in ("Short paper", "Long record"):
            targets = re.findall(r"\[" + label + r"\]\(([^)]+)\)", section)
            require(len(targets) == 1 and targets[0].startswith(f"../paper/{number}/"),
                    f"problem {number} lost its own {label.lower()}")
        texts = re.findall(r"\[Read as text\]\(([^)]+)\)", section)
        require(len(texts) == 2 and len(set(texts)) == 2,
                f"problem {number} needs both distinct text editions")
        require(row["what_is_checked"][0] in section, f"missing result {number}")
        require(row["claim_registration"]["programme_statement"] in section,
                f"missing result boundary {number}")
        require(row["modules"][0]["path"] in section, f"missing source evidence {number}")
        for obligation in row["open_obligations"]:
            require(obligation["statement"] in section, f"missing owned question {number}")
        issue_links = re.findall(r"\[Return work on #" + str(number) + r"\]\(([^)]+)\)", guide)
        require(len(issue_links) == 1, f"missing return route {number}")
        fields = parse_qs(urlparse(issue_links[0]).query)
        require(fields.get("question") == [f"Erdős #{number}: {row['question']}"], f"return scope lost {number}")
    contributing = text("CONTRIBUTING.md")
    human, marker, mechanics = contributing.partition("## For agents and maintainers")
    require(bool(marker), "contributor guide does not separate human meaning from agent mechanics")
    require(len(re.findall(r"\b[\w’'-]+\b", human)) >= 500, "human contribution route is too thin")
    human_flat = " ".join(human.lower().split())
    for forbidden in ("```", "|---", "python3 ", "scripts/", "--require-", "return.json"):
        require(forbidden not in human, f"human contribution route exposes implementation syntax: {forbidden}")
    for concept in ("pull request", "plain-language", "accepted receipt", "credit", "older clone", "architecture"):
        require(concept in human_flat, f"human contribution route omits {concept!r}")

    required_files = (
        "docs/research-commons/README.md",
        "docs/research-commons/CREDIT_POLICY.md",
        "docs/research-commons/ARCHITECTURE_CONTRIBUTIONS.md",
        "docs/research-commons/RETURN_PACKAGE_TEMPLATE.md",
        "docs/research-commons/schema/research-return-receipt.schema.json",
        "docs/research-commons/schema/research-return-receipt-v2.schema.json",
        ".github/ISSUE_TEMPLATE/research_progress.yml",
        ".github/ISSUE_TEMPLATE/research_return.yml",
        ".github/ISSUE_TEMPLATE/architecture_proposal.yml",
        ".github/ISSUE_TEMPLATE/review_offer.yml",
        ".github/PULL_REQUEST_TEMPLATE.md",
        "skills/README.md",
        "skills/install-clone-skills/SKILL.md",
        "skills/explain-public-system/SKILL.md",
        "skills/run-coupled-research-goals/SKILL.md",
        "skills/mine-open-problem/SKILL.md",
        "skills/lean-concurrent-validation/SKILL.md",
        "skills/maintain-public-infrastructure/SKILL.md",
        "skills/propagate-research-consequences/SKILL.md",
        "skills/add-open-problem/SKILL.md",
        "skills/submit-pull-request/SKILL.md",
        "skills/erdos-research-return/SKILL.md",
        "skills/public-mathematical-writing/SKILL.md",
        "scripts/install_agent_skills.py",
        "scripts/test_clone_skills.py",
        "scripts/continue_research.py",
        "scripts/validate_research_return.py",
        "scripts/accept_research_return.py",
        "scripts/build_research_contributions.py",
        "scripts/build_research_contribution_recognition.py",
        "scripts/test_public_writing_contract.py",
    )
    for path in required_files:
        require((ROOT / path).is_file(), f"clone-local contribution route is missing {path}")

    for source in (
        "CONTRIBUTING.md",
        "docs/CONTRIBUTE_BY_PAPER.md",
        "docs/READING_GUIDE.md",
        "docs/research-commons/README.md",
        "docs/research-commons/CREDIT_POLICY.md",
        "docs/research-commons/ARCHITECTURE_CONTRIBUTIONS.md",
        "docs/research-commons/RETURN_PACKAGE_TEMPLATE.md",
        "skills/README.md",
    ):
        for target in local_markdown_links(source):
            require(target.is_file(), f"{source} has a dead clone-local link: {target}")

    simple_issue = text(".github/ISSUE_TEMPLATE/research_progress.yml")
    for field in ("id: question", "id: finding", "id: evidence", "id: boundary", "id: credit"):
        require(field in simple_issue, f"plain-language research form omits {field}")
    for forbidden in ("python3", "return.json", "route-memory.json", "render: json"):
        require(forbidden not in simple_issue, f"plain-language research form exposes {forbidden}")

    architecture_issue = text(".github/ISSUE_TEMPLATE/architecture_proposal.yml")
    for field in ("id: area", "id: problem", "id: proposal", "id: replay", "id: credit", "id: roles"):
        require(field in architecture_issue, f"architecture proposal form omits {field}")
    architecture_guide = text("docs/research-commons/ARCHITECTURE_CONTRIBUTIONS.md")
    for label, form in (
        ("architecture proposal", "architecture_proposal.yml"),
        ("structured research return form", "research_return.yml"),
    ):
        targets = re.findall(r"\[" + re.escape(label) + r"\]\(([^)]+)\)", architecture_guide)
        require(len(targets) == 1, f"architecture guide omits actionable {label} route")
        route = urlparse(targets[0])
        origin = urlparse(repository_identity.load_identity()["current"]["origin"])
        require(route.scheme == origin.scheme and route.netloc == origin.netloc
                and route.path == origin.path + "/issues/new"
                and parse_qs(route.query).get("template") == [form],
                f"architecture guide sends {label} readers to source instead of a form")
    for concept in ("idea", "accepted receipt", "conceptualization", "software", "validation", "non-scalar"):
        require(concept in architecture_guide.lower(), f"architecture contribution path omits {concept!r}")
    receipt_schema = text(repository_identity.load_identity()["contracts"]["current_schema_path"])
    for contract in ('"architecture"', '"contribution_roles"', '"consider_architecture_adoption"'):
        require(contract in receipt_schema, f"receipt schema omits architecture contract {contract}")

    review_offer = text(".github/ISSUE_TEMPLATE/review_offer.yml")
    for field in (
        "labels: [\"review\"]",
        "id: lens",
        "id: target",
        "id: time",
        "id: background",
        "id: credit",
        "id: public_material",
        "never be quoted as endorsement",
        "silence is not treated as approval",
    ):
        require(field in review_offer, f"bounded review-offer form omits {field!r}")

    pull_request = text(".github/PULL_REQUEST_TEMPLATE.md")
    require("Credit and provenance" in pull_request, "pull request route omits contribution credit")
    require("What remains open or uncertain?" in pull_request, "pull request route omits result boundary")
    require("python3" not in pull_request and "```" not in pull_request, "pull request front door is command-first")

    submission_skill = text("skills/submit-pull-request/SKILL.md")
    submission_skill_flat = " ".join(submission_skill.split())
    for boundary in (
        "pull request",
        "explicit authorisation",
        "git diff --cached --check",
        "Never force-push",
        "does not mean that the patch is accepted",
    ):
        require(boundary in submission_skill_flat, f"submission skill omits {boundary!r}")

    skill = text("skills/erdos-research-return/SKILL.md")
    agent_entry = text("AGENTS.md")
    for marker in (
        "scripts/continue_research.py",
        "scripts/validate_research_return.py",
        "scripts/accept_research_return.py",
        "scripts/build_research_contributions.py",
    ):
        require(marker in skill, f"research-return skill omits local tool {marker}")
    require("skills/erdos-research-return/SKILL.md" in agent_entry, "compact agent entry omits return skill")
    registry = json.loads(text("skills/registry.json"))
    registered_skills = {row["id"] for row in registry["skills"]}
    for clone_skill in (
        "install-clone-skills",
        "explain-public-system",
        "run-coupled-research-goals",
        "mine-open-problem",
        "maintain-public-infrastructure",
        "propagate-research-consequences",
        "add-open-problem",
        "submit-pull-request",
    ):
        require(clone_skill in registered_skills, f"skill registry omits {clone_skill}")
    require(
        "agent_entry.py --skills" in agent_entry,
        "compact agent entry does not route to the complete skill registry",
    )
    returned_work = entry_packet(
        load_catalog(),
        "I cloned this repository, made mathematical progress, and want to send it back "
        "so it can be reviewed, assimilated, propagated, and credited",
    )
    require(
        returned_work["primary_lane"]["id"] == "return_research",
        "ordinary-language returned work does not reach the contribution lane",
    )
    require(
        returned_work["skills"][0]["id"] == "erdos-research-return",
        "ordinary-language returned work does not reach the assimilation skill",
    )

    consequence_skill = text("skills/propagate-research-consequences/SKILL.md")
    for contract in (
        "git diff --name-status <starting-commit>..HEAD",
        "--changed-from <starting-commit>",
        "update now",
        "verify unchanged",
        "Reconcile work from an older clone",
    ):
        require(contract in consequence_skill, f"consequence skill omits {contract!r}")
    require(
        "common ancestor" in submission_skill and "common ancestor" in skill,
        "submission and assimilation skills omit old-base Git semantics",
    )

    public_surfaces = "\n".join(
        text(path)
        for path in (
            "CONTRIBUTING.md",
            "docs/research-commons/README.md",
            "docs/research-commons/CREDIT_POLICY.md",
            "skills/erdos-research-return/SKILL.md",
        )
    )
    for forbidden in ("ai_workflow", "/Users/", "raw_seed.md", "private ledger path"):
        require(forbidden not in public_surfaces, f"public contribution route depends on private state: {forbidden}")

    require("structured" in mechanics.lower(), "agent mechanics do not expose the structured return path")
    print("contribution entry: human prose, clone-local return, provenance, credit, and update route PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
