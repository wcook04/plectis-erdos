#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Check that the newcomer architecture guide stays concrete and jargon-free."""

from __future__ import annotations

import json
import os
import re
import stat
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
GUIDE = ROOT / "docs/ARCHITECTURE.md"
README = ROOT / "README.md"
AGENTS = ROOT / "docs/agents/AGENT_GUIDE.md"
PAPER_README = ROOT / "paper" / "README.md"
SYSTEMS_PAPER = ROOT / "paper" / "systems" / "claim-faithful-publication-systems-paper.tex"
SYSTEMS_PDF = ROOT / "paper" / "systems" / "claim-faithful-publication-systems-paper.pdf"
PUBLICATION_CONTRACT = ROOT / "docs" / "publication_contract.json"
CLAIMS = ROOT / "docs" / "claims.json"
MAX_GUIDE_BYTES = 18_000
# Keep the architecture paper bounded without accumulating one-off magic-number
# raises.  Its legitimate explanatory load grows with the canonical publication
# inventory, whose exact membership is independently checked against the build
# and licence manifests.  A stable conceptual base plus a small per-artifact
# allowance therefore scales only when the governed public surface scales.
# The base now covers the complete private-to-public architecture rather than
# the former release-check case study: authority-aware routing, temporal work
# leases, resident metabolism, trace projections, federated mathematical
# memory, proof/publication gates, the scale/review boundary, and the public
# job lifecycle from invocation through consequence propagation and old-base
# assimilation. The enlarged base also covers the coupled discovery and corpus-
# stewardship roles, local-to-general digestion, and their public skill routes.
# The per-artifact increment remains the only
# inventory-dependent allowance.
# Raised from 66,000 on 2026-09-02. The base is meant to move only when the
# architecture the paper describes enlarges, and two sections now sit inside it
# that the previous base did not cover: the mathematical reasoning loop, and the
# argument for scaling from one clone to a search network. The per-artifact
# increment is still the only inventory-dependent allowance, and the guide
# itself was brought back under its own budget by cutting a restatement rather
# than by raising anything.
# Raised again from 70,000 on 2026-09-02, by the size of one further section the
# previous base did not cover: the compiled comprehension packet that an agent
# reasons over before it reaches the mathematics. The paper was first tightened
# and a duplicated drill-down ladder was cut, so the raise covers the new
# architecture and nothing else.
# Raised from 73_000 on 2026-09-14 after the related-work section absorbed
# five prior-art citations (Prove2Me, two Feng et al. reports, Henkel, Li et
# al.) that the paper had been missing; the text was trimmed twice first.
SYSTEMS_PAPER_BASE_BYTES = 75_000
SYSTEMS_PAPER_BYTES_PER_ARTIFACT = 1_000


class UnsafeArchitectureInput(ValueError):
    """An architecture-check input escaped the checkout or is not a file."""


def safe_architecture_text(path: Path, root: Path = ROOT) -> str:
    """Read one architecture input through a no-follow regular-file descriptor."""
    root = Path(os.path.abspath(root))
    candidate = Path(os.path.abspath(path))
    if candidate != root and root not in candidate.parents:
        raise UnsafeArchitectureInput(f"architecture input escaped checkout: {candidate}")
    current = candidate
    while True:
        if current.is_symlink():
            raise UnsafeArchitectureInput(f"symlinked architecture input: {candidate}")
        if current == root:
            break
        if current.parent == current:
            raise UnsafeArchitectureInput(f"architecture input escaped checkout: {candidate}")
        current = current.parent
    if not candidate.is_file():
        raise UnsafeArchitectureInput(
            f"architecture input is not a regular file: {candidate}"
        )

    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    if hasattr(os, "O_CLOEXEC"):
        flags |= os.O_CLOEXEC
    try:
        descriptor = os.open(candidate, flags)
    except OSError as exc:
        raise UnsafeArchitectureInput(
            f"architecture input could not be opened safely: {candidate}"
        ) from exc
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise UnsafeArchitectureInput(
                f"architecture input is not a regular file: {candidate}"
            )
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        try:
            return b"".join(chunks).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise UnsafeArchitectureInput(
                f"architecture input is not UTF-8: {candidate}"
            ) from exc
    finally:
        os.close(descriptor)

SECTION_ORDER = (
    "## What this repository is",
    "## The architecture in one page",
    "## Which file is authoritative for what",
    "## Repository map",
    "## A complete example",
    "## What happens when a change is made",
    "## How the checks run",
    "## What the checks do not prove",
    "## Where to start",
)

REQUIRED_ANCHOR_GROUPS = {
    "purpose_and_boundary": (
        "eight mathematical problem programmes",
        "self-contained public release",
    ),
    "three_decisions": (
        "Lean decides whether a formal proof",
        "A mathematician decides whether the public wording",
        "The release program decides whether the files",
    ),
    "authority_owners": (
        "Erdos249257.lean",
        "docs/claims.json",
        "docs/methodology.json",
        "scripts/check_release.py",
        ".github/workflows/lean.yml",
        "verification/comparator.json",
        "PALOMAR_POLICY_RECONCILIATION.json",
        "--route comparator_assurance",
        "--route palomar_qualification",
    ),
    "worked_example": (
        "certified_kill_instances",
        "verified finite instance",
        "beyond every fixed cutoff",
    ),
    "validation_split": (
        "lake build",
        "python3 scripts/check_release.py",
        "does not run Lean",
    ),
    "guarantee_ceiling": (
        "does not mean that a program understood every sentence",
        "does not prove that every important sentence was selected",
    ),
    "paper_lifecycle_boundary": (
        "The eight individual problem papers are the active mathematical routes",
        "archived provenance only, not an active gateway",
        "The archived combined #249/#257 PDF is not a default reading route",
    ),
}

REQUIRED_PATHS = (
    "lean/Erdos249257.lean",
    "lean/ErdosProblems.lean",
    "docs/claims.json",
    "docs/methodology.json",
    "docs/publication_contract.json",
    "docs/publication_evidence.json",
    "verification/comparator.json",
    "docs/verification/PALOMAR_QUALIFICATION.md",
    "docs/PALOMAR_POLICY_RECONCILIATION.json",
    "docs/ORIENTATION.md",
    "docs/SOURCE_MAP.md",
    "scripts/check_release.py",
    "scripts/check_cold_clone_comprehension.py",
    ".github/workflows/lean.yml",
    "paper/archive/erdos249-257-main-paper.tex",
)

# These labels belong to the evaluation history or to private agent doctrine.
# A first-principles repository guide has no reason to make a cold reader decode
# them. The full words Type A and Type B are included because they are private
# role labels in the parent workflow, not part of this public Lean project.
BANNED_SHORTHAND = (
    re.compile(r"\bM(?:10|[1-9])\b"),
    re.compile(r"\b9/10\b"),
    re.compile(r"\b5,207\b"),
    re.compile(r"\bMRS\b"),
    re.compile(r"\bquantifier\b", re.IGNORECASE),
    re.compile(r"\bType A\b", re.IGNORECASE),
    re.compile(r"\bType B\b", re.IGNORECASE),
    re.compile(r"\bAccess Skeleton\b", re.IGNORECASE),
    re.compile(r"\bVinum\b", re.IGNORECASE),
)

PAPER_SECTION_ORDER = (
    r"\section{A theorem and the explanation it needs}",
    r"\section{A problem-sized world}",
    r"\section{From corpus to insight}",
    r"\section{From a proof to a public claim}",
    r"\section{The contribution cycle}",
    r"\section{Eight problems in one repository}",
    r"\section{Relation to Prove2Me and other systems}",
    r"\section{Limits, and what stronger models change}",
    r"\section{Conclusion}",
    r"\section{Inspection routes and reproducibility}",
)

# The September 2026 rewrite replaced the architecture note with a shorter
# paper built around one unit of work, the problem-sized world. The pins below
# hold the claims that paper rests on and every limit it states: removing one
# should fail this check rather than quietly shrink the paper's boundary.
# The 24 September revision opens with worked mathematics instead of an
# account of the field, so its groups also pin each example's evidence class:
# the A-star estimates and the synthesis theorems are ordinary arguments, the
# reciprocal-summable case is credited to Erdos, and the totient independence
# is credited to Martin and to Yazdani and Shallit.
PAPER_REQUIRED_ANCHOR_GROUPS = {
    "plain_purpose": (
        "persistent unit of work, the problem-sized world",
        "Any model, provider or person can resume from the record",
        "accepted work returns to it with credit",
        "The other seven targets remain open",
        "Comparator, a checker the Lean FRO built",
        "formal refutation of the Formal Conjectures statement of Problem 1041",
    ),
    "grounding_in_the_field": (
        "faster than the mathematical community can read them",
        "every AI-generated proof is born an unsolved exposition problem",
        "Each of these concerns what a proof does not carry by itself",
    ),
    "worked_mathematics": (
        "The criterion reaches past reciprocal summability",
        "These estimates are ordinary arguments in the short paper",
        "The infinite tail is the hard step",
        "credits it to him",
        "does not identify its weighted condition with that remark",
        "irrationality for every infinite support remains open",
        "already implies the affine independence",
        "who credits it to Shallit",
        "carry no Lean mark",
    ),
    "four_decisions": (
        "Every result that returns to a world raises four decisions",
        "A successful check in one row settles nothing in another",
        "No deterministic check decides what is important",
    ),
    # The corpus-to-insight transfer is the paper's complete worked case of a
    # representation change: the rejected and accepted applications, the
    # division between the authored bridge and Lean, the constant's origin in
    # the source theorem's radix bound, and the prime-series boundary.
    "corpus_to_insight": (
        "The smallest complete case is a transfer between two problems",
        "The change of variable is the mathematical bridge",
        "The constant $1/31$ came from the radix bound 30",
        "establishing the criterion for the actual prime gaps remains open",
        "the admissible constants form the open interval",
        "acceptance and closure are recorded separately",
        "An enduring endpoint and a justified next step are different allocations",
    ),
    "world_and_obligations": (
        "Negative results are part of what the loop produces",
        "A Lean no-go theorem rules out a class of strategies",
        "the record states it in exactly that form",
    ),
    # The ledger's exact_or_stronger class includes equality: its declarations
    # state the result or one implying it by an immediate specialisation. An
    # earlier edition printed it as "a stronger form".
    "three_questions": (
        "Lean verifies that a proof establishes the formal statement written in the source",
        "requires Comparator to reject a deliberately altered statement",
        "This control exercises that mismatch path",
        "Comparator-checked",
        "The third question stays with people",
        "state it or a result that implies it by an immediate specialisation",
    ),
    "escaped_limitation": (
        "That requirement comes from a test in which a limitation escaped",
        "relationship had not been registered",
        "does not technically force a second independent mathematician",
    ),
    "contribution_cycle": (
        "research, checking and revision cycle",
        "an empty search never counts as evidence of no consequence",
        "Discovery and stewardship",
        "Neither inherits the other's authority",
        "plain-language research-progress issue or email",
        "No clone, proof, code or receipt schema is required",
        "Accepted work receives a public receipt tied to exact artifacts",
        "Acceptance does not establish theorem status, novelty, or release inclusion",
    ),
    "worked_example": (
        "Problem 1041 shows the cycle end to end",
        "whether the formal statement matches the 1958 wording",
    ),
    "production_boundary": (
        "Durable state lives in files",
        "semantic single-flight queue",
        "recorded separately from theorem failures",
        "It never changes the status of a mathematical claim",
        "becomes the exact remaining obligation",
        "The public repository replays without the private environment",
    ),
    # The summary table and the cycle caption once dropped hypotheses the
    # registry states: #243 needs a strictly increasing sequence of positive
    # integers, #249's rank formula needs k >= 2 and e >= 1 (at e = 0 the family
    # is phi(n) alone, of dimension one), and a refutation can settle a problem.
    # The #257 criterion needs a finite nonempty prime set, and the synthesis
    # class H_c is defined for c > 0.
    "result_hypotheses": (
        "For a strictly increasing sequence of positive integers",
        r"For every base $k\ge2$ and level $e\ge1$",
        "a problem closes only when a proof or a refutation settles its original statement",
        r"fix a finite nonempty set $P$ of primes",
        r"For $c>0$, let $\mathcal H_c$",
        r"with $p_n,c_n\in\mathbb Z$ and $2\le p_n\le30$",
        r"so every fixed $0<c<\tau$ works in the equivalence",
    ),
    "related_work": (
        "is the closest published system",
        "Persistence, correction, shared work and exact statement checking are therefore overlapping capabilities",
        "LeanMarathon maintains an evolving blueprint",
        "a direct precedent for the explanation a world keeps beside a formal proof",
        "the two designs developed independently",
    ),
    "limits_and_scaling": (
        "The same design serves stronger models",
        "The next measurement is comparative",
        "an information-equivalent written briefing",
        "A representation contrast holds information, tools and budget fixed",
        "discovery comparisons use held-out transformations or prospective continuations",
        "whether the workflow made those results more likely has not been measured",
        "no outside human contributor had opened a pull request or issue",
    ),
    "real_public_routes": (
        "docs/ARCHITECTURE.md",
        "lean/Erdos249257.lean",
        "lean/ErdosProblems.lean",
        "docs/claims.json",
        "verification/comparator.json",
        "scripts/check_release.py",
        ".github/workflows/lean.yml",
        "docs/research-commons/CREDIT_POLICY.md",
        "docs/research-commons/ARCHITECTURE_CONTRIBUTIONS.md",
    ),
}

# The cold-reader architecture guide still avoids private Type A/B labels and
# unexplained quantifier jargon.  The systems paper has the different job of
# explaining those mechanisms and the finite/unbounded mathematical boundary.
PAPER_BANNED_SHORTHAND = (
    re.compile(r"\bM(?:10|[1-9])\b"),
    re.compile(r"\b9/10\b"),
    re.compile(r"\b5,207\b"),
    re.compile(r"\bMRS\b"),
    re.compile(r"\bAccess Skeleton\b", re.IGNORECASE),
    re.compile(r"\bVinum\b", re.IGNORECASE),
)


def normalise(text: str) -> str:
    return " ".join(text.split())


def normalise_tex(text: str) -> str:
    """Flatten the small subset of TeX used by load-bearing prose anchors."""
    for _ in range(3):
        text = re.sub(
            r"\\(?:textbf|emph|texttt)\{([^{}]*)\}",
            r"\1",
            text,
        )
    text = text.replace(r"\_", "_").replace("{", "").replace("}", "")
    return normalise(text)


def require(condition: bool, message: str) -> None:
    """Enforce a release check even when callers run Python with ``-O``."""
    if not condition:
        raise AssertionError(message)


def validate_claim_scope(text: str, claims: dict) -> None:
    """Compare the guide's scope with registry identities, not a frozen slogan."""
    registered = {
        int(match.group(1))
        for problem_id in claims.get("external_verification_packet", {}).get("problem_ids", [])
        if (match := re.fullmatch(r"erdos_(\d+)", str(problem_id)))
    }
    scope = re.search(r"reviewed claim registry covers ([^.]+)\.", normalise(text))
    require(scope is not None, "architecture guide must state its reviewed claim scope")
    stated = {int(number) for number in re.findall(r"#(\d+)", scope.group(1))}
    require(bool(registered) and stated == registered, (
        f"architecture claim scope differs from docs/claims.json: "
        f"stated={sorted(stated)}, registered={sorted(registered)}"
    ))
def external_status_boundary() -> str:
    claims = json.loads(safe_architecture_text(CLAIMS))
    packet = claims.get("external_verification_packet", {})
    boundary = packet.get("boundary")
    require(isinstance(boundary, str) and boundary.strip(),
            "docs/claims.json lacks the external verification status boundary")
    return normalise(boundary)


def validate_guide(text: str) -> None:
    size = len(text.encode("utf-8"))
    require(size <= MAX_GUIDE_BYTES, (
        f"docs/ARCHITECTURE.md is {size} bytes (budget {MAX_GUIDE_BYTES})"
    ))

    positions = [text.find(heading) for heading in SECTION_ORDER]
    require(all(position >= 0 for position in positions), (
        f"architecture guide lost section sequence {SECTION_ORDER}"
    ))
    require(positions == sorted(positions), "architecture guide sections are out of order")
    validate_claim_scope(text, json.loads(safe_architecture_text(ROOT / "docs/claims.json")))

    compact = normalise_tex(text)
    require(external_status_boundary().casefold() in compact.casefold(),
            "architecture guide lost the authority-owned status boundary")
    for group_id, anchors in REQUIRED_ANCHOR_GROUPS.items():
        for anchor in anchors:
            require(normalise(anchor).casefold() in compact.casefold(), (
                f"architecture guide lost {group_id} anchor {anchor!r}"
            ))

    for pattern in BANNED_SHORTHAND:
        require(not pattern.search(text), (
            f"architecture guide exposes private or evaluation shorthand {pattern.pattern!r}"
        ))

    local_targets = {
        (GUIDE.parent / target.split("#", 1)[0]).resolve()
        for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text)
        if not target.startswith(("http://", "https://", "#"))
    }
    for rel in REQUIRED_PATHS:
        require((ROOT / rel).exists(), f"architecture guide names missing path {rel}")
        require((ROOT / rel).resolve() in local_targets or rel in text,
                f"architecture guide no longer links to {rel}")

    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        if target.startswith(("http://", "https://", "#")):
            continue
        path = target.split("#", 1)[0]
        require((GUIDE.parent / path).exists(), f"architecture guide has broken local link {target}")


def validate_systems_paper(text: str) -> None:
    """Keep the PDF source architecture-first rather than experiment-first."""
    size = len(text.encode("utf-8"))
    contract = json.loads(safe_architecture_text(PUBLICATION_CONTRACT))
    artifact_count = len(contract["artifacts"])
    byte_budget = (
        SYSTEMS_PAPER_BASE_BYTES
        + SYSTEMS_PAPER_BYTES_PER_ARTIFACT * artifact_count
    )
    require(size <= byte_budget, (
        f"systems architecture paper is {size} bytes "
        f"(budget {byte_budget} for {artifact_count} governed artifacts)"
    ))

    require(
        "Problem-Sized Lean Worlds" in text
        and "Persistent, checkable research records for AI-assisted mathematics"
        in text
    , "systems paper lost its plain architecture title")
    require(
        r"\newcommand{\repobase}{https://github.com/wcook04/plectis-erdos}" in text,
        "systems paper repository links do not use the canonical public repository",
    )
    require(
        text.count("% BEGIN generated_semantic_coverage_macros") == 1
        and text.count("% END generated_semantic_coverage_macros") == 1,
        "systems paper lost its semantic-corpus builder region",
    )

    positions = [text.find(heading) for heading in PAPER_SECTION_ORDER]
    require(all(position >= 0 for position in positions), (
        f"systems paper lost section sequence {PAPER_SECTION_ORDER}"
    ))
    require(positions == sorted(positions), "systems paper sections are out of order")

    compact = normalise_tex(text)
    for group_id, anchors in PAPER_REQUIRED_ANCHOR_GROUPS.items():
        for anchor in anchors:
            require(normalise(anchor).casefold() in compact.casefold(), (
                f"systems paper lost {group_id} anchor {anchor!r}"
            ))

    for pattern in PAPER_BANNED_SHORTHAND:
        require(not pattern.search(text), (
            f"systems paper exposes private or score-like shorthand {pattern.pattern!r}"
        ))

    require(len(re.findall(r"\bsentence\b", text, flags=re.IGNORECASE)) <= 4, (
        "systems paper has drifted back to a sentence-centred case study"
    ))
    require("certified_kill_instances" not in compact, (
        "systems paper regressed from public mathematical meaning to an internal claim id"
    ))
    for target in re.findall(r"\\repolink\{([^{}]+)\}\{", text):
        require((ROOT / target).is_file(), (
            f"systems paper links to missing repository file {target}"
        ))
    validate_pinned_evidence_links(text)
    require(SYSTEMS_PDF.is_file(), "rendered systems architecture PDF is missing")


PINNED_BLOB_LINK = re.compile(
    r"\\href\{\\repobase/blob/([0-9a-f]{40})/([^}#\\]+)(?:\\#([^}]+))?\}"
)
REPOLINK_PIN = re.compile(
    r"\\newcommand\{\\repolink\}\[2\]\{\\href\{\\repobase/blob/([0-9a-f]{40})/#1\}"
)


def heading_slug(heading: str) -> str:
    """GitHub's anchor for a Markdown heading, for the headings this repository uses."""
    text = re.sub(r"[`*_]", "", heading.strip().lower())
    text = re.sub(r"[^\w\- ]", "", text)
    return text.replace(" ", "-")


def pinned_file(commit: str, path: str) -> str | None:
    shown = subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=ROOT, capture_output=True, check=False,
    )
    if shown.returncode != 0:
        return None
    return shown.stdout.decode("utf-8", errors="replace")


def validate_pinned_evidence_links(text: str) -> None:
    """A pinned link must reach the evidence in the revision it names.

    A URL can resolve to a genuine historical file that predates the
    assertion sending the reader there. Every \\repolink target must exist at
    the macro's pinned commit, and every directly pinned \\href must exist at
    its commit, with any #fragment naming a heading that revision contains.
    """
    pin = REPOLINK_PIN.search(text)
    require(pin is not None, "systems paper lost its pinned repolink macro")
    for target in re.findall(r"\\repolink\{([^{}]+)\}\{", text):
        require(pinned_file(pin.group(1), target) is not None, (
            f"repolink target {target} is absent at its pinned commit {pin.group(1)[:12]}"
        ))
    for commit, path, fragment in PINNED_BLOB_LINK.findall(text):
        body = pinned_file(commit, path)
        require(body is not None, (
            f"pinned evidence link {path} is absent at {commit[:12]}"
        ))
        if fragment:
            slugs = {
                heading_slug(line.lstrip("#"))
                for line in body.splitlines()
                if line.startswith("#")
            }
            require(fragment in slugs, (
                f"pinned evidence link {path}#{fragment} names a section "
                f"absent at {commit[:12]}"
            ))


def validate_entry_links(
    readme: str,
    agents: str,
    paper_readme: str,
    guide: str,
) -> None:
    readme_first_impression = (
        readme.encode("utf-8")[:6_000].decode("utf-8", errors="ignore")
    )
    require(
        external_status_boundary().casefold()
        in normalise(readme_first_impression).casefold(),
        "README first impression lost the authority-owned status boundary",
    )
    require("](docs/ARCHITECTURE.md)" in readme,
            "README lost the architecture guide entry link")
    require(
        re.search(
            r"\]\([^)]*claim-faithful-publication-systems-paper\.pdf\)",
            guide,
        ),
        "architecture guide lost the printable systems-paper route",
    )
    compact_guide = normalise(guide).casefold()
    require(
        "you do not need to know lean" in compact_guide
        and "project history" in compact_guide,
        "architecture guide lost the no-Lean/no-history entry boundary",
    )
    for phrase in (
        "conditional producer",
        "unbounded or cofinal supply",
        "lcm-diagonal scales",
        "producer carry",
    ):
        require(phrase not in readme_first_impression.casefold(), (
            f"README first impression exposes unexplained phrase {phrase!r}"
        ))
    require("docs/ARCHITECTURE.md" in agents, "AGENTS lost the architecture guide route")
    require("plain-language human guide" in agents,
            "AGENTS lost the plain-language architecture guide route")
    compact_paper_readme = normalise(paper_readme)
    require("[`docs/ARCHITECTURE.md`](../docs/ARCHITECTURE.md)" in paper_readme,
            "paper README lost the architecture guide route")
    require(
        "short first-read paper" in compact_paper_readme
        and "longer complete reasoning record" in compact_paper_readme,
        "paper README lost the short-paper/reasoning-record boundary",
    )
    require(
        "repository layout, sources of truth, build path, and release infrastructure"
        in compact_paper_readme,
        "paper README lost the architecture-guide role",
    )
    require(
        "older joint #249/#257 paper is retained for provenance" in compact_paper_readme
        and "not the entry point for either problem" in compact_paper_readme,
        "paper README lost the maintained-versus-historical route boundary",
    )
    for manuscript in (
        "erdos249-257-main-paper.tex",
        "claim-faithful-publication-systems-paper.tex",
    ):
        require(manuscript in paper_readme,
                f"paper README lost manuscript route {manuscript}")


def main() -> int:
    validate_guide(safe_architecture_text(GUIDE))
    validate_systems_paper(safe_architecture_text(SYSTEMS_PAPER))
    validate_entry_links(
        safe_architecture_text(README),
        safe_architecture_text(AGENTS),
        safe_architecture_text(PAPER_README),
        safe_architecture_text(GUIDE),
    )
    print("architecture guide: first-principles structure and entry links verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
