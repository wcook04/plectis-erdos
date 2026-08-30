#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Build the public corpus descriptor and bounded orientation projections.

The descriptor is a self-describing navigation root for external agents.  It
keeps the last tagged release distinct from the exact formal-source checkpoint
and from the later navigation snapshot, carries content digests for the human papers, machine-readable paper,
source-sigil crosswalk, methodology contract, and exhaustive atlas, and embeds
only compact navigation data.  It does not duplicate the full declaration
atlas or acquire proof authority.

The companion orientation JSON and Markdown are deliberately small first-read
surfaces. They expose scale, the proved/open boundary, principal claims, and
typed drilldowns without asking a cold reader to load the exhaustive graphs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "docs" / "corpus_descriptor.json"
DESCRIPTOR_MAX_BYTES = 64_000
ORIENTATION_MAX_BYTES = 32_000
ORIENTATION_MARKDOWN_MAX_BYTES = 16_000
ORIENTATION_JSON = ROOT / "docs" / "orientation.json"
ORIENTATION_MARKDOWN = ROOT / "docs" / "ORIENTATION.md"
README_PATH = ROOT / "README.md"
WAVE_INDEX_PATH = ROOT / "docs" / "WAVE_INDEX.md"
CLAIMS_PATH = ROOT / "docs" / "claims.json"
PROBLEMS_PATH = ROOT / "docs" / "problems.json"
ATLAS_PATH = ROOT / "docs" / "declaration_atlas.json"
METHODOLOGY_PATH = ROOT / "docs" / "methodology.json"
MAIN_PAPER_TEX = ROOT / "paper" / "erdos249-257-main-paper.tex"
MAIN_PAPER_PDF = ROOT / "erdos249-257-main-paper.pdf"
PAPER_ALIASES_PATH = ROOT / "paper" / "module-aliases.json"
README_SCALE_BEGIN = "<!-- BEGIN generated_corpus_at_a_glance -->"
README_SCALE_END = "<!-- END generated_corpus_at_a_glance -->"
README_PRINCIPAL_BEGIN = "<!-- BEGIN generated_principal_declaration_anchors -->"
README_PRINCIPAL_END = "<!-- END generated_principal_declaration_anchors -->"
WAVE_SHAPE_BEGIN = "<!-- BEGIN generated_package_shape -->"
WAVE_SHAPE_END = "<!-- END generated_package_shape -->"


def canonical_digest(value: Any) -> str:
    encoded = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def file_digest(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def build_orientation(claims: dict[str, Any], atlas: dict[str, Any]) -> dict[str, Any]:
    """Project a bounded first-read capsule from the exhaustive owners."""
    principal_claims = []
    for claim in claims["claims"]:
        if not claim.get("readme_headline"):
            continue
        row = {
            "id": claim["id"],
            "status": claim["status"],
            "statement": claim["statement"],
            "paper_label": claim.get("paper_label"),
            "declarations": [
                {
                    "name": declaration["name"],
                    "module": declaration["module"],
                    "line": declaration["line"],
                }
                for declaration in claim["declarations"]
            ],
        }
        if claim.get("remaining_open_proposition_ids"):
            row["remaining_open_proposition_ids"] = claim["remaining_open_proposition_ids"]
        principal_claims.append(row)

    machine_paper = claims["machine_readable_paper"]
    publication_assembly = machine_paper["publication_assembly"]
    # The runnable per-route command is derivable from the id (see the
    # ``queries`` section); storing it per row would spend first-contact
    # budget on repetition.
    reading_routes = []
    for route in machine_paper["entrypoints"]:
        row: dict[str, Any] = {
            "id": route["id"],
            "intent": route["intent"],
            "read": route["read"],
        }
        if route.get("title"):
            row["title"] = route["title"]
        reading_routes.append(row)
    mathematical_programmes = [
        {
            "id": route["id"],
            "title": route["title"],
            "mathematical_focus": route["mathematical_focus"],
            "claim_ceiling": route["claim_ceiling"],
            "core_claim_count": len(route["core_claim_ids"]),
            "representative_claim_ids": route["core_claim_ids"][:2],
            "remaining_open_proposition_ids": route[
                "remaining_open_proposition_ids"
            ],
        }
        for route in machine_paper["entrypoints"]
        if route.get("route_kind") == "mathematical_programme"
    ]
    architecture = publication_assembly["publication_architecture"]
    editorial_architecture = {
        "canonical_gateway": {
            key: architecture["canonical_gateway"][key]
            for key in ("source", "decision")
        },
        "retained_companions": [
            {key: companion[key] for key in ("source", "decision")}
            for companion in architecture.get("retained_companions", [])
        ],
        "qualified_future_companion": {
            key: architecture["qualified_future_companion"][key]
            for key in ("id", "decision")
        },
    }
    state = publication_assembly["editorial_state"]
    editorial_state = {
        "current_priority": state["current_priority"],
        "active_inconsistencies": state["active_inconsistencies"],
        "blocked_decisions": state["blocked_decisions"],
    }
    return {
        "schema": "erdos249257-orientation/1",
        "artifact_role": "bounded_first_read_navigation_projection",
        "authority_posture": "navigation_projection_not_proof_authority",
        "proof_authority": "Lean source checked by the pinned Lean kernel",
        "release_provenance": claims["release"]["public_projection"],
        "release": {
            "version": claims["release"]["version"],
            "tag": claims["release"]["tag"],
            "lean_toolchain": claims["release"]["lean_toolchain"],
            "formal_source_ref": claims["release"]["formal_source"]["ref"],
            "formal_source_public_tag": claims["release"]["formal_source"]["public_tag"],
            "formal_source_publication_state": claims["release"]["formal_source"]["publication_state"],
        },
        "scale": atlas["summary"],
        "status_taxonomy": claims["status_taxonomy"],
        "remaining_open_propositions": claims["remaining_open_propositions"],
        "non_claims": claims["non_claims"],
        "principal_claims": principal_claims,
        "mathematical_programmes": mathematical_programmes,
        "editorial_architecture": editorial_architecture,
        "editorial_state": editorial_state,
        "source_provenance": {
            "formal_source_ref": claims["release"]["formal_source"]["ref"],
            "main_paper_source_digest": file_digest(MAIN_PAPER_TEX),
            "navigation_projection_identity": (
                "content digests in corpus descriptor; no checkout commit embedded"
            ),
        },
        "reading_routes": reading_routes,
        "drilldowns": {
            "exact_claims_and_argument_graph": "docs/claims.json",
            "machine_readable_paper": "docs/claims.json::machine_readable_paper",
            "exhaustive_declarations": "docs/declaration_atlas.json",
            "mathematical_methodology": "docs/methodology.json",
            "human_exposition": "erdos249-257-main-paper.pdf",
            # human_exposition is one digest-bound manuscript, and it is the one
            # the corpus marks retired. An agent that started here could reach
            # it and nothing else: the thirteen active manuscripts, and the
            # bounded index that names what each one answers and is not
            # authority for, were unreachable from the first-read projection.
            "paper_corpus": "docs/papers/corpus.json",
            "paper_source_sigils": "paper/module-aliases.json",
            "source_by_question": "docs/SOURCE_MAP.md",
            "development_chronology": "docs/WAVE_INDEX.md",
            "supported_root_import": "Erdos249257.lean",
            "supported_root_imports": ["Erdos249257.lean", "ErdosProblems.lean"],
        },
        "checks": {
            "release": "python3 scripts/check_release.py",
            "cold_clone_comprehension": "python3 scripts/check_cold_clone_comprehension.py",
            "orientation_freshness": "python3 scripts/build_corpus_descriptor.py --check",
            "rendered_paper_boundary": "python3 scripts/check_rendered_paper_boundary.py",
        },
        "queries": {
            "summary": "python3 scripts/query_corpus.py --format card",
            "claim": "python3 scripts/query_corpus.py --claim <claim_id>",
            "claim_status": "python3 scripts/query_corpus.py --status <claim_status> [--limit 1..100]",
            "paper_label": "python3 scripts/query_corpus.py --paper-label <TeX_label>",
            "paper_anchor": "python3 scripts/query_corpus.py --paper-anchor <TeX_label_or_source_ref>",
            "open_proposition": "python3 scripts/query_corpus.py --open <remaining_open.id>",
            "declaration": "python3 scripts/query_corpus.py --declaration <Lean_name>",
            "source_coordinate": "python3 scripts/query_corpus.py --source <module.lean:line>",
            "artifact_or_digest": "python3 scripts/query_corpus.py --artifact <path_or_sha256>",
            "module": "python3 scripts/query_corpus.py --module <path_or_id_or_paper_sigil>",
            "reading_route": "python3 scripts/query_corpus.py --route <route_id>",
            "mathematical_programme": "python3 scripts/query_corpus.py --route <programme_route_id>",
            "search": "python3 scripts/query_corpus.py --search <text> [--limit 1..100]",
        },
        "external_registration": {
            "path": "docs/corpus_descriptor.json",
            "schema": "erdos249257-corpus-descriptor/5",
            "maximum_bytes": DESCRIPTOR_MAX_BYTES,
            "inline": ["release_identity", "content_digests", "principal_claim_handles", "root_module_topology"],
            "expands_to": [
                "docs/claims.json",
                "docs/declaration_atlas.json",
                "docs/methodology.json",
                "erdos249-257-main-paper.pdf",
                "paper/module-aliases.json",
            ],
        },
    }


def render_orientation_markdown(orientation: dict[str, Any]) -> str:
    scale = orientation["scale"]
    # REUSE-IgnoreStart — these strings are emitted into the generated projection.
    lines = [
        "<!--",
        "SPDX-FileCopyrightText: 2026 Will Cook",
        "SPDX-License-Identifier: Apache-2.0",
        "",
        "Generated by scripts/build_corpus_descriptor.py. Do not edit by hand.",
        "-->",
        "",
        "# Corpus orientation",
        "",
        "This is the bounded first-read map for the public release. It is a navigation",
        "projection, not proof authority. The published Lean source checked by the pinned",
        "Lean kernel remains proof authority.",
        "",
        "## Release provenance",
        "",
        orientation["release_provenance"]["meaning"],
        "",
        "Public evidence of that release workflow: "
        + "; ".join(orientation["release_provenance"]["public_evidence"])
        + ".",
        "",
        orientation["release_provenance"]["boundary"],
    ]
    # REUSE-IgnoreEnd
    lines.extend(
        [
            "",
            "## What a claim status asserts",
            "",
            "A status states the exact public evidence claim, not a priority or novelty claim.",
            "The authored prior-art record, not this table, is the source for antecedents.",
            "",
            "| Status | Exact public meaning |",
            "|---|---|",
        ]
    )
    for status, meaning in orientation["status_taxonomy"].items():
        lines.append(f"| {status} | {meaning} |")
    lines.extend(["", "## Exact open boundary", ""])
    for row in orientation["remaining_open_propositions"]:
        lines.append(f"- `{row['id']}` — {row['statement']}")
    lines.extend(
        [
            "",
            "## Where the substance is",
            "",
            '- Both working records close with a section titled "The wall": every',
            "  attempted argument class stopped by a stated bound, recorded with",
            "  what it does not rule out.",
            '- The mathematics paper closes with "What we need from a mathematician":',
            "  four self-contained problems; a refuted route is withdrawn and the",
            "  refutation credited in the next edition.",
            "- [`docs/RESULTS.md`](RESULTS.md) opens with a ten-minute verdict.",
            "",
            "## Scale",
            "",
            "Navigation inventory, not results. Generated certificate shards are",
            "counted as formal source, never as separate mathematical claims.",
            "",
            "| Surface | Count |",
            "|---|---:|",
            "| Supported Lean roots | `Erdos249257.lean`, `ErdosProblems.lean` |",
            "| Problems in the public corpus | #68, #243, #249, #251, #257, #269, #1041, #1049 |",
            f"| Lean modules | {scale['module_count']:,} |",
            f"| Lean declarations | {scale['declaration_count']:,} |",
            f"| Theorem-like declarations | {scale['theorem_like_count']:,} |",
            f"| Manifest-marked generated declarations (a floor, not the share) | {scale['generated_certificate_declaration_count']:,} |",
            f"| Principal claim links | {scale['principal_claim_link_count']:,} |",
            "",
            "The exhaustive declaration and import index is",
            "[`docs/declaration_atlas.json`](declaration_atlas.json).",
        ]
    )
    lines.extend(
        [
            "",
            "## Mathematical programmes",
            "",
            "These are reading routes through the checked corpus, not extra claims.",
            "Each route states its mathematical focus and exact public claim ceiling.",
            "",
        ]
    )
    # Every ceiling is a full sentence, so a two-column table would be a stack of
    # paragraphs wearing a grid. The same route id, title, and ceiling read as a
    # list, in the shape the reading routes below already use.
    for route in orientation["mathematical_programmes"]:
        lines.append(f"- **{route['title']}** (`{route['id']}`)")
        lines.append(f"  - Ceiling: {route['claim_ceiling']}")
    lines.extend(
        [
            "",
            "Open one programme with",
            "`python3 scripts/query_corpus.py --route <programme_route_id>`.",
            "The packet returns the ordered claim handles, exact open boundary, related",
            "programmes, and source owners without loading the exhaustive graph.",
        ]
    )
    lines.extend(["", "## Principal claim routes", ""])
    lines.extend(
        [
            "| Claim | Status | Paper |",
            "|---|---|---|",
        ]
    )
    for claim in orientation["principal_claims"]:
        lines.append(
            f"| `{claim['id']}` | {claim['status']} | `{claim['paper_label']}` |"
        )
    lines.extend(
        [
            "",
            "Each row is only an entry handle. Read the claim statement and every attached",
            "declaration in [`docs/claims.json`](claims.json), then follow the paper label into",
            "the authored exposition. A conditional reduction or finite instance does not",
            "settle the open proposition attached to it.",
            "",
            "The first Lean anchor of each claim, in table order, as claim id,",
            "declaration name, then source coordinate:",
            "",
            "```text",
        ]
    )
    # A declaration name is an unbreakable token, so it sets a table column floor
    # wide enough to squash every other column. A fenced block scrolls inside
    # itself and keeps the name copy-paste clean.
    # Same order as the table above; the claim id is the shared key.
    for index, claim in enumerate(orientation["principal_claims"]):
        if index:
            lines.append("")
        first = claim["declarations"][0]
        lines.append(claim["id"])
        lines.append(f"    {first['name']}")
        lines.append(f"    {first['module']}:{first['line']}")
    lines.extend(
        [
            "```",
            "",
            "## Read by intent",
            "",
        ]
    )
    for route in orientation["reading_routes"]:
        paths = " → ".join(f"`{path}`" for path in route["read"])
        title = route.get("title") or route["intent"]
        lines.append(
            f"- **{title}** (`{route['id']}`): {paths}; "
            f"`python3 scripts/query_corpus.py --route {route['id']}`"
        )
    lines.extend(
        [
            "",
            "## Drill down",
            "",
            "- Exact statuses, statements, paper anchors, declarations, and argument edges:",
            "  [`docs/claims.json`](claims.json)",
            "- Complete eight-problem proof/paper/source/frontier matrix: [`docs/SOURCE_MAP.md#complete-eight-problem-return-matrix`](SOURCE_MAP.md#complete-eight-problem-return-matrix)",
            "- Development chronology: [`docs/WAVE_INDEX.md`](WAVE_INDEX.md)",
            "- Human mathematical account: [`erdos249-257-main-paper.pdf`](../erdos249-257-main-paper.pdf)",
            "- Machine form of this page: [`docs/orientation.json`](orientation.json)",
            "",
            "## External corpus registration",
            "",
            "[`docs/corpus_descriptor.json`](corpus_descriptor.json) uses schema",
            "`erdos249257-corpus-descriptor/5`. The release gate keeps it below 64 KB.",
            "It carries release identities, content digests, principal claim and declaration",
            "handles, and the root module topology. Complete claims, module imports,",
            "declaration prose, methodology, both authored papers, and the paper-to-Lean",
            "source-sigil crosswalk remain in their digest-bound expansion files.",
            "These authored surfaces remain distinct from Lean proof authority.",
            "",
            "## Query one handle",
            "",
            "The read-only query helper returns bounded JSON and typed drilldown handles:",
            "module packets expose import neighbours, claim packets expose typed edges",
            "and open-proposition packets preserve the unresolved target and its progress.",
            "Paper labels resolve to exact TeX lines; declaration packets add pinned Lean",
            "URLs, module context, and attached claims.",
            "",
            "```sh",
            "python3 scripts/query_corpus.py --format card",
            "python3 scripts/query_corpus.py --claim denominator_exclusion",
            "python3 scripts/query_corpus.py --paper-label res:farey",
            "python3 scripts/query_corpus.py --open remaining_open.unbounded_certificate_supply",
            "python3 scripts/query_corpus.py --declaration irrational_erdosSum_full_support",
            "python3 scripts/query_corpus.py --module Erdos249257/CertificateKernel.lean",
            "python3 scripts/query_corpus.py --module CerKer",
            "python3 scripts/query_corpus.py --route instant_orientation",
            "python3 scripts/query_corpus.py --route erdos249_diagonal_arithmetic",
            'python3 scripts/query_corpus.py --search "what remains open for 257" --limit 5',
            "```",
            "",
        ]
    )
    return "\n".join(lines)


# Module families emitted by generators rather than written by hand. The
# provenance-marker count in the atlas summary is a floor: the largest families
# predate the markers, so counting by family is the only honest measure of how
# much of the corpus is generated. Reporting the floor alone anchored readers on
# roughly 5%, when the measured share is over 85%.
GENERATED_MODULE_FAMILIES = (
    "FreePosition",
    "DiagonalPincerPrimeCertificates",
    "DiagonalPincerCertificates",
    "GeneratedCertificates",
    "Skip/Ladder",
    "Lift/Cert",
    "Lift/Recon",
)


def measured_generated_share(atlas: dict[str, Any]) -> dict[str, int]:
    """Count declarations living in generated certificate module families."""
    generated_declarations = 0
    generated_modules: set[str] = set()
    for declaration in atlas["declarations"]:
        module = declaration["module"]
        if any(family in module for family in GENERATED_MODULE_FAMILIES):
            generated_declarations += 1
            generated_modules.add(module)
    total = atlas["summary"]["declaration_count"]
    return {
        "generated_declarations": generated_declarations,
        "generated_modules": len(generated_modules),
        "declaration_count": total,
        "generated_percent": round(100 * generated_declarations / total),
    }


def render_readme_scale_strip(
    orientation: dict[str, Any], claims: dict[str, Any], atlas: dict[str, Any]
) -> str:
    scale = orientation["scale"]
    share = measured_generated_share(atlas)
    contribution_families = claims["machine_readable_paper"][
        "publication_assembly"
    ]["contribution_families"]
    return "\n".join(
        [
            README_SCALE_BEGIN,
            "<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->",
            "## Corpus at a glance",
            "",
            # Reviewed shape first, engineering inventory second. Leading with a
            # six-figure declaration count invited the inference that most of it
            # was authored mathematics; it is not, and size is not evidence.
            "The layer a mathematician should judge is small: "
            f"{len(claims['claims']):,} curated claim records in "
            f"{len(contribution_families):,} contribution families, reaching Lean source "
            f"through {scale['principal_claim_link_count']:,} principal declaration links. "
            "`SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest "
            "checked result per problem.",
            "",
            "The rest is engineering inventory. About "
            f"{share['generated_percent']}% of the {share['declaration_count']:,} "
            f"declarations ({share['generated_declarations']:,} across "
            f"{share['generated_modules']:,} modules) are machine-emitted certificate "
            "shards: one integer checked prime, one position excluded. The remainder "
            "is not all hand-written either.",
            "",
            "| Engineering inventory | Current size |",
            "|---|---:|",
            f"| Lean modules (the two library roots) | {scale['module_count']:,} |",
            f"| Formal results and supporting lemmas | {scale['theorem_like_count']:,} |",
            f"| Curated claim records | {len(claims['claims']):,} |",
            f"| Contribution families | {len(contribution_families):,} |",
            "",
            "Generated shards are counted as formal source and never as separate",
            "mathematical claims. Claim records span every status, including cited and",
            "open, and are partitioned exactly once.",
            "These are navigation counts, not novelty claims.",
            README_SCALE_END,
        ]
    )


def replace_readme_scale_strip(readme: str, replacement: str) -> str:
    start = readme.find(README_SCALE_BEGIN)
    end = readme.find(README_SCALE_END)
    if start < 0 or end < 0 or end < start:
        raise ValueError("README corpus-at-a-glance generated-region markers are missing")
    end += len(README_SCALE_END)
    return readme[:start] + replacement + readme[end:]


def render_readme_principal_declaration_anchors(orientation: dict[str, Any]) -> str:
    return "\n".join(
        [
            README_PRINCIPAL_BEGIN,
            "<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->",
            "## Following a result into Lean",
            "",
            "The paper links each headline result to the relevant source. For a particular",
            "topic, start with the [source map](docs/SOURCE_MAP.md); it gives the module",
            "order without asking you to decode Lean declaration names first.",
            README_PRINCIPAL_END,
        ]
    )


def replace_readme_principal_declaration_anchors(readme: str, replacement: str) -> str:
    start = readme.find(README_PRINCIPAL_BEGIN)
    end = readme.find(README_PRINCIPAL_END)
    if start < 0 or end < 0 or end < start:
        raise ValueError("README principal-declaration generated-region markers are missing")
    end += len(README_PRINCIPAL_END)
    return readme[:start] + replacement + readme[end:]


def render_wave_package_shape(atlas: dict[str, Any]) -> str:
    modules = {row["id"]: row for row in atlas["modules"]}

    def source_facts(module_id: str) -> tuple[dict[str, Any], Path, int]:
        row = modules[module_id]
        path = ROOT / row["path"]
        line_count = len(path.read_text(encoding="utf-8").splitlines())
        return row, path, line_count

    kernel, kernel_path, kernel_lines = source_facts("Erdos249257.CertificateKernel")
    generated, generated_path, generated_lines = source_facts(
        "Erdos249257.GeneratedCertificates"
    )
    generated_shards = sum(
        row["path"].startswith("Erdos249257/GeneratedCertificates/")
        for row in atlas["modules"]
    )
    pincer_prime_shards = sum(
        row["path"].startswith("Erdos249257/DiagonalPincerPrimeCertificates/")
        for row in atlas["modules"]
    )
    pincer_scale_aggregators = sum(
        row["path"].startswith("Erdos249257/DiagonalPincerCertificatesT")
        for row in atlas["modules"]
    )
    scale = atlas["summary"]
    return "\n".join(
        [
            WAVE_SHAPE_BEGIN,
            "<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->",
            "## Package shape",
            "",
            f"- `CertificateKernel.lean` ({kernel_path.stat().st_size / 1024**2:.2f} MiB, "
            f"{kernel_lines:,} lines, {kernel['declaration_count']:,} declarations; "
            f"{kernel['kind_counts'].get('theorem', 0):,} theorems and "
            f"{kernel['kind_counts'].get('lemma', 0):,} lemmas): the assembled microkernel and headline interfaces.",
            f"- `GeneratedCertificates.lean` ({generated_path.stat().st_size / 1024**2:.2f} MiB, "
            f"{generated_lines:,} lines, {generated['declaration_count']:,} declarations) plus "
            f"{generated_shards} generated shards: finite certificate instances checked by the Lean kernel.",
            f"- The diagonal-pincer family contains {pincer_prime_shards:,} isolated prime-certificate "
            f"modules and {pincer_scale_aggregators} scale aggregators. The shards are indexed through "
            "aggregators rather than presented as separate mathematical claims.",
            f"- Entire checked corpus: {scale['module_count']:,} modules, "
            f"{scale['declaration_count']:,} declarations, {scale['theorem_like_count']:,} theorem-like "
            f"declarations, and {scale['generated_certificate_declaration_count']:,} manifest-marked "
            "generated-certificate declarations (a classification floor, not the generated share). "
            "The release gate rejects `sorry`, `admit`, custom `axiom` declarations, and "
            "`native_decide`.",
            "",
            "These are generated inventory facts, not mathematical claim counts. The declaration atlas",
            "and Lean source remain the drilldown owners.",
            WAVE_SHAPE_END,
        ]
    )


def replace_generated_region(text: str, begin: str, end: str, replacement: str) -> str:
    start = text.find(begin)
    finish = text.find(end)
    if start < 0 or finish < 0 or finish < start:
        raise ValueError(f"generated-region markers are missing: {begin} / {end}")
    finish += len(end)
    return text[:start] + replacement + text[finish:]


def build() -> dict[str, Any]:
    claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    problems = json.loads(PROBLEMS_PATH.read_text(encoding="utf-8"))
    atlas = json.loads(ATLAS_PATH.read_text(encoding="utf-8"))
    methodology = json.loads(METHODOLOGY_PATH.read_text(encoding="utf-8"))
    paper_aliases = json.loads(PAPER_ALIASES_PATH.read_text(encoding="utf-8"))
    machine_paper = claims["machine_readable_paper"]
    release = claims["release"]

    formal_source = release["formal_source"]
    formal_ref = str(formal_source["ref"])
    if formal_source.get("ref_kind") == "commit":
        formal_commit = formal_ref
    else:
        current = (
            json.loads(OUTPUT.read_text(encoding="utf-8"))
            if OUTPUT.is_file()
            else {}
        )
        recorded = current.get("identity", {}).get("formal_source", {})
        formal_commit = (
            recorded.get("resolved_commit")
            if recorded.get("ref") == formal_ref
            else "unknown"
        )
    orientation = build_orientation(claims, atlas)
    root_paths = [
        machine_paper["module_graph"]["root"],
        *machine_paper["module_graph"].get("additional_roots", []),
    ]
    root_modules = {
        root_path: next(row for row in atlas["modules"] if row["path"] == root_path)
        for root_path in root_paths
    }
    principal_declaration_handles = [
        {"claim_id": claim["id"], **declaration}
        for claim in orientation["principal_claims"]
        for declaration in claim["declarations"]
    ]
    # The descriptor is a registration envelope, so its principal-claim rows
    # are handles rather than a second copy of authored claim prose.  Preserve
    # every status, paper, open-obligation, and Lean-source coordinate needed
    # to resolve a claim; the exact statement remains in the digest-bound
    # claims document and in the bounded orientation projection.
    principal_claim_handles = [
        {
            key: value
            for key, value in claim.items()
            if key != "statement"
        }
        for claim in orientation["principal_claims"]
    ]

    repository = str(release["repository"])
    return {
        "schema": "erdos249257-corpus-descriptor/5",
        "artifact_role": "self_describing_external_mathematical_corpus_root",
        "corpus_id": "plectis_lean_erdos249_257_public",
        "release_provenance": release["public_projection"],
        "authority_posture": {
            "proof": "Lean source checked by the pinned Lean kernel",
            "authored_argument": "docs/claims.json::machine_readable_paper.argument_graph",
            "navigation": "generated projections and this descriptor; not proof authority",
            "semantic_bridge": "approximate correspondence only; never a proof edge",
            "methodology": "docs/methodology.json defines mathematical methodology and claim-transition requirements; it is not proof authority or claim-status authority",
        },
        "identity": {
            "formal_source": {
                "ref": formal_ref,
                "ref_kind": formal_source["ref_kind"],
                "resolved_commit": formal_commit,
                "public_tag": formal_source["public_tag"],
                "publication_state": formal_source["publication_state"],
                "relationship_to_last_tag": formal_source["relationship_to_last_tag"],
                "last_release": {
                    "version": release["version"],
                    "tag": release["tag"],
                },
                "lean_toolchain": release["lean_toolchain"],
                "authority_role": "proof_bearing_committed_source_anchor",
            },
            "navigation_projection": {
                "identity_kind": "content_addressed_expansion_set",
                "authority_role": (
                    "machine_readable_navigation_identity_not_proof_authority"
                ),
                "content_identity_owner": "identity.content",
                "git_commit_not_embedded_reason": (
                    "A generated file cannot truthfully contain the Git commit "
                    "that first contains its own bytes. Current projection identity "
                    "is therefore the committed content-digest set, while the "
                    "formal-source commit remains separate."
                ),
            },
            "content": {
                "machine_readable_paper": {
                    "path": "docs/claims.json::machine_readable_paper",
                    "content_digest": canonical_digest(machine_paper),
                },
                "claims_document": {
                    "path": "docs/claims.json",
                    "content_digest": file_digest(CLAIMS_PATH),
                },
                "problem_index": {
                    "path": "docs/problems.json",
                    "content_digest": file_digest(PROBLEMS_PATH),
                },
                "declaration_atlas": {
                    "path": "docs/declaration_atlas.json",
                    "content_digest": file_digest(ATLAS_PATH),
                    "source_input_fingerprint": atlas["source_fingerprint"],
                },
                "methodology_contract": {
                    "path": "docs/methodology.json",
                    "content_digest": file_digest(METHODOLOGY_PATH),
                },
                "bounded_orientation": {
                    "path": "docs/orientation.json",
                    "content_digest": canonical_digest(orientation),
                },
                "human_exposition": {
                    "source_path": "paper/erdos249-257-main-paper.tex",
                    "source_content_digest": file_digest(MAIN_PAPER_TEX),
                    "rendered_path": "erdos249-257-main-paper.pdf",
                    "rendered_content_digest": file_digest(MAIN_PAPER_PDF),
                    "artifact_role": "authored_mathematician_facing_exposition",
                    "authority_posture": "authored_editorial_surface_not_Lean_proof_authority",
                },
                "paper_source_sigils": {
                    "path": "paper/module-aliases.json",
                    "content_digest": file_digest(PAPER_ALIASES_PATH),
                    "schema": paper_aliases["schema"],
                    "artifact_role": paper_aliases["artifact_role"],
                    "authority_posture": paper_aliases["authority_posture"],
                },
            },
        },
        "schemas": {
            "claims": claims["schema"],
            "problems": problems["schema"],
            "machine_readable_paper": machine_paper["schema"],
            "declaration_atlas": atlas["schema"],
            "methodology": methodology["schema"],
            "paper_module_aliases": paper_aliases["schema"],
        },
        "capabilities": {
            "global_argument_graph": True,
            "module_import_graph": True,
            "principal_claim_declaration_links": True,
            "high_salience_signatures": True,
            "exhaustive_declaration_lookup": "attached_atlas",
            "bounded_reverse_module_importers": True,
            "resolved_local_claim_argument_neighbourhood": True,
            "direct_remaining_open_proposition_lookup": True,
            "exact_cross_paper_claim_coordinates": True,
            "pinned_declaration_source_urls": True,
            "digest_bound_human_papers": True,
            "paper_sigil_crosswalk": True,
            "typed_human_paper_anchor_resolution": True,
            "unlabelled_formal_anchor_source_coordinate_handles": True,
            "declaration_to_human_paper_anchor_reverse_links": True,
            "direct_Lean_source_coordinate_resolution": True,
            "registered_artifact_and_digest_resolution": True,
            "typed_mathematical_programme_routes": True,
            "typed_claim_status_lookup": True,
            "declaration_level_proof_dependencies": False,
            "typed_remaining_open_propositions": True,
            "claim_transition_requirements": True,
            "claim_first_route_memory_resume": True,
            "human_mathematical_review_is_machine_decidable": False,
        },
        "retrieval_modes": {
            "global": {
                "source": "docs/orientation.json and compact_graph",
                "supports": [
                    "proved_open_boundary",
                    "principal_claim_routes",
                    "mathematical_programme_routes",
                    "release_scale",
                    "root_module_topology",
                ],
            },
            "concept": {
                "source": "scripts/query_corpus.py then attached claims or atlas",
                "supports": ["name", "signature", "docstring", "bounded_module_neighbourhood"],
            },
            "premise_chain": {
                "source": "docs/claims.json::machine_readable_paper.argument_graph and module_graph",
                "boundary": "The public atlas does not claim elaborator-derived declaration dependencies or accessibility annotations.",
            },
        },
        "summary": atlas["summary"],
        "compact_graph": {
            "status_taxonomy": claims["status_taxonomy"],
            "principal_claims": principal_claim_handles,
            "principal_claim_statement_owner": "docs/claims.json::claims",
            "non_claims": claims["non_claims"],
            "remaining_open_propositions": claims["remaining_open_propositions"],
            "mathematical_programmes": [
                {
                    "id": route["id"],
                    "title": route["title"],
                    "core_claim_count": len(route["core_claim_ids"]),
                    "representative_claim_ids": route["core_claim_ids"][:2],
                    "remaining_open_proposition_ids": route[
                        "remaining_open_proposition_ids"
                    ],
                }
                for route in machine_paper["entrypoints"]
                if route.get("route_kind") == "mathematical_programme"
            ],
            "module_topology": {
                "root": machine_paper["module_graph"]["root"],
                "roots": root_paths,
                "node_count": len(machine_paper["module_graph"]["nodes"]),
                "root_import_count": len(root_modules[root_paths[0]]["imports"]),
                "import_counts_by_root": {
                    root_path: len(root_modules[root_path]["imports"])
                    for root_path in root_paths
                },
                "auxiliary_root_count": len(
                    machine_paper["module_graph"].get("auxiliary_roots", [])
                ),
                "auxiliary_root_posture": machine_paper["module_graph"].get(
                    "auxiliary_root_contract", {}
                ).get("posture"),
                "full_graph": "docs/claims.json::machine_readable_paper.module_graph",
            },
            "argument_graph": machine_paper["argument_graph"],
            "methodology_capsule": {
                "path": "docs/methodology.json",
                "human_projection": "METHODOLOGY.md",
                "artifact_role": methodology["artifact_role"],
                "human_capsule": methodology["human_capsule"],
                "method_axiom_ids": [row["id"] for row in methodology["method_axioms"]],
                "transition_contract_ids": [row["id"] for row in methodology["transition_contracts"]],
                "change_classes": methodology["change_classes"],
                "full_contract": "docs/methodology.json",
            },
            "principal_declaration_handles": principal_declaration_handles,
            "mathematical_programme_query": (
                "python3 scripts/query_corpus.py --route <programme_route_id>"
            ),
            "claim_status_query": (
                "python3 scripts/query_corpus.py --status <claim_status>"
            ),
            "route_memory_query": (
                "python3 scripts/query_route_memory.py --problem <problem_number> "
                "[--route <mathematical_programme_id>]"
            ),
            "route_memory_contract": {
                "selector_source": "docs/problems.json::problems.erdos_number",
                "problem_selectors": [
                    row["erdos_number"] for row in problems["problems"]
                ],
                "validate": "python3 scripts/query_route_memory.py --validate <packet.json>",
                "authority_posture": (
                    "derived_navigation_resume_state_not_claim_or_proof_authority"
                ),
                "rejections": [
                    "stale_source_snapshot",
                    "cross_problem_route_or_declaration",
                    "invented_reference",
                    "resume_state_mismatch",
                ],
            },
        },
        "expansion": {
            "machine_readable_paper": {
                "path": "docs/claims.json::machine_readable_paper",
                "expected_content_digest": canonical_digest(machine_paper),
                "contains": [
                    "all_claims",
                    "authored_argument_graph",
                    "mathematical_programme_routes",
                    "complete_module_import_graph",
                ],
                "query": "python3 scripts/query_corpus.py --claim <claim_id>",
            },
            "problem_index": {
                "path": "docs/problems.json",
                "expected_content_digest": file_digest(PROBLEMS_PATH),
                "query": "python3 scripts/query_route_memory.py --problem <problem_number>",
                "authority_posture": (
                    "canonical_problem_selector_source_not_claim_or_proof_authority"
                ),
            },
            "exhaustive_declaration_atlas": {
                "path": "docs/declaration_atlas.json",
                "expected_content_digest": file_digest(ATLAS_PATH),
                "expected_source_input_fingerprint": atlas["source_fingerprint"],
                "availability": "optional_attached_corpus",
                "check": "python3 scripts/build_declaration_atlas.py --check",
            },
            "methodology_contract": {
                "path": "docs/methodology.json",
                "expected_content_digest": file_digest(METHODOLOGY_PATH),
                "human_projection": "METHODOLOGY.md",
                "check": "python3 scripts/build_methodology.py --check",
            },
            "human_exposition": {
                "source_path": "paper/erdos249-257-main-paper.tex",
                "expected_source_content_digest": file_digest(MAIN_PAPER_TEX),
                "rendered_path": "erdos249-257-main-paper.pdf",
                "expected_rendered_content_digest": file_digest(MAIN_PAPER_PDF),
                "authority_posture": "authored_editorial_surface_not_Lean_proof_authority",
            },
            "paper_source_sigils": {
                "path": "paper/module-aliases.json",
                "expected_content_digest": file_digest(PAPER_ALIASES_PATH),
                "schema": paper_aliases["schema"],
                "check": "python3 scripts/build_paper_module_aliases.py --check",
            },
        },
        "migration_from_v2": {
            "reason": "Version 2 embedded exhaustive graphs and full declaration prose in a surface described as compact.",
            "field_replacements": {
                "compact_graph.claims": "compact_graph.principal_claims; expand through docs/claims.json or query_corpus.py",
                "compact_graph.module_graph": "compact_graph.module_topology; expand through docs/claims.json::machine_readable_paper.module_graph",
                "compact_graph.high_salience_declarations": "compact_graph.principal_declaration_handles; expand through docs/declaration_atlas.json or query_corpus.py",
                "compact_graph.methodology_capsule extended fields": "docs/methodology.json",
            },
        },
        "migration_from_v4": {
            "reason": (
                "The former identity.navigation_snapshot.commit was a preserved "
                "historical label that could lag the generated content and be "
                "mistaken for its current Git identity."
            ),
            "field_replacements": {
                "identity.navigation_snapshot": (
                    "identity.navigation_projection plus identity.content digests"
                ),
                "orientation.source_revision": "orientation.source_provenance",
            },
        },
        "checks": {
            "descriptor": "python3 scripts/build_corpus_descriptor.py --check",
            "methodology": "python3 scripts/build_methodology.py --check",
            "methodology_mutations": "python3 scripts/test_methodology_contract.py",
            "release": "python3 scripts/check_release.py",
        },
    }


def render() -> str:
    return json.dumps(build(), ensure_ascii=False, separators=(",", ":")) + "\n"


def write_if_changed(path: Path, content: str) -> bool:
    """Write one generated projection only when its bytes changed."""
    if path.is_file() and path.read_text(encoding="utf-8") == content:
        return False
    path.write_text(content, encoding="utf-8")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the descriptor is stale")
    parser.add_argument(
        "--orientation-only",
        action="store_true",
        help="check or write only docs/ORIENTATION.md without touching sibling projections",
    )
    args = parser.parse_args()
    claims = json.loads(CLAIMS_PATH.read_text(encoding="utf-8"))
    atlas = json.loads(ATLAS_PATH.read_text(encoding="utf-8"))
    orientation = build_orientation(claims, atlas)
    expected = render()
    # This is a machine first-read packet with a strict byte ceiling. Compact
    # JSON preserves the complete object while keeping formatting whitespace
    # from crowding out newly registered routes or papers.
    expected_orientation_json = (
        json.dumps(orientation, ensure_ascii=False, separators=(",", ":")) + "\n"
    )
    expected_orientation_markdown = render_orientation_markdown(orientation)
    actual_readme = ""
    expected_readme = ""
    actual_wave_index = ""
    expected_wave_index = ""
    if not args.orientation_only:
        actual_readme = README_PATH.read_text(encoding="utf-8")
        expected_readme = replace_readme_scale_strip(
            actual_readme, render_readme_scale_strip(orientation, claims, atlas)
        )
        expected_readme = replace_readme_principal_declaration_anchors(
            expected_readme, render_readme_principal_declaration_anchors(orientation)
        )
        actual_wave_index = WAVE_INDEX_PATH.read_text(encoding="utf-8")
        expected_wave_index = replace_generated_region(
            actual_wave_index,
            WAVE_SHAPE_BEGIN,
            WAVE_SHAPE_END,
            render_wave_package_shape(atlas),
        )
    descriptor_bytes = len(expected.encode("utf-8"))
    orientation_bytes = len(expected_orientation_json.encode("utf-8"))
    orientation_markdown_bytes = len(expected_orientation_markdown.encode("utf-8"))
    if descriptor_bytes > DESCRIPTOR_MAX_BYTES:
        print(
            "corpus descriptor exceeds the registration-envelope budget: "
            f"{descriptor_bytes:,} > {DESCRIPTOR_MAX_BYTES:,} bytes"
        )
        return 1
    if orientation_bytes > ORIENTATION_MAX_BYTES:
        print(
            "orientation exceeds the bounded first-read budget: "
            f"{orientation_bytes:,} > {ORIENTATION_MAX_BYTES:,} bytes"
        )
        return 1
    if orientation_markdown_bytes > ORIENTATION_MARKDOWN_MAX_BYTES:
        print(
            "orientation Markdown exceeds the bounded first-read budget: "
            f"{orientation_markdown_bytes:,} > {ORIENTATION_MARKDOWN_MAX_BYTES:,} bytes"
        )
        return 1
    if args.check:
        actual = OUTPUT.read_text(encoding="utf-8") if OUTPUT.is_file() else ""
        actual_orientation_json = (
            ORIENTATION_JSON.read_text(encoding="utf-8") if ORIENTATION_JSON.is_file() else ""
        )
        actual_orientation_markdown = (
            ORIENTATION_MARKDOWN.read_text(encoding="utf-8")
            if ORIENTATION_MARKDOWN.is_file()
            else ""
        )
        if args.orientation_only:
            stale = actual_orientation_markdown != expected_orientation_markdown
        else:
            stale = (
                actual != expected
                or actual_orientation_json != expected_orientation_json
                or actual_orientation_markdown != expected_orientation_markdown
                or actual_readme != expected_readme
                or actual_wave_index != expected_wave_index
            )
        if stale:
            print(
                "corpus descriptor, orientation, README scale, or wave package-shape projection is stale; "
                "run python3 scripts/build_corpus_descriptor.py"
            )
            return 1
        if args.orientation_only:
            print(
                "orientation Markdown current: "
                f"bytes={orientation_markdown_bytes:,}/{ORIENTATION_MARKDOWN_MAX_BYTES:,}"
            )
        else:
            descriptor = json.loads(actual)
            print(
                "corpus descriptor and orientation current: "
                f"formal={descriptor['identity']['formal_source']['resolved_commit'][:8]} "
                "navigation=content-addressed "
                f"bytes={descriptor_bytes:,}/{DESCRIPTOR_MAX_BYTES:,}"
            )
        return 0
    outputs = [(ORIENTATION_MARKDOWN, expected_orientation_markdown)]
    if not args.orientation_only:
        outputs = [
            (OUTPUT, expected),
            (ORIENTATION_JSON, expected_orientation_json),
            *outputs,
            (README_PATH, expected_readme),
            (WAVE_INDEX_PATH, expected_wave_index),
        ]
    changed = [
        path.relative_to(ROOT).as_posix()
        for path, content in outputs
        if write_if_changed(path, content)
    ]
    print(
        "wrote "
        + (", ".join(changed) if changed else "no changed projections")
        + f"; descriptor bytes={descriptor_bytes:,}/{DESCRIPTOR_MAX_BYTES:,}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
