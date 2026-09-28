#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regenerate every committed projection in dependency order, then verify.

``check_release.py`` re-runs each committed projection's builder with
``--check`` and fails the release if any committed copy is stale. Refreshing
them by hand means remembering every command in the right order, and forgetting
one is not hypothetical: on 2026-07-19 a run of paper edits refreshed the corpus
descriptor and the publication entry packet but never re-ran
``refresh_source_coordinates.py``, so the paper anchors in ``docs/claims.json``
stayed pinned to pre-edit line numbers for ten commits and release-surfaces was
red the whole way.

That kept happening, so the list is no longer trusted to prose.
``test_refresh_projections_coverage.py`` reads ``check_release.py`` and fails
when the release gate checks a projection this pipeline never rebuilds. It
found five such projections on the day it was written.

Run this after editing claims, the atlas, the methodology, or the paper, and
commit whatever it rewrites together with the edit that caused it. Descriptor
schema 5 identifies generated navigation by content digests, so the refresh is
checkout-shape independent; the formal-source commit remains a separate proof
anchor.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import validation_singleflight as singleflight

ROOT = Path(__file__).resolve().parent.parent
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
SUBPROCESS_TIMEOUT_SECONDS = singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS
CHECK_WORKERS = 4
SANITIZED_GIT_ENVIRONMENT_KEYS = tuple(
    sorted(singleflight.GIT_CONTEXT_KEYS | singleflight.GIT_PROCESS_CONTROL_KEYS)
)
SANITIZED_RUNTIME_ENVIRONMENT_KEYS = tuple(
    sorted(singleflight.PYTHON_CONTEXT_KEYS | singleflight.LOCALE_KEYS)
)


def clean_environment() -> dict[str, str]:
    """Use the canonical isolated environment for every projection child."""
    return singleflight.command_environment()


def run(
    args: list[str], cwd: Path
) -> subprocess.CompletedProcess[str]:
    """Run a bounded projection command with checkout-independent state."""
    return subprocess.run(
        args,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
        timeout=SUBPROCESS_TIMEOUT_SECONDS,
        env=clean_environment(),
    )

# Dependency order, mirroring the sequence check_release.py verifies: the atlas
# and module graph read the Lean sources, the source coordinates read the atlas
# and the paper, and the corpus descriptor reads all of them. The entry packet
# reads the finished contract and claims, so it runs last: on 2026-07-21 it was
# the one projection this list omitted, and it stayed stale through the paper
# provenance edit while every builder listed above refreshed cleanly.
BUILDERS = (
    # Registry and skill frontmatter own the clone-local catalog projection.
    # Keeping this first makes entry drift visible before expensive projections.
    "scripts/agent_skill_catalog.py",
    "scripts/build_methodology.py",
    "scripts/build_module_graph.py",
    "scripts/build_declaration_atlas.py",
    # This compressed speed path is bound to the atlas fingerprint and must
    # refresh before any downstream projection consumes declaration search.
    "scripts/build_declaration_search_index.py",
    # The authored zones under docs/semantic/zones/ pin Lean line numbers by
    # hand, and until 2026-08-31 no refresher owned them at all: 3722 of the
    # 149090 pinned rows across 39 of the 94 zones had rotted onto the wrong
    # line, which is how test_cyclotomic_semantic_digest.py came to fail. This
    # reads the atlas and is read by the rosters and the corpus, so it sits
    # between them.
    "scripts/refresh_zone_source_coordinates.py",
    # Reads the Lean module headers and the atlas fingerprint. It had a
    # freshness check and no refresher, so it rotted until query_corpus
    # started rejecting it outright.
    "scripts/build_module_synopsis_index.py",
    # The rosters read the Lean data files and the authored zones, and the
    # semantic corpus reads the zones back. They belong above it.
    "scripts/build_off_diagonal_certificate_roster.py",
    "scripts/build_checked_diagonal_depth_roster.py",
    # Source-coordinate refresh rewrites docs/claims.json, which is an input
    # to the semantic corpus. It must therefore precede both semantic layers;
    # placing it afterwards makes one full refresh invalidate its own output.
    "scripts/refresh_source_coordinates.py",
    "scripts/refresh_reasoning_source_coordinates.py",
    # Normalize the paper corpus before the problem index reads its paper
    # routes and fingerprints it in docs/problem_library.json.
    "docs/papers/build_publication_taxonomy.py",
    # The no-clone reading edition is assembled from the normalized paper
    # corpus, the generated paper text and the shared research instruction in
    # skills/explore-the-corpus/SKILL.md. Listing it here makes the release
    # gate reject an edition that has drifted from the papers it carries.
    "scripts/build_reading_edition.py",
    # Reads the refreshed claims and writes docs/problems.json, which the
    # corpus descriptor and external verification builder read.
    "scripts/build_problem_index.py",
    "scripts/build_semantic_corpus.py",
    "scripts/build_theory_lab.py",
    "scripts/build_external_verification.py",
    # Authored source mappings consume the complete paper inventory and emit
    # exhaustive bibliography/citation and Lean-comment coverage views.
    "scripts/reanchor_source_attributions.py",
    "scripts/build_source_attributions.py",
    # The corpus descriptor reads paper/module-aliases.json, so the alias
    # builder has to come first. It did not until 2026-08-31, and the symptom
    # was a full refresh that reported its own descriptor stale and blamed an
    # impure builder: the descriptor was pure, it was just reading the aliases
    # from before the run.
    "scripts/build_paper_module_aliases.py",
    "scripts/build_corpus_descriptor.py",
    "scripts/build_publication_entry_packet.py",
    # Reads the final source/projection inventory; its own output is excluded
    # from that read set, so it runs last and cannot fingerprint itself.
    "scripts/corpus_substrate.py",
)

# Builders whose bare invocation is a dry run. The two rosters print their
# rendering to stdout unless told to write, and the reasoning-coordinate
# refresher behaves as a check. Until 2026-09-04 refresh() invoked every
# builder bare, so a full refresh "regenerated" the diagonal depth roster into
# a discarded pipe and then reported the tree as impure when its own --check
# still failed. test_refresh_projections_coverage.py now reads each builder's
# argument parser and fails when a builder that declares --write is missing
# from this table.
WRITE_FLAGS: dict[str, tuple[str, ...]] = {
    "scripts/corpus_substrate.py": ("--write",),
    "scripts/reanchor_source_attributions.py": ("--write", "--preserve-excerpts", "--base", "HEAD"),
    "scripts/build_off_diagonal_certificate_roster.py": ("--write",),
    "scripts/build_checked_diagonal_depth_roster.py": ("--write",),
    "scripts/refresh_reasoning_source_coordinates.py": ("--write",),
}

# These checks inspect shipped evidence only: no Lean, installs, regeneration,
# or local-receipt fallback. CI and cold release preparation share this owner.
# Budget reserved for cold admission by the workflow, excluding runner setup.
PREFLIGHT_BUDGET_SECONDS = 1200

PREFLIGHT_CHECKS: dict[str, tuple[str, ...]] = {
    **{builder: ("--check",) for builder in BUILDERS},
    "scripts/check_release.py": ("--source-identity-only", "--route-budgets-only", "--trust-only"),
    "scripts/check_publication_contract.py": (),
    "scripts/build_declaration_atlas.py": ("--check",),
    "scripts/build_declaration_search_index.py": ("--check",),
    "scripts/build_lean_dependency_index.py": ("--check", "--tracked-only"),
    "scripts/build_semantic_corpus.py": ("--check", "--tracked-only"),
    # First-contact checks also bind documented workflow behavior. Keep this
    # dependency-free CI lane inside the outgoing-commit gate, not just CI.
    "scripts/check_cold_clone_comprehension.py": ("--quick",),
    # The build/cache/exporter regression tests are cold Python checks too.
    # They must fail on the outgoing snapshot before GitHub allocates Lean.
    "scripts/check_ci_contracts.py": (),
}

# Omitted from mutation, never omitted from verification. A full Lean export
# is an explicit operation after source/projection changes have settled.
CHECK_ONLY_BUILDERS: dict[str, str] = {
    "scripts/check_release.py": "bind release.formal_source to the reviewed committed Lean tree",
    "scripts/check_publication_contract.py": "follow the named manuscript/PDF repair before restamping",
    "scripts/build_lean_dependency_index.py": (
        "run python3 scripts/build_lean_dependency_index.py --check --full-check "
        "--write-stale; commit the index and its tracked receipt, then recheck"
    ),
}


def check_command(builder: str) -> list[str]:
    return [sys.executable, str(ROOT / builder), *PREFLIGHT_CHECKS.get(builder, ("--check",))]


def failure_annotation(builder: str, detail: str) -> str:
    """Put the actual failed owner in Actions annotations, not just exit 1."""
    def escape(value: str) -> str:
        return value.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    command = "python3 " + " ".join([builder, *PREFLIGHT_CHECKS.get(builder, ())])
    return f"::error file={builder},title=Publication preflight failed::{escape(command + ': ' + detail[-2000:])}"


def preflight() -> int:
    """Reject stale shipped evidence before acquiring expensive resources."""
    def inspect(builder: str) -> tuple[str, str | None]:
        try:
            result = run(check_command(builder), cwd=ROOT)
            if result.returncode:
                return builder, result.stderr.strip() or result.stdout.strip() or f"exit {result.returncode}"
        except (OSError, subprocess.TimeoutExpired) as exc:
            return builder, str(exc)
        return builder, None

    # Read-only checks share one snapshot and retain registry order in reports.
    # Derive coverage from BUILDERS so new projections cannot escape preflight.
    with ThreadPoolExecutor(max_workers=CHECK_WORKERS) as executor:
        failures = [(builder, detail) for builder, detail in executor.map(inspect, PREFLIGHT_CHECKS)
                    if detail is not None]
    if failures:
        print("projection preflight failed; no build or preparation was started:")
        for builder, detail in failures:
            print(f"  {builder}: {detail}")
            if os.environ.get("GITHUB_ACTIONS") == "true":
                print(failure_annotation(builder, detail))
        if any(builder in BUILDERS for builder, _detail in failures):
            print("run python3 scripts/refresh_projections.py for Python-owned projections")
        if any(builder == "scripts/check_ci_contracts.py" for builder, _detail in failures):
            print("run python3 scripts/check_ci_contracts.py and repair every reported contract failure")
        for builder, _detail in failures:
            if builder in CHECK_ONLY_BUILDERS:
                print(f"  {builder}: {CHECK_ONLY_BUILDERS[builder]}")
        return 1
    print(f"projection preflight: all {len(PREFLIGHT_CHECKS)} projection and evidence checks passed")
    return 0


def tracked_diff() -> set[str]:
    result = run(["git", "diff", "--name-only"], cwd=ROOT)
    return {line for line in result.stdout.split("\n") if line}


def parse_args(argv: list[str] | None) -> argparse.Namespace:
    dependency_order = "\n".join(
        f"  {index}. {builder}" for index, builder in enumerate(BUILDERS, start=1)
    )
    parser = argparse.ArgumentParser(
        prog="refresh_projections.py",
        description=__doc__,
        epilog=f"Builders, in the dependency order this script runs them:\n{dependency_order}",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--check",
        action="store_true",
        help=(
            "report which committed projections are stale by running every "
            "builder's own --check, without regenerating or writing anything"
        ),
    )
    mode.add_argument(
        "--preflight", action="store_true",
        help="check portable source evidence without builds, regeneration or package installation",
    )
    return parser.parse_args(argv)


def check_only() -> int:
    """Run every builder's --check and report staleness without mutating the tree."""
    builders = (*BUILDERS, *CHECK_ONLY_BUILDERS)
    for builder in builders:
        script = ROOT / builder
        if not script.is_file():
            print(f"missing builder: {builder}")
            return 1

    def check_builder(builder: str) -> tuple[str, subprocess.CompletedProcess[str]]:
        return builder, run(check_command(builder), cwd=ROOT)

    # Check mode is read-only and every builder reads the same committed
    # generation. Preserve dependency order for mutation in refresh(), but do
    # not serialize independent freshness comparisons.
    with ThreadPoolExecutor(max_workers=min(CHECK_WORKERS, len(BUILDERS))) as executor:
        results = list(executor.map(check_builder, builders))
    stale = []
    for builder, result in results:
        if result.returncode != 0:
            stale.append((builder, result.stdout.strip() or result.stderr.strip()))

    if stale:
        print("projections are stale:")
        for builder, message in stale:
            print(f"  {builder}: {message}")
        print("run python3 scripts/refresh_projections.py for Python-owned projections")
        for builder, _message in stale:
            if builder in CHECK_ONLY_BUILDERS:
                print(f"  {builder}: {CHECK_ONLY_BUILDERS[builder]}")
        return 1

    print("refresh_projections --check: every projection is current")
    return 0


def refresh() -> int:
    """Regenerate every projection in dependency order, then verify convergence."""
    before = tracked_diff()

    for builder in BUILDERS:
        script = ROOT / builder
        if not script.is_file():
            print(f"missing builder: {builder}")
            return 1
        result = run(
            [sys.executable, str(script), *WRITE_FLAGS.get(builder, ())],
            cwd=ROOT,
        )
        if result.returncode != 0:
            print(f"{builder} failed:")
            print(result.stderr.strip() or result.stdout.strip())
            return 1

    stale = []
    for builder in BUILDERS:
        result = run(check_command(builder), cwd=ROOT)
        if result.returncode != 0:
            stale.append((builder, result.stdout.strip() or result.stderr.strip()))

    if stale:
        print("projections did not converge after a full refresh:")
        for builder, message in stale:
            print(f"  {builder}: {message}")
        print("this means a builder is not a pure function of the committed tree")
        return 1

    # Builders above can invalidate evidence they do not produce. Never report
    # overall success until those downstream consumers have also accepted it.
    for builder, repair in CHECK_ONLY_BUILDERS.items():
        result = run(check_command(builder), cwd=ROOT)
        if result.returncode:
            print(f"Python projections refreshed; {builder} still requires: {repair}")
            print(result.stderr.strip() or result.stdout.strip())
            return 1

    rewritten = sorted(tracked_diff() - before)
    if rewritten:
        print("refreshed:")
        for path in rewritten:
            print(f"  {path}")
        print(
            "commit these together with the edit that caused them; a content commit "
            "pushed without its refreshed projections is red in continuous integration"
        )
    else:
        print("refresh_projections: every projection was already current")
    return 0


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if args.preflight:
        return preflight()
    if args.check:
        return check_only()
    return refresh()


if __name__ == "__main__":
    sys.exit(main())
