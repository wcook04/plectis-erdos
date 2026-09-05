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
    # Reads the refreshed claims and writes docs/problems.json, which the
    # corpus descriptor reads.
    "scripts/build_problem_index.py",
    "scripts/build_semantic_corpus.py",
    "scripts/build_theory_lab.py",
    "scripts/build_external_verification.py",
    "docs/papers/build_publication_taxonomy.py",
    # The corpus descriptor reads paper/module-aliases.json, so the alias
    # builder has to come first. It did not until 2026-08-31, and the symptom
    # was a full refresh that reported its own descriptor stale and blamed an
    # impure builder: the descriptor was pure, it was just reading the aliases
    # from before the run.
    "scripts/build_paper_module_aliases.py",
    "scripts/build_corpus_descriptor.py",
    "scripts/build_publication_entry_packet.py",
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
    "scripts/build_off_diagonal_certificate_roster.py": ("--write",),
    "scripts/build_checked_diagonal_depth_roster.py": ("--write",),
    "scripts/refresh_reasoning_source_coordinates.py": ("--write",),
}


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
    parser.add_argument(
        "--check",
        action="store_true",
        help=(
            "report which committed projections are stale by running every "
            "builder's own --check, without regenerating or writing anything"
        ),
    )
    return parser.parse_args(argv)


def check_only() -> int:
    """Run every builder's --check and report staleness without mutating the tree."""
    for builder in BUILDERS:
        script = ROOT / builder
        if not script.is_file():
            print(f"missing builder: {builder}")
            return 1

    def check_builder(builder: str) -> tuple[str, subprocess.CompletedProcess[str]]:
        script = ROOT / builder
        return builder, run([sys.executable, str(script), "--check"], cwd=ROOT)

    # Check mode is read-only and every builder reads the same committed
    # generation. Preserve dependency order for mutation in refresh(), but do
    # not serialize independent freshness comparisons.
    with ThreadPoolExecutor(max_workers=min(CHECK_WORKERS, len(BUILDERS))) as executor:
        results = list(executor.map(check_builder, BUILDERS))
    stale = []
    for builder, result in results:
        if result.returncode != 0:
            stale.append((builder, result.stdout.strip() or result.stderr.strip()))

    if stale:
        print("projections are stale:")
        for builder, message in stale:
            print(f"  {builder}: {message}")
        print("run python3 scripts/refresh_projections.py to regenerate")
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
        result = run([sys.executable, str(ROOT / builder), "--check"], cwd=ROOT)
        if result.returncode != 0:
            stale.append((builder, result.stdout.strip() or result.stderr.strip()))

    if stale:
        print("projections did not converge after a full refresh:")
        for builder, message in stale:
            print(f"  {builder}: {message}")
        print("this means a builder is not a pure function of the committed tree")
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
    if args.check:
        return check_only()
    return refresh()


if __name__ == "__main__":
    sys.exit(main())
