#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Regenerate every committed projection in dependency order, then verify.

``check_release.py`` regenerates six projections with ``--check`` and fails if
any committed copy is stale. Refreshing them by hand means remembering six
commands in the right order, and forgetting one is not hypothetical: on
2026-07-19 a run of paper edits refreshed the corpus descriptor and the
publication entry packet but never re-ran ``refresh_source_coordinates.py``, so
the paper anchors in ``docs/claims.json`` stayed pinned to pre-edit line numbers
for ten commits and release-surfaces was red the whole way.

Run this after editing claims, the atlas, the methodology, or the paper, and
commit whatever it rewrites together with the edit that caused it. Descriptor
schema 5 identifies generated navigation by content digests, so the refresh is
checkout-shape independent; the formal-source commit remains a separate proof
anchor.
"""

from __future__ import annotations

import os
import subprocess
import sys
from collections.abc import Mapping
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENVIRONMENT_CONTRACT = "clean_committed_snapshot_subprocess_environment_v1"
SANITIZED_GIT_ENVIRONMENT_KEYS = (
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_INDEX_FILE",
    "GIT_NAMESPACE",
    "GIT_REPLACE_REF_BASE",
    "GIT_OBJECT_DIRECTORY",
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_COMMON_DIR",
)


def clean_environment(base: Mapping[str, str] | None = None) -> dict[str, str]:
    """Remove inherited Git selectors before any projection subprocess."""
    environment = dict(os.environ if base is None else base)
    for key in SANITIZED_GIT_ENVIRONMENT_KEYS:
        environment.pop(key, None)
    return environment


def run(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    """Run a projection command with checkout-independent Git state."""
    return subprocess.run(
        args,
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
        env=clean_environment(),
    )

# Dependency order, mirroring the sequence check_release.py verifies: the atlas
# and module graph read the Lean sources, the source coordinates read the atlas
# and the paper, and the corpus descriptor reads all of them. The entry packet
# reads the finished contract and claims, so it runs last: on 2026-07-21 it was
# the one projection this list omitted, and it stayed stale through the paper
# provenance edit while every builder listed above refreshed cleanly.
BUILDERS = (
    "build_methodology.py",
    "build_module_graph.py",
    "build_declaration_atlas.py",
    # Source-coordinate refresh rewrites docs/claims.json, which is an input
    # to the semantic corpus. It must therefore precede both semantic layers;
    # placing it afterwards makes one full refresh invalidate its own output.
    "refresh_source_coordinates.py",
    "build_semantic_corpus.py",
    "build_theory_lab.py",
    "build_corpus_descriptor.py",
    "build_paper_module_aliases.py",
    "build_publication_entry_packet.py",
)


def tracked_diff() -> set[str]:
    result = run(["git", "diff", "--name-only"], cwd=ROOT)
    return {line for line in result.stdout.split("\n") if line}


def main() -> int:
    before = tracked_diff()

    for builder in BUILDERS:
        script = ROOT / "scripts" / builder
        if not script.is_file():
            print(f"missing builder: scripts/{builder}")
            return 1
        result = run([sys.executable, str(script)], cwd=ROOT)
        if result.returncode != 0:
            print(f"scripts/{builder} failed:")
            print(result.stderr.strip() or result.stdout.strip())
            return 1

    stale = []
    for builder in BUILDERS:
        result = run([sys.executable, str(ROOT / "scripts" / builder), "--check"], cwd=ROOT)
        if result.returncode != 0:
            stale.append((builder, result.stdout.strip() or result.stderr.strip()))

    if stale:
        print("projections did not converge after a full refresh:")
        for builder, message in stale:
            print(f"  scripts/{builder}: {message}")
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


if __name__ == "__main__":
    sys.exit(main())
