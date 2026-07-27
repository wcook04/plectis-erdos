#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Generated projections must not depend on the shape of the checkout.

``check_release.py`` enforces freshness by regenerating each projection and
comparing it against the committed bytes. That comparison is only meaningful if
a projection is a pure function of the committed tree. A builder that consults
the refs a checkout happens to carry breaks the assumption: continuous
integration checks ``main`` out as a local branch and a pull request out as a
topic branch, so the same commit renders differently in the two jobs and one of
them fails with no file having changed.

That is not hypothetical. ``build_corpus_descriptor.py`` once recorded
``navigation_snapshot.publication_state``, derived from whether the navigation
commit was an ancestor of a local ``main`` ref. Branch builds rendered
``detached_navigation_snapshot`` and ``main`` builds rendered
``main_history_snapshot``, so release-surfaces was red on ``main`` for days and
no regeneration could fix it: refreshing on a branch broke ``main`` and
refreshing on ``main`` broke every pull request.

This test pins the invariant behaviourally rather than by inspecting source. It
copies the public tree into two version-control-free workspaces that differ only
in an inert checkout-shape marker, regenerates every projection in each, and
requires byte-identical output. Running without repository metadata also proves
that no projection builder needs to inspect a branch, index, or commit merely to
render current content.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Builders that check_release.py regenerates and compares against committed bytes.
BUILDERS = (
    "build_corpus_descriptor.py",
    "build_declaration_atlas.py",
    "build_module_graph.py",
    "build_paper_module_aliases.py",
    "build_methodology.py",
)

# Files those builders own. Compared byte-for-byte between the two checkouts.
PROJECTIONS = (
    "docs/corpus_descriptor.json",
    "docs/orientation.json",
    "docs/ORIENTATION.md",
    "docs/declaration_atlas.json",
    "docs/methodology.json",
    "docs/WAVE_INDEX.md",
    "README.md",
    "paper/module-aliases.json",
    "paper/module-aliases.tex",
)


def run(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, capture_output=True, text=True, check=False)


def materialise(destination: Path, shape: str) -> None:
    """Copy the public tree without version-control or build metadata."""
    ignored = shutil.ignore_patterns(
        ".git",
        ".lake",
        ".build",
        "__pycache__",
        "*.olean",
        "*.ilean",
    )
    shutil.copytree(ROOT, destination, ignore=ignored)
    marker = destination / ".checkout-shape"
    marker.mkdir()
    (marker / shape).write_text(
        "inert test marker; projection builders must ignore checkout shape\n",
        encoding="utf-8",
    )


def regenerate(checkout: Path) -> dict[str, bytes]:
    for builder in BUILDERS:
        script = checkout / "scripts" / builder
        if not script.is_file():
            continue
        result = run([sys.executable, str(script)], cwd=checkout)
        if result.returncode != 0:
            raise SystemExit(
                f"{builder} failed inside the shape probe at {checkout.name}: "
                f"{result.stderr.strip() or result.stdout.strip()}"
            )
    rendered: dict[str, bytes] = {}
    for relative in PROJECTIONS:
        path = checkout / relative
        if path.is_file():
            rendered[relative] = path.read_bytes()
    return rendered


def main() -> int:
    workspace = Path(tempfile.mkdtemp(prefix="projection-shape-"))
    try:
        as_main = workspace / "as-main"
        as_topic = workspace / "as-topic"
        materialise(as_main, shape="main")
        materialise(as_topic, shape="topic")

        rendered_main = regenerate(as_main)
        rendered_topic = regenerate(as_topic)

        divergent = sorted(
            relative
            for relative in set(rendered_main) | set(rendered_topic)
            if rendered_main.get(relative) != rendered_topic.get(relative)
        )
        if divergent:
            print(
                "generated projections depend on the shape of the checkout, so the same "
                "commit renders differently on main and on a pull request branch:"
            )
            for relative in divergent:
                print(f"  {relative}")
            print(
                "make the builder a pure function of the committed tree; do not consult "
                "which refs the checkout carries, and do not record ancestry relative to main"
            )
            return 1
    finally:
        shutil.rmtree(workspace, ignore_errors=True)

    print(
        f"test_projection_checkout_independence: {len(PROJECTIONS)} projections render "
        "identically in two version-control-free checkout shapes"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
