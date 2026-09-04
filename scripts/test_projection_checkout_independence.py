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

That is not hypothetical. ``build_corpus_descriptor.py`` once recorded a
snapshot publication state derived from whether a preserved navigation commit
was an ancestor of a local ``main`` ref. Branch builds and ``main`` builds then
rendered different labels, so release-surfaces was red on ``main`` for days and
no regeneration could fix it: refreshing on a branch broke ``main`` and
refreshing on ``main`` broke every pull request.

The descriptor now uses content digests for current navigation identity. It
does not preserve an old Git commit under a current-sounding snapshot field:
a generated file cannot contain the commit that first contains its own bytes.

This test pins the invariant behaviourally rather than by inspecting source. It
copies the public tree into two version-control-free workspaces that differ only
in an inert checkout-shape marker, regenerates every projection in each, and
requires byte-identical output. Running without repository metadata also proves
that no projection builder needs to inspect a branch, index, or commit merely to
render current content.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import patch

import validation_singleflight as singleflight
import refresh_source_coordinates

ROOT = Path(__file__).resolve().parent.parent

# Builders that refresh_projections.py runs, in the same dependency order.
BUILDERS = (
    "build_methodology.py",
    "build_module_graph.py",
    "build_declaration_atlas.py",
    "refresh_source_coordinates.py",
    "build_semantic_corpus.py",
    "build_theory_lab.py",
    "build_corpus_descriptor.py",
    "build_paper_module_aliases.py",
    "build_publication_entry_packet.py",
)

# Files those builders own. Compared byte-for-byte between the two checkouts.
PROJECTIONS = (
    "docs/corpus_descriptor.json",
    "docs/orientation.json",
    "docs/ORIENTATION.md",
    "docs/declaration_atlas.json",
    "docs/methodology.json",
    "docs/claims.json",
    "docs/semantic_corpus.json",
    "docs/semantic_corpus_check.json",
    "docs/theory_lab.json",
    "docs/publication_entry_packet.json",
    "docs/WAVE_INDEX.md",
    "README.md",
    "paper/erdos249-257-main-paper.tex",
    "paper/module-aliases.json",
    "paper/module-aliases.tex",
)

# Exercise the same hostile ambient state that a checkout launched from another
# Git worktree or developer Python environment can inherit.  The child builder
# processes must receive the canonical clean-snapshot environment instead.
HOSTILE_ENVIRONMENT = {
    "GIT_DIR": "/tmp/not-this-checkout/.git",
    "GIT_NAMESPACE": "refs/namespaces/not-this-release",
    "GIT_REPLACE_REF_BASE": "refs/replace/",
    "PYTHONPATH": "/tmp/not-this-python-path",
    "LC_ALL": "C",
    "LANG": "C",
}
IMMUTABLE_BULK_SUFFIXES = {".lean", ".pdf"}


def run(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=cwd,
        env=singleflight.command_environment(),
        capture_output=True,
        text=True,
        check=False,
        timeout=singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
    )


def check_run_contract() -> None:
    """Keep the version-control-free builder probe bounded and isolated."""
    completed = subprocess.CompletedProcess(["fixture"], 0, "", "")
    with patch.object(subprocess, "run", return_value=completed) as runner:
        observed = run(["fixture"], ROOT)

    if observed is not completed:
        raise SystemExit("projection run helper did not return the child result")
    kwargs = runner.call_args.kwargs
    if kwargs.get("timeout") != singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS:
        raise SystemExit("projection run helper must use the shared worker timeout")
    if kwargs.get("env") != singleflight.command_environment():
        raise SystemExit("projection run helper must use the canonical clean environment")


def check_source_coordinate_title_contract() -> None:
    """TeX and Unicode title spellings must resolve the same paper anchor."""
    anchors = (
        (
            "paper/erdos-68-factorial-denominator-irrationality.tex",
            "problem",
            "Erdős #68",
        ),
        (
            "paper/erdos-243-reciprocal-tail-rigidity.tex",
            "problem",
            "Erdős #243",
        ),
        (
            "paper/erdos-1041-lemniscate-newton-flow.tex",
            "problem",
            "Erdős #1041",
        ),
        ("paper/erdos249-257-main-paper.tex", "problem", r"Erd\H{o}s \#249"),
        ("paper/erdos-251-prime-gap-dyadic-series.tex", "section", "Introduction"),
        ("paper/erdos-269-three-prime-running-lcm.tex", "section", "Introduction"),
        ("paper/erdos-1049-rational-base-lambert.tex", "section", "Introduction"),
    )
    for source, environment, title in anchors:
        line = refresh_source_coordinates.paper_anchor_line(
            {"source": source, "environment": environment, "title": title}
        )
        if line < 1:
            raise SystemExit(f"paper anchor resolved to an invalid line: {source}")


def materialise(destination: Path, shape: str) -> None:
    """Materialise tracked ``HEAD`` without version-control or build metadata."""
    destination.mkdir()
    with tempfile.NamedTemporaryFile(
        dir=destination.parent, prefix=".projection-head-", suffix=".tar"
    ) as archive_file:
        archived = subprocess.run(
            ["git", "archive", "--format=tar", "HEAD"],
            cwd=ROOT,
            env=singleflight.command_environment(),
            stdout=archive_file,
            stderr=subprocess.PIPE,
            check=False,
            timeout=singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS,
        )
        if archived.returncode != 0:
            raise SystemExit(
                "could not materialise tracked HEAD: "
                + archived.stderr.decode("utf-8", errors="replace").strip()
            )
        archive_file.flush()
        archive_file.seek(0)
        with tarfile.open(fileobj=archive_file, mode="r:") as archive:
            archive.extractall(destination, filter="data")
    marker = destination / ".checkout-shape"
    marker.mkdir()
    (marker / shape).write_text(
        "inert test marker; projection builders must ignore checkout shape\n",
        encoding="utf-8",
    )


def clone_materialised_checkout(source: Path, destination: Path, shape: str) -> None:
    """Clone a metadata-free checkout without copying immutable bulk twice."""

    def copy_file(source_file: str, destination_file: str) -> str:
        source_path = Path(source_file)
        if source_path.suffix in IMMUTABLE_BULK_SUFFIXES:
            os.link(source_file, destination_file)
            return destination_file
        return shutil.copy2(source_file, destination_file)

    shutil.copytree(
        source,
        destination,
        copy_function=copy_file,
        ignore=shutil.ignore_patterns(".checkout-shape"),
    )
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
    check_run_contract()
    check_source_coordinate_title_contract()
    workspace = Path(tempfile.mkdtemp(prefix="projection-shape-"))
    try:
        as_main = workspace / "as-main"
        as_topic = workspace / "as-topic"
        materialise(as_main, shape="main")
        clone_materialised_checkout(as_main, as_topic, shape="topic")

        with patch.dict(os.environ, HOSTILE_ENVIRONMENT):
            # The two checkout shapes are deliberately independent.  Running
            # their ordered builder chains concurrently preserves every
            # dependency within a checkout while avoiding a second full wall-
            # clock pass over the 150 MB generated-certificate source corpus.
            with ThreadPoolExecutor(max_workers=2) as executor:
                main_future = executor.submit(regenerate, as_main)
                topic_future = executor.submit(regenerate, as_topic)
                rendered_main = main_future.result()
                rendered_topic = topic_future.result()

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
