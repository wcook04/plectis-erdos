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
materialises committed ``HEAD`` in a version-control-free workspace, gives it an
inert checkout-shape marker, and requires every builder in this bounded
release-shape probe to accept the committed bytes under a hostile inherited
environment. Running without
repository metadata proves that no projection builder needs to inspect a branch,
index, or commit merely to render current content. Requiring the check commands
to leave every projection byte-identical also keeps this cold-clone test
read-only without paying for two redundant 150 MB regeneration passes.
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

# Builders owning the projections sampled below, in dependency order.
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
    "docs/declaration_atlas_check.json",
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


def materialise(destination: Path) -> None:
    """Materialise tracked ``HEAD`` without version-control or build metadata."""
    destination.mkdir()
    archived = subprocess.Popen(
        ["git", "archive", "--format=tar", "HEAD"],
        cwd=ROOT,
        env=singleflight.command_environment(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if archived.stdout is None:
        archived.kill()
        raise SystemExit("could not materialise tracked HEAD: archive pipe unavailable")
    try:
        # Stream extraction avoids writing and rereading a second full copy of
        # the tracked Lean corpus merely to obtain a metadata-free checkout.
        with tarfile.open(fileobj=archived.stdout, mode="r|") as archive:
            archive.extractall(destination, filter="data")
        _, stderr = archived.communicate(
            timeout=singleflight.DEFAULT_WORKER_TIMEOUT_SECONDS
        )
    except (subprocess.TimeoutExpired, tarfile.TarError) as error:
        archived.kill()
        archived.communicate()
        raise SystemExit(f"could not materialise tracked HEAD: {error}") from error
    if archived.returncode != 0:
        raise SystemExit(
            "could not materialise tracked HEAD: "
            + stderr.decode("utf-8", errors="replace").strip()
        )
    marker = destination / ".checkout-shape"
    marker.mkdir()
    (marker / "metadata-free").write_text(
        "inert test marker; projection builders must ignore checkout shape\n",
        encoding="utf-8",
    )


def projection_bytes(checkout: Path) -> dict[str, bytes]:
    return {
        relative: path.read_bytes()
        for relative in PROJECTIONS
        if (path := checkout / relative).is_file()
    }


def validate_checkout(checkout: Path) -> None:
    before = projection_bytes(checkout)

    def check_builder(builder: str) -> tuple[str, subprocess.CompletedProcess[str]]:
        script = checkout / "scripts" / builder
        if not script.is_file():
            raise SystemExit(f"projection shape probe is missing builder: {builder}")
        return builder, run([sys.executable, str(script), "--check"], cwd=checkout)

    # Check mode is read-only: every builder compares committed inputs with
    # committed outputs. Bound the fan-out so independent JSON/source scans do
    # not become another serial tail in a fresh clone.
    with ThreadPoolExecutor(max_workers=min(4, len(BUILDERS))) as executor:
        results = list(executor.map(check_builder, BUILDERS))
    for builder, result in results:
        if result.returncode != 0:
            raise SystemExit(
                f"{builder} failed inside the shape probe at {checkout.name}: "
                f"{result.stderr.strip() or result.stdout.strip()}"
            )
    after = projection_bytes(checkout)
    mutated = sorted(
        relative
        for relative in set(before) | set(after)
        if before.get(relative) != after.get(relative)
    )
    if mutated:
        raise SystemExit(
            "projection checks mutated committed outputs: " + ", ".join(mutated)
        )


def main() -> int:
    check_run_contract()
    check_source_coordinate_title_contract()
    workspace = Path(tempfile.mkdtemp(prefix="projection-shape-"))
    try:
        checkout = workspace / "metadata-free"
        materialise(checkout)

        with patch.dict(os.environ, HOSTILE_ENVIRONMENT):
            validate_checkout(checkout)
    finally:
        shutil.rmtree(workspace, ignore_errors=True)

    print(
        f"test_projection_checkout_independence: {len(PROJECTIONS)} committed projections "
        "are current and read-only in a version-control-free checkout"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
