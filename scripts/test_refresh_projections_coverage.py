#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Contract: the refresh pipeline covers every projection the release gate checks.

``check_release.py`` fails the release when a committed projection is stale.
``refresh_projections.py`` is the command a contributor is told to run to make
them current. If the second list is a subset of the first, the documented
repair does not repair, and the contributor is left staring at a red gate with
no working route to green.

That has happened three times. Twice it was one omitted builder, recorded in
the ``refresh_projections`` docstring. The third time, on 2026-08-31, three
were missing at once: the two certificate rosters and the reasoning-coordinate
refresh. Prose kept losing the race against the list, so this is the guard that
does not.
"""

from __future__ import annotations

import ast
import re
import subprocess
from pathlib import Path
from unittest.mock import patch

import refresh_projections

ROOT = Path(__file__).resolve().parent.parent
CHECK_RELEASE = ROOT / "scripts" / "check_release.py"
BUILDER_NAME = re.compile(r"^(?:build|refresh)_[a-z0-9_]+\.py$")

# Verified by check_release.py but deliberately outside the refresh pipeline,
# each with the reason it does not belong there. Keep this list short and
# argued; it is the only supported way to be in one list and not the other.
DELIBERATELY_UNREFRESHED: dict[str, str] = {
    "build_lean_dependency_index.py": (
        "Requires a coordinated full Lean build and elaborated environment export; "
        "the Python projection refresh must not launch Lean implicitly. Run its "
        "--check --full-check --write-stale after the final projection refresh."
    ),
}


def require(condition: bool, message: str) -> None:
    """Keep coverage failures active when run with ``python -O``."""
    if not condition:
        raise AssertionError(message)


def checked_builders(source: str) -> set[str]:
    """Return every builder ``check_release.py`` invokes with ``--check``."""
    found: set[str] = set()
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if not isinstance(node, (ast.List, ast.Tuple)):
            continue
        literals = {
            item.value
            for item in ast.walk(node)
            if isinstance(item, ast.Constant) and isinstance(item.value, str)
        }
        if "--check" not in literals:
            continue
        found |= {name for name in literals if BUILDER_NAME.match(name)}
    return found


def check_check_only_dispatch() -> None:
    """The freshness scheduler must dispatch every authoritative builder once."""
    calls: list[tuple[str, ...]] = []
    original = refresh_projections.run

    def fake_run(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
        require(cwd == ROOT, "check-only dispatched outside the repository root")
        calls.append(tuple(args))
        return subprocess.CompletedProcess(args, 0, "current", "")

    refresh_projections.run = fake_run
    try:
        require(refresh_projections.check_only() == 0, "mocked check-only run failed")
    finally:
        refresh_projections.run = original
    dispatched = [Path(args[1]).relative_to(ROOT).as_posix() for args in calls]
    require(
        sorted(dispatched) == sorted((*refresh_projections.BUILDERS, *refresh_projections.CHECK_ONLY_BUILDERS)),
        "check-only dispatch dropped or duplicated a projection builder",
    )
    require(
        all("--tracked-only" in args for args in calls if Path(args[1]).name in (
            "build_semantic_corpus.py", "build_lean_dependency_index.py",
        )),
        "portable evidence check can fall back to local receipts",
    )


def check_external_evidence_is_not_silently_omitted() -> None:
    external = "scripts/build_lean_dependency_index.py"
    for operation in (refresh_projections.refresh, refresh_projections.check_only):
        calls = []

        def run(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
            calls.append(args)
            failed = args[1] == str(ROOT / external)
            return subprocess.CompletedProcess(args, int(failed), "", "stale receipt" if failed else "")

        with patch.object(refresh_projections, "run", side_effect=run), \
             patch.object(refresh_projections, "tracked_diff", return_value=set()):
            require(operation() == 1, "projection pipeline reported success with stale external evidence")
        require(all("--check" in args for args in calls if args[1] == str(ROOT / external)),
                "Python refresh launched an implicit Lean export")

    for failed in refresh_projections.PREFLIGHT_CHECKS:
        def run(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
            return subprocess.CompletedProcess(args, int(args[1] == str(ROOT / failed)), "", "fixture stale")
        with patch.object(refresh_projections, "run", side_effect=run):
            require(refresh_projections.preflight() == 1, f"preflight ignored {failed}")


def main() -> int:
    source = CHECK_RELEASE.read_text(encoding="utf-8")
    checked = checked_builders(source)
    require("refresh_projections.preflight()" in source, "release gate bypasses shared evidence preflight")
    checked.update(Path(path).name for path in refresh_projections.PREFLIGHT_CHECKS
                   if BUILDER_NAME.match(Path(path).name))

    # A parse that finds nothing would make every assertion below vacuous, so
    # the first thing this contract proves is that it can still see its input.
    require(
        len(checked) >= 8,
        "the release gate parse found only "
        f"{len(checked)} checked builder(s) in {CHECK_RELEASE.name}; the parse "
        "has drifted from how check_release.py now invokes them, and every "
        "assertion below it would have passed vacuously",
    )

    builders = [Path(entry).name for entry in refresh_projections.BUILDERS]
    require(
        len(builders) == len(set(builders)),
        f"refresh_projections.BUILDERS repeats an entry: {builders}",
    )

    for entry in refresh_projections.BUILDERS:
        require(
            (ROOT / entry).is_file(),
            f"refresh_projections.BUILDERS names a missing script: {entry}",
        )

    missing = sorted(checked - set(builders) - set(DELIBERATELY_UNREFRESHED))
    require(
        not missing,
        "check_release.py fails the release when these projections are stale, "
        "but refresh_projections.py never regenerates them, so the documented "
        f"repair cannot reach green: {missing}. Add each to "
        "refresh_projections.BUILDERS in dependency order, or record why it is "
        "exempt in DELIBERATELY_UNREFRESHED.",
    )

    # A builder whose bare invocation is a dry run must be told to write, or
    # the refresh silently discards its rendering. On 2026-09-04 the diagonal
    # depth roster was regenerated into a pipe this way and refresh() blamed
    # an impure builder for its own no-op.
    for entry in refresh_projections.BUILDERS:
        declares_write = '"--write"' in (ROOT / entry).read_text(encoding="utf-8")
        listed = "--write" in refresh_projections.WRITE_FLAGS.get(entry, ())
        require(
            declares_write == listed,
            f"{entry} declares --write={declares_write} but "
            f"refresh_projections.WRITE_FLAGS lists it={listed}; a bare run of "
            "a --write builder is a dry run, so keep the table exact",
        )

    for builder, reason in DELIBERATELY_UNREFRESHED.items():
        require(
            builder in checked,
            f"{builder} is recorded as a deliberate refresh exemption but the "
            "release gate no longer checks it; drop the exemption",
        )
        require(
            reason.strip(),
            f"{builder} is exempt from the refresh pipeline with no reason given",
        )

    # The problem library embeds the complete paper-corpus fingerprint, so a
    # taxonomy normalization after the index build invalidates the library
    # even when the problem's mathematical content has not changed.
    require(
        builders.index("build_publication_taxonomy.py")
        < builders.index("build_problem_index.py"),
        "build_problem_index.py reads and fingerprints docs/papers/corpus.json "
        "in docs/problem_library.json, so build_publication_taxonomy.py must "
        "run before it; otherwise a legitimate paper metadata refresh makes "
        "the same full pipeline fail convergence",
    )

    # The corpus descriptor reads paper/module-aliases.json. When the alias
    # builder ran after it, a full refresh reported its own descriptor stale
    # and accused a pure builder of impurity.
    require(
        builders.index("build_paper_module_aliases.py")
        < builders.index("build_corpus_descriptor.py"),
        "build_corpus_descriptor.py reads paper/module-aliases.json, so "
        "build_paper_module_aliases.py must run before it; with the current "
        "order a full refresh cannot converge",
    )
    check_check_only_dispatch()
    check_external_evidence_is_not_silently_omitted()

    print(
        "refresh projection coverage: PASS; "
        f"{len(checked)} release-checked builder(s), {len(builders)} refreshed, "
        f"{len(DELIBERATELY_UNREFRESHED)} argued exemption(s)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
