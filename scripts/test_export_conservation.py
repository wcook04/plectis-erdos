#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Adversarial tests for the private-to-public export conservation law.

The failure this encodes: an export that mirrors the private tree onto the
public one silently deletes candidate-only mathematics.  The audit named three
real specimens, and all three are used here as fixture names:

* `ErdosProblems/Erdos243/ReciprocalTailRigidity.lean` realisation bridge,
  the declarations at lines 1899, 1923 and 1949 of the release candidate;
* `ErdosProblems/Erdos249/LcmJumpKillFromDiagonal.lean`;
* `ExternalVerification257Strong`.

The assertions run over fixture directories, so the suite needs no private
checkout and no Lean.  A closing observation reports the live state of the
three specimens across whichever sibling trees are present, and never fails on
their absence.

Stdlib only, no Lean, no network, no git mutation.
"""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import export_conservation as conservation  # noqa: E402
from export_conservation import Declaration  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent

# The three specimens, addressed as the exporter addresses them.
RECIPROCAL_BRIDGE_MODULE = "ErdosProblems/Erdos243/ReciprocalTailRigidity.lean"
RECIPROCAL_BRIDGE_NAMES = (
    "tailRatio_eq_reciprocal_add_next",
    "tailRatio_eq_partialReciprocalSum_add",
    "reciprocalSeries_hasSum_of_tailRatio_tendsto_zero",
)
LCM_JUMP_MODULE = "ErdosProblems/Erdos249/LcmJumpKillFromDiagonal.lean"
LCM_JUMP_NAMES = (
    "periodLcm_jump_eq_height_at_one",
    "periodLcm_jump_eq_height_at_three",
)
STRONG_PACKAGE_MODULE = "ExternalVerification257Strong/Solution.lean"
STRONG_PACKAGE_NAMES = ("mem_iff_greedyBinaryDefect_sqrt_windows",)

TARGET_ONLY_SPECIMENS: tuple[Declaration, ...] = tuple(
    [(RECIPROCAL_BRIDGE_MODULE, name) for name in RECIPROCAL_BRIDGE_NAMES]
    + [(LCM_JUMP_MODULE, name) for name in LCM_JUMP_NAMES]
    + [(STRONG_PACKAGE_MODULE, name) for name in STRONG_PACKAGE_NAMES]
)

SHARED_MODULE = "ErdosProblems/Erdos243/ReciprocalTailRigidity.lean"
SHARED_NAMES = ("tailRatio", "reciprocalSeries")
SOURCE_ONLY: tuple[Declaration, ...] = (
    ("ErdosProblems/Erdos1041/AbelControlPolygon.lean", "trinomial_erdos1041_conclusion"),
)


def require(condition: bool, message: str) -> None:
    """Keep assertions active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def _lean_source(namespace: str, names: tuple[str, ...]) -> str:
    body = "\n\n".join(
        f"theorem {name} (n : Nat) : n = n := by\n  rfl" for name in names
    )
    return f"import Mathlib\n\nnamespace {namespace}\n\n{body}\n\nend {namespace}\n"


def build_fixture_trees(root: Path) -> tuple[Path, Path]:
    """A source tree missing what the target alone carries."""
    source = root / "source_tree"
    target = root / "target_tree"
    for tree in (source, target):
        path = tree / SHARED_MODULE
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(_lean_source("ErdosProblems.Erdos243", SHARED_NAMES))

    # Target-only specimen one: three extra bridge declarations appended to a
    # module both trees carry.  This is the shape that hides best, because the
    # module itself is present on both sides.
    bridge = target / RECIPROCAL_BRIDGE_MODULE
    bridge.write_text(
        bridge.read_text()
        + "\n"
        + _lean_source("ErdosProblems.Erdos243", RECIPROCAL_BRIDGE_NAMES)
    )

    # Target-only specimen two: a module the source tree does not have at all.
    lcm = target / LCM_JUMP_MODULE
    lcm.parent.mkdir(parents=True, exist_ok=True)
    lcm.write_text(_lean_source("ErdosProblems.Erdos249", LCM_JUMP_NAMES))

    # Target-only specimen three: a whole comparator package.
    strong = target / STRONG_PACKAGE_MODULE
    strong.parent.mkdir(parents=True, exist_ok=True)
    strong.write_text(
        _lean_source(
            "Erdos249257.ExternalVerification257Strong", STRONG_PACKAGE_NAMES
        )
    )

    # Source-only: mathematics the export is actually meant to carry across.
    extra = source / SOURCE_ONLY[0][0]
    extra.parent.mkdir(parents=True, exist_ok=True)
    extra.write_text(
        _lean_source("ErdosProblems.Erdos1041", (SOURCE_ONLY[0][1],))
    )
    return source, target


def tree_declarations(tree: Path) -> set[Declaration]:
    """Every `(module, bare declaration)` pair a fixture tree carries."""
    modules = sorted(
        path.relative_to(tree).as_posix() for path in tree.rglob("*.lean")
    )
    pairs = conservation.declarations_of_tree(tree, modules)
    return {(module, name.rsplit(".", 1)[-1]) for module, name in pairs}


def check_fixtures() -> int:
    """Prove a mirror export loses the specimens and a reconciled one does not."""
    checks = 0
    with tempfile.TemporaryDirectory() as raw:
        source_tree, target_tree = build_fixture_trees(Path(raw))
        source = tree_declarations(source_tree)
        target = tree_declarations(target_tree)

        for specimen in TARGET_ONLY_SPECIMENS:
            require(
                specimen in target,
                f"fixture target must carry the specimen {specimen}",
            )
            require(
                specimen not in source,
                f"fixture source must not carry the specimen {specimen}",
            )
        checks += 1

        plan = conservation.plan_export(source, target)
        require(
            set(TARGET_ONLY_SPECIMENS) <= plan.target_only,
            "every named specimen must be classified target-only",
        )
        require(
            set(SOURCE_ONLY) <= plan.source_only,
            "source-only mathematics must still be classified source-only",
        )
        require(
            set(TARGET_ONLY_SPECIMENS) <= plan.reconciled
            and set(SOURCE_ONLY) <= plan.reconciled,
            "the reconciled export must be the union of both trees",
        )
        checks += 1

        mirrored = conservation.mirror_export(source, target)
        report = conservation.check_conservation(source, target, mirrored)
        require(
            not report.conserved,
            "a mirror export escaped the conservation law",
        )
        require(
            set(TARGET_ONLY_SPECIMENS) <= report.deleted,
            "the mirror export report must name every deleted specimen: "
            f"missing {sorted(set(TARGET_ONLY_SPECIMENS) - report.deleted)}",
        )
        require(
            len(report.describe()) == len(report.deleted),
            "every deleted declaration must be described",
        )
        checks += 1

        reconciled = conservation.reconciled_export(source, target)
        report = conservation.check_conservation(source, target, reconciled)
        require(
            report.conserved,
            f"a reconciled export must conserve every declaration: {report.deleted}",
        )
        checks += 1

        # Dropping exactly one specimen from an otherwise reconciled export
        # must still be caught, one specimen at a time.
        for specimen in TARGET_ONLY_SPECIMENS:
            partial = reconciled - {specimen}
            report = conservation.check_conservation(source, target, partial)
            require(
                not report.conserved and specimen in report.deleted,
                f"dropping {specimen} escaped the conservation law",
            )
            checks += 1

        # An export must not invent declarations either.
        invented = reconciled | {("Invented/Module.lean", "invented_theorem")}
        report = conservation.check_conservation(source, target, invented)
        require(
            not report.conserved
            and ("Invented/Module.lean", "invented_theorem") in report.added,
            "an invented declaration escaped the conservation law",
        )
        checks += 1

        # An empty target has nothing to conserve, and an empty source must
        # not be read as authority to empty the target.
        report = conservation.check_conservation(source, set(), source)
        require(report.conserved, "an empty target must conserve trivially")
        report = conservation.check_conservation(set(), target, set())
        require(
            not report.conserved and report.deleted == frozenset(target),
            "an empty source must not authorise emptying the target",
        )
        checks += 1
    return checks


# --- statement digests -------------------------------------------------------

# The #243 specimen as a statement, not just a name. The realisation bridge
# survived in all three trees while the release copy carried the extra
# declarations, which is the shape a mirror export deletes. The same module is
# also the clearest case of the second failure: the module is present on both
# sides, the declaration keeps its name, and its hypotheses move.
BRIDGE_SOURCE = (
    "theorem tailRatio_eq_reciprocal_add_next (A : Set Nat) (n : Nat) :\n"
    "    tailRatio A n = 1 / n + tailRatio A (n + 1) := by\n"
    "  sorry\n"
)
BRIDGE_WITH_HYPOTHESIS = (
    "theorem tailRatio_eq_reciprocal_add_next (A : Set Nat) (hA : A.Infinite)\n"
    "    (n : Nat) :\n"
    "    tailRatio A n = 1 / n + tailRatio A (n + 1) := by\n"
    "  sorry\n"
)
BRIDGE_REFORMATTED = (
    "theorem    tailRatio_eq_reciprocal_add_next (A : Set Nat) (n : Nat) :\n"
    "    tailRatio A n = 1 / n + tailRatio A (n + 1) := by\n"
    "  rfl\n"
)

# Every declaration keyword the digest recognises. Losing one would make a
# whole class of declarations invisible to the law.
DIGEST_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "opaque",
    "axiom",
    "class",
    "structure",
    "inductive",
)


def check_statement_digest_fixtures() -> int:
    """A name that survives while its statement moves must be reported."""
    checks = 0

    source = conservation.statement_digests(BRIDGE_SOURCE)
    require(
        list(source) == ["tailRatio_eq_reciprocal_add_next"],
        f"the bridge fixture must yield exactly its declaration: {list(source)}",
    )
    checks += 1

    # Reformatting and a changed proof body must not move the digest. A digest
    # that moves on whitespace reports every export as non-conserved, which is
    # how a real check gets switched off.
    require(
        conservation.statement_digests(BRIDGE_REFORMATTED) == source,
        "whitespace and proof-body changes must not move a statement digest",
    )
    checks += 1

    # An added hypothesis must move it. This is the disconfirming case a
    # `(module, declaration)` set comparison reports as conserved.
    changed = conservation.statement_digests(BRIDGE_WITH_HYPOTHESIS)
    require(
        set(changed) == set(source)
        and changed["tailRatio_eq_reciprocal_add_next"]
        != source["tailRatio_eq_reciprocal_add_next"],
        "an added hypothesis under an unchanged name left the digest fixed",
    )
    checks += 1

    for keyword in DIGEST_KEYWORDS:
        digests = conservation.statement_digests(f"{keyword} fixtureName : Nat := 1\n")
        require(
            list(digests) == ["fixtureName"],
            f"the statement digest no longer recognises {keyword!r}",
        )
    checks += 1

    # A declaration name inside a proof body or a comment is not a declaration.
    require(
        not conservation.statement_digests(
            "-- theorem commented_out (n : Nat) : n = n\n  exact theorem_like n\n"
        ),
        "an indented reference must not be read as a declaration header",
    )
    checks += 1
    return checks


def check_statement_conservation_fixtures() -> int:
    """The two halves of the law separate, over the named specimens."""
    checks = 0
    module = RECIPROCAL_BRIDGE_MODULE
    key: Declaration = (module, "tailRatio_eq_reciprocal_add_next")
    source_map = {
        (module, name): f"sha256:{index}"
        for index, name in enumerate(RECIPROCAL_BRIDGE_NAMES)
    }

    faithful = conservation.check_statement_conservation(source_map, dict(source_map))
    require(faithful.conserved, "an identical export must conserve statements")
    require(not faithful.describe(), "a conserved export must describe nothing")
    checks += 1

    dropped = dict(source_map)
    del dropped[key]
    report = conservation.check_statement_conservation(source_map, dropped)
    require(
        not report.conserved and report.absent == frozenset({key}),
        f"a dropped declaration escaped the statement law: {report}",
    )
    require(
        any("drops source declaration" in line for line in report.describe()),
        "a dropped declaration must be described as dropped",
    )
    checks += 1

    restated = dict(source_map)
    restated[key] = "sha256:changed"
    report = conservation.check_statement_conservation(source_map, restated)
    require(
        not report.conserved and report.restated == frozenset({key}),
        f"a restated declaration escaped the statement law: {report}",
    )
    require(
        any("changes its statement" in line for line in report.describe()),
        "a restated declaration must be described as restated",
    )
    checks += 1

    # The two failures are separate. A dropped declaration is not a restated
    # one, and reporting either as the other sends the repair to the wrong
    # place.
    require(
        not report.absent,
        "a restated declaration must not also be reported as absent",
    )
    checks += 1

    # An export that adds a declaration conserves the source. Additions are the
    # ordinary case of an export that carries more than its input, and the
    # `(module, declaration)` half of the law already reports them separately.
    added = dict(source_map)
    added[(LCM_JUMP_MODULE, "periodLcm_jump_eq_height_at_one")] = "sha256:new"
    require(
        conservation.check_statement_conservation(source_map, added).conserved,
        "an added declaration must not break statement conservation",
    )
    checks += 1
    return checks


def check_statement_conservation_over_fixture_trees() -> int:
    """Run the statement law over real files, including the #243 specimen."""
    checks = 0
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        source_tree = root / "source_tree"
        result_tree = root / "result_tree"
        for tree, body in ((source_tree, BRIDGE_SOURCE), (result_tree, BRIDGE_SOURCE)):
            path = tree / RECIPROCAL_BRIDGE_MODULE
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"import Mathlib\n\n{body}")

        modules = [RECIPROCAL_BRIDGE_MODULE]
        source = conservation.statements_of_tree(source_tree, modules)
        result = conservation.statements_of_tree(result_tree, modules)
        require(
            conservation.check_statement_conservation(source, result).conserved,
            "an identical fixture tree must conserve statements",
        )
        checks += 1

        (result_tree / RECIPROCAL_BRIDGE_MODULE).write_text(
            f"import Mathlib\n\n{BRIDGE_WITH_HYPOTHESIS}"
        )
        result = conservation.statements_of_tree(result_tree, modules)
        report = conservation.check_statement_conservation(source, result)
        require(
            not report.conserved
            and report.restated
            == frozenset({(RECIPROCAL_BRIDGE_MODULE, "tailRatio_eq_reciprocal_add_next")}),
            f"a restated specimen escaped the tree-level law: {report}",
        )
        checks += 1

        # A module the result tree does not carry at all reports every one of
        # its declarations as absent rather than as restated.
        (result_tree / RECIPROCAL_BRIDGE_MODULE).unlink()
        report = conservation.check_statement_conservation(
            source, conservation.statements_of_tree(result_tree, modules)
        )
        require(
            not report.conserved and report.absent == frozenset(source),
            "a missing module escaped the tree-level law",
        )
        checks += 1
    return checks


def observe_live_specimens() -> list[str]:
    """Report, without asserting, where the three specimens actually live."""
    trees: dict[str, Path] = {"R release candidate": ROOT}
    # Sibling trees are located only through the environment; the public
    # checkout must not carry any operator-local absolute path.
    for label, variable in (
        ("P private tree", "PLECTIS_PRIVATE_LEAN_TREE"),
        ("C public Lean tree", "PLECTIS_PUBLIC_LEAN_TREE"),
    ):
        value = os.environ.get(variable, "").strip()
        if value:
            trees[label] = Path(value)
    lines: list[str] = []
    for label, tree in trees.items():
        if not tree.is_dir():
            lines.append(f"  {label}: tree not present, nothing observed")
            continue
        for module, names in (
            (RECIPROCAL_BRIDGE_MODULE, RECIPROCAL_BRIDGE_NAMES),
            (LCM_JUMP_MODULE, LCM_JUMP_NAMES),
            (STRONG_PACKAGE_MODULE, STRONG_PACKAGE_NAMES),
        ):
            path = tree / module
            if not path.is_file():
                lines.append(f"  {label}: {module} absent")
                continue
            declared = {
                name.rsplit(".", 1)[-1]
                for name in conservation.qualified_declarations(path)
            }
            missing = [name for name in names if name not in declared]
            if missing:
                lines.append(
                    f"  {label}: {module} present but missing {', '.join(missing)}"
                )
            else:
                lines.append(f"  {label}: {module} carries all named specimens")
    return lines


def main() -> int:
    checks = check_fixtures()
    statement_checks = (
        check_statement_digest_fixtures()
        + check_statement_conservation_fixtures()
        + check_statement_conservation_over_fixture_trees()
    )
    print(
        "test_export_conservation: "
        f"{checks} conservation fixtures held; "
        f"{len(TARGET_ONLY_SPECIMENS)} named specimens are preserved by a "
        "reconciled export and lost by a mirror export"
    )
    print(
        "test_export_conservation: "
        f"{statement_checks} statement fixtures held; a declaration that keeps "
        "its name and changes its statement is reported separately from one "
        "the export drops"
    )
    print("test_export_conservation: live specimen observation (not asserted)")
    for line in observe_live_specimens():
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
