#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Focused non-Lean tests for the public source-population planner."""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

import lean_source_population as population


class LeanSourcePopulationTest(unittest.TestCase):
    def fixture(self, sources: dict[str, str], lakefile: str = "") -> Path:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        for relative, content in sources.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        if lakefile:
            (root / "lakefile.toml").write_text(lakefile)
        return root

    def test_maximal_roots_cover_imported_and_orphan_sources(self) -> None:
        root = self.fixture(
            {
                "Pkg/Root.lean": "import Pkg.Leaf\n",
                "Pkg/Leaf.lean": "def leaf := 1\n",
                "Loose/Isolated.lean": "def isolated := 2\n",
            }
        )
        plan = population.current_source_plan(root)
        self.assertEqual(plan["targets"], ["Loose.Isolated", "Pkg.Root"])
        self.assertEqual(plan["module_count"], 3)
        self.assertEqual(plan["closure_count"], 3)

    def test_src_dir_logical_names_have_no_accidental_duplicate_roots(self) -> None:
        root = self.fixture(
            {
                "examples/Examples.lean": "import Examples.Leaf\n",
                "examples/Examples/Leaf.lean": "def leaf := 1\n",
                "examples/Loose.lean": "def loose := 2\n",
            },
            'name = "fixture"\n'
            '[[lean_lib]]\nname = "Examples"\nsrcDir = "examples"\n',
        )

        plan = population.current_source_plan(root)

        self.assertEqual(plan["targets"], ["Examples", "Loose"])
        self.assertEqual(plan["module_count"], 3)
        self.assertEqual(plan["maximal_root_count"], 2)
        self.assertEqual(plan["closure_count"], 3)

    def test_source_digest_changes_with_source_bytes(self) -> None:
        root = self.fixture({"Pkg.lean": "def value := 1\n"})
        before = population.current_source_plan(root)
        (root / "Pkg.lean").write_text("def value := 2\n")
        after = population.current_source_plan(root)
        self.assertNotEqual(before["sha256"], after["sha256"])

    def test_library_inventory_respects_src_dir_and_globs(self) -> None:
        root = self.fixture(
            {"examples/Present/Leaf.lean": "def leaf := 1\n"},
            'name = "fixture"\n'
            '[[lean_lib]]\nname = "Present"\nsrcDir = "examples"\n'
            'globs = ["Present.*"]\n'
            '[[lean_lib]]\nname = "Missing"\nsrcDir = "examples"\n',
        )
        inventory = population.declared_lean_library_inventory(root)
        self.assertEqual(inventory["declared_library_count"], 2)
        self.assertEqual(inventory["missing_declared_libraries"], ["Missing"])

    def test_cycle_is_rejected_even_when_reachable_from_a_root(self) -> None:
        root = self.fixture(
            {
                "Pkg/Root.lean": "import Pkg.A\n",
                "Pkg/A.lean": "import Pkg.B\n",
                "Pkg/B.lean": "import Pkg.A\n",
            }
        )
        with self.assertRaisesRegex(population.SourcePopulationError, "cyclic"):
            population.current_source_plan(root)


if __name__ == "__main__":
    unittest.main()
