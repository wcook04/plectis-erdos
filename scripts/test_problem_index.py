#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Problem-directory discovery must not depend on a curated companion list."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import build_problem_index as builder


class ProblemModuleTests(unittest.TestCase):
    def test_new_recursive_modules_preserve_curated_order_and_deduplicate(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            directory = root / "ErdosProblems/Erdos68"
            directory.mkdir(parents=True)
            for name in ("Main", "Zebra", "Alpha"):
                (directory / f"{name}.lean").write_text("", encoding="utf-8")
            row = {
                "directory": "ErdosProblems/Erdos68",
                "principal_module": "ErdosProblems.Erdos68.Main",
                "companion_modules": [
                    "ErdosProblems.Erdos68.Zebra",
                    "ErdosProblems.Erdos68.Main",
                    "ErdosProblems.Erdos68.Zebra",
                ],
            }
            with patch.object(builder, "ROOT", root):
                initial = builder.problem_modules(row)
                self.assertEqual(initial, [
                    "ErdosProblems.Erdos68.Main",
                    "ErdosProblems.Erdos68.Zebra",
                    "ErdosProblems.Erdos68.Alpha",
                ])
                (directory / "Nested").mkdir()
                (directory / "Nested/New.lean").write_text("", encoding="utf-8")
                self.assertEqual(builder.problem_modules(row), initial + [
                    "ErdosProblems.Erdos68.Nested.New",
                ])

    def test_directory_boundary_and_symlinked_source(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            directory = root / "ErdosProblems/Erdos68"
            directory.mkdir(parents=True)
            (directory / "Main.lean").write_text("", encoding="utf-8")
            row = {
                "directory": "ErdosProblems/Erdos68",
                "principal_module": "ErdosProblems.Erdos68.Main",
            }
            with patch.object(builder, "ROOT", root):
                for unsafe in ("../outside", "/outside", "other", "ErdosProblems/../other"):
                    with self.subTest(directory=unsafe), self.assertRaises(ValueError):
                        builder.problem_modules({**row, "directory": unsafe})
                (root / "outside.lean").write_text("", encoding="utf-8")
                (directory / "Linked.lean").symlink_to(root / "outside.lean")
                with self.assertRaisesRegex(ValueError, "symlinked"):
                    builder.problem_modules(row)

    def test_live_inventory_covers_disk_without_promoting_source_presence(self):
        source = json.loads(builder.SOURCE.read_text(encoding="utf-8"))
        # Minimal joins keep this test focused on module and judgment ownership.
        built = builder.build(source, {}, None, None)
        for row, projected in zip(source["problems"], built["problems"]):
            with self.subTest(problem=row["problem_id"]):
                curated = list(dict.fromkeys([
                    row["principal_module"], *row.get("companion_modules", []),
                ]))
                names = [module["module"] for module in projected["modules"]]
                self.assertEqual(names[:len(curated)], curated)
                disk = {
                    ".".join(path.relative_to(builder.ROOT).with_suffix("").parts)
                    for path in (builder.ROOT / row["directory"]).rglob("*.lean")
                }
                self.assertEqual(set(names), set(curated) | disk)
                self.assertEqual(len(names), len(set(names)))
                self.assertEqual(projected["what_is_checked"], row["what_is_checked"])
                self.assertEqual(projected["what_is_not_checked"], row["what_is_not_checked"])
                self.assertEqual(projected["external_check"], {"state": "no_review_matrix_row"})
                if row.get("research_corpus"):
                    self.assertEqual(projected["research_corpus"],
                                     builder.research_corpus_facts(row["research_corpus"]))


if __name__ == "__main__":
    unittest.main()
