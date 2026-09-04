#!/usr/bin/env python3
"""Regression tests for deterministic ClosureT64 dependency sharding."""

from __future__ import annotations

import unittest

import shard_closure_t64 as sharder


class ClosureT64ShardingTests(unittest.TestCase):
    def test_assignment_is_dependency_safe_and_deterministic(self) -> None:
        blocks = {
            "prime_lucas_2": "theorem prime_lucas_2 : Nat.Prime 2 := by\n  decide\n",
            "prime_lucas_3": "theorem prime_lucas_3 : Nat.Prime 3 := by\n  decide\n",
            "prime_lucas_5": (
                "theorem prime_lucas_5 : Nat.Prime 5 := by\n"
                "  exact prime_lucas_2\n"
            ),
            "prime_lucas_7": (
                "theorem prime_lucas_7 : Nat.Prime 7 := by\n"
                "  exact prime_lucas_3\n"
            ),
            "prime_lucas_11": (
                "theorem prime_lucas_11 : Nat.Prime 11 := by\n"
                "  exact prime_lucas_5\n"
            ),
        }
        shards, owner = sharder.assign_shards(blocks)
        self.assertEqual(sorted(shards), ["Level0A", "Level0B", "Level1A", "Level1B", "Level2A"])
        self.assertNotEqual(owner["prime_lucas_2"], owner["prime_lucas_3"])
        self.assertNotEqual(owner["prime_lucas_5"], owner["prime_lucas_7"])
        self.assertEqual(owner["prime_lucas_11"], "Level2A")

        rendered = sharder.shard_text(
            "Level2A", shards["Level2A"], blocks, owner
        )
        self.assertIn(f"import {sharder.MODULE_PREFIX}.{owner['prime_lucas_5']}", rendered)
        self.assertNotIn(f"import {sharder.MODULE_PREFIX}.{owner['prime_lucas_3']}", rendered)

    def test_cycles_and_missing_references_fail_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "unsharded"):
            sharder.dependencies(
                {
                    "prime_lucas_2": (
                        "theorem prime_lucas_2 : Nat.Prime 2 := by\n"
                        "  exact prime_lucas_3\n"
                    )
                }
            )
        with self.assertRaisesRegex(ValueError, "cycle"):
            sharder.depths(
                {
                    "prime_lucas_2": {"prime_lucas_3"},
                    "prime_lucas_3": {"prime_lucas_2"},
                }
            )


if __name__ == "__main__":
    unittest.main()
