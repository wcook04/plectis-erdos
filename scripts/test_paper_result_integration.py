#!/usr/bin/env python3
"""Focused read-only tests for the paper result-integration owner."""

from __future__ import annotations

import json
import unittest
from collections import Counter
from pathlib import Path

from build_paper_result_integration import (
    DISPLAY_BANDS,
    build,
    discover_per_entry_comparator_portfolio,
    render_order,
)


ROOT = Path(__file__).resolve().parents[1]
BUILDER = ROOT / "scripts" / "build_paper_result_integration.py"


class PaperResultIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.output, cls.fragments, cls.order_projection = build()
        cls.palomar = json.loads(
            (ROOT / "docs" / "PALOMAR_RESULT_SHOWCASE.json").read_text(
                encoding="utf-8"
            )
        )
        cls.order = cls.palomar["family_display_order"]
        cls.claims = json.loads(
            (ROOT / "docs" / "claims.json").read_text(encoding="utf-8")
        )

    def test_owner_uses_current_sources_without_generated_outputs(self) -> None:
        builder_text = BUILDER.read_text(encoding="utf-8")
        forbidden = (
            "v5-run",
            ".plectis-convergence",
            "STAGING_ORDER",
            "--publish-order",
            "--order-source",
        )
        self.assertFalse(any(token in builder_text for token in forbidden))
        self.assertIn("family_display_order=order", builder_text)
        self.assertEqual(self.order_projection, render_order(self.order))

    def test_complete_dynamic_population(self) -> None:
        counts = self.output["counts"]
        family_count = len(self.order)
        atom_count = sum(
            1
            for line in (ROOT / "docs" / "result-atoms.jsonl")
            .read_text(encoding="utf-8")
            .splitlines()
            if line.strip()
        )
        self.assertEqual(self.output["schema"], "plectis.paper-result-integration/2")
        self.assertEqual(counts["family_count"], family_count)
        self.assertEqual(counts["long_form_routed_family_count"], family_count)
        self.assertEqual(counts["result_atom_count"], atom_count)
        self.assertEqual(counts["populated_family_count"], family_count)
        self.assertEqual(counts["zero_atom_family_count"], 0)
        self.assertEqual(len(self.output["families"]), family_count)
        self.assertEqual(
            sum(row["result_atoms"]["count"] for row in self.output["families"]),
            atom_count,
        )
        self.assertEqual(len(self.fragments), len(self.output["problems"]))

    def test_palomar_order_and_editorial_ceiling_are_preserved(self) -> None:
        family_count = len(self.order)
        self.assertEqual(
            [row["global_display_order"] for row in self.order],
            list(range(1, family_count + 1)),
        )
        self.assertEqual(
            set(Counter(row["display_band"]["band"] for row in self.order)),
            set(DISPLAY_BANDS),
        )
        self.assertTrue(
            all(
                row["authority"]
                == {
                    "human_review_claim": False,
                    "novelty_claim": False,
                    "source": "attributed LLM family editorial decision",
                    "status": "llm_best_attempt_open_to_specialist_correction",
                }
                for row in self.order
            )
        )

    def test_current_comparator_portfolio_is_discovered_not_hard_coded(self) -> None:
        portfolio = discover_per_entry_comparator_portfolio()
        membership = json.loads((ROOT / "verification/comparator-replay-membership.json").read_text())
        coverage = portfolio["registered_claim_coverage"]
        self.assertEqual(coverage["formal_claim_count"], membership["registered_claim_coverage"]["formal_claim_count"])
        self.assertEqual(coverage["missing_formal_transport_count"], membership["registered_claim_coverage"]["missing_formal_transport_count"])
        self.assertEqual(coverage["atom_level_coverage"], "not_asserted_by_family_membership")
        self.assertEqual(
            self.output["assurance_portfolios"]["dynamic_comparator_replay_candidate"],
            portfolio,
        )
        self.assertEqual(
            self.output["counts"]["dynamic_comparator_replay_package_count"],
            portfolio["package_count"],
        )
        self.assertEqual(
            self.output["counts"]["dynamic_comparator_replay_interface_count"],
            portfolio["interface_count"],
        )
        self.assertEqual(
            self.output["counts"]["comparator_registered_selected_interface_count"],
            len(self.claims["external_verification_packet"]["main_results"]),
        )


if __name__ == "__main__":
    unittest.main()
