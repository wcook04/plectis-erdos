#!/usr/bin/env python3
"""Tests for ``build_argument_continuations.py`` on the toy-corpus export.

``scripts/fixtures/toy_argument_continuations_export.jsonl`` is the exporter's
output on the toy corpus in ``test_argument_continuation_export.py`` (refresh
it with ``PLECTIS_TEST_KEEP_EXPORT=<path>``). The expectations are computed by
hand from that corpus:

* supplied: ``Supply 3``, ``EvenP 2``, the guarded universal statement, the
  conjunction and the iff (unconditional theorems), and ``True``;
* open: ``Target``, ``OpenQ``, ``∀ n, Supply n``, ``∀ n, EvenP n``,
  ``EvenP 3``, ``3 ≥ 7`` and ``∀ n, n ≥ 7``;
* the only disguise class is ``{Target, OpenQ}`` (the iff read both ways);
* supplying ``∀ n, EvenP n`` supplies ``∀ n, Supply n``, ``Target`` and
  ``OpenQ``;
* the bundles of ``Target`` are four singletons, one per route.
"""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import build_argument_continuations as builder  # noqa: E402

FIXTURE = ROOT / "scripts" / "fixtures" / "toy_argument_continuations_export.jsonl"


class ToyGraph(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.graph = builder.Graph(builder.read_export(FIXTURE))
        cls.graph.analyse()
        cls.key = {}
        for key, node in cls.graph.statements.items():
            for text in [node["type"], *node.get("aliases", ())]:
                cls.key[text] = key

    def k(self, text: str) -> str:
        self.assertIn(text, self.key, f"statement {text!r} missing; have {sorted(self.key)}")
        return self.key[text]

    def names(self, keys) -> set[str]:
        out: set[str] = set()
        for k in keys:
            node = self.graph.statements[k]
            out.add(node["type"])
            out.update(node.get("aliases", ()))
        return out

    def test_aliases_merge(self) -> None:
        # Target, Named and the universal Supply statement are one statement.
        self.assertEqual(self.k("ToyCorpus.Target"), self.k("∀ (n : Nat), ToyCorpus.Supply n"))
        self.assertEqual(self.k("ToyCorpus.Named"), self.k("ToyCorpus.Target"))
        self.assertEqual(self.k("ToyCorpus.OpenQ"), self.k("∀ (n : Nat), ToyCorpus.EvenP n"))

    def test_supply(self) -> None:
        supplied = self.names(self.graph.supplied)
        for text in ("ToyCorpus.Supply 3", "ToyCorpus.EvenP 2",
                     "∀ (n : Nat), n ≥ 7 → ToyCorpus.Supply n", "True"):
            self.assertIn(text, supplied)
        for text in ("ToyCorpus.Target", "ToyCorpus.OpenQ", "∀ (n : Nat), ToyCorpus.Supply n",
                     "∀ (n : Nat), ToyCorpus.EvenP n", "ToyCorpus.EvenP 3", "3 ≥ 7"):
            self.assertNotIn(text, supplied)

    def test_witness_chain(self) -> None:
        tree = self.graph.proof_tree(self.k("∀ (n : Nat), n ≥ 7 → ToyCorpus.Supply n"))
        self.assertEqual(tree["producer"], "ToyCorpus.supply_ge")
        self.assertEqual(tree["from"], [])

    def test_disguise_class(self) -> None:
        classes = [frozenset(members) for members in self.graph.disguise_classes()]
        self.assertEqual(classes, [frozenset({self.k("ToyCorpus.Target"), self.k("ToyCorpus.OpenQ")})])

    def test_leverage(self) -> None:
        gained = self.graph.leverage(self.k("∀ (n : Nat), n ≥ 7"))
        self.assertEqual(gained, {self.k("ToyCorpus.Target"), self.k("ToyCorpus.OpenQ")})
        self.assertEqual(self.graph.leverage(self.k("ToyCorpus.EvenP 2")), set())

    def test_bundles(self) -> None:
        bundles, truncated = self.graph.bundles(self.k("ToyCorpus.Target"))
        self.assertFalse(truncated)
        self.assertEqual(sorted(map(tuple, bundles)),
                         sorted([(self.k("ToyCorpus.OpenQ"),), (self.k("∀ (n : Nat), n ≥ 7"),)]))

    def test_criticality(self) -> None:
        # Withdrawing supply_ge removes the only witness of the guarded statement,
        # and with it the only witness of `True` that goes through it survives
        # through uses_even_two, so exactly one statement is lost.
        lost = {self.graph.statements[k]["type"] for k in self.graph.criticality(producer="ToyCorpus.supply_ge")}
        self.assertEqual(lost, {"∀ (n : Nat), n ≥ 7 → ToyCorpus.Supply n"})
        # Supply 3 has an unconditional witness; removing EvenP 2 loses nothing else.
        self.assertEqual(self.graph.criticality(statement=self.k("ToyCorpus.EvenP 2")), set())

    def test_object_index(self) -> None:
        mentions = self.names(k for k, n in self.graph.statements.items() if "ToyCorpus.EvenP" in n["constants"])
        self.assertIn("∀ (n : Nat), ToyCorpus.EvenP n", mentions)
        self.assertIn("ToyCorpus.Supply 1 ∧ ToyCorpus.EvenP 2", mentions)

    def test_projection_writes(self) -> None:
        projection, graph_payload = builder.build(FIXTURE, ROOT)
        self.assertEqual(projection["schema"], builder.SCHEMA)
        self.assertEqual(projection["summary"]["disguise_classes"], 1)
        self.assertEqual(projection["summary"]["open_statements"], 5)
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "a.json"
            gz = Path(tmp) / "a.json.gz"
            builder.write_outputs(projection, graph_payload, out, gz)
            again = Path(tmp) / "b.json.gz"
            builder.write_outputs(projection, graph_payload, out, again)
            self.assertEqual(gz.read_bytes(), again.read_bytes(), "graph output must be byte-stable")
            self.assertEqual(json.loads(out.read_text())["schema"], builder.SCHEMA)


if __name__ == "__main__":
    unittest.main()
