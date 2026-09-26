#!/usr/bin/env python3
"""Tests for ``build_argument_continuations.py`` and ``query_continuations.py``.

``scripts/fixtures/toy_argument_continuations_export.jsonl`` is the exporter's
output on the toy corpus in ``test_argument_continuation_export.py`` (refresh
it with ``PLECTIS_TEST_KEEP_EXPORT=<path>``). The expectations below are
computed by hand from that corpus and look statements up by their rendered
type, so they survive changes of key:

* supplied: ``Supply 3``, ``EvenP 2``, the guarded universal statement, the
  conjunction and the iff (unconditional theorems), ``True``, and
  ``g 3 ≠ 0`` (a disequation producer instantiated at 3);
* open without the battery: ``Target`` and ``OpenQ`` (one disguise class, the
  iff read both ways, with their unfoldings ``∀ n, Supply n`` and
  ``∀ n, EvenP n``), ``EvenP 3``, ``3 ≥ 7``, ``∀ n, n ≥ 7`` and ``False``
  (``false_of_cert`` needs a certificate of unknown inhabitation);
* refuted without the battery: ``Q 3`` (a plain negation), ``g 5 = 0`` (a
  disequation read as a negation), ``R7 7`` (a conjunct), and ``Z7``, derived
  because ``a_first`` reduces the refuted ``R7 7`` to it;
* supplying ``∀ n, n ≥ 7`` supplies ``Target`` and ``OpenQ``;
* the bundles of ``Target`` are two singletons, one per route.

Hand-made streams cover the rules the toy corpus does not reach.
"""

from __future__ import annotations

import argparse
import gzip
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import build_argument_continuations as builder  # noqa: E402
import query_continuations as query  # noqa: E402

FIXTURE = ROOT / "scripts" / "fixtures" / "toy_argument_continuations_export.jsonl"
META = {"record": "meta", "schema": "plectis-argument-continuation-export/1", "lean_version": "test",
        "imports": ["Init"]}
SUMMARY = {"record": "summary", "truncated": False}


# --------------------------------------------------------------------------
# Hand-made export rows. A statement's key doubles as its rendered type.


def hyp(i: int, key: str, *, closed: bool = True, kind: str = "hypothesis") -> dict:
    row = {"i": i, "name": f"h{i}", "kind": kind, "prop": True, "closed": closed, "type": key}
    if closed:
        row["key"] = key
    return row


def data(i: int, type_: str, *, inhabited: bool = True, closed: bool = True, nonempty: str | None = None) -> dict:
    row = {"i": i, "name": f"x{i}", "kind": "data", "prop": False, "closed": closed, "type": type_,
           "inhabited": inhabited}
    if nonempty:
        row.update({"nonempty_key": nonempty, "nonempty_type": nonempty})
    return row


def theorem(name: str, binders: list[dict], conclusion: str | None = None, module: str = "M") -> dict:
    concl = {"closed": conclusion is not None, "type": conclusion or "schematic", "constants": []}
    if conclusion is not None:
        concl["key"] = conclusion
    return {"record": "theorem", "name": name, "module": module, "binders": binders, "conclusion": concl}


def statement(key: str, origin: str = "hypothesis") -> dict:
    return {"record": "statement", "key": key, "origin": origin, "type": key, "constants": []}


def match(head: str, producer: str, residuals: tuple[str, ...] = (), *, reading: str = "conclusion") -> dict:
    return {"record": "match", "statement": head, "producer": producer, "reading": reading, "status": "matched",
            "open_data": False, "residuals": [{"key": r, "type": r, "has_open_data": False} for r in residuals]}


def refute(key: str) -> dict:
    return {"record": "battery_refutation", "statement": key, "tactic": "decide", "kernel_checked": True}


def idle(name: str, dropped: list[tuple[int, str | None]], *, kernel_checked: bool = True,
         key: str | None = None) -> dict:
    row = {"record": "idle", "theorem": name, "type": f"stronger {name}", "kernel_checked": kernel_checked,
           "kernel_error": "", "dropped": [{"i": i, "type": k or "schematic", **({"key": k} if k else {})}
                                           for i, k in dropped]}
    if key:
        row["key"] = key
    return row


def graph_of(rows: list[dict], **options) -> builder.Graph:
    graph = builder.Graph([META, *rows, SUMMARY], **options)
    graph.analyse()
    return graph


def write_stream(directory: Path, rows: list[dict]) -> Path:
    path = directory / "export.jsonl"
    path.write_text("\n".join(json.dumps(r, ensure_ascii=False) for r in [META, *rows, SUMMARY]) + "\n",
                    encoding="utf-8")
    return path


def git_lean_tree() -> str | None:
    return query.git_lean_tree(ROOT)


# --------------------------------------------------------------------------
# The toy corpus


class ToyGraph(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        # Structural semantics on the toy's producer relation. The battery and
        # the idle strengthenings (which prove the toy's easy statements
        # outright) are tested separately.
        cls.graph = builder.Graph(builder.read_export(FIXTURE), include_battery=False, include_idle=False)
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
                     "∀ (n : Nat), n ≥ 7 → ToyCorpus.Supply n", "True", "ReviewToy.g 3 ≠ 0"):
            self.assertIn(text, supplied)
        for text in ("ToyCorpus.Target", "ToyCorpus.OpenQ", "∀ (n : Nat), ToyCorpus.Supply n",
                     "∀ (n : Nat), ToyCorpus.EvenP n", "ToyCorpus.EvenP 3", "3 ≥ 7", "False"):
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
        # The members of a disguise class share one closure.
        self.assertEqual(self.graph.leverage(self.k("ToyCorpus.Target")), {self.k("ToyCorpus.OpenQ")})
        self.assertEqual(self.graph.leverage(self.k("ToyCorpus.OpenQ")), {self.k("ToyCorpus.Target")})

    def test_bundles(self) -> None:
        bundles, truncated = self.graph.bundles(self.k("ToyCorpus.Target"))
        self.assertFalse(truncated)
        self.assertEqual(sorted(map(tuple, bundles)),
                         sorted([(self.k("ToyCorpus.OpenQ"),), (self.k("∀ (n : Nat), n ≥ 7"),)]))

    def test_criticality(self) -> None:
        # Withdrawing supply_ge removes the only witness of the guarded
        # statement; True keeps other witnesses, so exactly one statement is lost.
        lost = {self.graph.statements[k]["type"] for k in self.graph.criticality(producer="ToyCorpus.supply_ge")}
        self.assertEqual(lost, {"∀ (n : Nat), n ≥ 7 → ToyCorpus.Supply n"})
        # Supply 3 has an unconditional witness; removing EvenP 2 loses nothing else.
        self.assertEqual(self.graph.criticality(statement=self.k("ToyCorpus.EvenP 2")), set())

    def test_object_index(self) -> None:
        mentions = self.names(k for k, n in self.graph.statements.items() if "ToyCorpus.EvenP" in n["constants"])
        self.assertIn("∀ (n : Nat), ToyCorpus.EvenP n", mentions)
        self.assertIn("ToyCorpus.Supply 1 ∧ ToyCorpus.EvenP 2", mentions)

    def test_false_is_not_supplied(self) -> None:
        # false_of_cert {v} (cert : Cert v) : False: the certificate's type
        # mentions v and is not known to be inhabited, so the theorem gives no
        # reduction (defect #1).
        self.assertNotIn(self.k("False"), self.graph.supplied)
        self.assertIn("ReviewToy.false_of_cert", {row["producer"] for row in self.graph.existential})
        self.assertEqual(builder.kernel_status(self.graph, "ReviewToy.false_of_cert"), "conditional_on_schematic")

    def test_instance_binder_is_a_residual(self) -> None:
        # from_fact [MyFact P0] : P0 reduces P0 to MyFact P0, which is open.
        self.assertIn((self.k("ReviewToy.P0"), "ReviewToy.from_fact", "theorem",
                       (self.k("ReviewToy.MyFact ReviewToy.P0"),)), self.graph.reductions)
        self.assertNotIn(self.k("ReviewToy.P0"), self.graph.supplied)
        self.assertEqual(builder.kernel_status(self.graph, "ReviewToy.from_fact"), "conditional_on_open")

    def test_nonempty_statement(self) -> None:
        # Witness.bad (self : Witness): a closed data type not known to be
        # inhabited contributes the obligation Nonempty Witness.
        key = self.k("Nonempty ReviewToy.Witness")
        self.assertIn("ReviewToy.Witness.bad", self.graph.statements[key]["consumers"])
        self.assertEqual(self.graph.theorems["ReviewToy.Witness.bad"]["hypotheses"], [key])

    def test_open_data_rows_register_nothing(self) -> None:
        # from_witness leaves its Witness argument open and my_trans its middle
        # term: neither row is a reduction, and no residual of theirs becomes a
        # statement (defect #11).
        self.assertFalse([n["type"] for n in self.graph.statements.values() if "?_mvar" in (n["type"] or "")])
        self.assertNotIn(self.k("ReviewToy.P2 3"), self.graph.supplied)
        producers = {row["producer"] for row in self.graph.existential}
        self.assertTrue({"ReviewToy.from_witness", "ReviewToy.my_trans"} <= producers)

    def test_refutations(self) -> None:
        refuted = self.graph.refuted
        self.assertEqual(refuted[self.k("ReviewToy.Q 3")]["producer"], "ReviewToy.not_Q")
        self.assertEqual(refuted[self.k("ReviewToy.g 5 = 0")]["reading"], "ne_as_not")
        self.assertEqual(refuted[self.k("ReviewToy.R7 7")]["kind"], "kernel")
        # Z7 is refuted only through a_first : Z7 → R7 7 (defect #6).
        z7 = refuted[self.k("ReviewToy.Z7")]
        self.assertEqual((z7["kind"], z7["reaches"], z7["producers"]),
                         ("derived", self.k("ReviewToy.R7 7"), ["ReviewToy.a_first"]))
        for text in ("ReviewToy.Q 3", "ReviewToy.g 5 = 0", "ReviewToy.R7 7", "ReviewToy.Z7"):
            self.assertNotIn(self.k(text), self.graph.open)
            self.assertEqual(self.graph.status(self.k(text)), "refuted")
        vacuous = {name.split(".")[-1] for name, _ in self.graph.vacuous_theorems}
        self.assertEqual(vacuous, {"a_first", "b_second", "uses_Q3", "uses_g5"})
        self.assertEqual(self.graph.inconsistent, [])

    def test_alpha_variants_are_one_statement(self) -> None:
        hypotheses = {tuple(self.graph.theorems[f"ReviewToy.uses_s8_{s}"]["hypotheses"]) for s in "nmi"}
        self.assertEqual(len(hypotheses), 1)

    def test_idle_rows_can_be_left_out(self) -> None:
        graph = builder.Graph(builder.read_export(FIXTURE), include_battery=False, include_idle=False)
        graph.analyse()
        self.assertEqual(graph.idle, [])
        self.assertFalse([r for r in graph.reductions if r[2] == "idle"])


class ToyGraphWithIdle(unittest.TestCase):
    """Idle strengthenings on the toy, without the battery: a proof that never
    uses a hypothesis proves the stronger statement, and the kernel accepted
    each one the export lists."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.graph = builder.Graph(builder.read_export(FIXTURE), include_battery=False)
        cls.graph.analyse()
        cls.key = {}
        for key, node in cls.graph.statements.items():
            for text in [node["type"], *node.get("aliases", ())]:
                cls.key[text] = key

    def test_idle_rows(self) -> None:
        entries = {e["theorem"].split(".")[-1]: e for e in self.graph.idle}
        self.assertEqual(set(entries), {"fresh_of_open", "supply_ge", "supply_of_even", "uses_even_two",
                                        "uses_guarded", "uses_named"})
        # ∀ n, Fresh n is supplied only through fresh_of_open's idle row.
        fresh = self.key["∀ (n : Nat), ToyCorpus.Fresh n"]
        self.assertIn(fresh, self.graph.supplied)
        self.assertEqual(self.graph.reductions[self.graph.witness[fresh]][2], "idle")
        self.assertEqual(entries["fresh_of_open"]["dropped_open_without_idle"], [self.key["ToyCorpus.OpenQ"]])
        self.assertEqual(builder.kernel_status(self.graph, "ToyCorpus.fresh_of_open", after_idle=True),
                         "unconditional")

    def test_idle_strengthening_supplies_the_toy_target(self) -> None:
        # supply_of_even proves Supply n by rfl without using EvenP n, so the
        # kernel accepts ∀ n, Supply n outright: Target, which the producer
        # relation alone leaves open, is supplied, and OpenQ with it.
        for text in ("∀ (n : Nat), ToyCorpus.Supply n", "ToyCorpus.Target", "ToyCorpus.OpenQ"):
            self.assertIn(self.key[text], self.graph.supplied, text)
        self.assertEqual(self.graph.disguise_classes(), [])


class ToyGraphWithBattery(unittest.TestCase):
    def test_battery_supplies(self) -> None:
        graph = builder.Graph(builder.read_export(FIXTURE))
        graph.analyse()
        key = {}
        for k, node in graph.statements.items():
            for text in [node["type"], *node.get("aliases", ())]:
                key[text] = k
        # The battery proves ∀ n, EvenP n (= OpenQ); the iff then supplies Target.
        self.assertIn(key["ToyCorpus.OpenQ"], graph.supplied)
        self.assertIn(key["ToyCorpus.Target"], graph.supplied)
        self.assertEqual(graph.disguise_classes(), [])
        self.assertNotIn(key["∀ (n : Nat), n ≥ 7"], graph.supplied)
        # The battery refutes 3 ≥ 7, so supply_ge's instance at 3 is a dead route,
        # and nothing is both supplied and refuted.
        self.assertIn(key["3 ≥ 7"], graph.refuted)
        self.assertEqual(graph.inconsistent, [])
        self.assertTrue(any(row.get("kernel_checked") for row in graph.compositions_checked))
        # P0 unfolds to ∀ n, n = n + 1, which the battery refutes; from_fact
        # reduces P0 to MyFact P0, so that instance is refuted too.
        derived = graph.refuted[key["ReviewToy.MyFact ReviewToy.P0"]]
        self.assertEqual((derived["kind"], derived["reaches"]), ("derived", key["ReviewToy.P0"]))
        self.assertEqual(builder.kernel_status(graph, "ReviewToy.from_fact"), "conditional_on_refuted")
        self.assertNotIn(key["False"], graph.supplied)

    def test_projection_writes(self) -> None:
        projection, graph_payload = builder.build(FIXTURE, ROOT)
        self.assertEqual(projection["schema"], builder.SCHEMA)
        self.assertGreaterEqual(projection["summary"]["battery_closed_statements"], 2)
        self.assertEqual(projection["summary"]["disguise_classes"], 0)
        self.assertEqual(projection["summary"]["idle_theorems_kernel_checked"], 6)
        self.assertEqual(projection["source"]["export_imports"], builder.read_export(FIXTURE)[0].get("imports"))
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "a.json"
            gz = Path(tmp) / "a.json.gz"
            builder.write_outputs(projection, graph_payload, out, gz)
            again = Path(tmp) / "b.json.gz"
            builder.write_outputs(projection, graph_payload, out, again)
            self.assertEqual(gz.read_bytes(), again.read_bytes(), "graph output must be byte-stable")
            self.assertEqual(json.loads(out.read_text())["schema"], builder.SCHEMA)
            reloaded, _ = query.load(gz)
            fresh = builder.Graph(builder.read_export(FIXTURE))
            fresh.analyse()
            self.assertEqual(reloaded.supplied, fresh.supplied)
            self.assertEqual(set(reloaded.refuted), set(fresh.refuted))
            self.assertEqual(reloaded.disguise_classes(), fresh.disguise_classes())


# --------------------------------------------------------------------------
# Hand-made streams


class Binders(unittest.TestCase):
    def test_uninhabited_certificate_is_not_a_proof(self) -> None:
        # {v : ℕ} (cert : Cert v) : False, with and without the new fields.
        new = graph_of([theorem("T.false_of_cert", [data(0, "ℕ"), data(1, "Cert v", inhabited=False, closed=False)],
                                "False")])
        self.assertNotIn("False", new.supplied)
        old_binders = [{"i": 0, "name": "v", "kind": "data", "closed": True, "type": "ℕ"},
                       {"i": 1, "name": "cert", "kind": "data", "closed": False, "type": "Cert v"}]
        old = graph_of([theorem("T.false_of_cert", old_binders, "False")])
        self.assertNotIn("False", old.supplied)
        # An old export's data binder of a whitelisted type is assumed inhabited.
        plain = graph_of([theorem("T.zero", [{"i": 0, "name": "n", "kind": "data", "closed": True,
                                              "type": "ℕ → ℕ"}], "Z")])
        self.assertIn("Z", plain.supplied)

    def test_nonempty_residual(self) -> None:
        # not_universal (S : Seq) : ¬U needs a sequence: Nonempty Seq is a residual.
        rows = [theorem("T.not_universal", [data(0, "Seq", inhabited=False, nonempty="Nonempty Seq")], "¬U")]
        graph = graph_of(rows)
        self.assertEqual(graph.reductions, [("¬U", "T.not_universal", "theorem", ("Nonempty Seq",))])
        self.assertNotIn("¬U", graph.supplied)
        self.assertEqual(builder.kernel_status(graph, "T.not_universal"), "conditional_on_open")
        witnessed = graph_of([*rows, statement("Nonempty Seq"), match("Nonempty Seq", "T.seq_exists")])
        self.assertIn("¬U", witnessed.supplied)

    def test_instance_proposition_is_a_residual(self) -> None:
        graph = graph_of([theorem("T.from_fact", [hyp(0, "Fact P", kind="instance")], "P")])
        self.assertEqual(graph.reductions, [("P", "T.from_fact", "theorem", ("Fact P",))])
        self.assertNotIn("P", graph.supplied)
        schematic = graph_of([theorem("T.prime", [data(0, "ℕ"), hyp(1, "Fact p.Prime", closed=False,
                                                                       kind="instance")], "C")])
        self.assertEqual(schematic.reductions, [])
        self.assertEqual(builder.kernel_status(schematic, "T.prime"), "conditional_on_schematic")

    def test_open_data_rows_without_residual_keys(self) -> None:
        row = {"record": "match", "statement": "S", "producer": "T.trans", "reading": "conclusion",
               "status": "matched", "open_data": True,
               "residuals": [{"type": "a = ?m", "has_open_data": True}, {"type": "?m = b", "has_open_data": True}]}
        graph = graph_of([statement("S"), row])
        self.assertEqual(set(graph.statements), {"S"})
        self.assertEqual(graph.reductions, [])
        self.assertEqual(graph.existential[0]["residual_types"], ["a = ?m", "?m = b"])


class Refutation(unittest.TestCase):
    def rows(self) -> list[dict]:
        return [
            theorem("T.s", [], "S"),                          # S is supplied
            theorem("T.y_of_rs", [hyp(0, "R"), hyp(1, "S")], "Y"),
            theorem("T.r_of_q", [hyp(0, "Q")], "R"),
            theorem("T.y2_of_ac", [hyp(0, "A"), hyp(1, "C")], "Y2"),
            theorem("T.c_of_a", [hyp(0, "A")], "C"),
            theorem("T.goal", [hyp(0, "E")], "G"),
            theorem("T.goal_dead", [hyp(0, "Y")], "G"),
            refute("Y"), refute("Y2"),
        ]

    def test_backward_propagation(self) -> None:
        graph = graph_of(self.rows())
        # One unsupplied residual: R, then Q through R.
        self.assertEqual((graph.refuted["R"]["reaches"], graph.refuted["R"]["producers"]), ("Y", ["T.y_of_rs"]))
        self.assertEqual(graph.refuted["Q"]["reaches"], "R")
        # A supplies C and then Y2 through a two-residual reduction.
        self.assertEqual(graph.refuted["A"]["reaches"], "Y2")
        self.assertEqual(graph.refuted["A"]["producers"], ["T.c_of_a", "T.y2_of_ac"])
        self.assertNotIn("C", graph.refuted)  # C alone does not supply Y2
        self.assertEqual(graph.refuted["Y"]["kind"], "kernel")
        self.assertEqual(graph.open, {"C", "E", "G"})
        self.assertEqual(graph.status("R"), "refuted")
        for key in graph.open:
            self.assertFalse(graph.leverage(key) & set(graph.refuted))
        # G's route through the refuted Y is dead: its only bundle is {E}.
        self.assertEqual(graph.bundles("G"), ([["E"]], False))

    def test_projection_excludes_refuted(self) -> None:
        rows = [{**row, "module": "ErdosProblems.Erdos68.X"} if row["record"] == "theorem" else row
                for row in self.rows()]
        with tempfile.TemporaryDirectory() as tmp:
            projection, payload = builder.build(write_stream(Path(tmp), rows), Path(tmp))
            problem = projection["problems"]["68"]
            for card in problem["sinks"] + problem["highest_leverage"]:
                self.assertEqual(card["status"], "open")
            self.assertEqual({c["key"] for c in problem["refuted"]}, {"A", "Q", "R", "Y", "Y2"})
            self.assertEqual(projection["summary"]["refuted_statements"], 2)
            self.assertEqual(projection["summary"]["refuted_statements_derived"], 3)
            gz = Path(tmp) / "graph.json.gz"
            builder.write_outputs(projection, payload, Path(tmp) / "p.json", gz)
            graph, loaded = query.load(gz)
            packet = query.packet_markdown(graph, loaded, "68", 12)
            targets = packet.split("## 2.")[0]
            self.assertNotIn("`R`", targets.replace(" (refuted: this route is dead)", ""))
            self.assertIn("## Refuted statements", packet)
            self.assertEqual(query.statement_view(graph, loaded, "Q")["refutation"]["kind"], "derived")


class Bundles(unittest.TestCase):
    def test_route_through_an_ancestor(self) -> None:
        # T ← {A, B}, A ← N, T ← N, N ← {A, W}. {A, W} supplies N and hence T;
        # a memo keyed by node alone lost it after meeting N below A.
        graph = graph_of([theorem("T.t_ab", [hyp(0, "A"), hyp(1, "B")], "T"),
                          theorem("T.a_n", [hyp(0, "N")], "A"),
                          theorem("T.t_n", [hyp(0, "N")], "T"),
                          theorem("T.n_aw", [hyp(0, "A"), hyp(1, "W")], "N")])
        self.assertEqual(graph.bundles("T"), ([["N"], ["A", "B"], ["A", "W"]], False))

    def test_depth_limit_is_reported_and_singletons_found(self) -> None:
        chain = ["S", "L1", "L2", "L3", "L4", "L5", "N"]
        rows = [theorem(f"T.c{i}", [hyp(0, low)], high) for i, (high, low) in enumerate(zip(chain, chain[1:]))]
        rows += [theorem("T.direct", [hyp(0, "N")], "S"), theorem("T.nz", [hyp(0, "Z")], "N"),
                 theorem("T.pair", [hyp(0, "Z"), hyp(1, "W")], "S")]
        graph = graph_of(rows)
        bundles, truncated = graph.bundles("S")
        self.assertTrue(truncated)
        self.assertIn(["Z"], bundles)  # Z supplies N, which supplies S
        self.assertNotIn(["W", "Z"], bundles)  # absorbed by {Z}
        for bundle in bundles:
            for other in bundles:
                self.assertFalse(bundle != other and set(other) < set(bundle))


class Idle(unittest.TestCase):
    def test_statement_supplied_only_by_an_idle_row(self) -> None:
        rows = [theorem("T.c_of_h", [hyp(0, "H"), hyp(1, "K")], "C"), statement("H"), statement("K"),
                theorem("T.k", [], "K"), idle("T.c_of_h", [(0, "H")])]
        graph = graph_of(rows)
        self.assertIn("C", graph.supplied)
        head, producer, reading, residuals = graph.reductions[graph.witness["C"]]
        self.assertEqual((producer, reading, residuals), ("T.c_of_h", "idle", ("K",)))
        self.assertEqual(graph.idle[0]["dropped_open_without_idle"], ["H"])
        self.assertEqual(builder.kernel_status(graph, "T.c_of_h"), "conditional_on_open")
        self.assertEqual(builder.kernel_status(graph, "T.c_of_h", after_idle=True), "conditional_on_supplied")
        without = graph_of(rows, include_idle=False)
        self.assertNotIn("C", without.supplied)

    def test_unchecked_and_schematic_idle_rows(self) -> None:
        rows = [theorem("T.c_of_h", [hyp(0, "H")], "C"), idle("T.c_of_h", [(0, "H")], kernel_checked=False),
                theorem("T.d_of_hn", [data(0, "ℕ"), hyp(1, "H"), hyp(2, "P n", closed=False)], "D"),
                idle("T.d_of_hn", [(1, "H")])]
        graph = graph_of(rows)
        self.assertNotIn("C", graph.supplied)
        self.assertEqual(graph.idle_unchecked, 1)
        self.assertEqual(graph.idle[0]["reason"], "an obligation that mentions another binder remains")
        self.assertNotIn("D", graph.supplied)

    def test_keyed_stronger_statement_is_supplied(self) -> None:
        rows = [theorem("T.fresh", [hyp(0, "OpenQ"), data(1, "ℕ")], None),
                idle("T.fresh", [(0, "OpenQ")], key="∀ n, Fresh n")]
        graph = graph_of(rows)
        self.assertIn("∀ n, Fresh n", graph.supplied)
        self.assertEqual(graph.idle[0]["reason"], "conclusion mentions a binder")


class Build(unittest.TestCase):
    def test_problem_views_and_macros(self) -> None:
        # One open hypothesis attributed to a problem used to crash build()
        # (defect #4); the macro region carries every total.
        rows = [theorem("ErdosProblems.Erdos68.Foo.bar", [hyp(0, "P68")], "Q68", module="ErdosProblems.Erdos68.Foo"),
                statement("P68"), statement("Q68", "conclusion"),
                idle("ErdosProblems.Erdos68.Foo.bar", [(0, "P68")])]
        with tempfile.TemporaryDirectory() as tmp:
            projection, _ = builder.build(write_stream(Path(tmp), rows), Path(tmp))
        self.assertIn("68", projection["problems"])
        self.assertEqual(projection["summary"]["theorem_modules"], 1)
        self.assertEqual(projection["summary"]["idle_dropping_open"], 1)
        self.assertEqual(projection["idle"][0]["dropped"][0]["open_without_idle"], True)
        region = builder.paper_macro_region(projection)
        for macro in ("AGTheorems", "AGModules", "AGConditional", "AGStatements", "AGSupplied", "AGOpen",
                      "AGReductions", "AGImplications", "AGDisguiseClasses", "AGLargestDisguise",
                      "AGCompositions", "AGKernelCompositions", "AGPaperCompositions", "AGBatteryClosed",
                      "AGBatteryTried", "AGBudgetExhausted", "AGRefuted", "AGRefutedDerived", "AGBarriers",
                      "AGBarriersInGraph", "AGVacuous", "AGLabelDisagreements", "AGIdle", "AGIdleOpen"):
            self.assertIn(rf"\newcommand{{\{macro}}}", region)

    def test_semantic_audit(self) -> None:
        # conditional_implication nodes: one whose evidence has only schematic
        # hypotheses (consistent, defect #5), one whose evidence is
        # unconditional, and one whose open hypothesis the proof never uses.
        rows = [theorem("T.schematic", [data(0, "ℕ"), hyp(1, "Open n", closed=False)], None),
                theorem("T.plain", [], "Plain"),
                theorem("T.idle", [hyp(0, "Open")], "Concl"), idle("T.idle", [(0, "Open")])]
        nodes = [{"id": f"n.{name}", "logical_class": "conditional_implication", "problem": "68",
                  "evidence": [{"module": "M.lean", "line": line}]}
                 for line, name in ((1, "schematic"), (2, "plain"), (3, "idle"))]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "docs").mkdir()
            (root / "docs" / "lean_dependency_index.json").write_text(json.dumps({"nodes": [
                {"handle": f"T.{name}", "source_ref": f"lean/M.lean:{line}"}
                for line, name in ((1, "schematic"), (2, "plain"), (3, "idle"))]}), encoding="utf-8")
            with gzip.open(root / "docs" / "semantic_corpus.json.gz", "wt", encoding="utf-8") as handle:
                json.dump({"statement_nodes": nodes}, handle)
            audit = builder.audit_authored_layers(graph_of(rows), root)
        verdicts = {row["node"]: row["verdict"] for row in audit["semantic_logical_class"]["disagreements"]}
        self.assertEqual(verdicts, {"n.plain": "conditional_label_but_no_open_kernel_hypothesis",
                                    "n.idle": "conditional_label_but_proof_uses_no_open_hypothesis"})

    def test_transfer_uses_the_statements_own_attribution(self) -> None:
        # A problem-68 lemma supplies a statement only problem 257 states
        # (defect #9: the producer's problem used to be added to the statement's).
        rows = [theorem("ErdosProblems.Erdos257.Use.consumer", [hyp(0, "S257")], "C257",
                        module="ErdosProblems.Erdos257.Use"),
                theorem("ErdosProblems.Erdos68.Lib.lemma68", [data(0, "ℕ")], None, module="ErdosProblems.Erdos68.Lib"),
                statement("S257"), match("S257", "ErdosProblems.Erdos68.Lib.lemma68")]
        with tempfile.TemporaryDirectory() as tmp:
            projection, payload = builder.build(write_stream(Path(tmp), rows), Path(tmp))
            gz = Path(tmp) / "graph.json.gz"
            builder.write_outputs(projection, payload, Path(tmp) / "p.json", gz)
            graph, loaded = query.load(gz)
        result = query.cmd_transfer(graph, loaded, argparse.Namespace(limit=10))
        self.assertEqual(result["cross_problem_reductions"], 1)
        self.assertEqual((result["rows"][0]["producer_problem"], result["rows"][0]["statement_problems"]),
                         ("68", ["257"]))

    def test_criticality_refuses_ambiguous_names(self) -> None:
        rows = [theorem("A.lemma", [], "X"), theorem("B.lemma", [], "Y")]
        with tempfile.TemporaryDirectory() as tmp:
            projection, payload = builder.build(write_stream(Path(tmp), rows), Path(tmp))
            gz = Path(tmp) / "graph.json.gz"
            builder.write_outputs(projection, payload, Path(tmp) / "p.json", gz)
            graph, loaded = query.load(gz)
        with self.assertRaises(SystemExit):
            query.cmd_criticality(graph, loaded, argparse.Namespace(target="lemma", limit=5))
        self.assertEqual(query.cmd_criticality(graph, loaded, argparse.Namespace(target="A.lemma", limit=5))
                         ["theorem"], "A.lemma")

    def test_freshness_compares_the_lean_tree(self) -> None:
        current = git_lean_tree()
        if current is None:
            self.skipTest("no git checkout with a lean/ tree")
        with tempfile.TemporaryDirectory() as tmp:
            path = write_stream(Path(tmp), [theorem("T.x", [], "X")])
            (Path(tmp) / builder.LEAN_TREE_FILE).write_text(current + "\n", encoding="utf-8")
            (Path(tmp) / builder.SOURCE_REVISION_FILE).write_text("0" * 40 + "\n", encoding="utf-8")
            _, payload = builder.build(path, Path(tmp))
            self.assertEqual(payload["source"]["lean_tree"], current)
            self.assertEqual(payload["source"]["source_revision"], "0" * 40)
            self.assertNotIn("lean_source_fingerprint", payload["source"])
            self.assertEqual(query.freshness(payload)["state"], "current")
            _, stale = builder.build(path, Path(tmp), lean_tree="1" * 40)
            self.assertEqual(query.freshness(stale)["state"], "stale")
            (Path(tmp) / builder.LEAN_TREE_FILE).unlink()
            _, unknown = builder.build(path, Path(tmp))
            self.assertIsNone(unknown["source"]["lean_tree"])
            self.assertEqual(query.freshness(unknown, Path(tmp))["state"], "unknown")


if __name__ == "__main__":
    unittest.main()
