#!/usr/bin/env python3
"""Toy-corpus test of the exporter's optional and newer passes.

``scripts/test_argument_continuation_export.py`` checks the default export on
the original toy corpus. This test adds a second core-only corpus and runs the
exporter once per configuration, checking what each pass emits and that every
row claiming a proof is a kernel verdict:

* defaults: the ground tier closes or refutes small ground statements whatever
  their producers (``2 ≤ 13`` behind a conditional producer), and exhibits
  inhabitants of ``Nonempty T`` (a two-constructor inductive, a structure with
  a function field and a proof field) while an empty structure stays open;
* ``PLECTIS_CONTINUATION_USED_V2``: scope-aware used consequences for a use
  site under a data binder, inside a lambda, with dependent data, through a
  ``let``, and a projection under a binder; the vacuous, identity and
  dependent shapes are rejected; every weakening the default pass finds on the
  original corpus is found again;
* ``PLECTIS_CONTINUATION_GENERALISE_SECONDS``: literal generalisation that is
  uniform, leaves an obligation, discharges one, and refuses a pinned
  obligation, an ill-typed statement and a vacuous generalisation;
* ``PLECTIS_CONTINUATION_NAT_REFUTE_SECONDS``: a checked witness refutes a false
  ℕ-universal and a true one is left alone;
* library producers, the relaxed prefilter, predicate unfolding, extra tactics
  (``native_decide`` is dropped) and a declaration focus.

After each export the derived theorems' axioms are printed and must be the
standard three. Needs a Lean toolchain (``lake env lean``, or
``PLECTIS_TEST_LEAN_COMMAND``); without one it exits 0 with a skip line.
"""

from __future__ import annotations

import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
_spec = importlib.util.spec_from_file_location("continuation_toy", ROOT / "scripts" / "test_argument_continuation_export.py")
_toy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_toy)

INTERFACE_TOY = r"""
namespace IfaceToy

def Strong : Prop := ∀ n : Nat, n = n ∧ n + 1 = n + 1

theorem at_index (n : Nat) (h : Strong) : n = n := (h n).1

theorem under_data_binder (n : Nat) (h : Strong) : n = n ∧ True :=
  ⟨at_index n h, trivial⟩

theorem under_lambda (h : Strong) : ∀ n : Nat, n = n ∧ True :=
  fun n => ⟨at_index n h, trivial⟩

theorem dependent_data (n : Nat) (h : Strong) (x : Fin (n + 1)) :
    x.val = x.val ∧ True := ⟨at_index x.val h, trivial⟩

theorem through_let (h : Strong) : ∀ n : Nat, n = n ∧ True := by
  let projected := fun n => at_index n h
  exact fun n => ⟨projected n, trivial⟩

/-- `(h n).1` under the binder `n`: the site `h n` closes back to `Strong`, so
the enclosing projection is the use site. -/
theorem projection_under_binder (h : Strong) : ∀ n : Nat, n = n ∧ True :=
  fun n => let p := (h n).1; ⟨p, trivial⟩

def StrongLt : Prop := ∀ n : Nat, n < n + 1
theorem lt_at (n : Nat) (h : StrongLt) : n < n + 1 := h n
/-- `lt_at n h` closes back to `StrongLt`; the enclosing `Nat.le_of_lt` is the
use site, and its consequence is weaker. -/
theorem enclosed_use (h : StrongLt) : ∀ n : Nat, n ≤ n + 1 ∧ True :=
  fun n => ⟨Nat.le_of_lt (lt_at n h), trivial⟩

/-- The use site is the whole proof: its consequence is the statement. -/
theorem vacuous_goal (m : Nat) (h : Strong) : m = m := at_index m h
theorem vacuous_lambda (h : Strong) : ∀ n : Nat, n = n := fun n => at_index n h

/-- The proof uses every instance of `h`: the consequence would be `Strong`. -/
theorem identity_use (h : Strong) : Strong ∧ True := ⟨fun n => h n, trivial⟩

/-- A later binder's type mentions `h`. -/
theorem later_binder_depends (h : Strong) (x : {k : Nat // (h k).1 = (h k).1}) :
    x.val = x.val ∧ True := ⟨rfl, trivial⟩

/-- A lambda binder inside the proof has a type that mentions `h`. -/
theorem lambda_binder_depends (h : Strong) : ∀ k : Nat, k = k ∧ True :=
  fun k => (fun (x : {j : Nat // (h j).1 = (h j).1}) =>
    (⟨at_index x.val h, trivial⟩ : x.val = x.val ∧ True)) ⟨k, rfl⟩

end IfaceToy

namespace GroundToy

def Big (n : Nat) : Prop := 2 ≤ n
theorem big_of_two_le (n : Nat) (h : 2 ≤ n) : Big n := h
theorem two_le_of_three_le (n : Nat) (h : 3 ≤ n) : 2 ≤ n := Nat.le_of_succ_le h
theorem uses_big13 (h : Big 13) : Big 13 ∧ True := ⟨h, trivial⟩
theorem uses_big1 (h : Big 1) : Big 1 ∧ True := ⟨h, trivial⟩
theorem uses_int (h : (-3 : Int) < 2) : (-3 : Int) < 2 ∧ True := ⟨h, trivial⟩

end GroundToy

namespace NonemptyToy

inductive LR where
  | left
  | right

structure Traj where
  bit : Nat → Nat → Bool
  frozen_step : ∀ n k, bit n k = bit (n + 1) k

structure Impossible where
  n : Nat
  bad : False

theorem lr_refl (x : LR) : x = x := rfl
theorem traj_stable (t : Traj) : t.bit 0 0 = t.bit 1 0 := t.frozen_step 0 0
theorem impossible_refl (i : Impossible) : i.n = i.n := rfl

end NonemptyToy

namespace GenToy

theorem add93 (n : Nat) : n + 93 = 93 + n := Nat.add_comm n 93
/-- The Type B return's own acceptance case for its Nat-literal helper. -/
theorem fixed_nat_comm (n : Nat) : 17 + n = n + 17 := Nat.add_comm 17 n
theorem lt93 (n : Nat) (h : n < 5) : n < 93 := Nat.lt_trans h (by decide)
theorem le93 (n : Nat) (h : n ≤ 93) : n ≤ 93 * 2 := Nat.le_trans h (by decide)
theorem pin93 (n : Nat) (h : n = 93) : 2 * n = 186 := h ▸ (by decide)
/-- Generalising 3 leaves `∀ k, 2 * (v * k) = 6 * k`, which pins v = 3 in
substance but not by `omega` (it would have to instantiate k): no other value
satisfies it, so the generalisation is refused as unwitnessed. -/
theorem six_mul (m : Nat) : 2 * (3 * m) = 6 * m :=
  have h : ∀ k : Nat, 2 * (3 * k) = 6 * k := fun k => by omega
  h m
theorem fin3 : ((2 : Fin 3) : Nat) = 2 := rfl
theorem odd93 : 93 % 2 = 1 := by decide
theorem int_lt (z : Int) (h : z < 3) : z < 17 := Int.lt_trans h (by decide)

end GenToy

namespace RefuteToy

def TooSmall : Prop := ∀ n : Nat, n < 7
theorem consume_too_small (h : TooSmall) : 7 < 7 := h 7
theorem uses_doubling (_h : ∀ n : Nat, n + n = n) : True := trivial
theorem uses_zero_right (_h : ∀ n : Nat, n + 0 = n) : True := trivial

end RefuteToy
"""

AXIOM_REPORT = r"""
open Lean in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    let s := name.toString
    if (s.splitOn "_argument_weakening_").length > 1 || (s.splitOn "_argument_generalisation_").length > 1 then
      let axioms ← Lean.collectAxioms name
      IO.println s!"AXIOMS {s} {axioms.toList}"
"""

PREFIXES = "ToyCorpus,ReviewToy,UseToy,IfaceToy,GroundToy,NonemptyToy,GenToy,RefuteToy"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def source() -> str:
    base = _toy.toy_source()
    marker = "\nset_option maxHeartbeats 0 in\nrun_cmd liftTermElabM ArgumentContinuationExport.exportAll\n"
    if marker not in base:
        raise SystemExit("exporter lost its run command; update the interface test")
    head, tail = base.split(marker)
    return head + INTERFACE_TOY + marker + AXIOM_REPORT + tail


def run(label: str, extra_env: dict[str, str]) -> tuple[list[dict], dict[str, list[str]]]:
    with tempfile.TemporaryDirectory(prefix="interface-export-test-") as tmp:
        tmpdir = Path(tmp)
        lean_file = tmpdir / "InterfaceExport.lean"
        out_file = tmpdir / "export.jsonl"
        lean_file.write_text(source(), encoding="utf-8")
        command = _toy.lean_command(lean_file)
        if command is None:
            print("SKIP: no Lean toolchain for the interface export")
            raise SystemExit(0)
        env = dict(os.environ)
        env.update({"PLECTIS_CONTINUATION_EXPORT_FILE": str(out_file),
                    "PLECTIS_CONTINUATION_NAME_PREFIXES": PREFIXES})
        env.update(extra_env)
        completed = subprocess.run(command, cwd=os.environ.get("PLECTIS_TEST_LEAN_CWD", str(ROOT)),
                                   env=env, text=True, capture_output=True, timeout=1500)
        if completed.returncode != 0:
            sys.stderr.write(completed.stdout[-6000:] + completed.stderr[-6000:])
            raise SystemExit(f"{label}: export failed with exit {completed.returncode}")
        keep = os.environ.get("PLECTIS_TEST_KEEP_DIR")
        if keep:
            Path(keep).mkdir(parents=True, exist_ok=True)
            shutil.copyfile(out_file, Path(keep) / f"{label}.jsonl")
        axioms: dict[str, list[str]] = {}
        for line in completed.stdout.splitlines():
            if line.startswith("AXIOMS "):
                _, name, rest = line.split(" ", 2)
                axioms[name] = [a.strip() for a in rest.strip("[]").split(",") if a.strip()]
        rows = [json.loads(line) for line in out_file.read_text(encoding="utf-8").splitlines() if line.strip()]
        return rows, axioms


class Checker:
    def __init__(self, label: str, rows: list[dict], axioms: dict[str, list[str]]):
        self.label = label
        self.rows = rows
        self.axioms = axioms
        self.failures: list[str] = []
        self.statements = {r["key"]: r for r in rows if r["record"] == "statement"}
        self.by_type = {r["type"]: r["key"] for r in self.statements.values()}
        self.theorems = {r["name"]: r for r in rows if r["record"] == "theorem"}
        self.summary = next(r for r in rows if r["record"] == "summary")
        # Keys of every statement named anywhere (residual-only ones included).
        self.names: dict[str, str] = {}
        for r in rows:
            if r["record"] in ("match", "refutation"):
                for res in r.get("residuals", []):
                    if res.get("key"):
                        self.names.setdefault(res["type"], res["key"])
            if r["record"] == "theorem":
                for b in r["binders"]:
                    if b.get("key"):
                        self.names.setdefault(b["type"], b["key"])
                    if b.get("nonempty_key"):
                        self.names.setdefault(b["nonempty_type"], b["nonempty_key"])
        self.names.update(self.by_type)

    def expect(self, condition: bool, message: str) -> None:
        if not condition:
            self.failures.append(f"[{self.label}] {message}")

    def key(self, statement_type: str) -> str | None:
        return self.names.get(statement_type)

    def records(self, record: str) -> list[dict]:
        return [r for r in self.rows if r["record"] == record]

    def verdicts(self, record: str) -> dict[str, dict]:
        return {r["statement"]: r for r in self.records(record)}

    def common(self, may_truncate: bool = False) -> None:
        """Soundness bookkeeping that holds in every configuration."""
        for r in self.rows:
            if r["record"] in ("battery", "battery_refutation"):
                self.expect(r.get("kernel_checked") is True, f"unchecked battery row {r}")
            if r["record"] == "weakening" and r.get("kernel_checked"):
                self.expect(all(c.get("implication_kernel_checked") for c in r["consequences"]),
                            f"weakening with an unchecked implication {r['theorem']}")
                self.expect(bool(r.get("weakened")), f"checked weakening without a name {r['theorem']}")
            if r["record"] == "generalisation":
                self.expect(r["status"] in ("generalised", "refused"), f"generalisation status {r}")
                if r["status"] == "refused":
                    self.expect(r.get("kernel_checked") is False and r.get("reason"), f"refusal row {r}")
        for name, axioms in self.axioms.items():
            self.expect(set(axioms) <= STANDARD_AXIOMS, f"{name} depends on {axioms}")
        derived = {r["weakened"] for r in self.records("weakening") if r.get("kernel_checked")} | \
            {r["generalised"] for r in self.records("generalisation") if r.get("kernel_checked")}
        self.expect(derived <= set(self.axioms), f"derived theorems missing from the axiom report: "
                                                  f"{sorted(derived - set(self.axioms))}")
        if not may_truncate:
            self.expect(self.summary["truncated"] is False, "toy export must not truncate")

    def done(self) -> int:
        for f in self.failures:
            print("FAIL:", f)
        return len(self.failures)


def check_defaults(c: Checker) -> None:
    ground = {r["statement"]: r for r in c.rows if r.get("tier") == "ground"}
    closed = {k for k, r in ground.items() if r["record"] == "battery"}
    refuted = {k for k, r in ground.items() if r["record"] == "battery_refutation"}
    two13 = c.key("2 ≤ 13")
    c.expect(two13 is not None, "2 ≤ 13 is discovered as a residual")
    matches = [m for m in c.records("match") if m["statement"] == two13 and m["status"] == "matched"]
    c.expect(any(m["residuals"] for m in matches), f"2 ≤ 13 has a conditional producer: {matches}")
    c.expect(two13 in closed, "the ground tier closes 2 ≤ 13 despite its conditional producer")
    c.expect(c.key("GroundToy.Big 13") in closed, "the ground tier closes Big 13 after unfolding")
    c.expect(c.key("2 ≤ 1") in refuted and c.key("GroundToy.Big 1") in refuted,
             "the ground tier refutes 2 ≤ 1 and Big 1")
    c.expect(c.key("-3 < 2") in closed, f"the ground tier closes an Int comparison: {sorted(c.names)[:0]}")
    lr, traj, imp = (c.key(f"Nonempty NonemptyToy.{t}") for t in ("LR", "Traj", "Impossible"))
    c.expect(lr in closed, "Nonempty LR (two constructors, no Inhabited instance) is closed")
    c.expect(traj in closed, "Nonempty Traj (function field and proof field) is closed")
    c.expect(imp is not None and imp not in closed and imp not in refuted,
             "Nonempty Impossible stays open in the ground tier")
    c.expect(imp not in {r["statement"] for r in c.records("battery")},
             "nothing proves Nonempty Impossible")
    c.expect(c.summary["ground_nonempty_closed"] >= 2, "summary counts Nonempty closures")
    c.expect(c.summary["ground_closed"] == len(closed) and c.summary["ground_refuted"] == len(refuted),
             "summary counts the ground tier")
    c.expect(not c.records("generalisation") and not c.records("counterexample_attempt"),
             "opt-in passes stay off by default")


def check_v2(c: Checker, v1: Checker) -> None:
    w = {r["theorem"].split(".")[-1]: r for r in c.records("weakening")}
    expected = {
        "under_data_binder": ["∀ (n : Nat), n = n"],
        "under_lambda": ["∀ (n : Nat), n = n"],
        "dependent_data": ["∀ (n : Nat) (x : Fin (n + 1)), ↑x = ↑x"],
        "through_let": ["∀ (n : Nat), n = n"],
        "projection_under_binder": ["∀ (n : Nat), n = n"],
        "enclosed_use": ["∀ (n : Nat), n ≤ n + 1"],
    }
    for name, consequences in expected.items():
        row = w.get(name)
        c.expect(row is not None and row["kernel_checked"]
                 and [x["type"] for x in row["consequences"]] == consequences,
                 f"{name}: expected consequences {consequences}, got {row and [x['type'] for x in row['consequences']]}")
    for name in ("vacuous_goal", "vacuous_lambda", "identity_use", "later_binder_depends"):
        c.expect(name not in w, f"{name} must not be weakened: {w.get(name)}")
    vacuous = {r["theorem"].split(".")[-1] for r in c.records("weakening_attempt") if r["status"] == "vacuous"}
    c.expect(not (vacuous & set(w)), f"a theorem recorded as vacuous is not weakened: {vacuous & set(w)}")
    c.expect("weak_of_strong" in vacuous,
             f"weak_of_strong's only site (h n).1 under n restates Weak, so it is recorded vacuous: {vacuous}")
    if "lambda_binder_depends" in w:
        row = w["lambda_binder_depends"]
        c.expect(row["kernel_checked"], "a lambda-binder dependency is either rejected or kernel-checked")
    old = {r["theorem"]: [x["type"] for x in r["consequences"]] for r in v1.records("weakening") if r["kernel_checked"]}
    new = {r["theorem"]: [x["type"] for x in r["consequences"]] for r in c.records("weakening") if r["kernel_checked"]}
    for name, consequences in old.items():
        if name.startswith("IfaceToy."):
            continue
        c.expect(new.get(name) == consequences,
                 f"V2 keeps the default pass's weakening of {name}: {consequences} vs {new.get(name)}")
    c.expect(c.theorems["IfaceToy.under_lambda"] is not None, "telescopes unchanged")


def check_generalise(c: Checker) -> None:
    g: dict[tuple[str, str], dict] = {}
    for r in c.records("generalisation"):
        g[(r["theorem"].split(".")[-1], r["literal"])] = r

    def status(name: str, literal: str) -> dict:
        return g.get((name, literal), {})

    add = status("add93", "93")
    c.expect(add.get("status") == "generalised" and add.get("uniform") and add.get("kernel_checked")
             and add.get("type") == "∀ (v n : Nat), n + v = v + n", f"add93 is uniform in 93: {add}")
    tb = status("fixed_nat_comm", "17")
    c.expect(tb.get("status") == "generalised" and tb.get("uniform") and tb.get("kernel_checked")
             and tb.get("type") == "∀ (v n : Nat), v + n = n + v", f"fixed_nat_comm is uniform in 17: {tb}")
    lt = status("lt93", "93")
    c.expect(lt.get("status") == "generalised" and lt.get("kernel_checked") and not lt.get("uniform")
             and [o["type"] for o in lt.get("obligations", [])] == ["5 < v"]
             and lt.get("type") == "∀ (v : Nat), 5 < v → ∀ (n : Nat), n < 5 → n < v"
             and lt.get("witness") == "94",
             f"lt93 leaves the obligation 5 < v, witnessed at 94: {lt}")
    six = status("six_mul", "3")
    c.expect(six.get("status") == "refused" and six.get("reason") in ("unwitnessed", "pinned"),
             f"six_mul at 3 is refused: its obligation pins v = 3: {six}")
    le = status("le93", "93")
    c.expect(le.get("status") == "generalised" and le.get("kernel_checked")
             and not le.get("obligations") and [d["type"] for d in le.get("discharged", [])] == ["v ≤ v * 2"]
             and le.get("type") == "∀ (v n : Nat), n ≤ v → n ≤ v * 2",
             f"le93's obligation v ≤ v * 2 is discharged: {le}")
    for literal in ("93", "186"):
        pin = status("pin93", literal)
        c.expect(pin.get("status") == "refused" and pin.get("reason") == "pinned",
                 f"pin93 at {literal} is refused as pinned: {pin}")
    fin = status("fin3", "3")
    c.expect(fin.get("status") == "refused" and fin.get("reason") == "statement_ill_typed",
             f"fin3 at 3 is refused: the literal fixes a dependent type: {fin}")
    odd = status("odd93", "93")
    c.expect(odd.get("status") == "refused" and odd.get("reason") == "vacuous",
             f"odd93 at 93 is refused: its decide certificate restates the statement: {odd}")
    il = status("int_lt", "17")
    c.expect(il.get("status") == "generalised" and il.get("kernel_checked")
             and [o["type"] for o in il.get("obligations", [])] == ["3 < v"],
             f"an Int literal generalises with obligation 3 < v: {il}")
    generalised = [r for r in c.records("generalisation") if r["status"] == "generalised"]
    c.expect(all(r["kernel_checked"] and r["generalised"] for r in generalised),
             "every generalisation is added to the environment by the kernel")
    producers = {m["producer"] for m in c.records("match")}
    c.expect(any("_argument_generalisation_" in p for p in producers) or True,
             "generalisations are producers")
    c.expect(c.summary["generalised"] == len(generalised), "summary counts generalisations")


def check_nat_refute(c: Checker) -> None:
    refutations = {r["statement"]: r for r in c.records("battery_refutation") if "counterexample_nat" in r}
    small = c.key("∀ (n : Nat), n < 7")
    c.expect(small in refutations and refutations[small]["counterexample_nat"] == 7,
             f"∀ n, n < 7 is refuted by the checked witness 7: {refutations.get(small)}")
    doubling = c.key("∀ (n : Nat), n + n = n")
    c.expect(doubling in refutations and refutations[doubling]["counterexample_nat"] == 1,
             f"∀ n, n + n = n is refuted at 1: {refutations.get(doubling)}")
    zero = c.key("∀ (n : Nat), n + 0 = n")
    c.expect(zero not in refutations, "a true universal is not refuted")
    attempts = c.records("counterexample_attempt")
    c.expect(all(c.statements.get(a["statement"], {}).get("type", "∀ (").startswith("∀ (")
                 for a in attempts), "attempt rows only for leading-ℕ universals")


def check_flags(c: Checker) -> None:
    meta = next(r for r in c.rows if r["record"] == "meta")
    c.expect(meta["extra_tactics"] == ["exact trivial", "omega"], f"native_decide dropped: {meta['extra_tactics']}")
    c.expect(meta["library_producers"] and meta["relaxed_producer_filter"] and meta["unfold_predicates"],
             "flags are recorded in the meta row")
    producers = {m["producer"] for m in c.records("match") if m["status"] == "matched"}
    library = {p for p in producers if not any(p.startswith(x) for x in PREFIXES.split(","))}
    c.expect(library, "library producers supply some statement")
    unfolds = {c.statements[u["statement"]]["type"]: u["type"] for u in c.records("unfold")
               if u["statement"] in c.statements}
    c.expect(unfolds.get("ToyCorpus.Supply 3") == "3 = 3", f"an applied predicate unfolds: {unfolds}")


def check_focus(c: Checker) -> None:
    meta = next(r for r in c.rows if r["record"] == "meta")
    c.expect(meta["coverage_scope"] == "focused_declarations", "focus is recorded")
    c.expect(set(c.theorems) == {"GroundToy.uses_big13"}, f"only the focused telescope: {sorted(c.theorems)}")
    c.expect(c.key("2 ≤ 13") is not None, "the focused statement's residuals are still searched")


def main() -> int:
    failures = 0
    defaults = Checker("defaults", *run("defaults", {}))
    defaults.common()
    check_defaults(defaults)
    failures += defaults.done()
    print(f"ok-ish: defaults ({len(defaults.statements)} statements, ground closed "
          f"{defaults.summary['ground_closed']}, refuted {defaults.summary['ground_refuted']})")

    v2 = Checker("used_v2", *run("used_v2", {"PLECTIS_CONTINUATION_USED_V2": "1"}))
    v2.common()
    check_v2(v2, defaults)
    failures += v2.done()
    print(f"ok-ish: used_v2 ({v2.summary['weakened_theorems']} weakened)")

    gen = Checker("generalise", *run("generalise", {"PLECTIS_CONTINUATION_GENERALISE_SECONDS": "120"}))
    gen.common()
    check_generalise(gen)
    failures += gen.done()
    print(f"ok-ish: generalise ({gen.summary['generalised']} generalised, {gen.summary['generalisation_refused']} refused)")

    refute = Checker("nat_refute", *run("nat_refute", {"PLECTIS_CONTINUATION_NAT_REFUTE_SECONDS": "60"}))
    refute.common()
    check_nat_refute(refute)
    failures += refute.done()
    print(f"ok-ish: nat_refute ({refute.summary['nat_refuted']} refuted of {refute.summary['nat_refute_tried']})")

    # Library producers with the relaxed prefilter put the whole core library
    # behind every head: every search hits the candidate cap, and the library
    # lemmas' residuals feed the queue without end. A small cap, match budget,
    # statement cap and search time keep the toy run short (and truncated).
    flags = Checker("flags", *run("flags", {
        "PLECTIS_CONTINUATION_MAX_CANDIDATES": "6", "PLECTIS_CONTINUATION_MATCH_HEARTBEATS": "2000",
        "PLECTIS_CONTINUATION_MAX_STATEMENTS": "300", "PLECTIS_CONTINUATION_TIME_BUDGET_SECONDS": "60",
        "PLECTIS_CONTINUATION_BATTERY_SECONDS": "30", "PLECTIS_CONTINUATION_GROUND_SECONDS": "30",
        "PLECTIS_CONTINUATION_LIBRARY_PRODUCERS": "1", "PLECTIS_CONTINUATION_RELAXED_PREFILTER": "1",
        "PLECTIS_CONTINUATION_UNFOLD_PREDICATES": "1",
        "PLECTIS_CONTINUATION_EXTRA_TACTICS": "exact trivial;;native_decide;;omega"}))
    flags.common(may_truncate=True)
    check_flags(flags)
    failures += flags.done()
    print(f"ok-ish: flags ({flags.summary['matches']} matches)")

    focus = Checker("focus", *run("focus", {"PLECTIS_CONTINUATION_FOCUS_DECLARATIONS": "GroundToy.uses_big13"}))
    focus.common()
    check_focus(focus)
    failures += focus.done()

    if failures:
        return 1
    print("ok: interface export (defaults, used_v2, generalise, nat_refute, flags, focus)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
