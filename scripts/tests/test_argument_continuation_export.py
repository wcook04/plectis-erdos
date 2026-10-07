#!/usr/bin/env python3
"""Toy-corpus test for ``scripts/export_argument_continuations.lean``.

The exporter normally imports both corpus libraries. This test rewrites its
import header to core Lean, inserts a small corpus in namespace ``ToyCorpus``
at the ``@@TEST_DECLARATIONS@@`` marker, runs Lean once, and checks the
producer relation it emits against hand-computed expectations:

* a closed statement supplied outright, and one supplied with a residual;
* a universally quantified statement supplied under ``intro`` with the
  residual closed back over the bound variable;
* a guarded statement whose producer premise is discharged by the guard;
* an ``↔`` read in both directions, so each side reduces to the other (a
  disguise the graph builder must detect);
* an ``∧`` component supplied outright;
* the idle-hypothesis pass: a proof that never uses a hypothesis, with the
  stronger statement accepted by the kernel;
* the used-consequence pass (namespace ``UseToy``): a proof that uses a named
  input only through a lemma, a universal hypothesis at one instance, one
  conjunct, and an input whose used instance is false.

Namespace ``ReviewToy`` holds the shapes an adversarial review of the
exporter found mishandled, all without ``sorry``: a disequation producer that
must instantiate and refute an equation, a plain negation that must refute,
a propositional instance binder, a data binder carrying an impossible proof
(which must not count as unconditional), an antecedent first seen as a
conclusion, bound-variable renamings of one statement, an unusable match that
must not hide a leaf from the battery, and the generated lemmas of a
structure (which are not arguments of the corpus).

It needs a Lean toolchain (``lake env lean``); without one it exits 0 with a
skip line, because the no-Lean CI jobs cannot run it and the Lean build job
runs it for real.
"""

from __future__ import annotations

import _test_bootstrap  # noqa: F401

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXPORTER = ROOT / "scripts" / "export_argument_continuations.lean"

TOY = r"""
namespace ToyCorpus

def Supply (n : Nat) : Prop := n = n
def EvenP (n : Nat) : Prop := n % 2 = 0 ∨ n % 2 = 1
def Target : Prop := ∀ n : Nat, Supply n
def OpenQ : Prop := ∀ n : Nat, EvenP n

theorem supply_three : Supply 3 := rfl
theorem supply_of_even (n : Nat) (_h : EvenP n) : Supply n := rfl
theorem supply_ge (n : Nat) (_h : n ≥ 7) : Supply n := rfl
theorem open_iff_target : OpenQ ↔ Target :=
  ⟨fun _ _ => rfl, fun _ n => by unfold EvenP; omega⟩
theorem both : Supply 1 ∧ EvenP 2 := ⟨rfl, Or.inl rfl⟩

theorem uses_supply_three (h : Supply 3) : Supply 3 := h
theorem uses_universal (h : ∀ n : Nat, Supply n) : Target := h
theorem uses_guarded (_h : ∀ n : Nat, n ≥ 7 → Supply n) : True := trivial
theorem uses_guarded_nine (_h : ∀ n : Nat, n ≥ 9 → Supply n) : True := trivial
theorem uses_even_two (_h : EvenP 2) : True := trivial
theorem uses_target (h : Target) : OpenQ := open_iff_target.mpr h
theorem schematic (n : Nat) (h : Supply n) : Supply n := h

def Named : Prop := ∀ n : Nat, Supply n
theorem uses_named (_h : Named) : True := trivial
theorem named_of_even (h : ∀ n : Nat, EvenP n) : Named := fun n => supply_of_even n (h n)

def Fresh (n : Nat) : Prop := n = n
theorem fresh_of_open (_h : OpenQ) : ∀ n : Nat, Fresh n := fun _ => rfl

end ToyCorpus

namespace ReviewToy

def g (n : Nat) : Nat := n + 1
theorem g_ne (n : Nat) : g n ≠ 0 := Nat.succ_ne_zero n
theorem uses_g3 (h : g 3 ≠ 0) : g 3 ≠ 0 ∧ True := ⟨h, trivial⟩
theorem uses_g5 (h : g 5 = 0) : g 5 = 0 ∧ True := ⟨h, trivial⟩

def Q (n : Nat) : Prop := n < n
theorem not_Q (n : Nat) : ¬ Q n := Nat.lt_irrefl n
theorem uses_Q3 (h : Q 3) : Q 3 ∧ True := ⟨h, trivial⟩

class MyFact (p : Prop) : Prop where
  out : p
def P0 : Prop := ∀ n : Nat, n = n + 1
theorem from_fact [h : MyFact P0] : P0 := h.out

structure Witness where
  n : Nat
  bad : n < 0
def P2 (k : Nat) : Prop := k = k + 1
theorem from_witness (k : Nat) (w : Witness) : P2 k := absurd w.bad (Nat.not_lt_zero _)
theorem uses_P2 (h : P2 3) : P2 3 ∧ True := ⟨h, trivial⟩

structure Cert (v : Nat) where
  q : Nat
  small : q < 0
theorem false_of_cert {v : Nat} (cert : Cert v) : False := absurd cert.small (Nat.not_lt_zero _)

def R7 (n : Nat) : Prop := n < n
def Z7 : Prop := 7 < 7
theorem a_first (h : Z7) : R7 7 := h
theorem b_second (h : R7 7) : R7 7 ∧ True := ⟨h, trivial⟩
theorem not_R7_and (n : Nat) : ¬ R7 n ∧ True := ⟨Nat.lt_irrefl n, trivial⟩

def S8 (n : Nat) : Prop := n = n
theorem uses_s8_n (h : ∀ n, S8 n) : (∀ n, S8 n) ∧ True := ⟨h, trivial⟩
theorem uses_s8_m (h : ∀ m, S8 m) : (∀ m, S8 m) ∧ True := ⟨h, trivial⟩
theorem uses_s8_i (h : ∀ {n}, S8 n) : (∀ n, S8 n) ∧ True := ⟨fun _ => h, trivial⟩

theorem my_trans (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := h1 ▸ h2
theorem uses_225 (h : (2 : Nat) + 2 = 5) : (2 : Nat) + 2 = 5 ∧ True := ⟨h, trivial⟩

end ReviewToy

namespace UseToy

def dbl : Nat → Nat
  | 0 => 0
  | n + 1 => dbl n + 2
theorem dbl_eq (n : Nat) : dbl n = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [dbl, ih]; omega

/-- An open named input: no theorem proves it and the battery cannot. -/
def Strong : Prop := ∀ n : Nat, dbl n = 2 * n ∧ ∃ m, dbl m = m + 1
/-- The part of it the argument below needs, which a theorem proves by
induction (so the battery, which does not induct, cannot). -/
def Weak : Prop := ∀ n : Nat, dbl n = 2 * n
def Goal : Prop := ∀ n : Nat, dbl n ≤ 2 * n + 1

theorem weak_of_strong (h : Strong) : Weak := fun n => (h n).1
theorem weak_holds : Weak := dbl_eq
/-- Proved from the named input, through `weak_of_strong` only. -/
theorem goal_of_strong (h : Strong) : Goal :=
  fun n => Nat.le_succ_of_le (Nat.le_of_eq (weak_of_strong h n))

def Fam (n : Nat) : Prop := n + 0 = n
/-- Uses the universal hypothesis at one instance. -/
theorem fam_three (h : ∀ n : Nat, Fam n) : Fam 3 ∧ True := ⟨h 3, trivial⟩
/-- Uses one component of a conjunction. -/
theorem right_part (h : Strong ∧ Weak) : Weak ∧ True := ⟨h.2, trivial⟩
/-- Uses the hypothesis as it stands. -/
theorem uses_all (h : Strong) : Strong ∧ True := ⟨h, trivial⟩
/-- The weakened hypothesis sits between other binders. -/
theorem mixed (n : Nat) (h : Strong) (k : Nat) (hk : k = n) : dbl k ≤ 2 * n + 1 :=
  hk ▸ Nat.le_succ_of_le (Nat.le_of_eq (weak_of_strong h k))

/-- An input whose one used instance is false, so the input is refuted. -/
def Bad : Prop := ∀ f : Nat → Nat, f 0 = f 1
theorem odd_of_bad (h : Bad) : Nat.succ 0 = Nat.succ 1 ∧ True := ⟨h Nat.succ, trivial⟩

end UseToy
"""


def toy_source() -> str:
    source = EXPORTER.read_text(encoding="utf-8")
    header = "import Erdos249257\nimport ErdosProblems\nimport Lean\n"
    if not source.startswith(header):
        raise SystemExit("exporter header changed; update the toy test")
    # Core Lean only: the battery parses its scripts against the environment
    # and skips the Mathlib tactics a core-only toy lacks.
    source = "import Lean\n" + source[len(header):]
    marker = "-- @@TEST_DECLARATIONS@@"
    if marker not in source:
        raise SystemExit("exporter lost its test-declaration marker")
    return source.replace(marker, TOY)


def lean_command(path: Path) -> list[str] | None:
    override = os.environ.get("PLECTIS_TEST_LEAN_COMMAND")
    if override:
        return [*override.split(), str(path)]
    lake = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
    if not Path(lake).exists():
        return None
    return [lake, "env", "lean", str(path)]


def run_export() -> list[dict]:
    with tempfile.TemporaryDirectory(prefix="continuation-export-test-") as tmp:
        tmpdir = Path(tmp)
        lean_file = tmpdir / "ToyContinuationExport.lean"
        out_file = tmpdir / "export.jsonl"
        lean_file.write_text(toy_source(), encoding="utf-8")
        command = lean_command(lean_file)
        if command is None:
            print("SKIP: no Lean toolchain for the toy continuation export")
            raise SystemExit(0)
        env = dict(os.environ)
        env["PLECTIS_CONTINUATION_EXPORT_FILE"] = str(out_file)
        env["PLECTIS_CONTINUATION_NAME_PREFIXES"] = "ToyCorpus,ReviewToy,UseToy"
        completed = subprocess.run(
            command, cwd=os.environ.get("PLECTIS_TEST_LEAN_CWD", str(ROOT)),
            env=env, text=True, capture_output=True, timeout=900,
        )
        if completed.returncode != 0:
            sys.stderr.write(completed.stdout[-6000:] + completed.stderr[-6000:])
            raise SystemExit(f"toy export failed with exit {completed.returncode}")
        keep = os.environ.get("PLECTIS_TEST_KEEP_EXPORT")
        if keep:
            shutil.copyfile(out_file, keep)
        return [json.loads(line) for line in out_file.read_text(encoding="utf-8").splitlines() if line.strip()]


def main() -> int:
    rows = run_export()
    theorems = {r["name"]: r for r in rows if r["record"] == "theorem"}
    statements = {r["key"]: r for r in rows if r["record"] == "statement"}
    by_type = {r["type"]: r["key"] for r in statements.values()}
    matches = [r for r in rows if r["record"] == "match"]
    summary = [r for r in rows if r["record"] == "summary"][0]

    def supplied(statement_type: str) -> dict[str, list[str]]:
        key = by_type.get(statement_type)
        if key is None:
            raise AssertionError(f"statement not discovered: {statement_type!r}; have {sorted(by_type)}")
        out: dict[str, list[str]] = {}
        for m in matches:
            if m["statement"] == key and m["status"] == "matched":
                out.setdefault(m["producer"].split(".")[-1] + ":" + m["reading"], []).extend(
                    sorted(r["type"] for r in m["residuals"])
                )
        return out

    failures: list[str] = []

    def expect(condition: bool, message: str) -> None:
        if not condition:
            failures.append(message)

    # Telescope classification.
    guarded = theorems["ToyCorpus.uses_guarded"]["binders"][0]
    expect(guarded["kind"] == "hypothesis" and guarded["closed"], "guarded hypothesis must be closed")
    schematic = theorems["ToyCorpus.schematic"]["binders"]
    expect(schematic[0]["kind"] == "data", "schematic binder 0 is data")
    expect(schematic[1]["kind"] == "hypothesis" and not schematic[1]["closed"], "schematic hypothesis is not closed")
    expect(not theorems["ToyCorpus.schematic"]["conclusion"]["closed"], "schematic conclusion is not closed")

    s3 = supplied("ToyCorpus.Supply 3")
    expect(s3.get("supply_three:conclusion") == [], f"Supply 3 supplied outright: {s3}")
    expect(s3.get("supply_of_even:conclusion") == ["ToyCorpus.EvenP 3"], f"Supply 3 via EvenP 3: {s3}")

    universal = supplied("∀ (n : Nat), ToyCorpus.Supply n")
    expect(universal.get("supply_of_even:conclusion") == ["∀ (n : Nat), ToyCorpus.EvenP n"],
           f"universal statement reduces to universal EvenP: {universal}")

    guarded_supply = supplied("∀ (n : Nat), n ≥ 7 → ToyCorpus.Supply n")
    expect(guarded_supply.get("supply_ge:conclusion") == [],
           f"guard discharges the producer premise: {guarded_supply}")

    # A residual keeps the hypotheses that constrain its variables: the guard
    # `n ≥ 9` does not discharge `n ≥ 7` outright, and closing the residual over
    # `n` alone would state the false `∀ n, n ≥ 7`.
    nine = supplied("∀ (n : Nat), n ≥ 9 → ToyCorpus.Supply n")
    expect(nine.get("supply_ge:conclusion") == ["∀ (n : Nat), n ≥ 9 → n ≥ 7"],
           f"the residual keeps the guard on its variable: {nine}")

    target = supplied("ToyCorpus.Target")
    expect(target.get("open_iff_target:iff_mp_supplies_rhs") == ["ToyCorpus.OpenQ"],
           f"Target reduces to OpenQ through the iff: {target}")
    openq = supplied("ToyCorpus.OpenQ")
    expect(openq.get("open_iff_target:iff_mpr_supplies_lhs") == ["ToyCorpus.Target"],
           f"OpenQ reduces to Target through the iff: {openq}")

    unfolds = [r for r in rows if r["record"] == "unfold"]
    named_key = by_type.get("ToyCorpus.Named")
    universal_key = by_type.get("∀ (n : Nat), ToyCorpus.Supply n")
    expect(any(u["statement"] == named_key and u["unfolded"] == universal_key for u in unfolds),
           f"Named unfolds to the universal Supply statement: {unfolds}")
    named = supplied("ToyCorpus.Named")
    expect(named.get("named_of_even:theorem") is None, "theorem reductions are the builder's job")
    expect(named.get("named_of_even:conclusion") == ["∀ (n : Nat), ToyCorpus.EvenP n"],
           f"a producer whose conclusion is a named ∀-proposition still matches: {named}")

    even2 = supplied("ToyCorpus.EvenP 2")
    expect(even2.get("both:and_right") == [], f"EvenP 2 supplied by a conjunct: {even2}")

    compositions = [r for r in rows if r["record"] == "composition"]
    by_theorem = {c["theorem"].split(".")[-1]: c for c in compositions}
    guarded = by_theorem.get("uses_guarded")
    expect(guarded is not None and guarded["kernel_checked"],
           f"uses_guarded composes with supply_ge and the kernel accepts it: {compositions}")
    even = by_theorem.get("uses_even_two")
    expect(even is not None and even["kernel_checked"]
           and even["hypotheses"][0]["reading"] == "and_right",
           f"uses_even_two composes through a conjunct: {compositions}")
    expect("uses_target" not in by_theorem, "an open hypothesis must not compose")
    expect(summary["kernel_checked_compositions"] == sum(1 for c in compositions if c["kernel_checked"]),
           "summary counts kernel-checked compositions")

    battery = {statements[r["statement"]]["type"]: r["tactic"] for r in rows if r["record"] == "battery"}
    expect("ToyCorpus.EvenP 3" in battery, f"the battery closes EvenP 3 after unfolding: {battery}")
    expect("∀ (n : Nat), n ≥ 7" not in battery, f"the battery must not close a false statement: {battery}")
    expect("∀ (n : Nat), n ≥ 9 → n ≥ 7" in battery, f"the guarded residual is provable and the battery closes it: {battery}")
    expect("3 ≥ 7" not in battery, "the battery must not close 3 ≥ 7")
    refuted = {statements[r["statement"]]["type"] for r in rows if r["record"] == "battery_refutation"}
    expect("3 ≥ 7" in refuted, f"the battery refutes 3 ≥ 7: {refuted}")
    expect("ToyCorpus.EvenP 3" not in refuted, "a true statement must not be refuted")

    # Idle hypotheses: proofs that never use a hypothesis.
    idle = {r["theorem"].split(".")[-1]: r for r in rows if r["record"] == "idle"}
    openq_key = by_type.get("ToyCorpus.OpenQ")
    fresh = idle.get("fresh_of_open")
    expect(fresh is not None and fresh["kernel_checked"]
           and [d.get("key") for d in fresh["dropped"]] == [openq_key],
           f"fresh_of_open never uses its OpenQ hypothesis: {fresh}")
    for name in ("uses_named", "uses_even_two", "uses_guarded", "supply_of_even", "supply_ge"):
        expect(name in idle and idle[name]["kernel_checked"], f"{name} has an idle hypothesis: {sorted(idle)}")
    if "supply_of_even" in idle:
        expect("key" not in idle["supply_of_even"]["dropped"][0],
               "a schematic idle hypothesis carries no statement key")
    for name in ("schematic", "uses_target", "named_of_even", "uses_universal", "uses_supply_three",
                 "from_fact", "from_witness", "false_of_cert", "a_first", "uses_s8_i"):
        expect(name not in idle, f"{name} uses its hypothesis: {idle.get(name)}")
    expect(summary["idle_kernel_checked"] == sum(1 for r in idle.values() if r["kernel_checked"]),
           "summary counts kernel-checked idle theorems")

    # Review shapes.
    def rows_for(record: str, statement_type: str) -> list[dict]:
        key = by_type.get(statement_type)
        return [r for r in rows if r["record"] == record and r.get("statement") == key]

    g3 = [r for r in rows_for("match", "ReviewToy.g 3 ≠ 0") if r["status"] == "matched"]
    expect(any(r["producer"].endswith("g_ne") and not r["residuals"] and not r["open_data"] for r in g3),
           f"g_ne instantiates to supply g 3 ≠ 0: {g3}")
    g5 = [r for r in rows_for("refutation", "ReviewToy.g 5 = 0") if r["status"] == "matched"]
    expect(any(r["producer"].endswith("g_ne") and r["reading"] == "ne_as_not" and not r["residuals"] for r in g5),
           f"a proved disequation refutes the equation: {g5}")
    q3 = [r for r in rows_for("refutation", "ReviewToy.Q 3") if r["status"] == "matched"]
    expect(any(r["producer"].endswith("not_Q") and not r["residuals"] for r in q3),
           f"a plain negation refutes Q 3: {q3}")
    r7 = [r for r in rows_for("refutation", "ReviewToy.R7 7") if r["status"] == "matched"]
    expect(any(r["producer"].endswith("not_R7_and") for r in r7),
           f"an antecedent first enqueued as a conclusion is still refutation-searched: {r7}")
    p2 = [r for r in rows_for("match", "ReviewToy.P2 3") if r["producer"].endswith("from_witness")]
    expect(p2 and all(r["open_data"] for r in p2),
           f"a producer needing an uninhabited witness is not a usable match: {p2}")
    fact = theorems["ReviewToy.from_fact"]["binders"][0]
    expect(fact["kind"] == "instance" and fact["prop"] and fact["closed"] and fact.get("key"),
           f"a propositional instance binder is a closed antecedent: {fact}")
    witness = theorems["ReviewToy.from_witness"]["binders"][1]
    expect(witness["kind"] == "data" and witness["inhabited"] is False and witness.get("nonempty_key"),
           f"a closed data binder of unknown inhabitation becomes a Nonempty antecedent: {witness}")
    expect(theorems["ReviewToy.from_witness"]["binders"][0]["inhabited"] is True, "Nat is inhabited")
    cert = theorems["ReviewToy.false_of_cert"]["binders"][1]
    expect(cert["kind"] == "data" and cert["inhabited"] is False and not cert["closed"]
           and "nonempty_key" not in cert, f"a schematic data binder has no Nonempty antecedent: {cert}")
    s8 = {theorems[f"ReviewToy.uses_s8_{x}"]["binders"][0]["key"] for x in ("n", "m", "i")}
    expect(len(s8) == 1, f"renamed or implicit bound variables give one statement key: {s8}")
    expect("2 + 2 = 5" in refuted, f"an unusable match does not hide a leaf from the battery: {refuted}")
    generated = [n for n in theorems if n.split(".")[-1] in ("inj", "injEq", "sizeOf_spec")]
    expect(not generated, f"generated lemmas are not corpus arguments: {generated}")
    expect(all(len(k) == 32 and k[:8] != "00000000" for k in statements), "keys lead with the 64-bit hash")

    # Used consequences: what a proof derives from a hypothesis.
    weakenings = {r["theorem"].split(".")[-1]: r for r in rows if r["record"] == "weakening"}
    goal = weakenings.get("goal_of_strong")
    expect(goal is not None and goal["kernel_checked"]
           and [c["type"] for c in goal["consequences"]] == ["UseToy.Weak"]
           and goal["consequences"][0]["via"] == ["UseToy.weak_of_strong"]
           and goal["consequences"][0]["implication_kernel_checked"]
           and goal["hypothesis"] == by_type.get("UseToy.Strong"),
           f"goal_of_strong uses Strong only through weak_of_strong: {goal}")
    goal_supply = supplied("UseToy.Goal")
    expect(goal_supply.get("_argument_weakening_0:conclusion") == ["UseToy.Weak"],
           f"the weakened theorem supplies Goal from Weak: {goal_supply}")
    weak_supply = supplied("UseToy.Weak")
    expect(weak_supply.get("weak_holds:conclusion") == [], f"Weak is supplied outright: {weak_supply}")
    expect(any(c["theorem"].endswith("goal_of_strong._argument_weakening_0") and c["kernel_checked"]
               for c in compositions),
           f"the weakened theorem composes with weak_holds and the kernel accepts it: {compositions}")
    fam = weakenings.get("fam_three")
    expect(fam is not None and fam["kernel_checked"]
           and [c["type"] for c in fam["consequences"]] == ["UseToy.Fam 3"]
           and fam["consequences"][0]["via"] == ["hypothesis"],
           f"fam_three uses its universal hypothesis at 3 only: {fam}")
    right = weakenings.get("right_part")
    expect(right is not None and right["kernel_checked"]
           and [c["type"] for c in right["consequences"]] == ["UseToy.Weak"],
           f"right_part uses the second conjunct only: {right}")
    mixed = weakenings.get("mixed")
    expect(mixed is not None and mixed["kernel_checked"] and mixed["i"] == 1
           and [c["type"] for c in mixed["consequences"]] == ["UseToy.Weak"]
           and mixed["type"] == "∀ (n : Nat), UseToy.Weak → ∀ (k : Nat), k = n → UseToy.dbl k ≤ 2 * n + 1",
           f"a hypothesis between other binders is weakened in place: {mixed}")
    bad = weakenings.get("odd_of_bad")
    expect(bad is not None and bad["kernel_checked"]
           and [c["type"] for c in bad["consequences"]] == ["Nat.succ 0 = Nat.succ 1"],
           f"odd_of_bad uses Bad at Nat.succ only: {bad}")
    expect("Nat.succ 0 = Nat.succ 1" in refuted, f"the used instance of Bad is refuted: {refuted}")
    for name in ("uses_all", "weak_of_strong", "uses_target", "uses_universal", "named_of_even",
                 "uses_supply_three", "uses_g3", "a_first"):
        expect(name not in weakenings, f"{name} uses its hypothesis as it stands: {weakenings.get(name)}")
    expect(summary["weakened_theorems"] == sum(1 for r in weakenings.values() if r["kernel_checked"]) == 5,
           "summary counts the weakened theorems")
    expect(all(s["origin"] != "consequence" or s["key"] in {c["key"] for r in weakenings.values()
                                                              for c in r["consequences"]}
               for s in statements.values()), "consequence statements come from weakening rows")

    expect(summary["truncated"] is False, "toy export must not truncate")
    expect(summary["theorems"] == len(theorems), "summary theorem count")

    if failures:
        for failure in failures:
            print("FAIL:", failure)
        return 1
    print(f"ok: toy continuation export ({len(theorems)} theorems, {len(statements)} statements, "
          f"{sum(1 for m in matches if m['status'] == 'matched')} matches)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
