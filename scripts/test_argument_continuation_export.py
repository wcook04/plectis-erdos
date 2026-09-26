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
* an ``∧`` component supplied outright.

It needs a Lean toolchain (``lake env lean``); without one it exits 0 with a
skip line, because the no-Lean CI jobs cannot run it and the Lean build job
runs it for real.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
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
theorem uses_even_two (_h : EvenP 2) : True := trivial
theorem uses_target (h : Target) : OpenQ := open_iff_target.mpr h
theorem schematic (n : Nat) (h : Supply n) : Supply n := h

def Named : Prop := ∀ n : Nat, Supply n
theorem uses_named (_h : Named) : True := trivial
theorem named_of_even (h : ∀ n : Nat, EvenP n) : Named := fun n => supply_of_even n (h n)

end ToyCorpus
"""


def toy_source() -> str:
    source = EXPORTER.read_text(encoding="utf-8")
    header = "import Erdos249257\nimport ErdosProblems\nimport Lean\n"
    if not source.startswith(header):
        raise SystemExit("exporter header changed; update the toy test")
    # The battery quotes Mathlib tactics, so the toy needs them in scope; the
    # corpus imports all of Mathlib.
    source = ("import Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.Positivity\n"
              "import Mathlib.Tactic.Linarith\nimport Lean\n") + source[len(header):]
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
        env["PLECTIS_CONTINUATION_NAME_PREFIXES"] = "ToyCorpus"
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

    universal = supplied("∀ (n : ℕ), ToyCorpus.Supply n")
    expect(universal.get("supply_of_even:conclusion") == ["∀ (n : ℕ), ToyCorpus.EvenP n"],
           f"universal statement reduces to universal EvenP: {universal}")

    guarded_supply = supplied("∀ n ≥ 7, ToyCorpus.Supply n")
    expect(guarded_supply.get("supply_ge:conclusion") == [],
           f"guard discharges the producer premise: {guarded_supply}")

    target = supplied("ToyCorpus.Target")
    expect(target.get("open_iff_target:iff_mp_supplies_rhs") == ["ToyCorpus.OpenQ"],
           f"Target reduces to OpenQ through the iff: {target}")
    openq = supplied("ToyCorpus.OpenQ")
    expect(openq.get("open_iff_target:iff_mpr_supplies_lhs") == ["ToyCorpus.Target"],
           f"OpenQ reduces to Target through the iff: {openq}")

    unfolds = [r for r in rows if r["record"] == "unfold"]
    named_key = by_type.get("ToyCorpus.Named")
    universal_key = by_type.get("∀ (n : ℕ), ToyCorpus.Supply n")
    expect(any(u["statement"] == named_key and u["unfolded"] == universal_key for u in unfolds),
           f"Named unfolds to the universal Supply statement: {unfolds}")
    named = supplied("ToyCorpus.Named")
    expect(named.get("named_of_even:theorem") is None, "theorem reductions are the builder's job")

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
    expect("∀ (n : ℕ), n ≥ 7" not in battery, f"the battery must not close a false statement: {battery}")
    expect("3 ≥ 7" not in battery, "the battery must not close 3 ≥ 7")

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
