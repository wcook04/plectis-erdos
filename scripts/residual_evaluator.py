#!/usr/bin/env python3
"""Decide, with the kernel, whether a proof sketch reduced its target or renamed it.

Google DeepMind's AlphaProof Nexus paper reports in its failure analysis that its
evolutionary proof search "frequently offloaded a problem's core difficulty into a
single `sorry` within a helper lemma that reiterated the target statement in a
slightly different form", and that "explicitly prompting against this behavior
failed to prevent it". Its rating agents score sketches on, among other things,
"the plausibility of remaining goals".

That is a language model estimating a relation the kernel can sometimes decide.

Given a target proposition ``P`` and the residual obligations ``R_1 .. R_n`` a
sketch leaves unproved, this tool asks Lean three bounded questions:

    soundness    (⋀ R_i) → P      do the residuals suffice?
    laundering   P → (⋀ R_i)      is the residual the target again?
    refutation   ¬ (⋀ R_i)        is the residual outright false?

and, across a pair of sketches, one more:

    dominance    D_A → D_B        does A demand something logically stronger?

WHAT THIS IS NOT
----------------
This is not a proof-difficulty metric and not a score. Logical strength is not
computational difficulty: a stronger proposition can be easier because it has more
structure to exploit. The tool emits *vetoes* backed by kernel proofs, plus an
explicit abstention when the budget decides nothing.

The error asymmetry is deliberate and load-bearing. ``endpoint_equivalent`` is
reported only when Lean actually proves ``P → ⋀ R_i``, so a false accusation of
laundering is impossible. A sufficiently disguised restatement escapes into
``unknown_relation``. Missing a launderer is cheap; falsely rejecting a productive
representation change is not.

AUTHORITY
---------
Verdicts are derived from Lean's exit behaviour on the emitted probes. This module
must never author a verdict for a sketch. ``AuthoredVerdictError`` enforces that on
the fixture manifest: a manifest row may carry an *expected* verdict (it is a
labelled bench) but the evaluator must reach its own, and disagreement is reported
rather than reconciled.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Iterable

# --------------------------------------------------------------------------
# Verdict vocabulary
# --------------------------------------------------------------------------

#: The residual conjunction is provably equivalent to the target. The sketch
#: renamed the difficulty. Hard veto — this is the AlphaProof Nexus failure mode.
ENDPOINT_EQUIVALENT = "endpoint_equivalent"

#: The residual conjunction is provably false. The sketch rests on a
#: hallucinated "known result". Hard veto — the second reported failure mode.
RESIDUAL_REFUTED = "residual_refuted"

#: The residuals imply the target, no residual is equivalent to it, and none is
#: refuted. A candidate for real progress — NOT a proof that it is easier.
STRICT_DECOMPOSITION_CANDIDATE = "strict_decomposition_candidate"

#: The residuals do not visibly imply the target within budget. The sketch may be
#: incomplete rather than wrong; this is a warning, not a veto.
SKETCH_UNSOUND = "sketch_unsound"

#: The budget decided nothing. This is an abstention and must never be read as
#: progress.
UNKNOWN_RELATION = "unknown_relation"

VERDICTS = (
    ENDPOINT_EQUIVALENT,
    RESIDUAL_REFUTED,
    STRICT_DECOMPOSITION_CANDIDATE,
    SKETCH_UNSOUND,
    UNKNOWN_RELATION,
)

#: Hard vetoes. A sketch carrying one of these should not be ranked above a
#: sketch that carries none, whatever a rater thinks of its prose.
VETOES = frozenset({ENDPOINT_EQUIVALENT, RESIDUAL_REFUTED})


class AuthoredVerdictError(RuntimeError):
    """Raised when a manifest tries to supply a verdict instead of a label.

    A bench row may say what verdict it *expects* (``expect``); it may not say
    what the verdict *is*. The distinction is the whole point: if the evaluator
    could read its answer off the fixture, the bench would measure nothing.
    """


# --------------------------------------------------------------------------
# Tactic budget
# --------------------------------------------------------------------------

#: Fixed, ordered tactic ladder. Changing this changes every verdict, so it is
#: recorded in the receipt and treated as part of the evaluator's identity.
#: Ordered cheapest-first; `first` commits to the earliest success.
#:
#: The entries cover the shapes a sketch-to-target relation actually takes:
#: identity, symmetry, notation-level rewriting, universal instantiation,
#: base-plus-step induction, and small-witness refutation. It is a budget, not a
#: prover — everything it cannot close comes back as an abstention.
#:
#: Widening the ladder is not verdict-preserving. A newly-closed laundering probe
#: moves a sketch from `unknown_relation` to `endpoint_equivalent`, and a newly-
#: closed refutation probe overrides a laundering verdict. Every such move is a
#: correction backed by a kernel proof that was always available and merely out of
#: reach, but it is a change of verdict, and the budget id therefore belongs in
#: the receipt: two runs under different ladders are not comparable.
#:
#: The ladder must stay general. Tuning it against a specific bench until the
#: bench passes converts the benchmark into a record of its own tactic list.
TACTIC_LADDER: tuple[str, ...] = (
    # identity and trivial closure
    "exact fun h => h",
    "intro h; exact h",
    "intro h; simpa using h",
    # symmetry of a stated equality, pointwise
    "intro h; intro n; exact (h n).symm",
    "intro h; intro n; exact (h n)",
    # notation-level rewriting
    "intro h; intro n; simpa [pow_two, sq, Nat.mul_comm] using h n",
    "intro h; intro n; simpa [Finset.range_eq_Ico, Nat.add_comm, Nat.mul_comm] using h n",
    "intro h; simp_all [pow_two, sq, Finset.range_eq_Ico, Nat.add_comm, Nat.mul_comm]",
    # universal instantiation of a stronger statement
    "intro h; intro n; simpa using h 1 2 n",
    "intro h; intro n; simpa [Nat.mul_comm, Nat.mul_assoc] using h 1 2 n",
    # base case plus inductive step
    "intro h; obtain ⟨hb, hs⟩ := h; intro n; induction n with"
    " | zero => simpa using hb | succ k ih => simpa using hs k ih",
    "intro h; obtain ⟨hb, hs⟩ := h; intro n; induction n with"
    " | zero => exact hb | succ k ih => exact hs k ih",
    # Small-witness refutation. Instantiating a universal claim at a small value
    # and evaluating it is how a hallucinated "known result" dies.
    #
    # No alternative may contain a nested `by`. A `by` block inside a `first`
    # alternative elaborates eagerly; when it fails, `first` sees the enclosing
    # tactic succeed while the term quietly becomes `sorryAx`, so the probe reports
    # as decided and is not. Every refutation below therefore specialises into the
    # context and closes there.
    "intro h; have hx := h 0; simp at hx",
    "intro h; have hx := h 1; simp at hx",
    "intro h; have hx := h 2; simp at hx",
    "intro h; have hx := h 0; norm_num at hx",
    "intro h; have hx := h 1; norm_num at hx",
    "intro h; have hx := h 0; omega",
    "intro h; have hx := h 1; omega",
    "intro h; have hx := h 0; contradiction",
    "intro h; simpa using h 0",
    "intro h; simpa using h 1",
    # general proof search
    "intro h; omega",
    "tauto",
    "intro h; aesop",
    "aesop",
    "decide",
)

BUDGET_ID = "ladder_v3_independent"


def _attempt_lines(unfolds: Iterable[str], tactic: str, intros: Iterable[str] = ()) -> list[str]:
    """Render one tactic attempt as a standalone tactic block.

    Each (probe, tactic) pair gets its own declaration rather than becoming an
    alternative inside one `first | ... | ...` block. The `first` formulation was
    faster and wrong: `simpa` raises a nested elaboration error that `first` does
    not treat as a recoverable tactic failure, so the whole block aborts and the
    declaration is closed with `sorryAx`. Every alternative after the first risky
    one was therefore never tried, and probes reported as undecided when the proof
    was one line further down the ladder. Separate declarations cannot interfere.
    """
    lines: list[str] = []
    names = " ".join(sorted(set(unfolds)))
    if names:
        lines.append(f"  unfold {names}")
    bound = " ".join(intros)
    if bound:
        lines.append(f"  intro {bound}")
    lines.append(f"  {tactic}")
    return lines


class HarnessNotLiveError(RuntimeError):
    """Raised when the probe run cannot be trusted to have decided anything.

    The first version of this tool reported every probe as proved because the
    bench module failed to import: the resulting error landed on the import line,
    which no probe owned, so it was discarded and silence was read as success. A
    harness that returns universal success when nothing ran is worse than one that
    crashes, because it looks like a result.

    Two structural defences, both required to pass:

    * every Lean diagnostic must be attributable to a probe. An unattributed error
      means the file failed as a whole, and the run is void.
    * two control probes are emitted alongside the real ones. ``_control_true``
      must be proved and ``_control_false`` must fail. If the controls do not come
      back exactly that way, the harness is not discriminating and every other
      verdict in the run is meaningless.
    """


#: Emitted with every run. `_control_true` is trivially provable; `_control_false`
#: is unprovable within any budget. Their outcomes are checked, not reported.
CONTROL_PROBES: tuple[tuple[str, str, bool], ...] = (
    ("probe_control__true", "∀ n : ℕ, n = n", True),
    ("probe_control__false", "∀ n : ℕ, n = n + 1", False),
)


# --------------------------------------------------------------------------
# Manifest
# --------------------------------------------------------------------------


@dataclass
class Sketch:
    """One candidate proof sketch: a target and the obligations it leaves open."""

    sketch_id: str
    target: str
    residuals: list[str]
    #: What the bench author believes the evaluator should conclude. Compared
    #: against the derived verdict; never substituted for it.
    expect: str | None = None
    note: str = ""
    #: Binders the target and residuals share, as Lean source (`(n : ℕ) (h : P n)`).
    #: Every probe of the sketch is stated under them, so a relation between two
    #: sketches is decided pointwise, for the same `n` and `h`.
    binders: str = ""
    #: Constants to unfold before each tactic. Defaults to the target and residuals
    #: themselves, which a bench states as named propositions; a sketch with binders
    #: states applied terms, and names the constants to unfold here.
    unfold: list[str] | None = None

    def demand(self) -> str:
        """The residual conjunction, as a Lean term."""
        if len(self.residuals) == 1:
            return self.residuals[0]
        return "(" + " ∧ ".join(f"({r})" for r in self.residuals) + ")" if self.residuals else "True"

    def unfolds(self) -> list[str]:
        if self.unfold is not None:
            return list(self.unfold)
        return [] if self.binders.strip() else [self.target, *self.residuals]


def load_manifest(path: Path) -> tuple[str, list[Sketch]]:
    raw = json.loads(path.read_text())
    module = raw["module"]
    sketches: list[Sketch] = []
    for row in raw["sketches"]:
        if "verdict" in row:
            raise AuthoredVerdictError(
                f"sketch {row.get('sketch_id')!r} carries an authored 'verdict'. "
                "A bench row may declare 'expect'; the verdict is derived from Lean."
            )
        expect = row.get("expect")
        if expect is not None and expect not in VERDICTS:
            raise ValueError(
                f"sketch {row.get('sketch_id')!r} expects unknown verdict {expect!r}"
            )
        sketches.append(
            Sketch(
                sketch_id=row["sketch_id"],
                target=row["target"],
                residuals=list(row["residuals"]),
                expect=expect,
                note=row.get("note", ""),
                binders=row.get("binders", ""),
                unfold=row.get("unfold"),
            )
        )
    return module, sketches


# --------------------------------------------------------------------------
# Probe emission
# --------------------------------------------------------------------------

#: A named binder group `(x y : T)`, `{h : P x}` or `⦃…⦄`; instance brackets bind no name.
BINDER_GROUP = re.compile(r"[({⦃]\s*([^:(){}⦃⦄\[\]]+?)\s*:")

#: A probe name becomes a Lean declaration name, so it must be an identifier.
LEAN_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def binder_names(binders: str) -> list[str]:
    """Names a binder string introduces, in order: `(n : ℕ) {h : P n}` gives n, h."""
    return [name for group in BINDER_GROUP.findall(binders) for name in group.split()]


def close(statement: str, binders: str) -> str:
    """The statement under the sketch's binders, which every probe of the sketch shares."""
    return f"∀ {binders}, {statement}" if binders.strip() else statement


PROBE_MARK = re.compile(r"^probe_(?P<kind>soundness|laundering|refutation|dominance)__(?P<id>\S+)$")


@dataclass
class Probe:
    name: str
    kind: str
    subject: str
    statement: str
    unfolds: list[str]
    #: Binder names to introduce before each tactic.
    intros: list[str] = field(default_factory=list)


def build_probes(sketches: list[Sketch], *, cross: bool) -> list[Probe]:
    probes: list[Probe] = []
    for s in sketches:
        d = s.demand()
        names = binder_names(s.binders)
        probes.append(
            Probe(
                f"probe_soundness__{s.sketch_id}", "soundness", s.sketch_id,
                close(f"({d}) → ({s.target})", s.binders), s.unfolds(), names,
            )
        )
        # Laundering is asked per residual, in both directions, never of the
        # conjunction. `P → ⋀ R_i` holds for every correct decomposition — P
        # implies everything it entails — so testing the conjunction convicts a
        # valid base-plus-step split of the exact failure it is the opposite of.
        # A sketch launders when some single residual is equivalent to the target:
        # that residual is the target wearing another name, and the difficulty
        # never moved. A residual that is merely implied by the target, or merely
        # implies it, is doing real work in one direction.
        for k, r in enumerate(s.residuals):
            unfolds = [s.target, r] if s.unfold is None and not s.binders.strip() else s.unfolds()
            probes.append(
                Probe(f"probe_p2r{k}__{s.sketch_id}", f"p2r{k}", s.sketch_id,
                      close(f"({s.target}) → ({r})", s.binders), unfolds, names)
            )
            probes.append(
                Probe(f"probe_r2p{k}__{s.sketch_id}", f"r2p{k}", s.sketch_id,
                      close(f"({r}) → ({s.target})", s.binders), unfolds, names)
            )
        probes.append(
            Probe(
                f"probe_refutation__{s.sketch_id}", "refutation", s.sketch_id,
                close(f"¬ ({d})", s.binders) if not s.binders.strip() else f"¬ ({close(d, s.binders)})",
                s.residuals if s.unfold is None and not s.binders.strip() else s.unfolds(), [],
            )
        )
    if cross:
        # Dominance compares demands for the same target under the same binders:
        # `∀ ctx, D_A → D_B` says A asks for at least what B asks for, at every point.
        by_target: dict[tuple[str, str], list[Sketch]] = {}
        for s in sketches:
            by_target.setdefault((s.target, s.binders.strip()), []).append(s)
        for group in by_target.values():
            for a in group:
                for b in group:
                    if a.sketch_id == b.sketch_id:
                        continue
                    unfolds = ([*a.residuals, *b.residuals] if a.unfold is None and not a.binders.strip()
                               else sorted({*a.unfolds(), *b.unfolds()}))
                    probes.append(
                        Probe(
                            f"probe_dominance__{a.sketch_id}__over__{b.sketch_id}",
                            "dominance",
                            f"{a.sketch_id}>{b.sketch_id}",
                            close(f"({a.demand()}) → ({b.demand()})", a.binders),
                            unfolds, binder_names(a.binders),
                        )
                    )
    for probe in probes:
        if not LEAN_NAME.match(probe.name):
            raise ValueError(f"probe name {probe.name!r} is not a Lean identifier; "
                             "sketch ids must be letters, digits and underscores")
    return probes


def render_probe_file(module: str, probes: list[Probe], namespace: str) -> str:
    lines = [
        "-- GENERATED by residual_evaluator.py. Do not edit.",
        "-- Each theorem is one bounded question put to the kernel.",
        "-- A theorem that fails to elaborate means 'not decided within budget',",
        "-- never 'false'.",
        f"import {module}",
        "",
        f"open {namespace}",
        "",
    ]
    def emit(base: str, stmt: str, unfolds: list[str], intros: list[str]) -> None:
        # The axiom report follows its own theorem immediately. Collected at the
        # end of the file instead, none of them printed at all: Lean stops
        # emitting diagnostics once a file accumulates enough errors, and a probe
        # file is mostly failed attempts by construction. Interleaving means a
        # truncated run still reports every declaration it actually reached.
        for i, tac in enumerate(TACTIC_LADDER):
            lines.append(f"theorem {base}__t{i} : {stmt} := by")
            lines.extend(_attempt_lines(unfolds, tac, intros))
            lines.append(f"#print axioms {base}__t{i}")
            lines.append("")

    for p in probes:
        emit(p.name, p.statement, p.unfolds, p.intros)

    # Positive success signal. A `first | t1 | t2 | ...` block whose early
    # alternatives fail still emits their diagnostics, so "this probe reported no
    # error" is not the same as "this probe was proved" — the first version of
    # this tool read it that way and marked every simp-recovering probe unproved.
    # `#print axioms` only speaks for declarations that actually exist, so it is
    # evidence of proof rather than evidence of quiet. It also surfaces the axiom
    # budget, which is how a probe closed by `sorryAx` gets caught.
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------
# Lean invocation
# --------------------------------------------------------------------------


@dataclass
class ProbeResult:
    name: str
    kind: str
    subject: str
    statement: str
    proved: bool
    detail: str = ""
    axioms: list[str] = field(default_factory=list)


#: `#print axioms` output for one attempt: proof exists, with its axioms.
AXIOM_REPORT = re.compile(
    r"'(probe_\S+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", re.DOTALL
)


def axiom_reports(blob: str) -> dict[str, list[str]]:
    """Attempt name -> axioms, for every attempt the text reports as declared."""
    return {
        m.group(1): [a.strip() for a in (m.group(2) or "").split(",") if a.strip()]
        for m in AXIOM_REPORT.finditer(blob)
    }


def decide(probes: list[Probe], all_axioms: dict[str, list[str]],
           all_detail: dict[str, str]) -> list[ProbeResult]:
    """Probe results from axiom reports, refusing unless the controls discriminate."""

    # Same policy as paper_evidence.PERMITTED_AXIOMS. A shared low-dependency
    # policy owner is preferable to importing the entire paper pipeline here.
    permitted_axioms = {"propext", "Quot.sound", "Classical.choice"}

    def _winner(name: str) -> int | None:
        for i in range(len(TACTIC_LADDER)):
            key = f"{name}__t{i}"
            axioms = all_axioms.get(key)
            if isinstance(axioms, list) and all(isinstance(a, str) for a in axioms) and set(axioms) <= permitted_axioms:
                return i
        return None

    def _proved(name: str) -> bool:
        return _winner(name) is not None

    def _winning_tactic(name: str) -> str:
        winner = _winner(name)
        return TACTIC_LADDER[winner] if winner is not None else ""

    def _winning_axioms(name: str) -> list[str]:
        winner = _winner(name)
        return list(all_axioms[f"{name}__t{winner}"]) if winner is not None else []

    if not all_axioms:
        raise HarnessNotLiveError(
            "No probe produced an axiom report, so nothing in this run elaborated. "
            "Most often the bench module is not built into the search path."
        )
    for name, _stmt, must_prove in CONTROL_PROBES:
        if _proved(name) != must_prove:
            raise HarnessNotLiveError(
                f"control probe {name} came back proved={_proved(name)}, expected "
                f"{must_prove}. The harness is not discriminating; no verdict in "
                "this run can be trusted."
            )
    return [
        ProbeResult(
            name=pr.name, kind=pr.kind, subject=pr.subject, statement=pr.statement,
            proved=_proved(pr.name),
            detail=_winning_tactic(pr.name) or all_detail.get(pr.name, "not proved within budget"),
            axioms=_winning_axioms(pr.name),
        )
        for pr in probes
    ]


def control_probes() -> list[Probe]:
    return [Probe(name, "control", name, stmt, []) for name, stmt, _ in CONTROL_PROBES]


def emit_probe_files(module: str, namespace: str, probes: list[Probe], out_dir: Path) -> list[Path]:
    """One Lean file per probe, controls first, for a kernel-probe branch.

    The kernel-probe workflow elaborates each file on its own and keeps its log as
    `<file stem>.log`; `results_from_logs` reads those logs back.
    """
    out_dir.mkdir(parents=True, exist_ok=True)
    written = []
    for pr in control_probes() + probes:
        path = out_dir / f"{pr.name}.lean"
        path.write_text(render_probe_file(module, [pr], namespace))
        written.append(path)
    return written


def results_from_logs(probes: list[Probe], log_dir: Path) -> list[ProbeResult]:
    """Decide from the logs of an emitted run; a missing log decides nothing."""
    all_axioms: dict[str, list[str]] = {}
    all_detail: dict[str, str] = {}
    for pr in control_probes() + probes:
        log = log_dir / f"{pr.name}.log"
        if not log.exists():
            all_detail[pr.name] = "no log"
            continue
        all_axioms.update(axiom_reports(log.read_text(errors="replace")))
    return decide(probes, all_axioms, all_detail)


def run_probes(
    *,
    lean_root: Path,
    module: str,
    namespace: str,
    probes: list[Probe],
    probe_path: Path,
    timeout: int,
) -> list[ProbeResult]:
    """Elaborate every probe, one Lean file per probe, then refuse unless live.

    One file per probe, not one file for the whole bench. A probe file is mostly
    failed attempts by construction — that is what a tactic budget is — and Lean
    stops emitting diagnostics once a single file accumulates enough errors.
    Batched into one file, later sketches silently reported as undecided because
    Lean had stopped talking, not because the kernel had decided anything.
    """
    all_axioms: dict[str, list[str]] = {}
    all_detail: dict[str, str] = {}
    transcript: list[str] = []

    control_probes = [
        Probe(name, "control", name, stmt, []) for name, stmt, _ in CONTROL_PROBES
    ]
    for pr in control_probes + probes:
        text = render_probe_file(module, [pr], namespace)
        probe_path.write_text(text)
        transcript.append(text)
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(probe_path.relative_to(lean_root))],
                cwd=lean_root, capture_output=True, text=True, timeout=timeout,
            )
            blob = proc.stderr + "\n" + proc.stdout
        except subprocess.TimeoutExpired:
            blob = ""
            all_detail[pr.name] = "lean timed out"
        all_axioms.update(axiom_reports(blob))

    probe_path.write_text("\n".join(transcript))
    return decide(probes, all_axioms, all_detail)


def classify(sketch: Sketch, results: list[ProbeResult]) -> dict:
    """Derive a verdict from probe outcomes. Never consults ``sketch.expect``."""
    by_kind = {
        r.kind: r for r in results if r.subject == sketch.sketch_id and r.kind != "dominance"
    }
    sound = by_kind.get("soundness")
    refuted = by_kind.get("refutation")

    sound_ok = bool(sound and sound.proved)
    refuted_ok = bool(refuted and refuted.proved)

    # A residual launders when both directions close on that same residual.
    equivalent_residuals = [
        i for i in range(len(sketch.residuals))
        if (by_kind.get(f"p2r{i}") and by_kind[f"p2r{i}"].proved)
        and (by_kind.get(f"r2p{i}") and by_kind[f"r2p{i}"].proved)
    ]
    laundered_ok = bool(equivalent_residuals)

    # Order matters. A refuted residual is worse than a laundered one: the sketch
    # is not merely circular, it is unsound. Report the strongest veto.
    if refuted_ok:
        verdict = RESIDUAL_REFUTED
    elif laundered_ok:
        verdict = ENDPOINT_EQUIVALENT
    elif sound_ok:
        verdict = STRICT_DECOMPOSITION_CANDIDATE
    else:
        verdict = UNKNOWN_RELATION

    return {
        "sketch_id": sketch.sketch_id,
        "target": sketch.target,
        "binders": sketch.binders,
        "residuals": sketch.residuals,
        "verdict": verdict,
        "is_veto": verdict in VETOES,
        "receipts": {
            "soundness": sound_ok,
            "laundering": laundered_ok,
            "refutation": refuted_ok,
        },
        "equivalent_residuals": [sketch.residuals[i] for i in equivalent_residuals],
        "refutation_kind": "negated_universal" if sketch.binders.strip() else "pointwise",
        "target_implies_all_residuals": all(
            by_kind.get(f"p2r{i}") is not None and by_kind[f"p2r{i}"].proved
            for i in range(len(sketch.residuals))
        ),
        "expect": sketch.expect,
        "agrees_with_expectation": (sketch.expect is None or sketch.expect == verdict),
        "note": sketch.note,
    }


def dominance_edges(results: list[ProbeResult]) -> list[dict]:
    edges = []
    for r in results:
        if r.kind != "dominance" or not r.proved:
            continue
        a, b = r.subject.split(">", 1)
        edges.append(
            {
                "stronger_demand": a,
                "weaker_demand": b,
                "relation": "demand_of_A_implies_demand_of_B",
                "reading": (
                    f"{a} asks for a logically stronger residual than {b}; both suffice "
                    "for the same target. This is a logical relation, not a difficulty "
                    "comparison."
                ),
            }
        )
    return edges


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--manifest", required=True, type=Path)
    ap.add_argument("--lean-root", type=Path,
                    help="Directory containing lakefile + built Mathlib (a local run).")
    ap.add_argument("--emit", type=Path, metavar="DIR",
                    help="Write one probe file per probe (controls first) to DIR for a "
                         "kernel-probe branch, and stop.")
    ap.add_argument("--from-logs", type=Path, metavar="DIR",
                    help="Decide from the logs (<probe>.log) of an emitted run in DIR "
                         "instead of running Lean.")
    ap.add_argument("--out", type=Path, help="Write the JSON report here.")
    ap.add_argument("--probe-out", type=Path,
                    help="Keep the generated probe file at this path.")
    ap.add_argument("--namespace", default=None,
                    help="Lean namespace to open. Defaults to the module name.")
    ap.add_argument("--no-cross", action="store_true",
                    help="Skip cross-sketch dominance probes.")
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--check", action="store_true",
                    help="Exit 1 if any derived verdict disagrees with its expectation.")
    args = ap.parse_args(argv)

    if args.emit or args.from_logs:
        module, sketches = load_manifest(args.manifest)
        namespace = args.namespace or module
        probes = build_probes(sketches, cross=not args.no_cross)
        if args.emit:
            written = emit_probe_files(module, namespace, probes, args.emit)
            print(f"wrote {len(written)} probe file(s) to {args.emit}")
            return 0
        try:
            results = results_from_logs(probes, args.from_logs)
        except HarnessNotLiveError as exc:
            print(f"HARNESS NOT LIVE — no verdicts reported.\n{exc}", file=sys.stderr)
            return 3
        return report_and_exit(args, module, sketches, probes, results,
                               lean_root=str(args.from_logs), elapsed=0.0)

    if args.lean_root is None:
        ap.error("--lean-root is required for a local run (or use --emit / --from-logs)")
    lean_root = args.lean_root.resolve()
    if not (lean_root / "lakefile.toml").exists() and not (lean_root / "lakefile.lean").exists():
        print(f"REFUSED: {lean_root} has no lakefile; cannot run probes.", file=sys.stderr)
        return 2
    if shutil.which("lake") is None:
        print("REFUSED: `lake` not on PATH; cannot decide anything.", file=sys.stderr)
        return 2

    module, sketches = load_manifest(args.manifest)
    if args.namespace is None:
        args.namespace = module
    probes = build_probes(sketches, cross=not args.no_cross)

    probe_path = lean_root / "_residual_probe.lean"
    started = time.time()
    try:
        results = run_probes(
            lean_root=lean_root, module=module, namespace=args.namespace,
            probes=probes, probe_path=probe_path, timeout=args.timeout,
        )
    except HarnessNotLiveError as exc:
        print(f"HARNESS NOT LIVE — no verdicts reported.\n{exc}", file=sys.stderr)
        return 3
    elapsed = round(time.time() - started, 1)

    if args.probe_out:
        args.probe_out.write_text(probe_path.read_text())
    return report_and_exit(args, module, sketches, probes, results,
                           lean_root=str(lean_root), elapsed=elapsed)


def report_and_exit(args: argparse.Namespace, module: str, sketches: list[Sketch],
                    probes: list[Probe], results: list[ProbeResult], *,
                    lean_root: str, elapsed: float) -> int:
    verdicts = [classify(s, results) for s in sketches]
    edges = dominance_edges(results)

    disagreements = [v for v in verdicts if not v["agrees_with_expectation"]]
    report = {
        "schema": "residual_evaluator/1",
        "module": module,
        "lean_root": lean_root,
        "tactic_budget": {"id": BUDGET_ID, "ladder": list(TACTIC_LADDER)},
        "elapsed_seconds": elapsed,
        "sketch_count": len(sketches),
        "probe_count": len(probes),
        "verdicts": verdicts,
        "dominance_edges": edges,
        "veto_count": sum(1 for v in verdicts if v["is_veto"]),
        "abstention_count": sum(1 for v in verdicts if v["verdict"] == UNKNOWN_RELATION),
        "disagreements": [v["sketch_id"] for v in disagreements],
        "authority": (
            "Verdicts are derived from Lean's elaboration of the emitted probes under "
            "the recorded tactic budget. A failed probe means 'not decided within "
            "budget', never 'false'. Vetoes carry kernel proofs; abstentions carry "
            "nothing and must not be read as progress. This tool does not measure "
            "proof difficulty and does not rank sketches."
        ),
    }

    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(report, indent=2) + "\n")

    for v in verdicts:
        flag = "VETO" if v["is_veto"] else ("    " if v["agrees_with_expectation"] else "DIFF")
        print(f"{flag}  {v['sketch_id']:<24} {v['verdict']:<32} "
              f"sound={int(v['receipts']['soundness'])} "
              f"laundered={int(v['receipts']['laundering'])} "
              f"refuted={int(v['receipts']['refutation'])}")
    for e in edges:
        print(f"      dominance: {e['stronger_demand']} ⟹ {e['weaker_demand']}")
    print(f"\n{report['veto_count']} veto(s), {report['abstention_count']} abstention(s), "
          f"{len(disagreements)} disagreement(s) in {elapsed}s")

    if args.check and disagreements:
        for v in disagreements:
            print(f"DISAGREE {v['sketch_id']}: expected {v['expect']}, derived {v['verdict']}",
                  file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
