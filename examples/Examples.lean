-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Erdos249257
import ErdosProblems
import ExternalVerification.Solution

/-!
# Minimal downstream consumer

This module is not part of the `Erdos249257` library. It imports the package
root exactly as an external project would (`import Erdos249257`) and derives a
small corollary through the advertised public interface, so the release is
demonstrably usable from outside, not merely internally buildable. CI builds
it with `lake build Examples`.

The same proof-trust rules apply here as in the library: no `sorry`, no
`admit`, no new axioms (`scripts/check_release.py` scans this directory too).
-/

open Erdos249257

/-- Downstream instance of the headline theorem: the base-3 series
`∑ 1/(3ⁿ − 1)` is irrational, obtained by specialising
`irrational_erdosSum_full_support` exactly as a consumer project would. -/
theorem downstream_base_three_irrational :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((3 : ℝ) ^ (k + 1) - 1)) := by
  have h := irrational_erdosSum_full_support 3 (by norm_num)
  have hcast : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
  rwa [hcast] at h

/-- The release's own base-2 headline, reached through the public root
import: the Erdős–Borwein constant is irrational. -/
example : Irrational (∑' k : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) - 1)) :=
  irrational_erdosBorwein_series

/-- Downstream use of a conditional interface. The rational-gap lower bound
is supplied by the library, while the analytic shell estimate remains an
explicit hypothesis. In particular, this does not prove the universal
Erdős #257 statement for arbitrary infinite supports. -/
theorem downstream_conditional_rational_shell_bound
    (whole pfx : ℚ) (K X : ℕ)
    (hpositive : pfx < whole) (hX : 1 ≤ X)
    (hupper : (whole : ℝ) - (pfx : ℝ) ≤
      (K : ℝ) / (2 : ℝ) ^ X + 2 / (2 : ℝ) ^ (2 * X)) :
    (2 : ℝ) ^ X ≤
      ((whole.den * pfx.den : ℕ) : ℝ) * (K + 1) :=
  prefixDenominator_shell_power_bound_of_rational_difference
    whole pfx K X hpositive hX hupper

/-- The external import also exposes the exact finite correction for a
composite support multiplier.  This is a local divisor identity: it does not
bound arbitrary defects or prove the open #257 irrationality statement. -/
theorem downstream_composite_dilation_defect
    (A : Set ℕ) {a x : ℕ} (ha : a ∈ A) (ha0 : 0 < a) (hx0 : 0 < x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        CompositeDilationDefect.compositeDilationDefect A a x :=
  CompositeDilationDefect.supportCoeff_mul_eq_add_defect A ha ha0 hx0

/-! The centered-state recovery family is also a reusable consumer of the
problem-centric library.  Keep the signed recovery theorem as the one
downstream example: its centered-zero and Sylvester declarations are
mechanism evidence inside the same family, not separate endpoint claims. -/

/-- Downstream reuse of the exact #243 centered-state recovery mechanism.

The consumer keeps every load-bearing hypothesis visible: exact natural
`C/D` dynamics, `a > 1`, positive `C`, strict centering, a uniform lower
bound on the signed centered error, and division-free normalized vanishing.
It derives eventual zero centered defect, but does not assert that an
unrestricted reciprocal-tail orbit satisfies those hypotheses or solve
Erdős #243. -/
theorem downstream_bounded_negative_part_recovery
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (B : ℕ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n,
      E n = ErdosProblems.Erdos243.centeredState
        (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∀ n, Int.natAbs (E n) < C n)
    (hbound : ∀ n, -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 :=
  ErdosProblems.Erdos243.boundedNegativePart_eventually_zero
    a C D E B ha hCpos hC hD hE hcentered hbound hvanish

/-! The Boolean–Möbius transport is a second, genuinely reusable view of
#257 rationality: it removes the support from the downstream certificate while
retaining the exact rational numerator, denominator, and positivity boundary.
It is a normal-form constraint, not a contradiction or a solution of #257. -/

/-- Downstream reuse of the exact Boolean–Möbius rational-support equivalence.

The quotient-only certificate is useful to consumers that need to reason about
the carry orbit rather than reconstructing a support set.  The support-side
existence remains in the iff, and `q > 0` stays explicit. -/
theorem downstream_boolean_mobius_carry_normal_form
    (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U :=
  exists_normalized_support_fraction_iff_exists_booleanMobiusCarry p q hq

/-! The exact-row forest is a separate downstream reuse route for #257.  A
cofinal supply of positive rational-greedy skips feeds the local skipped-core
constructor and the cofinal-row closed-set consumer reaches `1/2`.  The
cofinal-skip hypothesis is deliberately left unproved: finite exact rows at
isolated endpoints do not supply cofinality, so this is not an unconditional
#257 counterexample or a solution of the universal problem. -/

/-- Downstream reuse of the exact Boolean--Möbius skip-row consequence.

The consumer keeps the hard global input visible as the explicit, unproved
`CofinalPositiveHalfGreedySkips` hypothesis and invokes the source's
proof-bearing endpoint theorem through the public root import. -/
theorem downstream_boolean_mobius_skip_row_consumer
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips hskips

/-! The half-membership endpoint is also available through the
Comparator-facing proof-bearing namespace.  This consumer records the exact
equivalence without pretending that an endpoint equivalence is itself an
arithmetic producer. -/

/-- Downstream reuse of the exact half-membership endpoint equivalence.

The imported Comparator-facing solution transports the endpoint
`(1 / 2 : ℝ) ∈ mersenneAchievementSet` to and from
`SeamGreedyUnboundedTerminalFalse`.  This example supplies no unbounded
terminal-false arithmetic producer: it establishes neither side
unconditionally and leaves the cofinal arithmetic input to a separate
producer.  It therefore does not solve the open #257 problem. -/
theorem downstream_half_membership_endpoint_equivalence :
    ((1 / 2 : ℝ) ∈ Erdos249257.ExternalVerification.mersenneAchievementSet) ↔
      Erdos249257.ExternalVerification.SeamGreedyUnboundedTerminalFalse := by
  exact
    Erdos249257.ExternalVerification.half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse

/-! The #249 fixed-precision tropical no-go is a finite synthetic consumer.
It realizes a concrete word of odd unit symbols, but the word is not extracted
from an actual totient sequence and the finite orbit is not an endpoint
producer for the binary totient series. -/

/-- Downstream reuse of the fixed-precision no-go on a concrete finite word.

The two-symbol word has odd units `1` and `3`, and the theorem supplies a
compatible orbit whose two successive states are centred at precision `2`.
This is deliberately synthetic finite data: it carries no actual-totient
arithmetic and does not establish an endpoint or irrationality result for
Erdős #249.  The open boundary remains the unbounded, totient-specific supply
required by the problem's canonical equivalent formulation. -/
theorem downstream_fixed_precision_synthetic_finite_orbit :
    ∃ states : List ℤ,
      Erdos249257.ExternalVerification.VUOrbit 2 0
          ([⟨0, 1⟩, ⟨1, 3⟩] :
            List Erdos249257.ExternalVerification.VUSymbol) states ∧
        List.Forall₂
          (fun σ e' =>
            |e'| ≤ Erdos249257.ExternalVerification.vuRadius 2 σ)
          ([⟨0, 1⟩, ⟨1, 3⟩] :
            List Erdos249257.ExternalVerification.VUSymbol)
          states := by
  have hodd :
      ∀ σ ∈
        ([⟨0, 1⟩, ⟨1, 3⟩] :
          List Erdos249257.ExternalVerification.VUSymbol),
        Odd σ.unit := by
    intro σ hσ
    simp at hσ
    rcases hσ with rfl | rfl
    · norm_num
    · norm_num
  exact
    Erdos249257.ExternalVerification.fixedPrecisionTropicalNoGo
      2 (by norm_num) _ hodd 0

/-! The #249 carry anti-compression family is a distinct rationality
consequence: quotient periodicity and torsion-free section rank coexist.  The
rank bound is not a finite-rank conclusion, and neither clause supplies an
irrationality proof.  In particular, the source's divisor-of-the-multiplier
geometric degeneration is the natural friction that prevents promoting
quotient periodicity to finite `ℚ`-rank.  The actual totient-specific producer
and the irrationality endpoint remain open.  The hard step is the source
transport from rationality to one common eventual carry period while preserving
the independent finite-level rank lower bound.

The consumer therefore keeps the rationality hypothesis, positive multiplier,
tempered integral orbit, all-level rank lower bound, and common eventual
periodicity visible in one theorem. -/

/-- Downstream reuse of the exact #249 carry anti-compression mechanism.

This is a necessary consequence of rationality for the binary totient series,
not a contradiction, finite-rank theorem, or solution of Erdős #249. -/
theorem downstream_totient_carry_anti_compression
    (hrational :
      ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := by
  have hseries : ¬ Irrational (binaryCoeffSeries Nat.totient) := by
    rw [binaryCoeffSeries_totient_eq]
    exact hrational
  exact not_irrational_totientSeries_implies_mod_period_and_unbounded_rank hseries
