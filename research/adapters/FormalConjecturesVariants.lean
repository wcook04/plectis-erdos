/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification.Solution

/-!
# Solved-variant candidates for Formal Conjectures

`FormalConjecturesAdapter` states the three propositions that
`google-deepmind/formal-conjectures` already carries as `sorry`, so an external
`formal_proof` link resolves to their exact text.  This file is the other
direction: statements upstream does not carry at all, offered as new
`erdos_NNN.variants.*` declarations.

Upstream is built out of those.  Measured at `9943b0a0` it holds 1,012
`erdos_NNN.variants.*` declarations across 343 problem files, and `CONTRIBUTING`
welcomes solved variants; `257.variants.tsum_top` and
`1049.variants.geq_2_integer` — the two the sibling adapter discharges — are
that shape.  For six of the eight problems this repository works on, upstream's
only declaration is the open question itself, so there is no hole to fill and a
variant is the whole available route.  `docs/formal_conjectures_crosswalk.json`
records those six as `not_a_candidate`, which is correct about discharging an
existing `sorry` and says nothing about adding one.

## What is here, and what is not

A statement earns a place here when it is about the **object the problem asks
about** rather than about a route this corpus happened to walk.  The exact rank
of the dyadic totient kernel is about `∑ φ(n)/2ⁿ`; a ten-hypothesis obstruction
on a normalised orbit is about an argument that failed here, and a reader
without this repository could not use it.  On that filter the #243 negative
orbits, the numeric `2 × 2` minor for #269, the base-`3/2` corridor no-go, and
the generic cleared-tail recurrence stay out, as does the `#249`
infinite-dimensionality corollary, which the claim registry already disclaims as
implied by Coons.

Each theorem below restates one Mathlib-only proposition from
`ExternalVerification.Statements` under the name it would take upstream, and
proves it by projection from `ExternalVerification.portfolioClaims`.  No new
mathematics: the content is the registered corpus declaration, and the
`Statements` vocabulary is already Mathlib-only, so contributing one upstream is
a move of its supporting definitions into `FormalConjecturesForMathlib` rather
than a port.

**Novelty is a separate question from contribution.** Upstream does not require
a variant to be new, only that its source and status are stated correctly.  The
prior-art position of the exact `2 ^ e + 1` rank and the odd-core basis against
Martin, and of the Mersenne measure results against the Kovač–Tao line, is
unresolved here and gates the wording of any upstream docstring — not whether
the theorem may be offered.

None of these settles any of the eight problems.  All eight remain open.
-/

namespace Erdos249257.FormalConjecturesVariants

open Module MeasureTheory
open scoped ENNReal
open Erdos249257.ExternalVerification

/-! ### Erdős 68 — `∑ 1/(n! − 1)`

Upstream's `68.lean` carries the open question and one variant.  This is an
exact hypothesis-free normal form: irrationality holds precisely when a carry
in the factorial-digit recurrence fails to be one, cofinally often.  It reduces
an analytic irrationality question to a statement about integers. -/

/-- The factorial-gap series is irrational exactly when cofinally many steps
carry something other than one. -/
theorem erdos_68_variants_iff_cofinal_nonunit_carries :
    Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1 :=
  irrational_factorialGapSeries_iff_cofinal_nonunit_carries

/-- The same equivalence in divisibility form: irrationality holds exactly when
the strict factorial successor cofinally misses divisibility by its index. -/
theorem erdos_68_variants_iff_cofinal_divisibility_miss :
    Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ ¬(m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m :=
  irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses

/-! ### Erdős 249 — `∑ φ(n)/2ⁿ`

Upstream's `249.lean` is thirty-eight lines and contains one declaration: the
open question.  It says nothing about the object.  These are exact structural
facts about the dyadic totient kernel that question is asking about. -/

/-- The rational span of the level-`e` dyadic totient kernel family has
dimension exactly `2 ^ e + 1`. -/
theorem erdos_249_variants_kernel_rank (e : ℕ) (he : 1 ≤ e) :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 :=
  finrank_totientKernelThroughLevelFamily_eq e he

/-- The full dyadic totient kernel span admits an explicit basis indexed by odd
cores. -/
theorem erdos_249_variants_odd_core_basis :
    Nonempty
      (Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily))) :=
  exists_totientDyadicSectionBasis

/-! ### Erdős 251 — `∑ pₙ/2ⁿ`

An exact transfer between the prime dyadic series and the consecutive-prime-gap
series.  The summability premise is itself proved in this corpus, by an
elementary polynomial prime bound rather than by assumption. -/

/-- Irrationality of the prime dyadic series is equivalent to irrationality of
the consecutive-prime-gap dyadic series. -/
theorem erdos_251_variants_prime_gap_transfer
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  irrational_tsum_primeDyadicTerm_iff_primeGap hprime

/-! ### Erdős 257 — `∑_{n ∈ A} 1/(2ⁿ − 1)`

The achievement set of the Mersenne weights is compact, perfect, totally
disconnected and nowhere dense, and has Lebesgue measure exactly one.  The
dichotomy classifies every support-restricted version: finite complement gives
an exact dyadic measure, infinite complement gives zero. -/

/-- The Mersenne achievement set has Lebesgue measure exactly one. -/
theorem erdos_257_variants_achievement_set_measure :
    volume mersenneAchievementSet = 1 :=
  volume_mersenneAchievementSet

/-- Complete measure classification of the support-restricted Mersenne
achievement sets: an exact dyadic value when the complement is finite, and zero
otherwise. -/
theorem erdos_257_variants_support_measure_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0) :=
  volume_supportedMersenneAchievementSet_dichotomy J

/-- For every nonempty finite support and every base coprime to the reduced
denominator, the multiplicative order is exactly the lcm of the support: the
period does not collapse. -/
theorem erdos_257_variants_finite_period_noncollapse
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hcop : Nat.Coprime b (finiteErdosSum F b).den) :
    orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id :=
  finite_period_noncollapse_rat_den_interface F b hF h0 hb hcop

/-! ### Erdős 269 — running lcm of the smooth numbers

An exact identity for the object in the three-prime case: the smooth-prefix lcm
is the product of the three maximal pure prime powers below the cutoff.  The
two-prime transcendence result is deliberately absent — Steve Fan posted the
same factorisation and conclusion before this note was released, no priority is
claimed for it, and no declaration here asserts it. -/

/-- For three pairwise distinct primes the smooth-prefix lcm equals the
three-prime height. -/
theorem erdos_269_variants_smooth_prefix_lcm
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x :=
  smoothPrefixLcm_eq_threePrimeHeight hp hq hr hpq hpr hqr hx

/-! ### Erdős 1041 — short connections inside polynomial lemniscates

Quantitative root retention under a constant perturbation.  This is the piece
most plainly reusable outside the problem, and the one likeliest to belong in
`FormalConjecturesForMathlib` rather than in a problem file. -/

/-- Under an explicit margin, every root of a small constant perturbation of a
monic split polynomial stays inside the open unit disc. -/
theorem erdos_1041_variants_perturbed_roots_in_unit_disk
    (f : Polynomial ℂ) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsplit : f.Splits) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hroots : ∀ b ∈ f.roots, ‖b‖ ≤ ρ) (hε : 0 < ε)
    (hmargin : ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ + ρ < 1)
    {shift : ℂ} (hshift : ‖shift‖ < ε) :
    ∀ a : ℂ, (f + Polynomial.C shift).eval a = 0 → ‖a‖ < 1 :=
  constant_perturbation_roots_in_unitDisk f hf hdeg hsplit hρ hroots hε
    hmargin hshift

/-! ## Erdős 249, over the vocabulary upstream would own

The two theorems above are stated over `ExternalVerification.Statements`, this
repository's Mathlib-only statement vocabulary.  Formal Conjectures cannot
import that module.  A statement contributed upstream has to be built out of
constants upstream owns, which for these two means a support file of its own --
`totientKernelSeq` and the five index and family objects around it.

Copying definitions across a repository boundary is where a `formal_proof` link
stops being exact.  Two textually identical definitions in two repositories are
two different constants, and a theorem about one is not, on its face, a theorem
about the other.  Prose asserting they agree is not a proof, and not needing to
take prose for it is the whole point of the link.

What follows closes that gap the only way that is checkable.  It declares the
same six objects a second time, in the namespace and with the bodies the
upstream support file uses, and restates the two propositions over *those*
constants.  The proofs are the two theorems above, accepted with no bridging
step: the vocabularies are definitionally equal, so a proof of one proposition
is a proof of the other, and the type checker is what says so.

A reviewer can diff the block below against the upstream support file character
by character, and read the two restatements as the ones the upstream
declarations carry.

Mutating either half breaks it, which is what makes the arrangement worth
anything.  Changing the rank to `2 ^ e + 2`, or the channel to
`2 ^ j * n + r + 1`, is a type mismatch rather than a warning. -/

end Erdos249257.FormalConjecturesVariants

open scoped Nat

namespace Nat

/-- The `(j, r)` dyadic channel of Euler's totient: the rational-valued
sequence `n ↦ φ (2 ^ j * n + r)`. -/
def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  φ (2 ^ j * n + r)

@[simp]
theorem totientKernelSeq_apply (j r n : ℕ) :
    totientKernelSeq j r n = φ (2 ^ j * n + r) := rfl

/-- The level-`0` channel is the totient sequence itself. -/
theorem totientKernelSeq_zero_zero : totientKernelSeq 0 0 = fun n => (φ n : ℚ) := by
  funext n
  simp

/-- The index of the dyadic totient channels of level at most `e`: a level
`j ≤ e` together with a residue modulo `2 ^ j`. -/
abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)

/-- Every dyadic totient channel of level at most `e`. -/
def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val

@[simp]
theorem totientKernelThroughLevelFamily_apply (e : ℕ)
    (j : Fin (e + 1)) (r : Fin (2 ^ j.val)) :
    totientKernelThroughLevelFamily e ⟨j, r⟩ = totientKernelSeq j.val r.val := rfl

/-- The index of all dyadic totient channels: a level `j` together with a
residue modulo `2 ^ j`. -/
abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)

/-- Every dyadic totient channel. -/
def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val

@[simp]
theorem fullTotientKernelFamily_apply (j : ℕ) (r : Fin (2 ^ j)) :
    fullTotientKernelFamily ⟨j, r⟩ = totientKernelSeq j r.val := rfl

/-- The index type of the odd-core description of the dyadic totient span: two
exceptional generators together with one generator per dyadic channel. -/
abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)

end Nat

namespace Erdos249257.FormalConjecturesErdos249

open Erdos249257.ExternalVerification

/-- `Erdos249.erdos_249.variants.dyadic_kernel_rank`, over the constants an
upstream support file would own. -/
theorem erdos_249_variants_dyadic_kernel_rank (e : ℕ) (he : 1 ≤ e) :
    Module.finrank ℚ
        (Submodule.span ℚ (Set.range (Nat.totientKernelThroughLevelFamily e))) =
      2 ^ e + 1 :=
  FormalConjecturesVariants.erdos_249_variants_kernel_rank e he

/-- `Erdos249.erdos_249.variants.odd_core_basis`, over the constants an upstream
support file would own. -/
theorem erdos_249_variants_odd_core_basis :
    Nonempty
      (Module.Basis Nat.TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range Nat.fullTotientKernelFamily))) :=
  FormalConjecturesVariants.erdos_249_variants_odd_core_basis

/-! ### The two vocabularies agree

The restatements above are accepted with no bridging step, which already says
the vocabularies are definitionally equal.  These say it outright, so the fact
is visible rather than implicit in a type-check. -/

/-- The upstream channel definition is this repository's. -/
theorem totientKernelSeq_eq (j r : ℕ) :
    Nat.totientKernelSeq j r = totientKernelSeq j r := rfl

/-- The upstream level-`e` family is this repository's. -/
theorem totientKernelThroughLevelFamily_eq (e : ℕ) :
    Nat.totientKernelThroughLevelFamily e = totientKernelThroughLevelFamily e := rfl

/-- The upstream full family is this repository's. -/
theorem fullTotientKernelFamily_eq :
    Nat.fullTotientKernelFamily = fullTotientKernelFamily := rfl

end Erdos249257.FormalConjecturesErdos249


/-! ## Erdős 257, over the vocabulary upstream would own

The finite-period theorem above is stated over
`ExternalVerification.finiteErdosSum`.  Formal Conjectures cannot import that
module.  The support this statement needs is one definition, and it belongs in
the problem file rather than in `FormalConjecturesForMathlib`: a finite sum over
a `Finset`, nothing reusable across problems.

Copying that definition across a repository boundary is where a `formal_proof`
link stops being exact.  Two textually identical definitions in two repositories
are two different constants.  What follows declares the same object a second
time, in the namespace an upstream `257.lean` would use, and restates the
proposition over *that* constant.  The proof is the theorem above, accepted with
no bridging step.

The coprimality hypothesis is retained.  Discharging it is a reduced-denominator
argument already proved in this corpus, but it is not a one-line Mathlib fact,
and the Formal Conjectures statement should not grow a rational-arithmetic
development just to hide a hypothesis the reader can see.

Mutating the conclusion from `F.lcm id` to `F.lcm id + 1` is a type mismatch. -/

namespace Erdos257

/-- The finite Erdős support series at integer base `b`, summed over a finite
set of exponents. -/
def finiteErdosSum (F : Finset ℕ) (b : ℕ) : ℚ :=
  ∑ n ∈ F, 1 / ((b : ℚ) ^ n - 1)

end Erdos257

namespace Erdos249257.FormalConjecturesErdos257

open Erdos249257.ExternalVerification

/-- `Erdos257.erdos_257.variants.finite_period_noncollapse`, over the constant
an upstream problem file would own. -/
theorem erdos_257_variants_finite_period_noncollapse
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hcop : Nat.Coprime b (Erdos257.finiteErdosSum F b).den) :
    orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id :=
  FormalConjecturesVariants.erdos_257_variants_finite_period_noncollapse
    F b hF h0 hb hcop

/-- The upstream finite-sum definition is this repository's. -/
theorem finiteErdosSum_eq (F : Finset ℕ) (b : ℕ) :
    Erdos257.finiteErdosSum F b = finiteErdosSum F b := rfl

end Erdos249257.FormalConjecturesErdos257

/-! ## Erdős 251, over the vocabulary upstream already owns

The transfer theorem at the top of this file pairs the *displayed* prime series
with the *normalized* gap series, so its two sides carry different denominators
and it exposes a `Summable` premise that the corpus has since proved
unconditionally.  Neither belongs in a statement offered upstream.

Upstream already owns the gap object: `FormalConjecturesForMathlib/
NumberTheory/PrimeGap.lean` defines `primeGap n = (n + 1).nth Nat.Prime -
n.nth Nat.Prime`, and `FormalConjecturesUtil` re-exports it.  So unlike the 249
and 257 blocks above, this one contributes *no* support vocabulary: the
definition below is upstream's, reproduced here only so the restatement
elaborates against a constant with upstream's body.

`erdos_251` sums `Nat.nth Nat.Prime n / 2 ^ n` from `n = 0`, so its first term
is `p₀ / 2⁰ = 2`; the classical one-based series is half of it.  Summation by
parts against that zero-based convention gives the constant `4`, not `2`.
Mutating `4` to `5`, or `primeGap n` to `primeGap (n + 1)`, is a type mismatch.
-/

/-- The prime gap: the difference between the `n+1`-th and `n`-th prime.
Upstream's definition, reproduced verbatim. -/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

namespace Erdos249257.FormalConjecturesErdos251

open ErdosProblems.Erdos251

/-- Summation by parts for the zero-based dyadic prime series, with the
denominator convention `erdos_251` displays on both sides. -/
theorem erdos_251_variants_prime_gap_identity :
    (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / (2 ^ n)) =
      4 + ∑' n : ℕ, (primeGap n : ℝ) / (2 ^ n) := by
  -- The corpus identity pairs the displayed prime series with the *normalized*
  -- gap series, whose denominator is `2 ^ (n + 1)`; the displayed gap term is
  -- twice it, which absorbs the `2 *`.
  have hterm : ∀ n : ℕ,
      (primeGap n : ℝ) / 2 ^ n = 2 * primeGapDyadicTerm n := by
    intro n
    rw [primeGapDyadicTerm, primeGap, pow_succ]
    norm_num [primeGap0, prime0]
    ring
  have hsum :
      (∑' n : ℕ, (primeGap n : ℝ) / 2 ^ n) =
        2 * ∑' n : ℕ, primeGapDyadicTerm n := by
    simpa only [hterm] using
      (summable_primeGapDyadicTerm.hasSum.mul_left 2).tsum_eq
  rw [hsum]
  simpa only [primeDisplayedDyadicTerm, prime0] using
    tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap
      summable_primeDyadicTerm

/-- Erdős 251 is exactly equivalent to irrationality of the corresponding
consecutive-prime-gap dyadic series.  No summability premise: convergence
follows inside the proof from the elementary bound `pₙ ≤ 1250 (n + 1) ^ 4`. -/
theorem erdos_251_variants_prime_gap_transfer :
    Irrational (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) / (2 ^ n)) ↔
      Irrational (∑' n : ℕ, (primeGap n : ℝ) / (2 ^ n)) := by
  rw [erdos_251_variants_prime_gap_identity]
  exact irrational_natCast_add_iff

/-- Upstream's gap definition is this repository's. -/
theorem primeGap_eq (n : ℕ) : primeGap n = primeGap0 n := rfl

end Erdos249257.FormalConjecturesErdos251

/-! ## Erdős 68, over the vocabulary upstream would own

The two `erdos_68_variants_*` theorems above are the same theorem in different
clothes.  The corpus bridge gives, for every `m ≥ 3`,

  `factorialGapStepCarry m = 1  ↔  (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m`

and both variants quantify cofinally, so the finitely many indices below `3`
cannot separate them.  Only one belongs upstream.

The divisibility form is the one to offer.  Its statement is purely integral —
an exact rational prefix, its strict factorial-grid successor, and a
divisibility test — so a reader can evaluate it without meeting the carry's
real-valued predecessor gap, and the support surface is two definitions rather
than five.  The carry form stays here as the internal exposition interface.

Upstream's `68.lean` opens `namespace Erdos68`, which is also where this
corpus keeps `factorialGapSeries`, so the two definitions below land in the
namespace an upstream support file would own.

`erdos_68` sums `1 / ((n + 2)! - 1)` from `n = 0`; this corpus writes the same
series as the universal tail after cutoff `1`.  The reindexing `1 + 1 + k =
k + 2` is the one non-definitional step below.  Mutating `Icc` to `Ico`, the
successor's `+ 1` to `+ 2`, or the divisor `m` to `m + 1` breaks the
restatement. -/

namespace Erdos68

/-- The exact rational prefix `∑ k ∈ {2, …, n}, 1 / (k! - 1)` of the
factorial-gap series. -/
def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

/-- The first integer strictly greater than `n! * x`. -/
def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

end Erdos68

namespace Erdos249257.FormalConjecturesErdos68

open Erdos249257.ExternalVerification

/-- This corpus writes the Erdős 68 series as the universal factorial-gap tail
after cutoff `1`; upstream writes it as a sum indexed from `n = 0` with
summand `1 / ((n + 2)! - 1)`.  They are the same real number. -/
theorem factorialGapSeries_eq_shifted_tsum :
    Erdos68.factorialGapSeries =
      ∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ) := by
  rw [Erdos68.factorialGapSeries, Erdos68.factorialGapTail_eq_shifted_tsum]
  apply tsum_congr
  intro n
  have h : 1 + 1 + n = n + 2 := by omega
  rw [h]
  push_cast
  ring

/-- `Erdos68.erdos_68.variants.iff_cofinal_divisibility_miss`, over upstream's
literal series and the two constants an upstream support file would own. -/
theorem erdos_68_variants_iff_cofinal_divisibility_miss :
    Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧
          ¬ ((m : ℤ) ∣
            Erdos68.strictFacTopRat (Erdos68.factorialGapPrefix m) m) := by
  rw [← factorialGapSeries_eq_shifted_tsum]
  exact irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses

/-- The upstream prefix definition is this repository's. -/
theorem factorialGapPrefix_eq (n : ℕ) :
    Erdos68.factorialGapPrefix n = factorialGapPrefix n := rfl

/-- The upstream strict-successor definition is this repository's. -/
theorem strictFacTopRat_eq (x : ℚ) (n : ℕ) :
    Erdos68.strictFacTopRat x n = strictFacTopRat x n := rfl

end Erdos249257.FormalConjecturesErdos68

/-! ## Erdős 257 measure, over the vocabulary upstream would own

Two candidates were prepared here: `volume mersenneAchievementSet = 1`, and
the support-restricted classification.  Only the second is offered.

The first is the second's `F = ∅` case.  Taking `J = Set.univ` in the
dichotomy below gives `F = ∅` and `volume = ((2 : ℝ≥0∞) ^ 0)⁻¹ = 1`, and this
corpus proves `supportedMersenneAchievementSet Set.univ = mersenneAchievementSet`
(`ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean`).  Offering both would
present one classification as two advances and would cost three further
definitions upstream for a strictly weaker statement.

`J` is the set of **allowed** coordinates; the omitted ones are `Jᶜ`.
Coordinate `k` carries exponent `k + 1`, so exponent `0` — whose Mersenne
weight is `1 / (2⁰ - 1)`, zero under Lean's division convention — never
enters.  Deleting finitely many coordinates costs one binary branch each,
giving `2⁻|F|`; deleting infinitely many drives the measure to `0`.

Six definitions are needed to state it, and none of the certificate-kernel,
sunflower, or half-counterexample machinery appears in its import closure.
Mutating `mersenneWeight (k + 1)` to `mersenneWeight k`, or `F.card` to
`F.card + 1`, breaks the restatement. -/

namespace Erdos257

/-- The real Mersenne weight `1 / (2 ^ n - 1)`. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

/-- The contribution of coordinate `k`, carrying exponent `k + 1`. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)

/-- The Mersenne subseries value coded by a binary digit string. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b

/-- Binary digit strings whose nonzero coordinates lie in `J`. -/
def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}

/-- The Mersenne digit map restricted to the allowed coordinates `J`. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1

/-- All Mersenne subseries sums using only coordinates from `J`. -/
def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)

end Erdos257

namespace Erdos249257.FormalConjecturesErdos257

open MeasureTheory
open scoped ENNReal
open Erdos249257.ExternalVerification

/-- `Erdos257.erdos_257.variants.support_measure_dichotomy`, over the constants
an upstream support file would own. -/
theorem erdos_257_variants_support_measure_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (Erdos257.supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧
        volume (Erdos257.supportedMersenneAchievementSet J) = 0) :=
  volume_supportedMersenneAchievementSet_dichotomy J

/-! ### Geometry of the same restricted sets

The measure above says how big these sets are; this says what shape they are,
over the same six definitions and with no further upstream cost.

Five predicates, and no sixth.  `IsClosed` is not a conjunct: the set is a
compact subset of `ℝ`, and `Perfect` carries closedness in its own first
component, so stating it would be padding rather than content.  `Perfect` is
the one predicate that needs `J.Infinite` -- a finite `J` admits finitely many
digit strings, so the set is finite and every point of it is isolated.

Total disconnectedness is stated for arbitrary `J` rather than only for the
full set.  `IsTotallyDisconnected s` unfolds to a condition quantified over
subsets of `s`, so it descends along `⊆` with no work, exactly as nowhere
density already does.  That is what makes a separate full-set geometry offer
redundant instead of merely overlapping: at `J = Set.univ` this theorem is the
full-set statement, since `supportedMersenneAchievementSet Set.univ =
mersenneAchievementSet`, and unique coding is the injectivity conjunct.  One
theorem, not two. -/

/-- `Erdos257.erdos_257.variants.supported_achievement_set_geometry`, over the
constants an upstream support file would own. -/
theorem erdos_257_variants_supported_achievement_set_geometry (J : Set ℕ) :
    Function.Injective (Erdos257.supportedMersenneDigitValue J) ∧
      IsCompact (Erdos257.supportedMersenneAchievementSet J) ∧
        IsTotallyDisconnected (Erdos257.supportedMersenneAchievementSet J) ∧
          IsNowhereDense (Erdos257.supportedMersenneAchievementSet J) ∧
            (J.Infinite → Perfect (Erdos257.supportedMersenneAchievementSet J)) :=
  ⟨ErdosProblems.Erdos257.supportedMersenneDigitValue_injective J,
    ErdosProblems.Erdos257.isCompact_supportedMersenneAchievementSet J,
    fun _ hsub => Erdos249257.isTotallyDisconnected_mersenneAchievementSet _
      (hsub.trans (ErdosProblems.Erdos257.supportedMersenneAchievementSet_subset J)),
    ErdosProblems.Erdos257.isNowhereDense_supportedMersenneAchievementSet J,
    fun hJ => ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet hJ⟩

/-- The upstream weight definition is this repository's. -/
theorem mersenneWeight_eq (n : ℕ) :
    Erdos257.mersenneWeight n = mersenneWeight n := rfl

/-- The upstream support-restricted achievement set is this repository's. -/
theorem supportedMersenneAchievementSet_eq (J : Set ℕ) :
    Erdos257.supportedMersenneAchievementSet J =
      supportedMersenneAchievementSet J := rfl


/-! ### Settled infinite-support families

`erdos_257` asks whether *every* infinite support gives an irrational sum.
These four say yes for four named families, in the shape the open statement
itself uses -- `∑' n : A, 1 / (b ^ n - 1)` over a subtype -- so they need no
upstream vocabulary at all.  `tsum_subtype` is the whole bridge from this
corpus's indicator-indexed `erdosSupportSeries`.

The two explicitly-indexed families are stated over `k` rather than over
`Set.range`, matching the checked source exactly; reindexing them through the
range set would add an injectivity obligation and buy nothing.

None of this is new mathematics.  Eventually periodic supports are the `0`-`1`
coefficient case of Luca-Tachiya; pairwise-coprime supports are Erdős (1968);
the factorial and powers-of-two families sit in the Erdős-Straus rapid-growth
framework, and Duverney later proved the powers-of-two value transcendental. -/

/-- Eventually periodic infinite supports. -/
theorem erdos_257_variants_eventually_periodic_support
    (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A)) (hA : A.Infinite) :
    Irrational (∑' n : A, (1 : ℝ) / ((b : ℝ) ^ (n : ℕ) - 1)) := by
  have h : (∑' n : A, (1 : ℝ) / ((b : ℝ) ^ (n : ℕ) - 1))
      = Erdos249257.erdosSupportSeries b A :=
    tsum_subtype A fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)
  rw [h]
  exact Erdos249257.irrational_erdosSupportSeries_eventuallyPeriodic
    b m N₀ A hb hm hper hA

/-- Infinite pairwise-coprime supports with summable reciprocals. -/
theorem erdos_257_variants_pairwise_coprime_support
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable fun a : A => (1 : ℝ) / (a : ℕ)) :
    Irrational (∑' n : A, (1 : ℝ) / ((b : ℝ) ^ (n : ℕ) - 1)) := by
  have h : (∑' n : A, (1 : ℝ) / ((b : ℝ) ^ (n : ℕ) - 1))
      = Erdos249257.erdosSupportSeries b A :=
    tsum_subtype A fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)
  rw [h]
  exact Erdos249257.irrational_erdosSupportSeries_pairwise_coprime b A hb hA hpair
    (summable_subtype_iff_indicator.mp hsum)

/-- The positive factorials as support. -/
theorem erdos_257_variants_factorial_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (Nat.factorial (k + 1)) - 1)) :=
  Erdos249257.irrational_erdosSum_factorial_support b hb

/-- The powers of two as support. -/
theorem erdos_257_variants_two_pow_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (2 ^ k) - 1)) :=
  Erdos249257.irrational_erdosSum_two_pow_support b hb

end Erdos249257.FormalConjecturesErdos257
