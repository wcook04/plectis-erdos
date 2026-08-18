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
