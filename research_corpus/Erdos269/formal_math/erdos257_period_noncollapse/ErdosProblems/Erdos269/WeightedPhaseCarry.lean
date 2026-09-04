import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

/-!
# Erdős #269: weighted phases and carry-faithfulness

This module formalizes the exact algebraic content of the weighted-phase
return.  It deliberately does not claim irrationality of the `{2,3,5}`
running-LCM series.  Its two permanent boundaries are:

* an exact integral carry has a finite residue coordinate plus an uncontrolled
  integral transfer;
* a finite observer is useful only when the symbolic realization factors
  through it, rather than merely after one numerical evaluation.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-! ## Weighted affine phases -/

/-- The integral exponent used by one Beatty-weight coordinate. -/
noncomputable def phaseWeightExp (a ξ : ℝ) (n : ℕ) : ℤ :=
  ⌊a * (n : ℝ) + ξ⌋

/-- Passing to the `dn+s` Cartier section changes slope `a` to `da` and
offset `ξ` to `ξ+sa`, with no boundary term. -/
theorem phaseWeightExp_mul_add
    (a ξ : ℝ) (d n s : ℕ) :
    phaseWeightExp a ξ (d * n + s) =
      phaseWeightExp (d * a) (ξ + s * a) n := by
  unfold phaseWeightExp
  congr 1
  push_cast
  ring

/-- The two symbolic weights attached to one phase coefficient. -/
noncomputable def phaseWeight
    (q r : ℕ) (a b ξ η : ℝ) (n : ℕ) : ℝ :=
  (q : ℝ) ^ (-phaseWeightExp a ξ n) *
    (r : ℝ) ^ (-phaseWeightExp b η n)

/-- Weighted phase coefficient for an abstract phase-count function.  The
separate `phaseConeCount_mul_add` identity can be supplied as `hsplit` below. -/
noncomputable def weightedPhaseCoeff
    (N : ℝ → ℕ → ℕ)
    (q r : ℕ) (τ a b ξ η : ℝ) (n : ℕ) : ℝ :=
  (N τ n : ℝ) * phaseWeight q r a b ξ η n

/-- The weight part of the affine-phase Cartier identity. -/
theorem phaseWeight_mul_add
    (q r : ℕ) (a b ξ η : ℝ) (d n s : ℕ) :
    phaseWeight q r a b ξ η (d * n + s) =
      phaseWeight q r (d * a) (d * b)
        (ξ + s * a) (η + s * b) n := by
  simp only [phaseWeight, phaseWeightExp_mul_add]

/-- Exact target-faithful weighted affine-phase coefficient identity.  This
theorem makes the finite cone-count split an explicit hypothesis instead of
silently identifying the unweighted coefficient series with the numerical
target. -/
theorem weightedPhaseCoeff_mul_add
    (N : ℝ → ℕ → ℕ)
    (q r : ℕ) (lam mu τ a b ξ η : ℝ)
    (d n s : ℕ)
    (hsplit :
      N τ (d * n + s) =
        ∑ s₀ ∈ Finset.range d,
          ∑ s₁ ∈ Finset.range d,
            ∑ s₂ ∈ Finset.range d,
              N ((((s : ℝ) + τ - s₀ - lam * s₁ - mu * s₂) / d)) n) :
    weightedPhaseCoeff N q r τ a b ξ η (d * n + s) =
      ∑ s₀ ∈ Finset.range d,
        ∑ s₁ ∈ Finset.range d,
          ∑ s₂ ∈ Finset.range d,
            weightedPhaseCoeff N q r
              ((((s : ℝ) + τ - s₀ - lam * s₁ - mu * s₂) / d))
              (d * a) (d * b) (ξ + s * a) (η + s * b) n := by
  simp only [weightedPhaseCoeff, phaseWeight_mul_add]
  rw [hsplit]
  push_cast
  simp only [Finset.sum_mul]

/-! ## Integral carry = finite residue + uncontrolled transfer -/

/-- Canonical integral carry residue. -/
def carryResidue (B c : ℤ) : ℤ :=
  c % B

/-- Integral transfer coordinate complementary to `carryResidue`. -/
def carryQuotient (B c : ℤ) : ℤ :=
  c / B

/-- The bounded residue digit in the exact carry decomposition. -/
def residueDigit (B base residue nextResidue : ℤ) : ℤ :=
  (base * residue - nextResidue) / B

/-- Euclidean reconstruction of a carry from its residue and transfer. -/
theorem carry_eq_residue_add_mul_quotient (B c : ℤ) :
    carryResidue B c + carryQuotient B c * B = c := by
  exact Int.emod_add_ediv_mul c B

/-- Rationality's exact carry recurrence decomposes into a finite residue
digit and an integral coboundary.  No recurrence or finite-state property of
the quotient coordinate is assumed or concluded. -/
theorem carry_eq_residueDigit_add_coboundary
    (B : ℤ) (hB : 0 < B)
    (base carry digit : ℕ → ℤ)
    (hrec : ∀ n,
      carry (n + 1) = base n * carry n - B * digit n) :
    let residue := fun n => carryResidue B (carry n)
    let quotient := fun n => carryQuotient B (carry n)
    ∀ n,
      digit n =
        residueDigit B (base n)
          (residue n) (residue (n + 1)) +
        base n * quotient n -
        quotient (n + 1) := by
  dsimp
  intro n
  have hn := carry_eq_residue_add_mul_quotient B (carry n)
  have hn1 := carry_eq_residue_add_mul_quotient B (carry (n + 1))
  have hnum :
      base n * carryResidue B (carry n) -
          carryResidue B (carry (n + 1)) =
        B * (digit n - base n * carryQuotient B (carry n) +
          carryQuotient B (carry (n + 1))) := by
    linear_combination base n * hn - hn1 - hrec n
  have hdiv :
      B ∣ base n * carryResidue B (carry n) -
        carryResidue B (carry (n + 1)) := by
    refine ⟨digit n - base n * carryQuotient B (carry n) +
      carryQuotient B (carry (n + 1)), ?_⟩
    simpa [mul_comm] using hnum
  have hdigit :
      residueDigit B (base n) (carryResidue B (carry n))
          (carryResidue B (carry (n + 1))) =
        digit n - base n * carryQuotient B (carry n) +
          carryQuotient B (carry (n + 1)) := by
    unfold residueDigit
    rw [Int.ediv_eq_iff_eq_mul_left hB.ne' hdiv]
    simpa [mul_comm] using hnum
  rw [hdigit]
  ring

/-- The residue coordinate is genuinely finite for a positive modulus. -/
theorem carryResidue_mem_interval
    (B c : ℤ) (hB : 0 < B) :
    0 ≤ carryResidue B c ∧ carryResidue B c < B := by
  exact ⟨Int.emod_nonneg _ hB.ne', Int.emod_lt_of_pos _ hB⟩

/-- When the next residue is the canonical reduction of `base * residue`,
the corresponding digit lies in the expected finite alphabet. -/
theorem residueDigit_mem_interval
    (B base residue nextResidue : ℤ)
    (hB : 0 < B) (hbase : 0 < base)
    (hresidue : 0 ≤ residue ∧ residue < B)
    (hnext : nextResidue = (base * residue) % B) :
    0 ≤ residueDigit B base residue nextResidue ∧
      residueDigit B base residue nextResidue < base := by
  let a := base * residue
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg hbase.le hresidue.1
  have haLt : a < base * B := by
    dsimp [a]
    nlinarith
  have hrem0 : 0 ≤ a % B := Int.emod_nonneg _ hB.ne'
  have hremLt : a % B < B := Int.emod_lt_of_pos _ hB
  have hrecon : a % B + a / B * B = a :=
    Int.emod_add_ediv_mul a B
  have hnum : a - a % B = (a / B) * B := by
    linarith
  have hdiv : B ∣ a - a % B := by
    refine ⟨a / B, ?_⟩
    simpa [mul_comm] using hnum
  have hdigit : residueDigit B base residue nextResidue = a / B := by
    unfold residueDigit
    rw [hnext]
    change (a - a % B) / B = a / B
    rw [Int.ediv_eq_iff_eq_mul_left hB.ne' hdiv]
    simpa [mul_comm] using hnum
  rw [hdigit]
  constructor <;> nlinarith

/-! ## Unit-carry rational shadows -/

/-- Every multiplicative jump product is positive. -/
theorem jumpProduct_pos
    (base x : ℕ → ℕ)
    (hx0 : x 0 = 1)
    (hx : ∀ n, x (n + 1) = base n * x n)
    (hbase : ∀ n, 2 ≤ base n) :
    ∀ n, 0 < x n := by
  intro n
  induction n with
  | zero => simp [hx0]
  | succ n ih =>
      rw [hx n]
      exact Nat.mul_pos (by have := hbase n; omega) ih

/-- One unit-carry shadow coefficient is an exact reciprocal difference. -/
theorem unitCarry_shadow_term
    (base x : ℕ → ℕ)
    (hx0 : x 0 = 1)
    (hx : ∀ n, x (n + 1) = base n * x n)
    (hbase : ∀ n, 2 ≤ base n)
    (n : ℕ) :
    ((base n - 1 : ℕ) : ℚ) / x (n + 1) =
      (1 : ℚ) / x n - (1 : ℚ) / x (n + 1) := by
  have hxn : x n ≠ 0 :=
    Nat.ne_of_gt (jumpProduct_pos base x hx0 hx hbase n)
  have hbn : base n ≠ 0 := by have := hbase n; omega
  rw [hx n]
  norm_num [Nat.cast_sub (by have := hbase n; omega : 1 ≤ base n), hxn, hbn]
  field_simp

/-- Finite telescoping identity for the constant positive carry shadow. -/
theorem unitCarry_shadow_window
    (base x : ℕ → ℕ)
    (hx0 : x 0 = 1)
    (hx : ∀ n, x (n + 1) = base n * x n)
    (hbase : ∀ n, 2 ≤ base n)
    (M L : ℕ) (hML : M ≤ L) :
    ∑ n ∈ Finset.Ico M L,
      ((base n - 1 : ℕ) : ℚ) / x (n + 1) =
      (1 : ℚ) / x M - (1 : ℚ) / x L := by
  induction L with
  | zero =>
      have hM : M = 0 := by omega
      subst M
      simp
  | succ L ih =>
      by_cases hM : M ≤ L
      · rw [Finset.sum_Ico_succ_top hM, ih hM,
          unitCarry_shadow_term base x hx0 hx hbase L]
        ring
      · have hEq : M = L + 1 := by omega
        subst M
        simp

/-- Coefficients obtained by keeping a true finite prefix and replacing the
tail by the unit-carry shadow. -/
def tailSpliceCoeff
    (trueCoeff base : ℕ → ℕ) (M n : ℕ) : ℕ :=
  if n < M then trueCoeff n else base n - 1

/-- Every finite tail splice has an exact rational partial-sum formula.  This
is the finite algebraic core of the rational unit-carry countermodel. -/
theorem tailSplice_partialSum
    (trueCoeff base x : ℕ → ℕ)
    (hx0 : x 0 = 1)
    (hx : ∀ n, x (n + 1) = base n * x n)
    (hbase : ∀ n, 2 ≤ base n)
    (M L : ℕ) (hML : M ≤ L) :
    ∑ n ∈ Finset.Ico 0 L,
      ((tailSpliceCoeff trueCoeff base M n : ℕ) : ℚ) / x (n + 1) =
      (∑ n ∈ Finset.Ico 0 M,
        (trueCoeff n : ℚ) / x (n + 1)) +
      (1 : ℚ) / x M - (1 : ℚ) / x L := by
  rw [← Finset.sum_Ico_consecutive (f := fun n =>
    ((tailSpliceCoeff trueCoeff base M n : ℕ) : ℚ) / x (n + 1))
    (Nat.zero_le M) hML]
  have hprefix :
      (∑ n ∈ Finset.Ico 0 M,
        ((tailSpliceCoeff trueCoeff base M n : ℕ) : ℚ) / x (n + 1)) =
      ∑ n ∈ Finset.Ico 0 M, (trueCoeff n : ℚ) / x (n + 1) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnM := (Finset.mem_Ico.mp hn).2
    simp [tailSpliceCoeff, hnM]
  have htail :
      (∑ n ∈ Finset.Ico M L,
        ((tailSpliceCoeff trueCoeff base M n : ℕ) : ℚ) / x (n + 1)) =
      (1 : ℚ) / x M - (1 : ℚ) / x L := by
    calc
      _ = ∑ n ∈ Finset.Ico M L,
          ((base n - 1 : ℕ) : ℚ) / x (n + 1) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hMn := (Finset.mem_Ico.mp hn).1
        simp [tailSpliceCoeff, Nat.not_lt.mpr hMn]
      _ = _ := unitCarry_shadow_window base x hx0 hx hbase M L hML
  rw [hprefix, htail]
  ring

/-! ## Function-faithful observers -/

/-- Abstract Cartier system together with its symbolic realization. -/
structure CartierRealisation
    (𝕜 State Func Letter : Type*)
    [Semiring 𝕜] [AddCommMonoid State] [Module 𝕜 State]
    [AddCommMonoid Func] [Module 𝕜 Func] where
  step : Letter → State →ₗ[𝕜] State
  cartier : Letter → Func →ₗ[𝕜] Func
  realise : State →ₗ[𝕜] Func
  commutes :
    ∀ a, realise.comp (step a) = (cartier a).comp realise

/-- The exact missing condition: equality in the observer must imply equality
after symbolic realization, not merely after one scalar evaluation. -/
def FunctionFaithfulObserver
    {𝕜 State Func E : Type*}
    [Semiring 𝕜] [AddCommMonoid State] [Module 𝕜 State]
    [AddCommMonoid Func] [Module 𝕜 Func]
    [AddCommMonoid E] [Module 𝕜 E]
    (realise : State →ₗ[𝕜] Func) (C : State →ₗ[𝕜] E) : Prop :=
  LinearMap.ker C ≤ LinearMap.ker realise

/-- Kernel inclusion is exactly the pointwise faithfulness consumed by a
finite quotient argument. -/
theorem realise_eq_of_observer_eq
    {𝕜 State Func E : Type*}
    [Ring 𝕜] [AddCommGroup State] [Module 𝕜 State]
    [AddCommGroup Func] [Module 𝕜 Func]
    [AddCommGroup E] [Module 𝕜 E]
    (realise : State →ₗ[𝕜] Func) (C : State →ₗ[𝕜] E)
    (hfaith : FunctionFaithfulObserver realise C)
    {x y : State} (hxy : C x = C y) :
    realise x = realise y := by
  have hmem : x - y ∈ LinearMap.ker C := by
    simpa [LinearMap.mem_ker] using sub_eq_zero.mpr hxy
  have hout := hfaith hmem
  change realise (x - y) = 0 at hout
  rw [map_sub] at hout
  exact sub_eq_zero.mp hout

/-- An explicit factorization through a finite-dimensional observer forces
the realised symbolic span to be finite-dimensional.  A scalar value alone
does not provide this factorization. -/
theorem finite_realisedSpan_of_factorisation
    {𝕜 State Func E : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup State] [Module 𝕜 State]
    [AddCommGroup Func] [Module 𝕜 Func]
    [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (realise : State →ₗ[𝕜] Func)
    (C : State →ₗ[𝕜] E)
    (readout : E →ₗ[𝕜] Func)
    (hfactor : realise = readout.comp C) :
    FiniteDimensional 𝕜 (LinearMap.range realise) := by
  letI : FiniteDimensional 𝕜 (LinearMap.range readout) :=
    FiniteDimensional.of_surjective readout.rangeRestrict
      readout.surjective_rangeRestrict
  let inclusion :
      LinearMap.range realise →ₗ[𝕜] LinearMap.range readout :=
    { toFun := fun z => ⟨z.1, by
          rcases z.2 with ⟨s, hs⟩
          refine ⟨C s, ?_⟩
          rw [← hs, hfactor]
          rfl⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  have hinj : Function.Injective inclusion := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : LinearMap.range readout => (z : Func)) hxy
  exact FiniteDimensional.of_injective inclusion hinj

/-- A finite-dimensional function-faithful observer already forces the
realised symbolic span to be finite-dimensional; no chosen readout map is
needed.  The realization descends to the quotient by the observer kernel,
which embeds in the finite-dimensional observer range. -/
theorem finite_realisedSpan_of_functionFaithfulObserver
    {𝕜 State Func E : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup State] [Module 𝕜 State]
    [AddCommGroup Func] [Module 𝕜 Func]
    [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (realise : State →ₗ[𝕜] Func)
    (C : State →ₗ[𝕜] E)
    (hfaith : FunctionFaithfulObserver realise C) :
    FiniteDimensional 𝕜 (LinearMap.range realise) := by
  letI : FiniteDimensional 𝕜 (State ⧸ LinearMap.ker C) :=
    FiniteDimensional.of_injective
      C.quotKerEquivRange.toLinearMap C.quotKerEquivRange.injective
  rw [← Submodule.range_liftQ (LinearMap.ker C) realise hfaith]
  infer_instance

end ErdosProblems.Erdos269
