import Erdos249257.DiagonalFreshLossBridge

/-!
# Fresh-prime deficit decomposition

This module rewrites the literal foreign Möbius channel from
`DiagonalFreshLossBridge` in the endpoint coordinates used by the governed
Möbius-curvature and weighted-deficit probes.

At a height `H`, the old-prime model at the endpoint `k * H + s` keeps the
prime support already present in `H`.  Its value is

`((k * H + s) / gcd(rad(H), s)) * φ(gcd(rad(H), s))`.

The actual diagonal increment is exactly the old increment plus the lower
endpoint deficit minus the upper endpoint deficit.  Applying one or two
curvature operators gives the coefficient rows `[-2, 1, 1]` and
`[-8, 4, 2, 1, 1]` used by the arithmetic probes.  The final inequalities
are purely ordered-ring consequences.  A general divisor-support lemma proves
the endpoint deficits nonnegative, so the displayed adverse weighted deficit
is unconditionally the only loss from the old-prime margin.

No cofinal deficit bound or irrationality conclusion is asserted here.
-/

namespace Erdos249257.DiagonalFreshLossBridge

open scoped BigOperators

/-- The old-prime endpoint mass at `k * H + s`.  Only the prime support in
the radical of `H` is retained; the gcd can be taken with `s` because that
radical divides `H`. -/
def oldPrimeEndpointMass (H k s : ℕ) : ℤ :=
  let R := RadicalMobiusShadow.squarefreeKernel H
  let g := R.gcd s
  ((((k * H + s) / g) * g.totient : ℕ) : ℤ)

/-- The signed loss from the old-prime endpoint model to the actual Euler
totient. -/
def endpointFreshDeficit (H k s : ℕ) : ℤ :=
  oldPrimeEndpointMass H k s - (Nat.totient (k * H + s) : ℤ)

/-- Adding prime support can only lower Euler's density: if `g ∣ n`, then
`φ(n) / n ≤ φ(g) / g`, stated without division. -/
theorem totient_mul_le_mul_totient_of_dvd
    {g n : ℕ} (hg : 0 < g) (hn : 0 < n) (hgn : g ∣ n) :
    n.totient * g ≤ n * g.totient := by
  classical
  let f : ℕ → ℚ := fun p => 1 - (p : ℚ)⁻¹
  have hsubset : g.primeFactors ⊆ n.primeFactors :=
    Nat.primeFactors_mono hgn hn.ne'
  have hprod :
      (∏ p ∈ n.primeFactors, f p) ≤
        ∏ p ∈ g.primeFactors, f p := by
    apply Finset.prod_le_prod_of_subset_of_le_one hsubset
    · intro p hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpOne : (1 : ℚ) ≤ (p : ℚ) := by
        exact_mod_cast hpPrime.one_le
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hpOne)
    · intro p _hp _hnew
      have hpInv : (0 : ℚ) ≤ (p : ℚ)⁻¹ := by positivity
      linarith
  have hscale : (0 : ℚ) ≤ (n : ℚ) * (g : ℚ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hprod hscale
  have hq :
      (n.totient : ℚ) * (g : ℚ) ≤
        (n : ℚ) * (g.totient : ℚ) := by
    rw [Nat.totient_eq_mul_prod_factors n,
      Nat.totient_eq_mul_prod_factors g]
    change
      ((n : ℚ) * ∏ p ∈ n.primeFactors, f p) * (g : ℚ) ≤
        (n : ℚ) * ((g : ℚ) * ∏ p ∈ g.primeFactors, f p)
    convert hscaled using 1 <;> ring
  exact_mod_cast hq

/-- Division form of `totient_mul_le_mul_totient_of_dvd`. -/
theorem totient_le_div_mul_totient_of_dvd
    {g n : ℕ} (hg : 0 < g) (hn : 0 < n) (hgn : g ∣ n) :
    n.totient ≤ (n / g) * g.totient := by
  have hmul := totient_mul_le_mul_totient_of_dvd hg hn hgn
  have hscaled : n.totient * g ≤ ((n / g) * g.totient) * g := by
    calc
      n.totient * g ≤ n * g.totient := hmul
      _ = ((n / g) * g) * g.totient :=
        congrArg (fun x => x * g.totient) (Nat.div_mul_cancel hgn).symm
      _ = ((n / g) * g.totient) * g := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hscaled hg

/-- Every old-prime endpoint mass dominates the actual totient. -/
theorem endpointFreshDeficit_nonneg
    (H k s : ℕ) (hH : 0 < H) (hk : 0 < k) :
    0 ≤ endpointFreshDeficit H k s := by
  let R := RadicalMobiusShadow.squarefreeKernel H
  let g := R.gcd s
  have hRpos : 0 < R := RadicalMobiusShadow.squarefreeKernel_pos H
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left s hRpos
  have hRdH : R ∣ H := RadicalMobiusShadow.squarefreeKernel_dvd H
  have hgdH : g ∣ H := (Nat.gcd_dvd_left R s).trans hRdH
  have hgds : g ∣ s := Nat.gcd_dvd_right R s
  have hgdn : g ∣ k * H + s :=
    Nat.dvd_add (dvd_mul_of_dvd_right hgdH k) hgds
  have hnpos : 0 < k * H + s := by positivity
  have htot :=
    totient_le_div_mul_totient_of_dvd hgpos hnpos hgdn
  unfold endpointFreshDeficit oldPrimeEndpointMass
  change 0 ≤ ((((k * H + s) / g) * g.totient : ℕ) : ℤ) -
    (Nat.totient (k * H + s) : ℤ)
  exact sub_nonneg.mpr (by exact_mod_cast htot)

/-- The old Möbius increment is the height-density
`(H / gcd(rad(H),s)) * φ(gcd(rad(H),s))`. -/
theorem oldMobiusIncrement_eq_div_gcd_mul_totient
    (H s : ℕ) (hH : 0 < H) :
    oldMobiusIncrement H s =
      (((H / (RadicalMobiusShadow.squarefreeKernel H).gcd s) *
          ((RadicalMobiusShadow.squarefreeKernel H).gcd s).totient : ℕ) : ℤ) := by
  let R := RadicalMobiusShadow.squarefreeKernel H
  let g := R.gcd s
  have hRdH : R ∣ H := RadicalMobiusShadow.squarefreeKernel_dvd H
  have hgdR : g ∣ R := Nat.gcd_dvd_left R s
  rw [oldMobiusIncrement_eq_scale_gcdWordCoeff H s hH]
  change (((H / R : ℕ) : ℤ)) *
      (RepunitMobiusNumerator.gcdWordCoeff R s : ℤ) =
    ((((H / g) * g.totient : ℕ) : ℤ))
  rw [RepunitMobiusNumerator.gcdWordCoeff]
  change (((H / R : ℕ) : ℤ)) * ((((R / g) * g.totient : ℕ) : ℤ)) =
    ((((H / g) * g.totient : ℕ) : ℤ))
  have hdiv : H / g = (H / R) * (R / g) :=
    (Nat.div_mul_div hRdH hgdR).symm
  rw [hdiv]
  push_cast
  ring

/-- The endpoint old-prime mass is affine in the endpoint multiplier `k`;
its slope is exactly the landed old Möbius increment. -/
theorem oldPrimeEndpointMass_eq_affine
    (H k s : ℕ) (hH : 0 < H) :
    oldPrimeEndpointMass H k s =
      (k : ℤ) * oldMobiusIncrement H s +
        ((((s / (RadicalMobiusShadow.squarefreeKernel H).gcd s) *
            ((RadicalMobiusShadow.squarefreeKernel H).gcd s).totient : ℕ) : ℤ)) := by
  let R := RadicalMobiusShadow.squarefreeKernel H
  let g := R.gcd s
  have hRpos : 0 < R := RadicalMobiusShadow.squarefreeKernel_pos H
  have hRdH : R ∣ H := RadicalMobiusShadow.squarefreeKernel_dvd H
  have hgdR : g ∣ R := Nat.gcd_dvd_left R s
  have hgdH : g ∣ H := hgdR.trans hRdH
  have hgdMul : g ∣ k * H := dvd_mul_of_dvd_right hgdH k
  have hquot : (k * H + s) / g = k * (H / g) + s / g := by
    rw [Nat.add_div_of_dvd_right hgdMul, Nat.mul_div_assoc k hgdH]
  rw [oldPrimeEndpointMass, hquot,
    oldMobiusIncrement_eq_div_gcd_mul_totient H s hH]
  change (((k * (H / g) + s / g) * g.totient : ℕ) : ℤ) =
    (k : ℤ) * ((((H / g) * g.totient : ℕ) : ℤ)) +
      ((((s / g) * g.totient : ℕ) : ℤ))
  push_cast
  ring

/-- The upper old-prime endpoint mass minus the lower one is exactly one old
Möbius increment. -/
theorem oldPrimeEndpointMass_two_sub_one
    (H s : ℕ) (hH : 0 < H) :
    oldPrimeEndpointMass H 2 s - oldPrimeEndpointMass H 1 s =
      oldMobiusIncrement H s := by
  rw [oldPrimeEndpointMass_eq_affine H 2 s hH,
    oldPrimeEndpointMass_eq_affine H 1 s hH]
  ring

/-- Exact endpoint-deficit decomposition of the actual height increment. -/
theorem diagonalHeightIncrement_eq_old_add_endpointFreshDeficits
    (H s : ℕ) (hH : 0 < H) :
    diagonalHeightIncrement H s =
      oldMobiusIncrement H s + endpointFreshDeficit H 1 s -
        endpointFreshDeficit H 2 s := by
  have hmass := oldPrimeEndpointMass_two_sub_one H s hH
  unfold diagonalHeightIncrement endpointFreshDeficit
  norm_num only [one_mul, two_mul]
  rw [show H + s = 1 * H + s by omega]
  linarith

/-- The literal foreign Möbius channel is precisely lower endpoint deficit
minus upper endpoint deficit. -/
theorem finiteForeignChannelIncrement_eq_endpointFreshDeficit_sub
    (H s : ℕ) (hH : 0 < H) :
    finiteForeignChannelIncrement H s =
      endpointFreshDeficit H 1 s - endpointFreshDeficit H 2 s := by
  have hsplit :=
    diagonalHeightIncrement_eq_oldMobius_add_finiteForeign H s hH
  have hendpoint :=
    diagonalHeightIncrement_eq_old_add_endpointFreshDeficits H s hH
  linarith

/-- Discrete second difference, in the offset convention of the
Möbius-curvature probe. -/
def offsetCurvature (f : ℕ → ℤ) (s : ℕ) : ℤ :=
  f (s + 1) - 2 * f s + f (s + 2)

/-- The two-step affine branch used by the three-rank probe. -/
def fourCurvaturePlusShift (f : ℕ → ℤ) (s : ℕ) : ℤ :=
  4 * offsetCurvature f s + offsetCurvature f (s + 2)

/-- The two-step branch has the exact five-letter coefficient row
`[-8, 4, 2, 1, 1]`. -/
theorem fourCurvaturePlusShift_eq_fivePoint (f : ℕ → ℤ) (s : ℕ) :
    fourCurvaturePlusShift f s =
      -8 * f s + 4 * f (s + 1) + 2 * f (s + 2) +
        f (s + 3) + f (s + 4) := by
  unfold fourCurvaturePlusShift offsetCurvature
  rw [show s + 2 + 1 = s + 3 by omega,
    show s + 2 + 2 = s + 4 by omega]
  ring

/-- Exact Möbius-curvature split into the old density curvature and the two
endpoint deficit curvatures. -/
theorem offsetCurvature_diagonalHeightIncrement_eq_old_add_deficits
    (H s : ℕ) (hH : 0 < H) :
    offsetCurvature (diagonalHeightIncrement H) s =
      offsetCurvature (oldMobiusIncrement H) s +
        offsetCurvature (endpointFreshDeficit H 1) s -
          offsetCurvature (endpointFreshDeficit H 2) s := by
  simp only [offsetCurvature]
  rw [diagonalHeightIncrement_eq_old_add_endpointFreshDeficits H s hH,
    diagonalHeightIncrement_eq_old_add_endpointFreshDeficits H (s + 1) hH,
    diagonalHeightIncrement_eq_old_add_endpointFreshDeficits H (s + 2) hH]
  ring

/-- Exact five-point weighted-deficit split. -/
theorem fourCurvaturePlusShift_diagonalHeightIncrement_eq_old_add_deficits
    (H s : ℕ) (hH : 0 < H) :
    fourCurvaturePlusShift (diagonalHeightIncrement H) s =
      fourCurvaturePlusShift (oldMobiusIncrement H) s +
        fourCurvaturePlusShift (endpointFreshDeficit H 1) s -
          fourCurvaturePlusShift (endpointFreshDeficit H 2) s := by
  unfold fourCurvaturePlusShift
  rw [offsetCurvature_diagonalHeightIncrement_eq_old_add_deficits H s hH,
    offsetCurvature_diagonalHeightIncrement_eq_old_add_deficits H (s + 2) hH]
  ring

/-- The adverse deficit budget for the first curvature branch. -/
def firstBranchAdverseDeficit (H s : ℕ) : ℤ :=
  2 * endpointFreshDeficit H 1 s + endpointFreshDeficit H 2 (s + 1) +
    endpointFreshDeficit H 2 (s + 2)

/-- The adverse deficit budget for the five-point branch. -/
def secondBranchAdverseDeficit (H s : ℕ) : ℤ :=
  8 * endpointFreshDeficit H 1 s +
    4 * endpointFreshDeficit H 2 (s + 1) +
    2 * endpointFreshDeficit H 2 (s + 2) +
    endpointFreshDeficit H 2 (s + 3) +
    endpointFreshDeficit H 2 (s + 4)

/-- Nonnegative endpoint deficits reduce the old first-branch margin by at
most the exact adverse weighted deficit used by the finite probe. -/
theorem oldCurvature_sub_firstBranchAdverseDeficit_le_actual
    (H s : ℕ) (hH : 0 < H) :
    offsetCurvature (oldMobiusIncrement H) s -
        firstBranchAdverseDeficit H s ≤
      offsetCurvature (diagonalHeightIncrement H) s := by
  have hLow1 := endpointFreshDeficit_nonneg H 1 (s + 1) hH (by omega)
  have hLow2 := endpointFreshDeficit_nonneg H 1 (s + 2) hH (by omega)
  have hTop0 := endpointFreshDeficit_nonneg H 2 s hH (by omega)
  rw [offsetCurvature_diagonalHeightIncrement_eq_old_add_deficits H s hH]
  unfold offsetCurvature firstBranchAdverseDeficit
  linarith

/-- Nonnegative endpoint deficits reduce the old five-point margin by at
most the exact adverse weighted deficit used by the finite probe. -/
theorem oldFivePoint_sub_secondBranchAdverseDeficit_le_actual
    (H s : ℕ) (hH : 0 < H) :
    fourCurvaturePlusShift (oldMobiusIncrement H) s -
        secondBranchAdverseDeficit H s ≤
      fourCurvaturePlusShift (diagonalHeightIncrement H) s := by
  have hLow1 := endpointFreshDeficit_nonneg H 1 (s + 1) hH (by omega)
  have hLow2 := endpointFreshDeficit_nonneg H 1 (s + 2) hH (by omega)
  have hLow3 := endpointFreshDeficit_nonneg H 1 (s + 3) hH (by omega)
  have hLow4 := endpointFreshDeficit_nonneg H 1 (s + 4) hH (by omega)
  have hTop0 := endpointFreshDeficit_nonneg H 2 s hH (by omega)
  rw [fourCurvaturePlusShift_diagonalHeightIncrement_eq_old_add_deficits H s hH]
  rw [fourCurvaturePlusShift_eq_fivePoint,
    fourCurvaturePlusShift_eq_fivePoint,
    fourCurvaturePlusShift_eq_fivePoint]
  unfold secondBranchAdverseDeficit
  linarith

#print axioms oldMobiusIncrement_eq_div_gcd_mul_totient
#print axioms endpointFreshDeficit_nonneg
#print axioms oldPrimeEndpointMass_eq_affine
#print axioms diagonalHeightIncrement_eq_old_add_endpointFreshDeficits
#print axioms finiteForeignChannelIncrement_eq_endpointFreshDeficit_sub
#print axioms fourCurvaturePlusShift_eq_fivePoint
#print axioms offsetCurvature_diagonalHeightIncrement_eq_old_add_deficits
#print axioms fourCurvaturePlusShift_diagonalHeightIncrement_eq_old_add_deficits
#print axioms oldCurvature_sub_firstBranchAdverseDeficit_le_actual
#print axioms oldFivePoint_sub_secondBranchAdverseDeficit_le_actual

end Erdos249257.DiagonalFreshLossBridge
