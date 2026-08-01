import ErdosProblems.Erdos269.ThreeChannelBlockRigidity

/-!
# Erdős #269: carry-lift extinction

This module formalizes the exact consumer left by the carry-to-coboundary
audit.  A carry lift naturally satisfies a weighted error recurrence.  If its
induced perturbation were nevertheless block-null and had the two genuine
anchors, the existing three-channel rigidity theorem would kill the
perturbation and force exponential error growth.

No declaration constructs the missing bounded residue lift or asserts
irrationality of the `{2,3,5}` running-LCM series.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-! ## Lift algebra and the weighted block defect -/

/-- Shell perturbation reconstructed from an integer lift. -/
def carryLiftPerturbation
    (base digit z : ℕ → ℤ) (n : ℕ) : ℤ :=
  base n * z n - z (n + 1) - digit n

/-- Integral error between a lift and the exact carry. -/
def carryLiftError
    (D : ℤ) (z carry : ℕ → ℤ) (n : ℕ) : ℤ :=
  D * z n - carry n

/-- The exact one-step weighted-coboundary identity. -/
theorem carryLiftError_succ
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (n : ℕ) :
    carryLiftError D z carry (n + 1) =
      base n * carryLiftError D z carry n -
        D * carryLiftPerturbation base digit z n := by
  simp only [carryLiftError, carryLiftPerturbation]
  rw [hcarry n]
  ring

/-- Finite telescoping for consecutive differences. -/
theorem sum_Ico_sub_succ
    (E : ℕ → ℤ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (E n - E (n + 1)) =
      E a - E b := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ico_succ_top hab', ih hab']
        ring
      · have ha : a = b + 1 := by omega
        subst a
        simp

/-- Summing the carry recurrence gives the exact weighted block defect.  The
last sum is the obstruction to obtaining ordinary `ChannelBlockNull`. -/
theorem carryLift_blockDefect
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (a b : ℕ) (hab : a ≤ b) :
    D * (∑ n ∈ Finset.Ico a b,
      carryLiftPerturbation base digit z n) =
      carryLiftError D z carry a -
        carryLiftError D z carry b +
      ∑ n ∈ Finset.Ico a b,
        (base n - 1) * carryLiftError D z carry n := by
  have hstep : ∀ n,
      D * carryLiftPerturbation base digit z n =
        carryLiftError D z carry n -
          carryLiftError D z carry (n + 1) +
        (base n - 1) * carryLiftError D z carry n := by
    intro n
    have h := carryLiftError_succ D base digit z carry hcarry n
    linarith
  rw [Finset.mul_sum]
  calc
    (∑ n ∈ Finset.Ico a b,
        D * carryLiftPerturbation base digit z n) =
        ∑ n ∈ Finset.Ico a b,
          ((carryLiftError D z carry n -
              carryLiftError D z carry (n + 1)) +
            (base n - 1) * carryLiftError D z carry n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact hstep n
    _ = (∑ n ∈ Finset.Ico a b,
          (carryLiftError D z carry n -
            carryLiftError D z carry (n + 1))) +
        ∑ n ∈ Finset.Ico a b,
          (base n - 1) * carryLiftError D z carry n := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_Ico_sub_succ _ a b hab]

/-! ## Two-anchor extinction and exponential error growth -/

/-- Direct consumer of the checked channel-potential classification and
two-anchor extinction theorem. -/
theorem perturbation_eq_zero_of_blockNull_twoAnchors
    {jumpBase : ℕ → Prime235}
    {ε : ℕ → ℤ}
    (hbase : Function.Surjective jumpBase)
    (hnull : ChannelBlockNull jumpBase ε)
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 : ε n23 = 0)
    (hanchor25 : ε n25 = 0) :
    ∀ n, ε n = 0 := by
  rcases
      (channelBlockNull_iff_channelPotential
        jumpBase ε hbase).mp hnull with
    ⟨C, hpotential⟩
  exact channelCoboundary_eq_zero_of_two_anchors
    hpotential
    h23start h23end
    h25start h25end
    hanchor23 hanchor25

/-- Once the perturbation vanishes, the lift error is exactly the product of
all previous bases times its initial value. -/
theorem carryLiftError_eq_product_of_perturbation_zero
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (hzero :
      ∀ n, carryLiftPerturbation base digit z n = 0) :
    ∀ N,
      carryLiftError D z carry N =
        (∏ n ∈ Finset.range N, base n) *
          carryLiftError D z carry 0 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [carryLiftError_succ D base digit z carry hcarry]
      simp only [hzero, mul_zero, sub_zero, ih, Finset.prod_range_succ]
      ring

/-- Products of integer bases at least two grow at least as fast as `2^N`. -/
theorem two_pow_le_natAbs_prod_range
    (base : ℕ → ℤ)
    (hbaseTwo : ∀ n, (2 : ℤ) ≤ base n) :
    ∀ N, 2 ^ N ≤
      Int.natAbs (∏ n ∈ Finset.range N, base n) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, Int.natAbs_mul, pow_succ]
      apply Nat.mul_le_mul ih
      have hbnonneg : 0 ≤ base N := (by have := hbaseTwo N; omega)
      have hbcast : (2 : ℤ) ≤ (Int.natAbs (base N) : ℤ) := by
        simpa [Int.natAbs_of_nonneg hbnonneg] using hbaseTwo N
      exact_mod_cast hbcast

/-- Complete extinction consumer with an arbitrary error bound.  It suffices
that the proposed bound falls below `2^N` once. -/
theorem no_carryLift_of_errorBound_below_twoPow
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (jumpBase : ℕ → Prime235)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (hchannel : Function.Surjective jumpBase)
    (hnull :
      ChannelBlockNull jumpBase
        (carryLiftPerturbation base digit z))
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 :
      carryLiftPerturbation base digit z n23 = 0)
    (hanchor25 :
      carryLiftPerturbation base digit z n25 = 0)
    (herror0 : carryLiftError D z carry 0 ≠ 0)
    (bound : ℕ → ℕ)
    (hbounded :
      ∀ n, Int.natAbs (carryLiftError D z carry n) ≤ bound n)
    (hbaseTwo : ∀ n, (2 : ℤ) ≤ base n)
    (N : ℕ) (hbelow : bound N < 2 ^ N) :
    False := by
  have hzero :
      ∀ n, carryLiftPerturbation base digit z n = 0 :=
    perturbation_eq_zero_of_blockNull_twoAnchors
      hchannel hnull
      h23start h23end h25start h25end
      hanchor23 hanchor25
  have hproduct :=
    carryLiftError_eq_product_of_perturbation_zero
      D base digit z carry hcarry hzero N
  have hproductAbs := congrArg Int.natAbs hproduct
  rw [Int.natAbs_mul] at hproductAbs
  have herror0Pos :
      0 < Int.natAbs (carryLiftError D z carry 0) :=
    Int.natAbs_pos.mpr herror0
  have herror0One :
      1 ≤ Int.natAbs (carryLiftError D z carry 0) := by
    omega
  have hlower :
      2 ^ N ≤ Int.natAbs (carryLiftError D z carry N) := by
    rw [hproductAbs]
    calc
      2 ^ N ≤
          Int.natAbs (∏ n ∈ Finset.range N, base n) :=
        two_pow_le_natAbs_prod_range base hbaseTwo N
      _ = Int.natAbs (∏ n ∈ Finset.range N, base n) * 1 := by
        simp
      _ ≤ Int.natAbs (∏ n ∈ Finset.range N, base n) *
          Int.natAbs (carryLiftError D z carry 0) :=
        Nat.mul_le_mul_left _ herror0One
  have := hbounded N
  omega

/-- Uniformly bounded nonzero lift errors are therefore impossible. -/
theorem no_bounded_carryLift_of_blockNull_twoAnchors
    (D : ℤ)
    (base digit z carry : ℕ → ℤ)
    (jumpBase : ℕ → Prime235)
    (hcarry :
      ∀ n, carry (n + 1) =
        base n * carry n - D * digit n)
    (hchannel : Function.Surjective jumpBase)
    (hnull :
      ChannelBlockNull jumpBase
        (carryLiftPerturbation base digit z))
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 :
      carryLiftPerturbation base digit z n23 = 0)
    (hanchor25 :
      carryLiftPerturbation base digit z n25 = 0)
    (herror0 : carryLiftError D z carry 0 ≠ 0)
    (M : ℕ)
    (hbounded :
      ∀ n, Int.natAbs (carryLiftError D z carry n) ≤ M)
    (hbaseTwo : ∀ n, (2 : ℤ) ≤ base n) :
    False := by
  apply no_carryLift_of_errorBound_below_twoPow
    D base digit z carry jumpBase hcarry
    hchannel hnull
    h23start h23end h25start h25end
    hanchor23 hanchor25 herror0
    (fun _ => M) hbounded hbaseTwo (M + 1)
  exact (Nat.lt_succ_self M).trans (M + 1).lt_two_pow_self

/-! ## Exact first-block obstruction -/

/-- An integer within distance one of a real number in `(0,1)` is binary. -/
theorem int_eq_zero_or_one_of_unit_accuracy
    {T : ℝ} {z : ℤ}
    (hTpos : 0 < T) (hTone : T < 1)
    (hacc : |(z : ℝ) - T| < 1) :
    z = 0 ∨ z = 1 := by
  rw [abs_lt] at hacc
  have hzLower : (-1 : ℝ) < (z : ℝ) := by linarith
  have hzUpper : (z : ℝ) < 2 := by linarith
  have hzLowerInt : (-1 : ℤ) < z := by exact_mod_cast hzLower
  have hzUpperInt : z < (2 : ℤ) := by exact_mod_cast hzUpper
  omega

/-- For four binary lifts, the two desired anchors force the middle
perturbation to be one, hence the first complete `2`-block sum is one. -/
theorem binaryLift_twoAnchors_force_firstBlock_sum_one
    (z0 z1 z2 z3 : ℤ)
    (hz0 : z0 = 0 ∨ z0 = 1)
    (hz1 : z1 = 0 ∨ z1 = 1)
    (hz2 : z2 = 0 ∨ z2 = 1)
    (hz3 : z3 = 0 ∨ z3 = 1)
    (hanchor23 : 2 * z0 - z1 - 1 = 0)
    (hanchor25 : 2 * z2 - z3 - 1 = 0) :
    (2 * z0 - z1 - 1) +
      (3 * z1 - z2 - 1) = 1 := by
  rcases hz0 with hz0 | hz0 <;>
    rcases hz1 with hz1 | hz1 <;>
      rcases hz2 with hz2 | hz2 <;>
        rcases hz3 with hz3 | hz3
  all_goals omega

/-- Representation-independent four-state obstruction: no lift accurate to
within one at four states in `(0,1)` can have both anchors and a null first
`2`-block. -/
theorem no_unitAccurateLift_with_twoAnchors_and_firstTwoBlockNull
    (T0 T1 T2 T3 : ℝ)
    (z0 z1 z2 z3 : ℤ)
    (hT0 : 0 < T0 ∧ T0 < 1)
    (hT1 : 0 < T1 ∧ T1 < 1)
    (hT2 : 0 < T2 ∧ T2 < 1)
    (hT3 : 0 < T3 ∧ T3 < 1)
    (hacc0 : |(z0 : ℝ) - T0| < 1)
    (hacc1 : |(z1 : ℝ) - T1| < 1)
    (hacc2 : |(z2 : ℝ) - T2| < 1)
    (hacc3 : |(z3 : ℝ) - T3| < 1)
    (hanchor23 : 2 * z0 - z1 - 1 = 0)
    (hanchor25 : 2 * z2 - z3 - 1 = 0)
    (hfirstBlock :
      (2 * z0 - z1 - 1) +
        (3 * z1 - z2 - 1) = 0) :
    False := by
  have hz0 :=
    int_eq_zero_or_one_of_unit_accuracy hT0.1 hT0.2 hacc0
  have hz1 :=
    int_eq_zero_or_one_of_unit_accuracy hT1.1 hT1.2 hacc1
  have hz2 :=
    int_eq_zero_or_one_of_unit_accuracy hT2.1 hT2.2 hacc2
  have hz3 :=
    int_eq_zero_or_one_of_unit_accuracy hT3.1 hT3.2 hacc3
  have hsum :=
    binaryLift_twoAnchors_force_firstBlock_sum_one
      z0 z1 z2 z3 hz0 hz1 hz2 hz3 hanchor23 hanchor25
  omega

/-- If the first and third boundaries are both channel `2`, a signed first
block sum equal to one directly refutes `ChannelBlockNull`. -/
theorem not_channelBlockNull_of_firstTwoBlock_sum_one
    (jumpBase : ℕ → Prime235) (ε : ℕ → ℤ)
    (hbase0 : jumpBase 0 = .two)
    (hbase2 : jumpBase 2 = .two)
    (hsum : ε 0 + ε 1 = 1) :
    ¬ ChannelBlockNull jumpBase ε := by
  intro hnull
  have hprefix := hnull 0 2 (hbase0.trans hbase2.symm)
  simp [channelPrefix, Finset.sum_range_succ] at hprefix
  omega

end ErdosProblems.Erdos269
