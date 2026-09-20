import Erdos249257.JointExponentTransport

/-! The long #249 manuscript's affine annihilation of the specified divisor
terms (`catalogue:mob:e3`): the closed form of the `d`th Möbius term of
`R_{mH}`, its affineness in the multiplier `m`, the annihilation by any
finite family of coefficients with vanishing zeroth and first moments, the
particular four multipliers `(1,3,5,15)` with coefficients `(4,-3,-2,1)`,
their moments `0, 0, 152`, and the finite-depth truncation with its sharp
error radius `19H + 5L + 5`. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.ExponentOnlyTransport
open Erdos249257.JointExponentTransport
open scoped BigOperators

/-- The manuscript's `K_d(N) = N/(d(2ᵈ-1)) + 2ᵈ/(2ᵈ-1)²`, the `d`th term of
the Möbius expansion of `R_N` with its sign `μ(d)` removed. -/
def mobiusTermKernel (d N : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)) + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)

/-- **The `d`th Möbius term at a multiple of `d`** (`catalogue:mob:e3`,
first sentence): for `d > 0` with `d ∣ N`, the transport kernel is
`μ(d)·K_d(N)`, which is affine in `N` and hence in the multiplier `m` when
`N = mH`. -/
theorem transportResidueKernel_eq_mobiusTermKernel {d N : ℕ}
    (hd : 0 < d) (hdN : d ∣ N) :
    transportResidueKernel d N
      = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * mobiusTermKernel d N := by
  have hmod : N % d = 0 := Nat.mod_eq_zero_of_dvd hdN
  have hoff : transportResidueOffset d N = d := by
    simp [transportResidueOffset, hmod]
  have hd2 : (2 : ℝ) ≤ (2 : ℝ) ^ d := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hne : (2 : ℝ) ^ d - 1 ≠ 0 := by linarith
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [transportResidueKernel, hoff, mobiusTermKernel, Nat.sub_self, pow_zero]
  push_cast
  field_simp
  ring

/-- **Affine annihilation** (`catalogue:mob:e3`, second sentence): a finite
family of real coefficients whose zeroth and first moments vanish kills every
`K_d` term along the ray `H ↦ mH`. -/
theorem mobiusTermKernel_moment_annihilation
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (m : ι → ℕ) (d H : ℕ)
    (hzero : ∑ i, c i = 0) (hfirst : ∑ i, c i * (m i : ℝ) = 0) :
    ∑ i, c i * mobiusTermKernel d (m i * H) = 0 := by
  have hsplit : ∀ i : ι, c i * mobiusTermKernel d (m i * H)
      = (c i * (m i : ℝ)) * ((H : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)))
        + c i * ((2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)) := by
    intro i
    simp only [mobiusTermKernel]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, hzero, hfirst]
  ring

/-- **The four multipliers `(1,3,5,15)` with coefficients `(4,-3,-2,1)`**
(`catalogue:mob:e3`, display): `K_d(15H) - 3K_d(3H) - 2K_d(5H) + 4K_d(H) = 0`
for every `d` and `H`. -/
theorem joint35_mobiusTermKernel_zero (d H : ℕ) :
    mobiusTermKernel d (15 * H) - 3 * mobiusTermKernel d (3 * H)
      - 2 * mobiusTermKernel d (5 * H) + 4 * mobiusTermKernel d H = 0 := by
  simp only [mobiusTermKernel]
  push_cast
  ring

/-- **The moments of the four coefficients**: the zeroth and first moments of
`(4,-3,-2,1)` against the multipliers `(1,3,5,15)` vanish while the second is
`152`; equivalently `XY - 3X - 2Y + 4` takes the values `0, 0, 152` at
`(1,1)`, `(3,5)`, `(9,25)`. -/
theorem joint35_coefficient_moments :
    ((4 : ℝ) + (-3) + (-2) + 1 = 0)
      ∧ ((4 : ℝ) * 1 + (-3) * 3 + (-2) * 5 + 1 * 15 = 0)
      ∧ ((4 : ℝ) * 1 ^ 2 + (-3) * 3 ^ 2 + (-2) * 5 ^ 2 + 1 * 15 ^ 2 = 152)
      ∧ ((1 : ℝ) * 1 - 3 * 1 - 2 * 1 + 4 = 0)
      ∧ ((3 : ℝ) * 5 - 3 * 3 - 2 * 5 + 4 = 0)
      ∧ ((9 : ℝ) * 25 - 3 * 9 - 2 * 25 + 4 = 152) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The truncation at depth `L`** (`catalogue:mob:e3`, second display): the
finite window `U` is `joint35ConeWindow H L`, and
`2ᴸ(R_{15H} - 3R_{3H} - 2R_{5H} + 4R_H) - U` equals the shifted-tail error
`(R_{15H+L} + 4R_{H+L}) - (3R_{3H+L} + 2R_{5H+L})`, whose absolute value is at
most `19H + 5L + 5`.  Both parenthesised terms lie between `0` and that same
bound, by `0 ≤ R_n ≤ n+1`. -/
theorem joint35_truncation_error (H L : ℕ) (hH : 1 ≤ H) :
    (2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)
      = (totientTail (15 * H + L) + 4 * totientTail (H + L))
        - (3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L))
    ∧ |(2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)|
      ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)
    ∧ (0 ≤ totientTail (15 * H + L) + 4 * totientTail (H + L)
        ∧ totientTail (15 * H + L) + 4 * totientTail (H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ))
    ∧ (0 ≤ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
        ∧ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)) := by
  have hsplit := two_pow_mul_joint35Cone_eq_window_add_shifted H L
  have hbound := abs_joint35ConeShiftedTail_le H L hH
  have h15p := totientTail_pos (15 * H + L)
  have h3p := totientTail_pos (3 * H + L)
  have h5p := totientTail_pos (5 * H + L)
  have h1p := totientTail_pos (H + L)
  have h15u := totientTail_le_succ (15 * H + L) (by omega)
  have h3u := totientTail_le_succ (3 * H + L) (by omega)
  have h5u := totientTail_le_succ (5 * H + L) (by omega)
  have h1u := totientTail_le_succ (H + L) (by omega)
  have herr : (2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
      - 2 * totientTail (5 * H) + 4 * totientTail H)
      - (joint35ConeWindow H L : ℝ) = joint35ConeShiftedTail H L := by
    have h := hsplit
    unfold joint35ConeTail at h
    linarith
  refine ⟨?_, ?_, ⟨by linarith, ?_⟩, ⟨by linarith, ?_⟩⟩
  · rw [herr]
    unfold joint35ConeShiftedTail
    ring
  · rw [herr]
    have : ((19 * H + 5 * L + 5 : ℕ) : ℝ) = ((sharpJoint35ConeRadius H L : ℤ) : ℝ) := by
      unfold sharpJoint35ConeRadius
      push_cast
      ring
    rw [this]
    exact hbound
  · push_cast at h15u h1u ⊢
    linarith
  · push_cast at h3u h5u ⊢
    linarith

/-- **The sufficient nonintegrality condition** (`catalogue:mob:e3`, last
display): if `19H + 5L + 5 < U mod 2ᴸ < 2ᴸ - (19H + 5L + 5)` then the
four-tail combination is not an integer. -/
theorem joint35_nonintegral_of_separated_window {H L : ℕ} (hH : 1 ≤ H)
    (hlow : ((19 * H + 5 * L + 5 : ℕ) : ℤ) < joint35ConeWindow H L % 2 ^ L)
    (hhigh : joint35ConeWindow H L % 2 ^ L
      < 2 ^ L - ((19 * H + 5 * L + 5 : ℕ) : ℤ)) :
    (totientTail (15 * H) - 3 * totientTail (3 * H)
      - 2 * totientTail (5 * H) + 4 * totientTail H) ∉ Set.range ((↑) : ℤ → ℝ) := by
  have hradius : ((19 * H + 5 * L + 5 : ℕ) : ℤ) = sharpJoint35ConeRadius H L := by
    unfold sharpJoint35ConeRadius
    push_cast
    ring
  have hcert : sharpJoint35ConeCert H L := by
    constructor
    · rw [← hradius]; exact hlow
    · rw [← hradius]; exact hhigh
  have h := joint35Cone_notMem_int_of_cert hH hcert
  unfold joint35ConeTail at h
  exact h

#print axioms transportResidueKernel_eq_mobiusTermKernel
#print axioms mobiusTermKernel_moment_annihilation
#print axioms joint35_mobiusTermKernel_zero
#print axioms joint35_coefficient_moments
#print axioms joint35_truncation_error
#print axioms joint35_nonintegral_of_separated_window
end ErdosProblems.Erdos249.PaperCompleteR21
