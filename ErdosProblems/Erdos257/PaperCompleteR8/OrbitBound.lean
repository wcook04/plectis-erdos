import ErdosProblems.Erdos257.PaperCompleteR8.FiniteMeans
import ErdosProblems.Erdos257.WeightedSupportAveraging

/-!
# Real-base complete-orbit bookkeeping

Generalises the *repaired existing* binary proof in
Erdos249257/ReciprocalSupportIrrationality.lean, lines 153--280,
without changing its finite permutation argument. Unlike the binary result,
this applies at B=2^α for α arbitrarily close to zero.
NOT COMPILED in this return. No premise is an irrationality conclusion.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Exact geometric mass of one complete positive-multiple orbit. -/
theorem sum_kernelWeight_gcdOrbit (B : ℝ) (hB : 1 < B)
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) :
    (∑ k ∈ Finset.range (d / Nat.gcd L d), kernelWeight B d ((k + 1) * L)) =
      1 / (B ^ Nat.gcd L d - 1) := by
  classical
  let g := Nat.gcd L d
  let q := L / g
  let h := d / g
  -- Mathlib/Data/Nat/GCD/Basic.lean: gcd positivity, cancellation and coprime quotient.
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hL
  have hgL : g ∣ L := Nat.gcd_dvd_left L d
  have hgd : g ∣ d := Nat.gcd_dvd_right L d
  have hLfac : g * q = L := Nat.mul_div_cancel' hgL
  have hdfac : g * h = d := Nat.mul_div_cancel' hgd
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right L hd) hg
  have hcop : Nat.Coprime q h := Nat.coprime_div_gcd_div_gcd hg
  let e : Fin h → Fin h := fun j =>
    ⟨((j : ℕ) + 1) * q % h, Nat.mod_lt _ hh⟩
  have heinj : Function.Injective e := by
    intro a b hab
    have habval : (e a : ℕ) = (e b : ℕ) := congrArg Fin.val hab
    have hmod : ((a : ℕ) + 1) * q ≡ ((b : ℕ) + 1) * q [MOD h] := habval
    -- Mathlib/Data/Nat/ModEq.lean: cancel_right_of_coprime,
    -- add_left_cancel', eq_of_lt_of_lt (pinned source opened).
    have hcancel : (a : ℕ) + 1 ≡ (b : ℕ) + 1 [MOD h] :=
      Nat.ModEq.cancel_right_of_coprime hcop.symm.gcd_eq_one hmod
    have habmod : (a : ℕ) ≡ (b : ℕ) [MOD h] := by
      have hcancel' : 1 + (a : ℕ) ≡ 1 + (b : ℕ) [MOD h] := by
        simpa only [add_comm] using hcancel
      exact hcancel'.add_left_cancel' 1
    exact Fin.ext (habmod.eq_of_lt_of_lt a.isLt b.isLt)
  -- Mathlib/Data/Fintype/Card.lean: Finite.surjective_of_injective.
  have hebij : Function.Bijective e :=
    ⟨heinj, Finite.surjective_of_injective heinj⟩
  have hresidue : ∀ j : Fin h,
      (((j : ℕ) + 1) * L) % d = g * (e j : ℕ) := by
    intro j
    rw [← hLfac, ← hdfac]
    rw [show ((j : ℕ) + 1) * (g * q) = g * (((j : ℕ) + 1) * q) by ring]
    rw [Nat.mul_mod_mul_left]
  have hsumPerm :
      (∑ j : Fin h, B ^ ((((j : ℕ) + 1) * L) % d)) =
        ∑ r : Fin h, B ^ (g * (r : ℕ)) := by
    -- Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean: Fintype.sum_bijective.
    apply Fintype.sum_bijective e hebij
    intro j
    rw [hresidue]
  have hpowg : B ^ g ≠ 1 := ne_of_gt (one_lt_pow₀ hB hg.ne')
  have hdenD : B ^ d - 1 ≠ 0 := ne_of_gt (kernel_den_pos hB hd)
  have hdenG : B ^ g - 1 ≠ 0 := sub_ne_zero.mpr hpowg
  calc
    (∑ k ∈ Finset.range (d / Nat.gcd L d), kernelWeight B d ((k + 1) * L)) =
        (∑ j : Fin h, B ^ ((((j : ℕ) + 1) * L) % d)) / (B ^ d - 1) := by
      -- Mathlib/Algebra/BigOperators/Fin.lean: Fin.sum_univ_eq_sum_range.
      rw [show d / Nat.gcd L d = h from rfl, ← Fin.sum_univ_eq_sum_range]
      simp only [kernelWeight, Finset.sum_div]
    _ = (∑ r : Fin h, B ^ (g * (r : ℕ))) / (B ^ d - 1) := by rw [hsumPerm]
    _ = (∑ r ∈ Finset.range h, (B ^ g) ^ r) / (B ^ d - 1) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply congrArg (fun z : ℝ => z / (B ^ d - 1))
      -- Mathlib/Data/Fintype/BigOperators.lean: Fintype.sum_congr.
      apply Fintype.sum_congr
      intro r
      rw [pow_mul]
    _ = ((B ^ g) ^ h - 1) / (B ^ g - 1) / (B ^ d - 1) := by
      -- Mathlib/Algebra/Field/GeomSum.lean: geom_sum_eq.
      rw [geom_sum_eq hpowg]
    _ = 1 / (B ^ Nat.gcd L d - 1) := by
      change ((B ^ g) ^ h - 1) / (B ^ g - 1) / (B ^ d - 1) = 1 / (B ^ g - 1)
      rw [← pow_mul, hdfac]
      field_simp [hdenD, hdenG]

/-- Every aligned block is the same orbit, not only the initial block. -/
theorem sum_kernelWeight_gcdOrbit_block (B : ℝ) (hB : 1 < B)
    (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (b : ℕ) :
    (∑ j ∈ Finset.range (d / Nat.gcd L d),
      kernelWeight B d ((b * (d / Nat.gcd L d) + j + 1) * L)) =
      1 / (B ^ Nat.gcd L d - 1) := by
  let g := Nat.gcd L d
  let q := L / g
  let h := d / g
  have hLfac : g * q = L := Nat.mul_div_cancel' (Nat.gcd_dvd_left L d)
  have hdfac : g * h = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right L d)
  have hperiod : d ∣ h * L := by
    refine ⟨q, ?_⟩
    rw [← hdfac, ← hLfac]
    ring
  have heq :
      (∑ j ∈ Finset.range (d / Nat.gcd L d),
        kernelWeight B d ((b * (d / Nat.gcd L d) + j + 1) * L)) =
      ∑ j ∈ Finset.range (d / Nat.gcd L d), kernelWeight B d ((j + 1) * L) := by
    apply Finset.sum_congr rfl
    intro j _hj
    unfold kernelWeight
    apply congrArg (fun z : ℕ => B ^ z / (B ^ d - 1))
    change ((b * h + j + 1) * L) % d = ((j + 1) * L) % d
    have hdecomp : (b * h + j + 1) * L = b * (h * L) + (j + 1) * L := by ring
    have hbperiod : d ∣ b * (h * L) := dvd_mul_of_dvd_right hperiod b
    rw [hdecomp, Nat.add_mod, Nat.mod_eq_zero_of_dvd hbperiod, zero_add]
    exact Nat.mod_mod _ _
  rw [heq]
  exact sum_kernelWeight_gcdOrbit B hB L d hL hd

/-- Complete blocks plus at most one incomplete block. -/
theorem sum_kernelWeight_le_gcdBlockCount (B : ℝ) (hB : 1 < B)
    (L d T : ℕ) (hL : 0 < L) (hd : 0 < d) :
    (∑ m ∈ Finset.range T, kernelWeight B d ((m + 1) * L)) ≤
      (((T / (d / Nat.gcd L d) : ℕ) : ℝ) + 1) / (B ^ Nat.gcd L d - 1) := by
  let g := Nat.gcd L d
  let h := d / g
  let C : ℝ := 1 / (B ^ g - 1)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hL
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right L hd) hg
  have hblock : ∀ q : ℕ,
      (∑ j ∈ Finset.range h, kernelWeight B d ((q * h + j + 1) * L)) = C := by
    intro q
    exact sum_kernelWeight_gcdOrbit_block B hB L d hL hd q
  have hr := blockRemainder_le_blockSum
    (fun k => kernelWeight B d ((k + 1) * L)) h C hh
    (fun k => kernelWeight_nonneg hB d _) hblock T
  rw [sum_range_eq_mul_blockSum_add_blockRemainder _ h C hblock T]
  calc
    _ ≤ ((T / h : ℕ) : ℝ) * C + C := add_le_add le_rfl hr
    _ = _ := by dsimp [C, h, g]; ring

/-- Retain the geometric gcd factor: needed by the weighted schedule. -/
theorem progressionMean_kernel_le_gcdMean_add_error (B : ℝ) (hB : 1 < B)
    (L d T : ℕ) (hL : 0 < L) (hd : 0 < d) (hT : 0 < T) :
    progressionMean L T (kernelWeight B d) ≤
      (Nat.gcd L d : ℝ) / ((d : ℝ) * (B ^ Nat.gcd L d - 1)) +
      1 / ((T : ℝ) * (B ^ Nat.gcd L d - 1)) := by
  let g := Nat.gcd L d
  let h := d / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hL
  have hh : 0 < h := Nat.div_pos (Nat.gcd_le_right L hd) hg
  have hdFac : g * h = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right L d)
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hden : 0 < B ^ g - 1 := kernel_den_pos hB hg
  have hratio : (T : ℝ) / h = (T : ℝ) * g / d := by
    rw [← hdFac]
    push_cast
    have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    field_simp [hgR, hhR.ne']
  have hquot : ((T / h : ℕ) : ℝ) ≤ (T : ℝ) * g / d := by
    rw [← hratio]
    -- Mathlib/Data/Nat/Cast/Order/Field.lean: Nat.cast_div_le.
    exact Nat.cast_div_le
  have hsum := sum_kernelWeight_le_gcdBlockCount B hB L d T hL hd
  unfold progressionMean
  calc
    _ ≤ ((((T / h : ℕ) : ℝ) + 1) / (B ^ g - 1)) / T :=
      div_le_div_of_nonneg_right hsum hTR.le
    _ ≤ (((T : ℝ) * g / d + 1) / (B ^ g - 1)) / T := by
      have hquot' : ((T / h : ℕ) : ℝ) + 1 ≤ (T : ℝ) * g / d + 1 := by
        linarith only [hquot]
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hquot' hden.le) hTR.le
    _ = _ := by
      change ((T : ℝ) * g / d + 1) / (B ^ g - 1) / T =
        (g : ℝ) / ((d : ℝ) * (B ^ g - 1)) + 1 / ((T : ℝ) * (B ^ g - 1))
      field_simp [hTR.ne', hdR.ne', hden.ne']
      <;> ring

/-- Uniform version of the complete-orbit estimate. -/
theorem progressionMean_kernel_le_mean_add_error (B : ℝ) (hB : 1 < B)
    (L d T : ℕ) (hL : 0 < L) (hd : 0 < d) (hT : 0 < T) :
    progressionMean L T (kernelWeight B d) ≤
      1 / ((d : ℝ) * (B - 1)) + 1 / ((T : ℝ) * (B - 1)) := by
  let g := Nat.gcd L d
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hL
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hgap : 0 < B - 1 := sub_pos.mpr hB
  have hG : 0 < B ^ g - 1 := kernel_den_pos hB hg
  have hcycle : (g : ℝ) / (B ^ g - 1) ≤ 1 / (B - 1) :=
    cycle_ratio_le_inv_sub_one hB g hg
  have hfirst : (g : ℝ) / ((d : ℝ) * (B ^ g - 1)) ≤
      1 / ((d : ℝ) * (B - 1)) := by
    have h := div_le_div_of_nonneg_right hcycle hdR.le
    simpa only [div_div, mul_comm] using h
  have hpow : B ≤ B ^ g := by
    calc B = B ^ (1 : ℕ) := (pow_one B).symm
      _ ≤ B ^ g := pow_le_pow_right₀ hB.le hg
  have hinv : 1 / (B ^ g - 1) ≤ 1 / (B - 1) :=
    div_le_div_of_nonneg_left (by norm_num) hgap (sub_le_sub_right hpow 1)
  have hsecond : 1 / ((T : ℝ) * (B ^ g - 1)) ≤
      1 / ((T : ℝ) * (B - 1)) := by
    have h := div_le_div_of_nonneg_right hinv hTR.le
    simpa only [div_div, mul_comm] using h
  exact (progressionMean_kernel_le_gcdMean_add_error B hB L d T hL hd hT).trans
    (add_le_add hfirst hsecond)

end ErdosProblems.Erdos257.PaperCompleteR8
end
