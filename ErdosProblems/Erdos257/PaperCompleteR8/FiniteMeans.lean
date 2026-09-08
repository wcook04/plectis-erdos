import ErdosProblems.Erdos257.PaperCompleteR7.CoverKernel
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Actual finite dyadic observation means

Round 8 proof text against Lean 4.29.1 / Mathlib
5e932f97dd25535344f80f9dd8da3aab83df0fe6. NOT COMPILED in this return.
The average samples exactly the positive progression points (m+1)*L.
No independently chosen existential return is substituted for an average.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- The literal modular atom requested in mandate 1a. -/
def kernelWeight (B : ℝ) (d n : ℕ) : ℝ :=
  B ^ (n % d) / (B ^ d - 1)

/-- Average at the T positive multiples of L. -/
def progressionMean (L T : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.range T, f ((m + 1) * L)) / (T : ℝ)

/-- Average the progression averages over R ≤ j < R+M, T=2^j. -/
def dyadicMean (L R M : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.Ico R (R + M), progressionMean L (2 ^ j) f) / (M : ℝ)

/-- A positive modulus and base give a positive denominator. -/
theorem kernel_den_pos {B : ℝ} (hB : 1 < B) {d : ℕ} (hd : 0 < d) :
    0 < B ^ d - 1 := by
  -- Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean: one_lt_pow₀,
  -- pow_nonneg, pow_pos and the power-order lemmas (opened at the pin).
  have hp : 1 < B ^ d := one_lt_pow₀ hB hd.ne'
  exact sub_pos.mpr hp

theorem kernelWeight_nonneg {B : ℝ} (hB : 1 < B) (d n : ℕ) :
    0 ≤ kernelWeight B d n := by
  by_cases hd : d = 0
  · subst d
    simp only [kernelWeight, pow_zero, sub_self, div_zero, le_refl]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hBpos : 0 < B := lt_trans zero_lt_one hB
    exact div_nonneg (pow_nonneg hBpos.le _) (kernel_den_pos hB hdpos).le

/-- Linearity is valid even for an empty mean (total division convention). -/
theorem progressionMean_add (L T : ℕ) (f g : ℕ → ℝ) :
    progressionMean L T (fun n => f n + g n) =
      progressionMean L T f + progressionMean L T g := by
  -- Finite-sum APIs: Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean.
  unfold progressionMean
  rw [Finset.sum_add_distrib, add_div]

theorem dyadicMean_add (L R M : ℕ) (f g : ℕ → ℝ) :
    dyadicMean L R M (fun n => f n + g n) =
      dyadicMean L R M f + dyadicMean L R M g := by
  unfold dyadicMean
  simp only [progressionMean_add, Finset.sum_add_distrib, add_div]

theorem progressionMean_const (L T : ℕ) (hT : 0 < T) (c : ℝ) :
    progressionMean L T (fun _ => c) = c := by
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold progressionMean
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hTne]

theorem dyadicMean_const (L R M : ℕ) (hM : 0 < M) (c : ℝ) :
    dyadicMean L R M (fun _ => c) = c := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hpow : ∀ j : ℕ, 0 < (2 : ℕ) ^ j := fun j => by positivity
  have hcard : (Finset.Ico R (R + M)).card = M := by
    -- Mathlib/Order/Interval/Finset/Nat.lean: Nat.card_Ico.
    rw [Nat.card_Ico]
    omega
  have hsum : (∑ j ∈ Finset.Ico R (R + M), progressionMean L (2 ^ j) (fun _ => c)) =
      (∑ _j ∈ Finset.Ico R (R + M), c) := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact progressionMean_const L (2 ^ j) (hpow j) c
  unfold dyadicMean
  rw [hsum, Finset.sum_const, hcard, nsmul_eq_mul]
  field_simp [hMne]

theorem progressionMean_nonneg (L T : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) : 0 ≤ progressionMean L T f := by
  unfold progressionMean
  exact div_nonneg (Finset.sum_nonneg (fun m _ => hf _)) (Nat.cast_nonneg T)

theorem dyadicMean_nonneg (L R M : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) : 0 ≤ dyadicMean L R M f := by
  unfold dyadicMean
  exact div_nonneg
    (Finset.sum_nonneg (fun j _ => progressionMean_nonneg L _ f hf))
    (Nat.cast_nonneg M)

theorem progressionMean_mono (L T : ℕ) (f g : ℕ → ℝ)
    (hfg : ∀ n, f n ≤ g n) : progressionMean L T f ≤ progressionMean L T g := by
  unfold progressionMean
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun m _ => hfg _)) (Nat.cast_nonneg T)

theorem dyadicMean_mono (L R M : ℕ) (f g : ℕ → ℝ)
    (hfg : ∀ n, f n ≤ g n) : dyadicMean L R M f ≤ dyadicMean L R M g := by
  unfold dyadicMean
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun j _ => progressionMean_mono L _ f g hfg))
    (Nat.cast_nonneg M)

/-- Extract a point from the *same* two-stage finite mean. -/
theorem exists_sample_lt_of_dyadicMean_lt
    (L R M : ℕ) (hM : 0 < M) (f : ℕ → ℝ) (c : ℝ)
    (hmean : dyadicMean L R M f < c) :
    ∃ j m : ℕ, R ≤ j ∧ j < R + M ∧ m < 2 ^ j ∧ f ((m + 1) * L) < c := by
  have hs : (Finset.Ico R (R + M)).Nonempty := by
    refine ⟨R, Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩⟩
    omega
  have hcard : (Finset.Ico R (R + M)).card = M := by
    -- Mathlib/Order/Interval/Finset/Nat.lean: Nat.card_Ico.
    rw [Nat.card_Ico]
    omega
  have hout :
      (∑ j ∈ Finset.Ico R (R + M), progressionMean L (2 ^ j) f) /
        ((Finset.Ico R (R + M)).card : ℝ) < c := by
    rw [hcard]
    exact hmean
  obtain ⟨j, hj, hjmean⟩ := exists_lt_of_mean_lt
    (Finset.Ico R (R + M)) hs (fun j => progressionMean L (2 ^ j) f) hout
  have hT : 0 < (2 : ℕ) ^ j := by positivity
  have ht : (Finset.range (2 ^ j)).Nonempty :=
    ⟨0, Finset.mem_range.mpr hT⟩
  have hin :
      (∑ m ∈ Finset.range (2 ^ j), f ((m + 1) * L)) /
        ((Finset.range (2 ^ j)).card : ℝ) < c := by
    rw [Finset.card_range]
    exact hjmean
  obtain ⟨m, hm, hfm⟩ := exists_lt_of_mean_lt
    (Finset.range (2 ^ j)) ht (fun m => f ((m + 1) * L)) hin
  exact ⟨j, m, (Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2,
    Finset.mem_range.mp hm, hfm⟩

/-- The common-observation-scale lemma: explicit common L,R,M, not two
unrelated existential returns. It also retains divisibility of the witness. -/
theorem exists_common_progression_sample
    (L R M : ℕ) (hL : 0 < L) (hM : 0 < M)
    (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (ε : ℝ)
    (hbudget : dyadicMean L R M f + dyadicMean L R M g < ε) :
    ∃ N : ℕ, 0 < N ∧ L ∣ N ∧ L ≤ N ∧ f N < ε ∧ g N < ε := by
  have hsum : dyadicMean L R M (fun n => f n + g n) < ε := by
    rw [dyadicMean_add]
    exact hbudget
  obtain ⟨j, m, _hjlo, _hjhi, _hm, hpoint⟩ :=
    exists_sample_lt_of_dyadicMean_lt L R M hM (fun n => f n + g n) ε hsum
  let N := (m + 1) * L
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos m) hL
  have hdiv : L ∣ N := ⟨m + 1, by dsimp [N]; ring⟩
  have hLN : L ≤ N := by
    have h := Nat.mul_le_mul_right L (show 1 ≤ m + 1 by omega)
    simpa only [one_mul] using h
  have hfN : f N < ε := lt_of_le_of_lt (le_add_of_nonneg_right (hg N)) hpoint
  have hgN : g N < ε := lt_of_le_of_lt (le_add_of_nonneg_left (hf N)) hpoint
  exact ⟨N, hN, hdiv, hLN, hfN, hgN⟩

end ErdosProblems.Erdos257.PaperCompleteR8
end
