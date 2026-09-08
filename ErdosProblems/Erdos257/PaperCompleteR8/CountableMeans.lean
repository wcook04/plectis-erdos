import ErdosProblems.Erdos257.PaperCompleteR8.DyadicKernel

/-!
# Summable families of actual modular tests

NOT COMPILED. This supplies the countable interchange and sampling layer after
(S), with explicit summability hypotheses. The index type can be a pair of
indices, so the theorem applies to both frame and conductor indices at once.
It does not assume a lower bound on the fractional exponents.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Pointwise domination by reciprocal conductor, needed before exchanging
an infinite sum with the finite observation mean. -/
theorem kernelWeight_le_pointwise_majorant
    (B : ℝ) (hB : 1 < B) (d N : ℕ) (hd : 0 < d) :
    kernelWeight B d N ≤ (2 * (N : ℝ) + 1) / ((d : ℝ) * (B - 1)) := by
  have hgap : 0 < B - 1 := sub_pos.mpr hB
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) * (B - 1) := mul_pos hdR hgap
  by_cases hfar : 2 * N < d
  · have h := kernelWeight_le_of_twice_lt hB d N hfar
    have hnum : (1 : ℝ) ≤ 2 * (N : ℝ) + 1 := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith only [hN0]
    exact h.trans (div_le_div_of_nonneg_right hnum hden.le)
  · have hN : 0 < N := by omega
    have h := progressionMean_kernel_le_mean_add_error B hB N d 1 hN hd (by decide)
    have hone : progressionMean N 1 (kernelWeight B d) = kernelWeight B d N := by
      simp only [progressionMean, Finset.sum_range_one, zero_add, one_mul,
        Nat.cast_one, div_one]
    rw [hone] at h
    have hbound : (d : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (by omega : d ≤ 2 * N)
    have hsecond : (1 : ℝ) / (B - 1) ≤
        (2 * (N : ℝ)) / ((d : ℝ) * (B - 1)) := by
      apply (div_le_div_iff₀ hgap hden).2
      have hs := mul_le_mul_of_nonneg_right hbound hgap.le
      simpa only [one_mul] using hs
    calc
      _ ≤ 1 / ((d : ℝ) * (B - 1)) + 1 / (B - 1) := by simpa using h
      _ ≤ 1 / ((d : ℝ) * (B - 1)) + (2 * (N : ℝ)) / ((d : ℝ) * (B - 1)) :=
        add_le_add (le_refl _) hsecond
      _ = _ := by ring

/-- Finite means commute with a countable (or any summable-index) family. -/
theorem tsum_progressionMean {ι : Type*} (u : ι → ℕ → ℝ)
    (hu : ∀ N : ℕ, Summable (fun i => u i N)) (L T : ℕ) :
    (∑' i, progressionMean L T (u i)) =
      progressionMean L T (fun N => ∑' i, u i N) := by
  -- Mathlib/Topology/Algebra/InfiniteSum/Basic.lean: Summable.tsum_finsetSum.
  -- Mathlib/Topology/Algebra/InfiniteSum/Ring.lean: tsum_div_const.
  unfold progressionMean
  rw [tsum_div_const]
  rw [Summable.tsum_finsetSum]
  intro m _hm
  exact hu ((m + 1) * L)

/-- Summability of an indexed family of finite progression averages. -/
theorem summable_progressionMean {ι : Type*} (u : ι → ℕ → ℝ)
    (hu : ∀ N : ℕ, Summable (fun i => u i N)) (L T : ℕ) :
    Summable (fun i => progressionMean L T (u i)) := by
  -- `summable_sum` is the additive form of `multipliable_prod` in
  -- Mathlib/Topology/Algebra/InfiniteSum/Basic.lean.
  have hsum : Summable (fun i => ∑ m ∈ Finset.range T, u i ((m + 1) * L)) :=
    summable_sum (fun m _hm => hu ((m + 1) * L))
  exact hsum.div_const (T : ℝ)

/-- The two-stage mean commutes with the whole indexed sum. -/
theorem tsum_dyadicMean {ι : Type*} (u : ι → ℕ → ℝ)
    (hu : ∀ N : ℕ, Summable (fun i => u i N)) (L R M : ℕ) :
    (∑' i, dyadicMean L R M (u i)) =
      dyadicMean L R M (fun N => ∑' i, u i N) := by
  unfold dyadicMean
  rw [tsum_div_const]
  rw [Summable.tsum_finsetSum]
  · apply congrArg (fun z : ℝ => z / (M : ℝ))
    apply Finset.sum_congr rfl
    intro j _hj
    exact tsum_progressionMean u hu L (2 ^ j)
  · intro j _hj
    exact summable_progressionMean u hu L (2 ^ j)

/-- No interchange is made until pointwise summability has been established. -/
theorem summable_weighted_kernel_family {ι : Type*}
    (B : ι → ℝ) (d : ι → ℕ) (c : ι → ℝ)
    (hB : ∀ i, 1 < B i) (hd : ∀ i, 0 < d i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => c i / ((d i : ℝ) * (B i - 1)))) (N : ℕ) :
    Summable (fun i => c i * kernelWeight (B i) (d i) N) := by
  -- Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean: Summable.of_nonneg_of_le.
  have hmajor : Summable (fun i =>
      (2 * (N : ℝ) + 1) * (c i / ((d i : ℝ) * (B i - 1)))) :=
    hs.mul_left (2 * (N : ℝ) + 1)
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro i
    exact mul_nonneg (hc i) (kernelWeight_nonneg (hB i) (d i) N)
  · intro i
    have h := mul_le_mul_of_nonneg_left
      (kernelWeight_le_pointwise_majorant (B i) (hB i) (d i) N (hd i)) (hc i)
    convert h using 1 <;> ring

/-- Scalar linearity is exact, including a zero-size mean. -/
theorem dyadicMean_const_mul (L R M : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    dyadicMean L R M (fun N => c * f N) = c * dyadicMean L R M f := by
  unfold dyadicMean progressionMean
  simp only [← Finset.mul_sum]
  simp only [mul_div_assoc]
  rw [← Finset.mul_sum]
  ring

/-- (S) for a whole summable family, with the same scales for every term. -/
theorem dyadicMean_tsum_kernel_le {ι : Type*}
    (B : ι → ℝ) (d : ι → ℕ) (c : ι → ℝ)
    (hB : ∀ i, 1 < B i) (hB2 : ∀ i, B i ≤ 2)
    (hd : ∀ i, 0 < d i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => c i / ((d i : ℝ) * (B i - 1))))
    (L R M : ℕ) (hL : 0 < L) (hM : 0 < M) :
    dyadicMean L R M (fun N => ∑' i, c i * kernelWeight (B i) (d i) N) ≤
      (1 + 4 * (L : ℝ) / M) *
        (∑' i, c i / ((d i : ℝ) * (B i - 1))) := by
  let u : ι → ℕ → ℝ := fun i N => c i * kernelWeight (B i) (d i) N
  let K : ℝ := 1 + 4 * (L : ℝ) / M
  have hu : ∀ N : ℕ, Summable (fun i => u i N) :=
    summable_weighted_kernel_family B d c hB hd hc hs
  have hdom : Summable (fun i => K * (c i / ((d i : ℝ) * (B i - 1)))) := hs.mul_left K
  have hpoint : ∀ i, dyadicMean L R M (u i) ≤
      K * (c i / ((d i : ℝ) * (B i - 1))) := by
    intro i
    change dyadicMean L R M (fun N => c i * kernelWeight (B i) (d i) N) ≤ _
    rw [dyadicMean_const_mul]
    have h := mul_le_mul_of_nonneg_left
      (dyadicMean_kernelWeight_le (B i) (hB i) (hB2 i) L (d i) R M hL (hd i) hM) (hc i)
    convert h using 1 <;> dsimp [K] <;> ring
  have hleft : Summable (fun i => dyadicMean L R M (u i)) := by
    refine Summable.of_nonneg_of_le ?_ hpoint hdom
    intro i
    exact dyadicMean_nonneg L R M (u i)
      (fun N => mul_nonneg (hc i) (kernelWeight_nonneg (hB i) (d i) N))
  -- Mathlib/Topology/Algebra/InfiniteSum/Order.lean: Summable.tsum_le_tsum.
  have htsum := Summable.tsum_le_tsum hpoint hleft hdom
  rw [tsum_dyadicMean u hu L R M, tsum_mul_left] at htsum
  exact htsum

/-- Countably many tests have one good positive multiple. An observation
budget, not a separate existential witness for each test, is consumed. -/
theorem exists_sample_for_countable_kernel_tests {ι : Type*}
    (B : ι → ℝ) (d : ι → ℕ) (c : ι → ℝ)
    (hB : ∀ i, 1 < B i) (hB2 : ∀ i, B i ≤ 2)
    (hd : ∀ i, 0 < d i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => c i / ((d i : ℝ) * (B i - 1))))
    (L R M : ℕ) (hL : 0 < L) (hM : 0 < M) (ε : ℝ)
    (hcost : (1 + 4 * (L : ℝ) / M) *
      (∑' i, c i / ((d i : ℝ) * (B i - 1))) < ε) :
    ∃ N : ℕ, 0 < N ∧ L ∣ N ∧
      (∑' i, c i * kernelWeight (B i) (d i) N) < ε := by
  have havg := dyadicMean_tsum_kernel_le B d c hB hB2 hd hc hs L R M hL hM
  obtain ⟨j, m, _hjlo, _hjhi, _hm, hsample⟩ :=
    exists_sample_lt_of_dyadicMean_lt L R M hM
      (fun N => ∑' i, c i * kernelWeight (B i) (d i) N) ε (havg.trans_lt hcost)
  refine ⟨(m + 1) * L, Nat.mul_pos (Nat.succ_pos m) hL, ?_, hsample⟩
  exact ⟨m + 1, by ring⟩

end ErdosProblems.Erdos257.PaperCompleteR8
end
