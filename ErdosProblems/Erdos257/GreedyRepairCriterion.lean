import ErdosProblems.Erdos257.BatchReturnSynthesis

/-!
# A repair criterion for every nonnegative real target

The four-ninths argument does not require a rational or periodic target.
For the actual greedy support of `x`, subtract its Lambert prefix integer
from `floor (2^N x)`. Membership is equivalent to cofinal nonincreases of
this natural defect, and also to a repair in every explicit square-root
window. Nonmembership forces geometric growth through the actual fatal gap.
-/

namespace ErdosProblems.Erdos257

open Erdos249257 Filter

noncomputable section

def greedyBinaryDefect (x : ℝ) (N : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ N * x⌋₊ -
    binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N

theorem greedyBinaryPrefix_le_floor {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N ≤
      ⌊(2 : ℝ) ^ N * x⌋₊ := by
  apply Nat.le_floor
  have hp := binaryCoeffPrefix_greedySupport_le hx N
  have hn := binaryCoeffPrefixNumerator_div_pow
    (supportCoeff (greedyMersenneSupport x)) N
  have hpos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have heq := (div_eq_iff hpos.ne').mp hn
  nlinarith

theorem greedyBinaryDefect_cast {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    (greedyBinaryDefect x N : ℝ) =
      (⌊(2 : ℝ) ^ N * x⌋₊ : ℝ) -
      (binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N : ℝ) := by
  exact Nat.cast_sub (greedyBinaryPrefix_le_floor hx N)

/-- The next floor digit is nonnegative; its periodicity is irrelevant. -/
theorem greedyBinaryDefect_succ_lower {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    2 * (greedyBinaryDefect x N : ℝ) -
        supportCoeff (greedyMersenneSupport x) (N + 1) ≤
      (greedyBinaryDefect x (N + 1) : ℝ) := by
  have hf : 2 * ⌊(2 : ℝ) ^ N * x⌋₊ ≤ ⌊(2 : ℝ) ^ (N + 1) * x⌋₊ := by
    apply Nat.le_floor
    have h := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ N * x by positivity)
    push_cast
    rw [pow_succ]
    nlinarith
  have hfR : 2 * (⌊(2 : ℝ) ^ N * x⌋₊ : ℝ) ≤
      (⌊(2 : ℝ) ^ (N + 1) * x⌋₊ : ℝ) := by exact_mod_cast hf
  rw [greedyBinaryDefect_cast hx, greedyBinaryDefect_cast hx,
    binaryCoeffPrefixNumerator]
  push_cast
  linarith

/-- A repair bounds the actual defect by the actual next divisor load. -/
theorem greedyBinaryDefect_le_load_of_repair {x : ℝ} (hx : 0 ≤ x) (N : ℕ)
    (hr : greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N) :
    greedyBinaryDefect x N ≤ supportCoeff (greedyMersenneSupport x) (N + 1) := by
  have h := greedyBinaryDefect_succ_lower hx N
  have hrR : (greedyBinaryDefect x (N + 1) : ℝ) ≤
      (greedyBinaryDefect x N : ℝ) := by exact_mod_cast hr
  have : (greedyBinaryDefect x N : ℝ) ≤
      (supportCoeff (greedyMersenneSupport x) (N + 1) : ℝ) := by linarith
  exact_mod_cast this

/-- Removing the finite Lambert prefix leaves the scaled actual greedy
remainder and a nonnegative future-multiple tail. -/
theorem greedy_scaled_remainder_le_defect_add_one
    {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    (2 : ℝ) ^ N * greedyMersenneRemainder x N ≤
      (greedyBinaryDefect x N : ℝ) + 1 := by
  let A := greedyMersenneSupport x
  let AN := A ∩ Set.Iic N
  have hpref :
      (∑ k ∈ Finset.range N, Set.indicator A mersenneWeight (k + 1)) =
        binaryCoeffPrefix (supportCoeff A) N +
          binaryCoeffTail (supportCoeff AN) N / (2 : ℝ) ^ N := by
    rw [← positiveMersenneSupportValue_inter_Iic_eq_prefix A N,
      positiveMersenneSupportValue_eq_erdosSupportSeries,
      erdosSupportSeries_two_eq_binaryCoeffSeries,
      binaryCoeffSeries_eq_prefix_add_tail _ (supportCoeff_le_self _) N,
      binaryCoeffPrefix_supportCoeff_inter_Iic_eq A le_rfl]
  have hgreedy := greedyMersenne_prefix_add_remainder x N
  change x = (∑ k ∈ Finset.range N, Set.indicator A mersenneWeight (k + 1)) +
    greedyMersenneRemainder x N at hgreedy
  rw [hpref] at hgreedy
  have hnum := binaryCoeffPrefixNumerator_div_pow (supportCoeff A) N
  have htail := binaryCoeffTail_nonneg (supportCoeff AN) N
  have hcast := greedyBinaryDefect_cast hx N
  have hfloor := Nat.lt_floor_add_one ((2 : ℝ) ^ N * x)
  have hpow : (2 : ℝ) ^ N ≠ 0 := by positivity
  change (greedyBinaryDefect x N : ℝ) = (⌊(2 : ℝ) ^ N * x⌋₊ : ℝ) -
    (binaryCoeffPrefixNumerator (supportCoeff A) N : ℝ) at hcast
  field_simp [hpow] at hgreedy hnum
  nlinarith

/-- The support-uniform strip holds at every rank of a represented target. -/
theorem greedyBinaryDefect_le_sqrt_of_mem {x : ℝ}
    (hx : 0 ≤ x) (hm : x ∈ mersenneAchievementSet) (N : ℕ) :
    (greedyBinaryDefect x N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) + 4 := by
  rcases hm with ⟨A, hA0, hvalue⟩
  have hs : greedyMersenneSupport x = A := by
    rw [hvalue]
    exact greedySupport_supportValue_eq A hA0
  have hseries : binaryCoeffSeries (supportCoeff A) = x := by
    rw [← erdosSupportSeries_two_eq_binaryCoeffSeries,
      ← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  have hsplit := binaryCoeffSeries_eq_prefix_add_tail
    (supportCoeff A) (supportCoeff_le_self A) N
  have hnum := binaryCoeffPrefixNumerator_div_pow (supportCoeff A) N
  have hpow : (2 : ℝ) ^ N ≠ 0 := by positivity
  have htailEq : (2 : ℝ) ^ N * x -
      (binaryCoeffPrefixNumerator (supportCoeff A) N : ℝ) =
      binaryCoeffTail (supportCoeff A) N := by
    rw [hseries, ← hnum] at hsplit
    field_simp [hpow] at hsplit
    nlinarith
  have hf := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ N * x by positivity)
  have hc := greedyBinaryDefect_cast hx N
  rw [hs] at hc
  have ht := binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A N
  linarith

/-- A cofinal linear bound already rules out the geometric growth of an
actual fatal greedy remainder. -/
theorem mem_of_greedyBinaryDefect_cofinal_linear_bound
    {x : ℝ} (hx : 0 ≤ x)
    (hb : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ greedyBinaryDefect x N ≤ N + 1) :
    x ∈ mersenneAchievementSet := by
  by_contra hnot
  have hfail : ¬ ∀ n, greedyMersenneRemainder x n ≤ mersenneTail n := by
    intro h
    exact hnot ((mem_mersenneAchievementSet_iff_greedy_survival x).2 ⟨hx, h⟩)
  push Not at hfail
  obtain ⟨n, hn⟩ := hfail
  let δ := greedyMersenneRemainder x n - mersenneTail n
  have hδ : 0 < δ := sub_pos.mpr hn
  have hN : Tendsto (fun m : ℕ => (m : ℝ) / (2 : ℝ) ^ m)
      atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have hOne : Tendsto (fun m : ℕ => (1 : ℝ) / (2 : ℝ) ^ m)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hratio : Tendsto (fun m : ℕ => ((m : ℝ) + 2) / (2 : ℝ) ^ m)
      atTop (nhds 0) := by
    convert hN.add (hOne.const_mul 2) using 1
    · funext m; ring
    · simp
  have hev : ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 2) / (2 : ℝ) ^ m < δ :=
    (tendsto_order.1 hratio).2 δ hδ
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  obtain ⟨N, hNbig, hNb⟩ := hb (max n K)
  have hnN : n ≤ N := (le_max_left _ _).trans hNbig
  have heq := greedyMersenneRemainder_sub_tail_eq_of_fatalAt_add hn (N - n)
  have hind : n + (N - n) = N := by omega
  rw [hind] at heq
  have ht := mersenneTail_nonneg N
  have hrem : δ ≤ greedyMersenneRemainder x N := by dsimp [δ]; linarith
  have hscaled := mul_le_mul_of_nonneg_left hrem
    (show 0 ≤ (2 : ℝ) ^ N by positivity)
  have hdef := greedy_scaled_remainder_le_defect_add_one hx N
  have hbR : (greedyBinaryDefect x N : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hNb
  have hsmall := hK N ((le_max_right _ _).trans hNbig)
  have hstrict : (N : ℝ) + 2 < δ * (2 : ℝ) ^ N :=
    (div_lt_iff₀ (by positivity)).mp hsmall
  nlinarith

/-- Cofinal nonincreases characterise membership for every nonnegative real
target, with no rationality or periodic-digit hypothesis. -/
theorem mem_iff_greedyBinaryDefect_cofinal_repairs {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  constructor
  · intro hm K
    obtain ⟨N, hKN, _, hr⟩ := exists_repair_in_sqrt_window
      (greedyBinaryDefect x) (greedyBinaryDefect_le_sqrt_of_mem hx hm) K
    exact ⟨N, hKN, hr⟩
  · intro hr
    apply mem_of_greedyBinaryDefect_cofinal_linear_bound hx
    intro K
    obtain ⟨N, hKN, hNr⟩ := hr K
    exact ⟨N, hKN, (greedyBinaryDefect_le_load_of_repair hx N hNr).trans
      (supportCoeff_le_self _ (N + 1))⟩

/-- The explicit square-root deadline is uniform in the represented value. -/
theorem mem_iff_greedyBinaryDefect_sqrt_windows {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        greedyBinaryDefect x (N + 1) ≤ greedyBinaryDefect x N := by
  constructor
  · intro hm K
    exact exists_repair_in_sqrt_window (greedyBinaryDefect x)
      (greedyBinaryDefect_le_sqrt_of_mem hx hm) K
  · intro h
    apply (mem_iff_greedyBinaryDefect_cofinal_repairs hx).2
    intro K
    obtain ⟨N, hKN, _, hr⟩ := h K
    exact ⟨N, hKN, hr⟩

/-- A cofinal bound by the actual next divisor load is an equivalent producer. -/
theorem mem_iff_greedyBinaryDefect_cofinal_load_bound {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
        greedyBinaryDefect x N ≤ supportCoeff (greedyMersenneSupport x) (N + 1) := by
  constructor
  · intro hm K
    obtain ⟨N, hKN, hr⟩ := (mem_iff_greedyBinaryDefect_cofinal_repairs hx).1 hm K
    exact ⟨N, hKN, greedyBinaryDefect_le_load_of_repair hx N hr⟩
  · intro h
    apply mem_of_greedyBinaryDefect_cofinal_linear_bound hx
    intro K
    obtain ⟨N, hKN, hN⟩ := h K
    exact ⟨N, hKN, hN.trans (supportCoeff_le_self _ (N + 1))⟩

/-- The linear comparison suffices at cofinally many ranks. -/
theorem mem_iff_greedyBinaryDefect_cofinal_linear_bound {x : ℝ} (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ greedyBinaryDefect x N ≤ N + 1 := by
  constructor
  · intro hm K
    obtain ⟨N, hKN, hN⟩ := (mem_iff_greedyBinaryDefect_cofinal_load_bound hx).1 hm K
    exact ⟨N, hKN, hN.trans (supportCoeff_le_self _ (N + 1))⟩
  · exact mem_of_greedyBinaryDefect_cofinal_linear_bound hx

/-- One finite strict-increase window excludes the actual target. -/
theorem not_mem_of_greedyBinaryDefect_strict_sqrt_window {x : ℝ} (hx : 0 ≤ x)
    (K : ℕ) (hstrict : ∀ N : ℕ, K ≤ N → N < K + 2 * Nat.sqrt K + 12 →
      greedyBinaryDefect x N < greedyBinaryDefect x (N + 1)) :
    x ∉ mersenneAchievementSet := by
  intro hm
  obtain ⟨N, hKN, hNK, hr⟩ := (mem_iff_greedyBinaryDefect_sqrt_windows hx).1 hm K
  exact (not_lt_of_ge hr) (hstrict N hKN hNK)

#print axioms mem_iff_greedyBinaryDefect_cofinal_repairs
#print axioms mem_iff_greedyBinaryDefect_sqrt_windows
#print axioms mem_iff_greedyBinaryDefect_cofinal_load_bound
#print axioms mem_iff_greedyBinaryDefect_cofinal_linear_bound
#print axioms not_mem_of_greedyBinaryDefect_strict_sqrt_window

end
end ErdosProblems.Erdos257
