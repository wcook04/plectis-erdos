import ErdosProblems.Erdos1049.SourcePolynomialR11
import Mathlib

/-!
# Exact weighted floor blocks for the actual thirteen intervals

Rewrites the weighted totient sum as thirteen reciprocal floor blocks.
The lower reciprocal endpoint is strict and the upper one weak. This file
constructs the literal finite weighted sums and identifies each block with
a difference of totient prefixes. It does not label this finite identity as
an asymptotic estimate or assume a summatory-totient error bound.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open PaperR11
open scoped BigOperators

/-- The thirteen rational half-open intervals, not a replacement support. -/
def sourceIntervals : Finset (ℚ × ℚ) :=
  {(1/14, 1/12), (1/7, 1/6), (3/14, 1/4), (2/7, 1/3),
   (5/14, 2/5), (3/7, 7/15), (1/2, 8/15), (4/7, 3/5),
   (9/14, 2/3), (5/7, 11/15), (11/14, 4/5),
   (6/7, 13/15), (13/14, 14/15)}

theorem sourceIntervals_card : sourceIntervals.card = 13 := by
  norm_num [sourceIntervals]

theorem sourceIntervals_bounds (uv : ℚ × ℚ) (huv : uv ∈ sourceIntervals) :
    (0 : ℝ) < uv.1 ∧ (uv.1 : ℝ) < uv.2 ∧ (uv.2 : ℝ) ≤ 1 := by
  norm_num [sourceIntervals] at huv
  rcases huv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem omegaSupport_iff_sourceIntervals (x : ℝ) :
    PaperR7.InOmegaSupport x ↔
      ∃ uv ∈ sourceIntervals, (uv.1 : ℝ) ≤ x ∧ x < (uv.2 : ℝ) := by
  norm_num [sourceIntervals, PaperR7.InOmegaSupport]

/-- Reversing reciprocals reverses which boundary is strict. -/
theorem reciprocal_block_iff (n l k u v : ℝ) (hl : 0 < l)
    (hk : 0 ≤ k) (hu : 0 < u) (huv : u < v) :
    k + u ≤ n / l ∧ n / l < k + v ↔
      n / (k + v) < l ∧ l ≤ n / (k + u) := by
  have hku : 0 < k + u := by linarith
  have hkv : 0 < k + v := by linarith
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_lt_iff₀ hkv).2
      simpa only [mul_comm] using (div_lt_iff₀ hl).1 hhi
    · apply (le_div_iff₀ hku).2
      simpa only [mul_comm] using (le_div_iff₀ hl).1 hlo
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (le_div_iff₀ hl).2
      simpa only [mul_comm] using (le_div_iff₀ hku).1 hhi
    · apply (div_lt_iff₀ hl).2
      simpa only [mul_comm] using (div_lt_iff₀ hkv).1 hlo

/-- The integer block index is forced to be the actual floor. This proves
both directions, including points exactly at rational endpoints. -/
theorem fract_mem_iff_reciprocal_block (n l u v : ℝ)
    (hn : 0 ≤ n) (hl : 0 < l) (hu : 0 < u) (huv : u < v) (hv : v ≤ 1) :
    u ≤ Int.fract (n / l) ∧ Int.fract (n / l) < v ↔
      ∃ k : ℤ, 0 ≤ k ∧ n / ((k : ℝ) + v) < l ∧
        l ≤ n / ((k : ℝ) + u) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have hk : 0 ≤ ⌊n / l⌋ := Int.floor_nonneg.mpr (div_nonneg hn hl.le)
    refine ⟨⌊n / l⌋, hk, ?_⟩
    apply (reciprocal_block_iff n l (⌊n / l⌋ : ℝ) u v hl
      (by exact_mod_cast hk) hu huv).1
    change u ≤ n / l - (⌊n / l⌋ : ℝ) at hlo
    change n / l - (⌊n / l⌋ : ℝ) < v at hhi
    constructor <;> linarith
  · rintro ⟨k, hk, hlo, hhi⟩
    have hb := (reciprocal_block_iff n l (k : ℝ) u v hl
      (by exact_mod_cast hk) hu huv).2 ⟨hlo, hhi⟩
    have hf : ⌊n / l⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
    change u ≤ n / l - (⌊n / l⌋ : ℝ) ∧ n / l - (⌊n / l⌋ : ℝ) < v
    rw [hf]
    constructor <;> linarith [hb.1, hb.2]

open Classical in
/-- The exact source weight is the indicator of the literal interval union. -/
theorem actual_sourceWeight_indicator (n l : ℕ) :
    sourceWeight n l =
      if PaperR7.InOmegaSupport (Int.fract ((n : ℝ) / l)) then 1 else 0 := by
  classical
  have hi := PaperR7.omega_indicator (Int.fract ((n : ℝ) / l))
    (Int.fract_nonneg _) (Int.fract_lt_one _)
  have hw : sourceWeight n l = PaperR7.omegaWeight (Int.fract ((n : ℝ) / l)) := by
    exact (omegaWeight_fract _).symm
  rw [hw]
  by_cases hs : PaperR7.InOmegaSupport (Int.fract ((n : ℝ) / l))
  · rw [if_pos hs]
    exact hi.2.mpr hs
  · rw [if_neg hs]
    rcases hi.1 with h | h
    · exact h
    · exact (hs (hi.2.mp h)).elim

/-- All thirteen blocks are connected to the actual weight, not merely to
an unrelated periodic step function. -/
theorem actual_sourceWeight_one_iff_blocks (n l : ℕ) (hl : 0 < l) :
    sourceWeight n l = 1 ↔
      ∃ uv ∈ sourceIntervals, ∃ k : ℤ, 0 ≤ k ∧
        (n : ℝ) / ((k : ℝ) + (uv.2 : ℝ)) < l ∧
        (l : ℝ) ≤ (n : ℝ) / ((k : ℝ) + (uv.1 : ℝ)) := by
  classical
  rw [actual_sourceWeight_indicator]
  have hi : (if PaperR7.InOmegaSupport (Int.fract ((n : ℝ) / l)) then (1 : ℤ) else 0) = 1 ↔
      PaperR7.InOmegaSupport (Int.fract ((n : ℝ) / l)) := by
    split_ifs <;> simp_all
  rw [hi, omegaSupport_iff_sourceIntervals]
  apply exists_congr
  intro uv
  apply and_congr_right
  intro huv
  obtain ⟨hu, huv', hv⟩ := sourceIntervals_bounds uv huv
  exact fract_mem_iff_reciprocal_block n l uv.1 uv.2
    (Nat.cast_nonneg _) (by exact_mod_cast hl) hu huv' hv

/-- A finite totient prefix retains the exact integer cut-off. -/
noncomputable def finiteTotientPrefix (N : ℕ) (x : ℝ) : ℤ :=
  ∑ l ∈ Finset.Icc 1 N, if (l : ℝ) ≤ x then (l.totient : ℤ) else 0

/-- Exact finite interval summation, before any analytic approximation. -/
theorem finite_totient_block (N : ℕ) (lo hi : ℝ) (h : lo ≤ hi) :
    (∑ l ∈ Finset.Icc 1 N,
      if lo < (l : ℝ) ∧ (l : ℝ) ≤ hi then (l.totient : ℤ) else 0) =
      finiteTotientPrefix N hi - finiteTotientPrefix N lo := by
  classical
  unfold finiteTotientPrefix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlo : (l : ℝ) ≤ lo
  · have hhi : (l : ℝ) ≤ hi := hlo.trans h
    simp [hlo, hhi, not_lt_of_ge hlo]
  · have hlo' : lo < (l : ℝ) := lt_of_not_ge hlo
    by_cases hhi : (l : ℝ) ≤ hi <;> simp [hlo, hlo', hhi]

/-- A reciprocal block is a difference S(n/(k+u))-S(n/(k+v)),
not the difference with either endpoint shifted by one. -/
theorem actual_reciprocal_totient_block (N : ℕ) (n k u v : ℝ)
    (hn : 0 ≤ n) (hk : 0 ≤ k) (hu : 0 < u) (huv : u < v) :
    (∑ l ∈ Finset.Icc 1 N,
      if n / (k + v) < (l : ℝ) ∧ (l : ℝ) ≤ n / (k + u)
      then (l.totient : ℤ) else 0) =
      finiteTotientPrefix N (n / (k + u)) -
        finiteTotientPrefix N (n / (k + v)) := by
  apply finite_totient_block
  exact div_le_div_of_nonneg_left hn (by linarith) (by linarith)

noncomputable def actualWeightedTotientSum (n : ℕ) : ℤ :=
  ∑ l ∈ Finset.Icc 1 (15 * n), sourceWeight n l * (l.totient : ℤ)

/-- Literal weighted sum to literal thirteen-interval indicator. -/
theorem actual_weighted_totient_indicator (n : ℕ) :
    actualWeightedTotientSum n =
      ∑ l ∈ Finset.Icc 1 (15 * n),
        if ∃ uv ∈ sourceIntervals,
          (uv.1 : ℝ) ≤ Int.fract ((n : ℝ) / l) ∧
          Int.fract ((n : ℝ) / l) < (uv.2 : ℝ)
        then (l.totient : ℤ) else 0 := by
  classical
  unfold actualWeightedTotientSum
  apply Finset.sum_congr rfl
  intro l hl
  rw [actual_sourceWeight_indicator, omegaSupport_iff_sourceIntervals]
  split_ifs <;> simp

end ErdosProblems.Erdos1049.PaperR12
