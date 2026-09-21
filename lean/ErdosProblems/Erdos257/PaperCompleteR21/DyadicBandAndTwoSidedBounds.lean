import Erdos249257.HalfUpperResetCriticalBand
import Erdos249257.HalfCylinderMiddleCarryLowerBound

/-!
Paper-form restatements of two asserted environments from the long
Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

* `record:257bm-c11` (`a257_front.tex:4212`), "Testing one nearest dyadic
  boundary": `paper_critical_dyadic_band_index_unique`,
  `paper_critical_dyadic_boundary_is_smallest`,
  `paper_critical_dyadic_band_index_eq_top_of_le_two`,
  `paper_dyadic_band_escape_iff_single_test`.
* `record:257bm-i13` (`a257_front.tex:4985`), "Two-sided dyadic bounds":
  `paper_two_sided_dyadic_bound`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfUpperResetCriticalBand
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## `record:257bm-c11` -- testing one nearest dyadic boundary -/

/-- The paper's `j_* := max {0 ≤ j ≤ d : E ≤ 2^(d-j+1)}` is the unique index
satisfying `CriticalDyadicBandIndex d E j`. -/
theorem paper_critical_dyadic_band_index_unique {d E : ℕ}
    (hE : E ≤ 2 ^ (d + 1)) :
    ∃! j : ℕ, CriticalDyadicBandIndex d E j := by
  obtain ⟨j, hj⟩ := exists_criticalDyadicBandIndex hE
  refine ⟨j, hj, ?_⟩
  intro i hi
  by_contra hne
  -- Two distinct critical indices contradict each other's defining clauses.
  have key : ∀ a b : ℕ, CriticalDyadicBandIndex d E a →
      CriticalDyadicBandIndex d E b → a < b → False := by
    intro a b ha hb hab
    obtain ⟨had, haE, hanext⟩ := ha
    obtain ⟨hbd, hbE, _⟩ := hb
    rcases hanext with hlast | hgap
    · omega
    · have hexp : d - b + 1 ≤ d - (a + 1) + 1 := by omega
      have hpow : (2 : ℕ) ^ (d - b + 1) ≤ 2 ^ (d - (a + 1) + 1) :=
        Nat.pow_le_pow_right (by norm_num) hexp
      omega
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact key i j hi hj hlt
  · exact hne heq
  · exact key j i hj hi hgt

/-- "The boundary `2^(d-j_*+1)` is the smallest power at least `E` among the
finite list `2, 4, …, 2^(d+1)`." -/
theorem paper_critical_dyadic_boundary_is_smallest {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    E ≤ 2 ^ (d - j + 1) ∧
      ∀ i : ℕ, i ≤ d → E ≤ 2 ^ (d - i + 1) →
        (2 : ℕ) ^ (d - j + 1) ≤ 2 ^ (d - i + 1) := by
  obtain ⟨hjd, hjE, hjnext⟩ := hj
  refine ⟨hjE, ?_⟩
  intro i hid hiE
  by_cases hij : i ≤ j
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exfalso
    rcases hjnext with hlast | hgap
    · omega
    · have hexp : d - i + 1 ≤ d - (j + 1) + 1 := by omega
      have hpow : (2 : ℕ) ^ (d - i + 1) ≤ 2 ^ (d - (j + 1) + 1) :=
        Nat.pow_le_pow_right (by norm_num) hexp
      omega

/-- "In particular `j_* = d` when `E ≤ 2`." -/
theorem paper_critical_dyadic_band_index_eq_top_of_le_two {d E j : ℕ}
    (hE : E ≤ 2) (hj : CriticalDyadicBandIndex d E j) :
    j = d := by
  obtain ⟨hjd, hjE, hjnext⟩ := hj
  rcases hjnext with hlast | hgap
  · exact hlast
  · exfalso
    have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ (d - (j + 1) + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [pow_one] at hpow
    omega

/-- Paper display of `record:257bm-c11`: for `E ≤ 2^(d+1)` and the critical
index `j_*`, the universal band family

`∀ 0 ≤ j ≤ d, 2^(d-j+1) < E ∨ E + 2(d+j) ≤ 2^(d-j+1)`

is equivalent to the single inequality `E + 2(d+j_*) ≤ 2^(d-j_*+1)`. -/
theorem paper_dyadic_band_escape_iff_single_test {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    DyadicBandEscape d E ↔ E + 2 * (d + j) ≤ 2 ^ (d - j + 1) := by
  constructor
  · intro hall
    rcases hall j hj.1 with habove | hbelow
    · have := hj.2.1
      omega
    · exact hbelow
  · intro hgap
    exact dyadicBandEscape_of_critical hj hgap

/-! ## `record:257bm-i13` -- two-sided dyadic bounds -/

/-- Paper display of `record:257bm-i13`: under the local cell-escape
hypothesis, `∀ s ≥ 5, min(rem(s), overshoot(s)) ≤ 2^s`. -/
theorem paper_two_sided_dyadic_bound
    (hescape : SeamTwoSidedDyadicCellEscape) (s : ℕ) (hs : 5 ≤ s) :
    min (seamIntegerGreedyRemainder s) ((seamAdjacentCut s hs).overshoot) ≤
      2 ^ s := by
  rcases hescape.twoSided s hs with hrem | hover
  · exact le_trans (min_le_left _ _) hrem
  · exact le_trans (min_le_right _ _) hover

#print axioms paper_critical_dyadic_band_index_unique
#print axioms paper_critical_dyadic_boundary_is_smallest
#print axioms paper_critical_dyadic_band_index_eq_top_of_le_two
#print axioms paper_dyadic_band_escape_iff_single_test
#print axioms paper_two_sided_dyadic_bound

end ErdosProblems.Erdos257.PaperCompleteR21
