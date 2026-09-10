import ErdosProblems.Erdos251.SparseScheduleDensityR8
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Interval filling on the constructed sparse centres

UNCOMPILED round-8 source. Unlike the inherited feedback theorem, the
capacity, overlap and vanishing inputs here are proved for a schedule
actually constructed from the arbitrary divergent envelope.

This file stops at the indexed correction sum. Ambient zero-extension and
its all-index cumulative congruences, and the polylogarithmic support-rate
specialisation, remain explicitly listed in the handoff. It is NOT labelled
a proof of the complete displayed sparse proposition.

Pinned Mathlib sources checked before using their APIs:
* Analysis/SpecificLimits/Normed.lean: summable_pow_mul_geometric_of_norm_lt_one.
* Topology/Algebra/InfiniteSum/Group.lean: Summable.comp_injective, tsum_sub.
* Topology/Algebra/InfiniteSum/ENNReal.lean: Summable.of_nonneg_of_le.
* Topology/Algebra/InfiniteSum/NatInt.lean: summable_nat_add_iff,
  Summable.tsum_eq_zero_add, tendsto_sum_nat_add.
* Topology/Algebra/InfiniteSum/Order.lean: tsum_nonneg, Summable.le_tsum.
-/

noncomputable section
open Filter Topology
namespace ErdosProblems.Erdos251.PaperR8.SparseSchedule

/-- Positive dyadic weight at the actual, nonconsecutive centre. -/
def weight (f : ℕ → ℝ) (start j : ℕ) : ℝ := 1 / 2 ^ (centre f start j + 1)

theorem weight_pos (f : ℕ → ℝ) (start j : ℕ) : 0 < weight f start j := by
  unfold weight
  positivity

/-- A summable linear majorant, with no bound assumed on the input envelope. -/
theorem linear_weight_summable :
    Summable (fun n : ℕ => ((n : ℝ) + 1) / 2 ^ (n + 1)) := by
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ 0 * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 (by norm_num)
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have hs := (h1.add h0).mul_left (1 / 2 : ℝ)
  apply hs.congr
  intro n
  simp only [pow_zero, pow_one, one_mul, div_pow, one_pow, pow_succ]
  ring

/-- All actual scheduled capacities have finite total dyadic mass. -/
theorem capacity_weight_summable (f : ℕ → ℝ) (start : ℕ)
    (hstart : Ready f start 0) :
    Summable (fun j => (capacity f start j : ℝ) * weight f start j) := by
  have hsub := linear_weight_summable.comp_injective (centre_strictMono f start).injective
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (Nat.cast_nonneg _) (weight_pos f start j).le) ?_ hsub
  intro j
  have hb : (capacity f start j : ℝ) ≤ (centre f start j : ℝ) + 1 := by
    exact_mod_cast (capacity_budget f start hstart j).2
  simpa only [Function.comp_apply, weight, mul_one_div] using
    (div_le_div_of_nonneg_right hb
      (by positivity : (0 : ℝ) ≤ 2 ^ (centre f start j + 1)))

def lowerTerm (f : ℕ → ℝ) (start j : ℕ) : ℝ :=
  (modulus f start j : ℝ) * weight f start j

def upperTerm (f : ℕ → ℝ) (start j : ℕ) : ℝ :=
  ((capacity f start j : ℝ) - modulus f start j) * weight f start j

def widthTerm (f : ℕ → ℝ) (start j : ℕ) : ℝ :=
  ((capacity f start j : ℝ) - 2 * modulus f start j) * weight f start j

theorem term_order (f : ℕ → ℝ) (start j : ℕ) :
    0 ≤ lowerTerm f start j ∧
    lowerTerm f start j ≤ upperTerm f start j ∧
    upperTerm f start j ≤ (capacity f start j : ℝ) * weight f start j := by
  have hA : 2 * (modulus f start j : ℝ) ≤ capacity f start j := by
    exact_mod_cast twice_modulus_le_capacity f start j
  have hM : (0 : ℝ) ≤ modulus f start j := Nat.cast_nonneg _
  have hw := (weight_pos f start j).le
  dsimp [lowerTerm, upperTerm]
  refine ⟨mul_nonneg hM hw, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) hw
  · exact mul_le_mul_of_nonneg_right (by linarith) hw

theorem terms_summable (f : ℕ → ℝ) (start : ℕ) (hstart : Ready f start 0) :
    Summable (lowerTerm f start) ∧ Summable (upperTerm f start) ∧
      Summable (widthTerm f start) := by
  have hcap := capacity_weight_summable f start hstart
  have hl : Summable (lowerTerm f start) :=
    Summable.of_nonneg_of_le (fun j => (term_order f start j).1)
      (fun j => (term_order f start j).2.1.trans (term_order f start j).2.2) hcap
  have hu : Summable (upperTerm f start) :=
    Summable.of_nonneg_of_le
      (fun j => (term_order f start j).1.trans (term_order f start j).2.1)
      (fun j => (term_order f start j).2.2) hcap
  refine ⟨hl, hu, ?_⟩
  apply (hu.sub hl).congr
  intro j
  dsimp [upperTerm, lowerTerm, widthTerm]
  ring

def lowerTail (f : ℕ → ℝ) (start n : ℕ) : ℝ := ∑' j, lowerTerm f start (j + n)
def upperTail (f : ℕ → ℝ) (start n : ℕ) : ℝ := ∑' j, upperTerm f start (j + n)

theorem lowerTail_nonnegative (f : ℕ → ℝ) (start n : ℕ) : 0 ≤ lowerTail f start n :=
  tsum_nonneg (fun j => (term_order f start (j + n)).1)

theorem lowerTail_step (f : ℕ → ℝ) (start : ℕ) (hstart : Ready f start 0) (n : ℕ) :
    lowerTail f start n = lowerTerm f start n + lowerTail f start (n + 1) := by
  have hs := (summable_nat_add_iff n).mpr (terms_summable f start hstart).1
  have he := hs.tsum_eq_zero_add
  simpa only [lowerTail, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using he

theorem upperTail_step (f : ℕ → ℝ) (start : ℕ) (hstart : Ready f start 0) (n : ℕ) :
    upperTail f start n = upperTerm f start n + upperTail f start (n + 1) := by
  have hs := (summable_nat_add_iff n).mpr (terms_summable f start hstart).2.1
  have he := hs.tsum_eq_zero_add
  simpa only [upperTail, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using he

theorem tail_width (f : ℕ → ℝ) (start : ℕ) (hstart : Ready f start 0) (n : ℕ) :
    upperTail f start n - lowerTail f start n = ∑' j, widthTerm f start (j + n) := by
  have hl := (summable_nat_add_iff n).mpr (terms_summable f start hstart).1
  have hu := (summable_nat_add_iff n).mpr (terms_summable f start hstart).2.1
  rw [upperTail, lowerTail, ← hu.tsum_sub hl]
  apply tsum_congr
  intro j
  dsimp [upperTerm, lowerTerm, widthTerm]
  ring

theorem widthTerm_nonnegative (f : ℕ → ℝ) (start j : ℕ) : 0 ≤ widthTerm f start j := by
  have hA : 2 * (modulus f start j : ℝ) ≤ capacity f start j := by
    exact_mod_cast twice_modulus_le_capacity f start j
  exact mul_nonneg (sub_nonneg.mpr hA) (weight_pos f start j).le

/-- The next-site integer budget supplies overlap of the complete tails. -/
theorem generated_overlap (f : ℕ → ℝ) (start : ℕ) (hstart : Ready f start 0) (j : ℕ) :
    (modulus f start j : ℝ) * weight f start j ≤
      upperTail f start (j + 1) - lowerTail f start (j + 1) := by
  have hbudget : (modulus f start j : ℝ) * 2 ^ gap (level f start j) +
      2 * modulus f start (j + 1) ≤ capacity f start (j + 1) := by
    exact_mod_cast next_capacity_overlap f start j
  have hweights : weight f start j =
      2 ^ gap (level f start j) * weight f start (j + 1) := by
    unfold weight
    rw [centre_succ]
    rw [show centre f start j + gap (level f start j) + 1 =
      (centre f start j + 1) + gap (level f start j) by omega, pow_add]
    field_simp
    rw [pow_add, pow_succ]
  have hfirst : (modulus f start j : ℝ) * weight f start j ≤
      widthTerm f start (j + 1) := by
    rw [hweights]
    unfold widthTerm
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (weight_pos f start (j + 1)).le
  have hs := (summable_nat_add_iff (j + 1)).mpr (terms_summable f start hstart).2.2
  have htail : widthTerm f start (j + 1) ≤ ∑' k, widthTerm f start (k + (j + 1)) := by
    simpa only [Nat.zero_add] using
      hs.le_tsum 0 (fun k _ => widthTerm_nonnegative f start (k + (j + 1)))
  rw [tail_width f start hstart (j + 1)]
  exact hfirst.trans htail

theorem upperTail_tendsto_zero (f : ℕ → ℝ) (start : ℕ) :
    Tendsto (upperTail f start) atTop (𝓝 0) :=
  tendsto_sum_nat_add (upperTerm f start)

/-- There is a single nondegenerate interval for all digit choices. -/
theorem generated_interval_nonempty (f : ℕ → ℝ) (start : ℕ) (hstart : Ready f start 0) :
    lowerTail f start 0 < upperTail f start 0 := by
  have hov := generated_overlap f start hstart 0
  have hp : 0 < (modulus f start 0 : ℝ) * weight f start 0 :=
    mul_pos (by exact_mod_cast modulus_pos f start 0) (weight_pos f start 0)
  have hw := widthTerm_nonnegative f start 0
  rw [upperTail_step f start hstart 0, lowerTail_step f start hstart 0]
  dsimp [upperTerm, lowerTerm, widthTerm] at hw ⊢
  linarith

theorem lowerTail_positive (f : ℕ → ℝ) (start : ℕ) (hstart : Ready f start 0) :
    0 < lowerTail f start 0 := by
  rw [lowerTail_step f start hstart 0]
  have ht : 0 < lowerTerm f start 0 :=
    mul_pos (by exact_mod_cast modulus_pos f start 0) (weight_pos f start 0)
  exact add_pos_of_pos_of_nonneg ht (lowerTail_nonnegative f start 1)

/-- The variable-capacity hypotheses have now all been discharged for the
constructed schedule. This is an indexed sum, not an ambient-word endpoint. -/
theorem generated_interval_filling (f : ℕ → ℝ) (start : ℕ)
    (hstart : Ready f start 0) {y : ℝ}
    (hyl : lowerTail f start 0 ≤ y) (hyu : y ≤ upperTail f start 0) :
    ∃ d : ℕ → ℕ,
      (∀ j, d j ≤ capacity f start j) ∧
      (∀ j, (modulus f start j : ℤ) ∣ ((∑ i ∈ Finset.range (j + 1), d i : ℕ) : ℤ)) ∧
      HasSum (fun j => (d j : ℝ) / 2 ^ (centre f start j + 1)) y := by
  obtain ⟨d, hd, hc, hs⟩ := ResidueFeedback.exists_feedback_digits_hasSum
    (modulus_pos f start) (twice_modulus_le_capacity f start)
    (weight_pos f start) (lowerTail_nonnegative f start)
    (lowerTail_step f start hstart) (upperTail_step f start hstart)
    (generated_overlap f start hstart) (upperTail_tendsto_zero f start) hyl hyu
  refine ⟨d, hd, hc, ?_⟩
  simpa only [weight, mul_one_div] using hs

/-- Main partial endpoint: one support, one nondegenerate positive interval,
and all indexed correction targets, constructed from f and K alone.
The seed is chosen before y, and every capacity hypothesis is discharged. -/
theorem arbitrary_envelope_indexed_interval (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ start : ℕ, ∃ lo hi : ℝ,
      K ≤ start ∧ (Set.range (centre f start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre f start)) ∧ 0 < lo ∧ lo < hi ∧
      ∀ y : ℝ, lo ≤ y → y ≤ hi → ∃ d : ℕ → ℕ,
        (∀ j, (d j : ℝ) ≤ f (centre f start j)) ∧
        (∀ j, (modulus f start j : ℤ) ∣
          ((∑ i ∈ Finset.range (j + 1), d i : ℕ) : ℤ)) ∧
        HasSum (fun j => (d j : ℝ) / 2 ^ (centre f start j + 1)) y := by
  obtain ⟨start, hK, hready, hsupport, hdensity, hbudget⟩ :=
    exists_sparse_budgeted_support f hf K
  refine ⟨start, lowerTail f start 0, upperTail f start 0,
    hK, hsupport, hdensity, lowerTail_positive f start hready,
    generated_interval_nonempty f start hready, ?_⟩
  intro y hyl hyu
  obtain ⟨d, hd, hc, hs⟩ := generated_interval_filling f start hready hyl hyu
  refine ⟨d, ?_, hc, hs⟩
  intro j
  have hdR : (d j : ℝ) ≤ capacity f start j := by exact_mod_cast hd j
  exact hdR.trans (hbudget j).1

/-- Remaining ambient-word endpoint, made explicit rather than assumed.
The constructed indexed digits must still be embedded with the corresponding
finite-prefix identity. This definition is not asserted as a theorem. -/
def AmbientSparseRationalisation_target : Prop :=
  ∀ f : ℕ → ℝ, Tendsto f atTop atTop → ∀ K : ℕ,
    ∃ S : Set ℕ, ∃ lo hi : ℝ,
      S ⊆ Set.Ici K ∧ UpperBanachZero S ∧ 0 < lo ∧ lo < hi ∧
      ∀ y : ℝ, lo ≤ y → y ≤ hi → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
          q ∣ e n ∧ q ∣ ∑ i ∈ Finset.range n, e i) ∧
        HasSum (fun n : ℕ => (e n : ℝ) / 2 ^ (n + 1)) y

/-- The quantitative polylogarithmic counting input is NOT supplied by
upper Banach density zero. Its proof remains part of the paper label. -/
def PolylogarithmicRate_target : Prop :=
  ∀ α : ℝ, 0 < α → ∀ start : ℕ,
    Ready (fun n => (Real.log ((n : ℝ) + 3)) ^ α) start 0 →
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ((supportSlice (centre (fun n => (Real.log ((n : ℝ) + 3)) ^ α) start) X X).card : ℝ) ≤
        C * X / Real.log (Real.log ((X : ℝ) + 3))

#print axioms arbitrary_envelope_indexed_interval
#print axioms generated_interval_filling
#print axioms generated_interval_nonempty
end ErdosProblems.Erdos251.PaperR8.SparseSchedule
