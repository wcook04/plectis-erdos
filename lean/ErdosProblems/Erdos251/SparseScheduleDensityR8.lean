import ErdosProblems.Erdos251.SparseScheduleR8
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Uniform interval counting for the round-8 sparse schedule

New UNCOMPILED source. Upper Banach density zero is stated in the equivalent
integer-reciprocal form: for every positive R, eventually every length-L
interval has at most L/R support points. This is uniform in the interval's
starting point, not merely natural density zero.

Pinned Mathlib APIs:
* Data/Finset/Card.lean: card_bij, card_le_card_of_injOn, card_union_le.
* Order/Interval/Finset/Nat.lean: membership in Ico.
-/

noncomputable section
open Finset Filter Topology

namespace ErdosProblems.Erdos251.PaperR8.SparseSchedule

/-- Actual support points in the half-open interval [a,a+L). -/
def supportSlice (c : ℕ → ℕ) (a L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico a (a + L)).filter (fun n => n ∈ Set.range c)

/-- Indices of those support points. A strictly increasing natural map
satisfies j <= c j, so range(a+L) suffices. -/
def indexSlice (c : ℕ → ℕ) (a L : ℕ) : Finset ℕ :=
  (Finset.range (a + L)).filter (fun j => a ≤ c j ∧ c j < a + L)

theorem supportSlice_card (c : ℕ → ℕ) (hc : StrictMono c) (a L : ℕ) :
    (supportSlice c a L).card = (indexSlice c a L).card := by
  classical
  symm
  apply Finset.card_bij (fun j _ => c j)
  · intro j hj
    have hbounds := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr hbounds, ⟨j, rfl⟩⟩
  · intro i hi j hj heq
    exact hc.injective heq
  · intro n hn
    obtain ⟨hnI, j, rfl⟩ := Finset.mem_filter.mp hn
    have hb := Finset.mem_Ico.mp hnI
    refine ⟨j, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((index_le_of_strictMono c hc j).trans_lt hb.2), hb⟩

/-- Equal quotient bins have width strictly less than R. -/
theorem equal_bin_close {x y R : ℕ} (hR : 0 < R) (h : x / R = y / R) :
    y < x + R := by
  have hx := Nat.mod_add_div x R
  have hy := Nat.mod_add_div y R
  have hxm := Nat.mod_lt x hR
  have hym := Nat.mod_lt y hR
  rw [← h] at hy
  omega

/-- Quantitative bound, including the finite irregular prefix J. -/
theorem supportSlice_card_le (c : ℕ → ℕ) (hc : StrictMono c)
    (J R : ℕ) (hR : 0 < R)
    (hsep : ∀ j, J ≤ j → R ≤ c (j + 1) - c j) (a L : ℕ) :
    (supportSlice c a L).card ≤ J + L / R + 1 := by
  classical
  let late := (indexSlice c a L).filter (fun j => J ≤ j)
  have hlate : late.card ≤ L / R + 1 := by
    have hmap : Set.MapsTo (fun j => (c j - a) / R)
        (late : Set ℕ) (Finset.range (L / R + 1) : Set ℕ) := by
      intro j hj
      have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      have hnum : c j - a ≤ L := by omega
      have hdiv : (c j - a) / R ≤ L / R := Nat.div_le_div_right hnum
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hdiv)
    have hinj : Set.InjOn (fun j => (c j - a) / R) (late : Set ℕ) := by
      intro i hi j hj heq
      have hiJ := (Finset.mem_filter.mp hi).2
      have hjJ := (Finset.mem_filter.mp hj).2
      have hib := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      have hjb := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      have hclose1 := equal_bin_close hR heq
      have hclose2 := equal_bin_close hR heq.symm
      obtain hij | hij | hij := lt_trichotomy i j
      · have hs := hsep i hiJ
        have hm : c (i + 1) ≤ c j := hc.monotone (Nat.succ_le_of_lt hij)
        omega
      · exact hij
      · have hs := hsep j hjJ
        have hm : c (j + 1) ≤ c i := hc.monotone (Nat.succ_le_of_lt hij)
        omega
    have hcard := Finset.card_le_card_of_injOn
      (fun j => (c j - a) / R) hmap hinj
    simpa only [Finset.card_range] using hcard
  have hsub : indexSlice c a L ⊆ Finset.range J ∪ late := by
    intro j hj
    by_cases hearly : j < J
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_range.mpr hearly))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hj, by omega⟩))
  have htotal : (indexSlice c a L).card ≤ J + late.card := by
    have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simpa only [Finset.card_range] using h
  rw [supportSlice_card c hc a L]
  omega

/-- Reciprocal-integer characterisation of upper Banach density zero. -/
def UpperBanachZero (S : Set ℕ) : Prop := by
  classical
  exact ∀ R : ℕ, 0 < R → ∃ L₀ : ℕ, ∀ a L : ℕ, L₀ ≤ L →
    R * ((Finset.Ico a (a + L)).filter (fun n => n ∈ S)).card ≤ L

/-- Divergent successive spacings imply upper Banach density zero,
uniformly over every translate of the interval. -/
theorem upperBanachZero_of_eventual_spacing (c : ℕ → ℕ) (hc : StrictMono c)
    (hgap : ∀ R, ∃ J, ∀ j, J ≤ j → R ≤ c (j + 1) - c j) :
    UpperBanachZero (Set.range c) := by
  classical
  intro R hR
  obtain ⟨J, hJ⟩ := hgap (2 * R)
  refine ⟨2 * R * (J + 1), ?_⟩
  intro a L hL
  have h2R : 0 < 2 * R := Nat.mul_pos (by decide) hR
  have hcL := supportSlice_card_le c hc J (2 * R) h2R hJ a L
  have hdiv : L / (2 * R) * (2 * R) ≤ L := Nat.div_mul_le_self L (2 * R)
  have hmul := Nat.mul_le_mul_left (2 * R) hcL
  change R * (supportSlice c a L).card ≤ L
  nlinarith

/-- The generated support satisfies the requested translated-interval
zero-density condition, not just a cofinal spacing assertion. -/
theorem generated_support_upperBanachZero (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop) (start : ℕ) :
    UpperBanachZero (Set.range (centre f start)) :=
  upperBanachZero_of_eventual_spacing (centre f start)
    (centre_strictMono f start) (eventual_spacing f hf start)

/-- Exact arbitrary-envelope support package. The polylogarithmic *rate*
is deliberately not inferred from upper Banach density zero. -/
theorem exists_sparse_budgeted_support (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ start : ℕ, K ≤ start ∧ Ready f start 0 ∧
      (Set.range (centre f start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre f start)) ∧
      (∀ j, (capacity f start j : ℝ) ≤ f (centre f start j) ∧
        capacity f start j ≤ centre f start j + 1) := by
  obtain ⟨start, hK, hready, hmono, hbudget, _⟩ :=
    exists_budgeted_schedule f hf K
  refine ⟨start, hK, hready, ?_, generated_support_upperBanachZero f hf start, hbudget⟩
  rintro n ⟨j, rfl⟩
  exact hK.trans (hmono.monotone (Nat.zero_le j))

#print axioms exists_sparse_budgeted_support
end ErdosProblems.Erdos251.PaperR8.SparseSchedule
