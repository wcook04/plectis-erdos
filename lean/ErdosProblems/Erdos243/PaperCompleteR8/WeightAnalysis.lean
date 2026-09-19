import ErdosProblems.Erdos243.PaperCompleteR8.Foundation
import ErdosProblems.Erdos243.PaperCompleteR7.RealTail
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The analytic part of the weighted-record assembly

Uncompiled round-8 candidates. No assumed divergence of sampled weights is
left in the paper-facing theorem. Its source is the displayed improper
integral and antitonicity on `[1, infinity)`.

Pinned source checks:
* Analysis/SumIntegralComparisons.lean: AntitoneOn.integral_le_sum.
* Topology/Algebra/InfiniteSum/Real.lean: summable_of_sum_range_le.
* Topology/Algebra/InfiniteSum/NatInt.lean: summable_nat_add_iff.
* Algebra/BigOperators/Group/Finset/Basic.lean: sum_range_add, sum_range_succ.
* Topology/Algebra/InfiniteSum/Order.lean: Summable.sum_le_tsum.
* Algebra/Order/BigOperators/Group/Finset.lean: sum_le_sum,
  sum_le_sum_of_subset_of_nonneg.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR8

open Filter MeasureTheory
open scoped BigOperators

/-- Restriction to natural heights, with a harmless constant value at zero. -/
noncomputable def heightWeight (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  f (max 1 (n : ℝ))

/-- Improper integral divergence, without assigning `tsum` or a Bochner
integral its default value on a nonintegrable function. -/
def DivergentIntegral (f : ℝ → ℝ) : Prop :=
  Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop

theorem heightWeight_antitone
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1)) :
    Antitone (heightWeight f) := by
  intro m n hmn
  change f (max 1 (n : ℝ)) ≤ f (max 1 (m : ℝ))
  apply hf
  · exact (show (1 : ℝ) ≤ max 1 (m : ℝ) from le_max_left _ _)
  · exact (show (1 : ℝ) ≤ max 1 (n : ℝ) from le_max_left _ _)
  · exact max_le_max le_rfl (by exact_mod_cast hmn)

theorem heightWeight_nonneg
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (n : ℕ) :
    0 ≤ heightWeight f n := hf _ (le_max_left _ _)

theorem heightWeight_eq
    (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n) :
    heightWeight f n = f n := by
  have hnNat : (1 : ℕ) ≤ n := Nat.succ_le_iff.mpr hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  exact congrArg f (max_eq_right hnR)

/-- Integral divergence implies nonsummability of the actual integer
height weights, not of a different translated weight. -/
theorem not_summable_heightWeight
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : DivergentIntegral f) :
    ¬ Summable (heightWeight f) := by
  intro hs
  let M : ℝ := ∑' n, heightWeight f (n + 1)
  -- Topology/Algebra/InfiniteSum/Group.lean: Summable.comp_injective.
  have ht : Summable (fun n : ℕ => heightWeight f (n + 1)) :=
    hs.comp_injective (fun i j hij => by omega)
  have hupper : ∀ N : ℕ, (∫ x in (1 : ℝ)..(1 + (N : ℝ)), f x) ≤ M := by
    intro N
    have hmono : AntitoneOn f (Set.Icc 1 (1 + (N : ℝ))) := by
      intro x hx y hy hxy
      exact hf hx.1 hy.1 hxy
    -- Analysis/SumIntegralComparisons.lean.
    have hcomp := hmono.integral_le_sum
    have hsum : (∑ i ∈ Finset.range N, f (1 + (i : ℝ))) =
        ∑ i ∈ Finset.range N, heightWeight f (i + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [heightWeight_eq f (i + 1) (by omega)]
      congr 1
      push_cast
      ring
    rw [hsum] at hcomp
    exact hcomp.trans (ht.sum_le_tsum (Finset.range N)
      (fun i _ => heightWeight_nonneg f hpos (i + 1)))
  have hnat : Tendsto (fun N : ℕ => 1 + (N : ℝ)) atTop atTop := by
    have hc := PaperCompleteR7.strictMono_nat_cast_tendsto_atTop
      (fun n : ℕ => n + 1) (fun i j hij => by dsimp only at *; omega)
      (fun n => by change 0 < n + 1; omega)
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hc
  have hnatdiv := hdiv.comp hnat
  have hev : ∀ᶠ N : ℕ in atTop,
      M + 1 ≤ ∫ x in (1 : ℝ)..(1 + (N : ℝ)), f x :=
    (tendsto_atTop.mp hnatdiv) (M + 1)
  obtain ⟨N, hN⟩ := hev.exists
  have hu := hupper N
  linarith

/-- Blocking a decreasing sequence into intervals of length P. -/
theorem antitone_block_sum
    (f : ℕ → ℝ) (hf : Antitone f) (x P K : ℕ) :
    (∑ i ∈ Finset.range (P * K), f (x + i)) ≤
      (P : ℝ) * ∑ k ∈ Finset.range K, f (x + k * P) := by
  induction K with
  | zero => simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, mul_zero, le_refl]
  | succ K ih =>
      have hblock : (∑ i ∈ Finset.range P, f (x + (P * K + i))) ≤
          (P : ℝ) * f (x + K * P) := by
        calc
          (∑ i ∈ Finset.range P, f (x + (P * K + i))) ≤
              ∑ _i ∈ Finset.range P, f (x + K * P) := by
            apply Finset.sum_le_sum
            intro i _
            apply hf
            rw [Nat.mul_comm K P]
            omega
          _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range (P * K), f (x + i)) +
            (∑ i ∈ Finset.range P, f (x + (P * K + i))) ≤
            (P : ℝ) * (∑ k ∈ Finset.range K, f (x + k * P)) +
              (P : ℝ) * f (x + K * P) := add_le_add ih hblock
        _ = _ := by ring

/-- A divergent nonnegative decreasing series remains divergent on every
nondegenerate arithmetic progression. This closes the analytic input in the
already-checked finite record-crossing consumer. -/
theorem progression_not_summable
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ n, 0 ≤ f n)
    (hdiv : ¬ Summable f) (x P : ℕ) (hP : 0 < P) :
    ¬ Summable (fun k : ℕ => f (x + k * P)) := by
  intro hs
  apply hdiv
  -- Topology/Algebra/InfiniteSum/Real.lean.
  apply summable_of_sum_range_le hpos
    (c := (∑ i ∈ Finset.range x, f i) +
      (P : ℝ) * ∑' k : ℕ, f (x + k * P))
  intro N
  have hNP : N ≤ x + P * N := by nlinarith
  have hextend : (∑ i ∈ Finset.range N, f i) ≤
      ∑ i ∈ Finset.range (x + P * N), f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNP)
      (fun i _ _ => hpos i)
  have hblock := antitone_block_sum f hf x P N
  have hbound := hs.sum_le_tsum (Finset.range N) (fun k _ => hpos (x + k * P))
  have hmul := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg P)
  rw [Finset.sum_range_add] at hextend
  exact hextend.trans (add_le_add_right (hblock.trans hmul) _)

/-- Tail reindexing is checked separately from the arithmetic argument. -/
theorem summable_shift_iff (f : ℕ → ℝ) (T : ℕ) :
    Summable (fun n => f (T + n)) ↔ Summable f := by
  -- Topology/Algebra/InfiniteSum/NatInt.lean (to_additive of
  -- `multipliable_nat_add_iff`).
  simpa only [Nat.add_comm] using (summable_nat_add_iff (f := f) T)

/-- Finite-support direction, with a concrete finite sum as the bound. -/
theorem summable_of_eventually_zero_nonneg
    (f : ℕ → ℝ) (hpos : ∀ n, 0 ≤ f n)
    (hz : ∃ N, ∀ n, N ≤ n → f n = 0) : Summable f := by
  obtain ⟨N, hN⟩ := hz
  apply summable_of_sum_range_le hpos (c := ∑ i ∈ Finset.range N, f i)
  intro n
  by_cases hn : n ≤ N
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun i _ _ => hpos i)
  · have hNn : N ≤ n := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNn
    rw [Finset.sum_range_add]
    have htail : (∑ i ∈ Finset.range k, f (N + i)) = 0 :=
      Finset.sum_eq_zero (fun i _ => hN (N + i) (by omega))
    rw [htail, add_zero]

end ErdosProblems.Erdos243.PaperCompleteR8
