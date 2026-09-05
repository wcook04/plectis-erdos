import Erdos249257.SupportSunflowerDichotomy
import Erdos249257.AllBaseReciprocalSupportIrrationality

/-!
# Bouquet irrationality from reciprocal summability

The support-class conclusion follows from the actual petal reciprocal bound.
The older forced-slot selector is unnecessary for this irrationality theorem.
-/

namespace Erdos249257.SupportSunflowerDichotomy

namespace OrthogonalPetalBouquet

/-- Every orthogonal-petal bouquet is already reciprocal-summable.  The
summable petal hypothesis dominates the ray reciprocals because every positive
core only enlarges its petal; the exceptional frame is finite.  Consequently
this bouquet interface cannot reach the reciprocal-divergent regime. -/
theorem summable_reciprocalSupportTerm {A : Set ℕ}
    (hB : OrthogonalPetalBouquet A) :
    Summable (reciprocalSupportTerm A) := by
  classical
  have hray : Summable (fun i : ℕ => (1 : ℝ) / (hB.ray i : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun i => ?_)
      hB.summable_inv_petal
    have hcore : (1 : ℝ) ≤ (hB.core i : ℝ) := by
      exact_mod_cast hB.core_pos i
    have hpetal : (0 : ℝ) < (hB.petal i : ℝ) := by
      exact_mod_cast Nat.zero_lt_of_lt (hB.petal_one_lt i)
    have hden : (hB.petal i : ℝ) ≤
        (hB.core i : ℝ) * (hB.petal i : ℝ) := by
      nlinarith
    simpa [ray, Nat.cast_mul] using
      one_div_le_one_div_of_le hpetal hden
  let e : ℕ ≃ Set.range hB.ray := Equiv.ofInjective hB.ray hB.ray_injective
  have hrangeSubtype :
      Summable (fun d : Set.range hB.ray => (1 : ℝ) / (d : ℕ)) := by
    have hcomp : Summable
        ((fun i : ℕ => (1 : ℝ) / (hB.ray i : ℝ)) ∘ e.symm) :=
      hray.comp_injective e.symm.injective
    refine hcomp.congr (fun d => ?_)
    change (1 : ℝ) / (hB.ray (e.symm d) : ℝ) = (1 : ℝ) / (d : ℕ)
    rw [Equiv.apply_ofInjective_symm hB.ray_injective]
  have hrange : Summable
      (Set.indicator (Set.range hB.ray)
        (fun d : ℕ => (1 : ℝ) / (d : ℝ))) := by
    exact summable_subtype_iff_indicator.mp hrangeSubtype
  have hexceptional : Summable
      (Set.indicator (↑hB.exceptional : Set ℕ)
        (fun d : ℕ => (1 : ℝ) / (d : ℝ))) := by
    refine summable_of_ne_finset_zero (s := hB.exceptional) (fun d hd => ?_)
    simp [Set.indicator, hd]
  refine Summable.of_nonneg_of_le
    (fun d => Set.indicator_nonneg (fun _ _ => by positivity) d)
    (fun d => ?_) (hexceptional.add hrange)
  have hexceptional_nonneg :
      0 ≤ Set.indicator (↑hB.exceptional : Set ℕ)
        (fun a : ℕ => (1 : ℝ) / (a : ℝ)) d :=
    Set.indicator_nonneg (fun _ _ => by positivity) d
  have hrange_nonneg :
      0 ≤ Set.indicator (Set.range hB.ray)
        (fun a : ℕ => (1 : ℝ) / (a : ℝ)) d :=
    Set.indicator_nonneg (fun _ _ => by positivity) d
  by_cases hdA : d ∈ A
  · have hdA' := hdA
    rw [hB.support_eq] at hdA'
    rcases hdA' with hdexceptional | hdray
    · rw [reciprocalSupportTerm, Set.indicator_of_mem hdA,
        Set.indicator_of_mem hdexceptional]
      exact le_add_of_nonneg_right hrange_nonneg
    · have hdray' : d ∈ Set.range hB.ray := by
        simpa [ray] using hdray
      rw [reciprocalSupportTerm, Set.indicator_of_mem hdA,
        Set.indicator_of_mem hdray']
      exact le_add_of_nonneg_left hexceptional_nonneg
  · have hlhs : reciprocalSupportTerm A d = 0 := by
      simp [reciprocalSupportTerm, hdA]
    rw [hlhs]
    exact add_nonneg hexceptional_nonneg hrange_nonneg

end OrthogonalPetalBouquet

/-- Every finite-core orthogonal-petal bouquet has irrational value at every
integer base at least two. No forced-slot selection is assumed. -/
theorem irrational_erdosSupportSeries_of_orthogonalPetalBouquet_allBase
    (b : ℕ) (hb : 2 ≤ b) {A : Set ℕ} (hB : OrthogonalPetalBouquet A) :
    Irrational (erdosSupportSeries b A) := by
  exact irrational_erdosSupportSeries_of_summable_reciprocal b A hb hB.infinite
    hB.summable_reciprocalSupportTerm

#print axioms OrthogonalPetalBouquet.summable_reciprocalSupportTerm
#print axioms irrational_erdosSupportSeries_of_orthogonalPetalBouquet_allBase

end Erdos249257.SupportSunflowerDichotomy
