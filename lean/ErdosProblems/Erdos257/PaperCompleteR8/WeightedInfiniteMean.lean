import ErdosProblems.Erdos257.PaperCompleteR8.WeightedSchedule

/-!
# Pass the uniform finite bound to the actual infinite support

Summability of every series exchanged here precedes the exchange.
No ordinary reciprocal-summability assumption on the support is added.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset Filter
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Summability through the two FINITE averaging operations. -/
theorem summable_dyadicMean {ι : Type*} (u : ι → ℕ → ℝ)
    (hu : ∀ N, Summable (fun i => u i N)) (Q R M : ℕ) :
    Summable (fun i => dyadicMean Q R M (u i)) := by
  have hs : Summable (fun i => ∑ j ∈ Finset.Ico R (R+M),
      progressionMean Q (2^j) (u i)) :=
    summable_sum (fun j _ => summable_progressionMean u hu Q (2^j))
  exact hs.div_const (M:ℝ)

theorem kernelWeight_nat_eq_shiftedRadixAtom (b N d : ℕ) :
    kernelWeight (b:ℝ) d N = shiftedRadixAtom b N d := by
  by_cases hd : d=0
  · subst d; simp [kernelWeight,shiftedRadixAtom]
  · simp only [kernelWeight,shiftedRadixAtom,hd,if_false]

/-- A finite support displacement is bounded by its actual real-base potential. -/
theorem finite_displacement_le_kernelSum (b : ℕ) (hb : 2 ≤ b)
    (F : Finset ℕ) (N : ℕ) :
    displacement b (F:Set ℕ) N ≤ ∑ a ∈ F, kernelWeight (b:ℝ) a N := by
  classical
  rw [displacement_eq_tsum b (F:Set ℕ) N hb]
  rw [tsum_eq_sum (s:=F)]
  · apply Finset.sum_le_sum
    intro a ha
    rw [Set.indicator_of_mem (show a∈(F:Set ℕ) from ha),displacementAtom,
      ← kernelWeight_nat_eq_shiftedRadixAtom,← kernelWeight_nat_eq_shiftedRadixAtom]
    exact sub_le_self _ (kernelWeight_nonneg (by exact_mod_cast (by omega : 1<b)) a 0)
  · intro a ha
    simp [ha]

/-- Uniform infinite weighted estimate, derived from all finite subfamilies. -/
theorem dyadicMean_support_le_profile
    (b : ℕ) (hb : 2 ≤ b) (E : Set ℕ) (hE0 : 0 ∉ E)
    (Q G M : ℕ) (hQ : 0 < Q) (hG : 0 < G) (hM : 0 < M)
    (h : ℕ → ℕ) (hprof : GcdProfile Q G h)
    (hs : Summable (Set.indicator E (profileWeight (b:ℝ) h))) :
    dyadicMean Q M M (displacement b E) ≤
      (1+2*(Q:ℝ)/M) * (∑' a, Set.indicator E (profileWeight (b:ℝ) h) a) +
      weightedScheduleError (b:ℝ) Q G M := by
  classical
  let u : ℕ → ℕ → ℝ := fun a N => Set.indicator E (displacementAtom b N) a
  let w := Set.indicator E (profileWeight (b:ℝ) h)
  let K : ℝ := 1+2*(Q:ℝ)/M
  let e := weightedScheduleError (b:ℝ) Q G M
  have hu : ∀ N, Summable (fun a => u a N) := fun N =>
    summable_displacementAtom b E N hb
  have hmeans := summable_dyadicMean u hu Q M M
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hb1 : (1:ℝ) < b := lt_of_lt_of_le (by norm_num) hbR
  have hw0 : ∀ a, 0 ≤ w a := by
    intro a
    by_cases ha : a∈E
    · have hap : 0<a := Nat.pos_of_ne_zero (fun hz => hE0 (hz ▸ ha))
      simpa [w,ha] using profileWeight_nonneg (b:ℝ) hb1 h a (hprof a hap).1
    · simp [w,ha]
  have hfinite : ∀ S : Finset ℕ,
      (∑ a ∈ S, dyadicMean Q M M (u a)) ≤ K*(∑' a,w a)+e := by
    intro S
    let F := S.filter (fun a => a∈E)
    have hFpos : ∀ a∈F,0<a := by
      intro a ha
      have hEa := (Finset.mem_filter.mp ha).2
      exact Nat.pos_of_ne_zero (fun hz => hE0 (hz ▸ hEa))
    have hval : ∀ N, (∑ a ∈ S,u a N)=displacement b (F:Set ℕ) N := by
      intro N
      rw [displacement_eq_tsum b (F:Set ℕ) N hb]
      rw [tsum_eq_sum (s:=F)]
      · have hh : (∑ a ∈ F,Set.indicator (F:Set ℕ) (displacementAtom b N) a) =
            ∑ a ∈ F,displacementAtom b N a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Set.indicator_of_mem (show a∈(F:Set ℕ) from ha) _
        rw [hh]
        dsimp [F,u]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hEa : a∈E <;> simp [hEa]
      · intro a ha
        simp [ha]
    have hmeanEq : (∑ a ∈ S,dyadicMean Q M M (u a)) =
        dyadicMean Q M M (displacement b (F:Set ℕ)) := by
      rw [← dyadicMean_finsetSum]
      exact congrArg (dyadicMean Q M M) (funext hval)
    have hfiniteBound := dyadicMean_finite_frame_le_profile (b:ℝ) hbR Q G M hQ hG hM h hprof F hFpos
    have hdisp := dyadicMean_mono Q M M (displacement b (F:Set ℕ))
      (fun N => ∑ a∈F,kernelWeight (b:ℝ) a N)
      (finite_displacement_le_kernelSum b hb F)
    have hWF : (∑ a∈F,profileWeight (b:ℝ) h a) ≤ ∑' a,w a := by
      have heq : (∑ a∈F,profileWeight (b:ℝ) h a) = ∑ a∈F,w a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (Set.indicator_of_mem (Finset.mem_filter.mp ha).2 _).symm
      rw [heq]
      exact hs.sum_le_tsum F (fun a _ => hw0 a)
    have hscale := mul_le_mul_of_nonneg_left hWF (by positivity : 0≤K)
    rw [hmeanEq]
    -- Expose the error package: the finite theorem associates its two errors differently.
    dsimp [K, e, weightedScheduleError] at hscale ⊢
    linarith only [hdisp, hfiniteBound, hscale]
  have ht := hmeans.tsum_le_of_sum_le hfinite
  rw [tsum_dyadicMean u hu Q M M] at ht
  have hfun : (fun N => ∑' a,u a N)=displacement b E := by
    funext N
    exact (displacement_eq_tsum b E N hb).symm
  rw [hfun] at ht
  exact ht

/-- The tail of a nonnegative summable series is small after deleting a finite
initial index set. Both the ordinary and indicator tails are identified. -/
theorem tsum_index_tail_eq (g : ℕ → ℝ) (hg : Summable g)
    (hg0 : ∀ a,0≤g a) (n : ℕ) :
    (∑' a, if n≤a then g a else 0) = ∑' k,g (k+n) := by
  classical
  let p : ℕ→ℝ := fun a => if a<n then g a else 0
  let t : ℕ→ℝ := fun a => if n≤a then g a else 0
  have hp : Summable p := by
    apply Summable.of_nonneg_of_le _ _ hg
    · intro a; dsimp [p]; split_ifs <;> simp [hg0]
    · intro a; dsimp [p]; split_ifs <;> simp [hg0]
  have ht : Summable t := by
    apply Summable.of_nonneg_of_le _ _ hg
    · intro a; dsimp [t]; split_ifs <;> simp [hg0]
    · intro a; dsimp [t]; split_ifs <;> simp [hg0]
  have hpoint : (fun a => p a+t a)=g := by
    funext a
    dsimp [p,t]
    by_cases h : a<n
    · rw [if_pos h,if_neg (by omega),add_zero]
    · rw [if_neg h,if_pos (by omega),zero_add]
  have hsum := hp.tsum_add ht
  rw [hpoint] at hsum
  have hpval : (∑' a,p a)=∑ a∈Finset.range n,g a := by
    rw [tsum_eq_sum (s:=Finset.range n)]
    · apply Finset.sum_congr rfl
      intro a ha
      exact if_pos (Finset.mem_range.mp ha)
    · intro a ha
      exact if_neg (fun h => ha (Finset.mem_range.mpr h))
  rw [hpval] at hsum
  have hsplit := hg.sum_add_tsum_nat_add n
  change (∑' a,t a)=_
  linarith only [hsum,hsplit]

/-- A genuine finite support prefix leaves arbitrarily small weighted mass. -/
theorem exists_finite_weighted_tail (b : ℕ) (hb : 2 ≤ b)
    (P : Finset ℕ) (E : Set ℕ)
    (hs : Summable (Set.indicator E (primeWeightedTerm b P)))
    {ε : ℝ} (hε : 0<ε) :
    ∃ F : Finset ℕ, (F:Set ℕ) ⊆ E ∧
      Summable (Set.indicator (E \ (F:Set ℕ)) (primeWeightedTerm b P)) ∧
      (∑' a,Set.indicator (E \ (F:Set ℕ)) (primeWeightedTerm b P) a)<ε := by
  classical
  let g := Set.indicator E (primeWeightedTerm b P)
  have hg0 : ∀ a,0≤g a := fun a => Set.indicator_nonneg
    (fun a _ => primeWeightedTerm_nonneg b hb P a) a
  have hlim := tendsto_sum_nat_add g
  have hevent : ∀ᶠ n in atTop,(∑' k,g (k+n))<ε := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨n,hn⟩ := hevent.exists
  let F := (Finset.range n).filter (fun a => a∈E)
  have hFE : (F:Set ℕ) ⊆ E := fun a ha => (Finset.mem_filter.mp ha).2
  have hfun : Set.indicator (E \ (F:Set ℕ)) (primeWeightedTerm b P) =
      fun a => if n≤a then g a else 0 := by
    funext a
    by_cases hEa : a∈E
    · by_cases han : a<n
      · have haF : a∈F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr han,hEa⟩
        simp [haF,han,show ¬n≤a by omega,g]
      · have haF : a∉F := fun ha => han (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        simp [haF,hEa,show n≤a by omega,g]
    · have haF : a∉F := fun ha => hEa (hFE ha)
      simp [hEa,haF,g]
  have htail : Summable (fun a => if n≤a then g a else 0) := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro a
      split_ifs
      · exact hg0 a
      · exact le_rfl
    · intro a
      split_ifs
      · exact le_rfl
      · exact hg0 a
  refine ⟨F,hFE,?_,?_⟩
  · rw [hfun]; exact htail
  · rw [hfun,tsum_index_tail_eq g hs hg0 n]
    exact hn

end ErdosProblems.Erdos257.PaperCompleteR8
end
