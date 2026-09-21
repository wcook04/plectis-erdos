import ErdosProblems.Erdos257.PaperCompleteR8.WeightedInfiniteMean
import ErdosProblems.Erdos257.PaperCompleteR8.MixedGaugeConsumer

/-!
# End-to-end weighted and mixed support candidates

This module proves the previously isolated weighted finite-mean
producer from the actual FinitePrimeWeighted data. It does not assume that
producer. The concluding declarations assert precisely the two Prop-valued
paper goals; the separate strengthened positive-cover goal is proved in
PositiveCoverReturn. No parent statement is asserted.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- A finite prefix vanishes at every sample of a common divisible modulus. -/
theorem dyadicMean_remove_annihilated_prefix (b : ℕ) (hb : 2≤b)
    (E : Set ℕ) (F : Finset ℕ) (hFE : (F:Set ℕ) ⊆ E)
    (Q R M : ℕ) (hdiv : ∀ a∈F,a∣Q) :
    dyadicMean Q R M (displacement b E) =
      dyadicMean Q R M (displacement b (E \ (F:Set ℕ))) := by
  unfold dyadicMean
  apply congrArg (fun x:ℝ => x/(M:ℝ))
  apply Finset.sum_congr rfl
  intro j hj
  unfold progressionMean
  apply congrArg (fun x:ℝ => x/((2^j:ℕ):ℝ))
  apply Finset.sum_congr rfl
  intro m hm
  have hQN : Q∣(m+1)*Q := ⟨m+1,by ring⟩
  have hzero := displacement_finset_eq_zero b F ((m+1)*Q) hb
    (fun a ha => (hdiv a ha).trans hQN)
  rw [displacement_partition b E (F:Set ℕ) ((m+1)*Q) hb hFE,hzero,zero_add]

/-- The complete weighted producer, with prefix divisibility and one actual
finite dyadic observation window. -/
theorem weightedDyadicMeanTarget : WeightedDyadicMeanTarget := by
  classical
  intro b E hb hE0 hE ε hε L₀ hL₀
  obtain ⟨P,hPn,hP,hs⟩ := hE
  obtain ⟨F,hFE,hTail,hSmall⟩ := exists_finite_weighted_tail b hb P E hs
    (div_pos hε (by norm_num : (0:ℝ)<4))
  have hFpos : ∀ a∈F,0<a := by
    intro a ha
    exact Nat.pos_of_ne_zero (fun hz => hE0 (hz ▸ hFE ha))
  let L := L₀ * F.prod id
  have hL : 0<L := Nat.mul_pos hL₀ (Finset.prod_pos hFpos)
  have hL₀L : L₀∣L := dvd_mul_right _ _
  have hFL : ∀ a∈F,a∣L := fun a ha =>
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id ha) L₀
  let c := P.prod id
  have hc : 2≤c := primeProduct_ge_two P hPn hP
  obtain ⟨H,hH,Hsmall⟩ := exists_large_half_pow_lt (max 4 (L+c+2))
    (div_pos hε (by norm_num : (0:ℝ)<64))
  have hH4 : 4≤H := (le_max_left _ _).trans hH
  have hHC : L+c+2≤H := (le_max_right _ _).trans hH
  let Q := primeSamplingModulus L P H
  let G : ℕ := 2^H
  let M := 4*Q
  let D := E \ (F:Set ℕ)
  have hQ : 0<Q := primeSamplingModulus_pos hL P hP H
  have hG : 0<G := Nat.pow_pos (by decide)
  have hM : 0<M := Nat.mul_pos (by decide) hQ
  have hLQ : L∣Q := left_dvd_primeSamplingModulus L P H
  have hFQ : ∀ a∈F,a∣Q := fun a ha => (hFL a ha).trans hLQ
  have hD0 : 0∉D := fun hd => hE0 hd.1
  have hprof : GcdProfile Q G (primeSetPart P) := primeSamplingModulus_profile hL P hP H
  let W := ∑' a,Set.indicator D (primeWeightedTerm b P) a
  have hW0 : 0≤W := tsum_nonneg (fun a => Set.indicator_nonneg
    (fun a _ => primeWeightedTerm_nonneg b hb P a) a)
  have hWsmall : W<ε/4 := hSmall
  have hMean := dyadicMean_support_le_profile b hb D hD0 Q G M hQ hG hM
    (primeSetPart P) hprof hTail
  have hEbound : weightedScheduleError (b:ℝ) Q G M ≤ 26*(1/2:ℝ)^H :=
    weightedScheduleError_le (b:ℝ) (by exact_mod_cast hb) L c H hL hc hH4 hHC
  have hQreal : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  have hfactor : 1+2*(Q:ℝ)/(M:ℝ)≤2 := by
    dsimp [M]
    push_cast
    have heq : 1+2*(Q:ℝ)/(4*(Q:ℝ))=(3/2:ℝ) := by
      field_simp [hQreal]
      <;> ring
    rw [heq]
    norm_num
  have hscale := mul_le_mul_of_nonneg_right hfactor hW0
  have hsmall : dyadicMean Q M M (displacement b D)<ε := by
    change dyadicMean Q M M (displacement b D) ≤
      (1+2*(Q:ℝ)/M)*W + weightedScheduleError (b:ℝ) Q G M at hMean
    nlinarith only [hMean,hscale,hEbound,hWsmall,Hsmall,hε]
  refine ⟨Q,M,M,hQ,hL₀L.trans hLQ,le_rfl,?_⟩
  rw [dyadicMean_remove_annihilated_prefix b hb E F hFE Q M M hFQ]
  exact hsmall

/-- The "more precisely" clause of the weighted theorem: small positive
returns occur beyond every prescribed index. The sampling modulus is chosen
as a multiple of that index before extracting a point from the finite mean. -/
theorem weighted_displacement_cofinal_close_return
    (b : ℕ) (E : Set ℕ) (hb : 2 ≤ b) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted b E) (hInf : E.Infinite)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < displacement b E m ∧ displacement b E m < ε := by
  obtain ⟨Q, R, M, hQ, hdiv, hM, hsmall⟩ :=
    weightedDyadicMeanTarget b E hb hE0 hE ε hε (max 1 N) (by omega)
  obtain ⟨j, m, _, _, _, hsample⟩ :=
    exists_sample_lt_of_dyadicMean_lt Q R M (by omega) (displacement b E) ε hsmall
  have hNQ : N ≤ Q := (le_max_right 1 N).trans (Nat.le_of_dvd hQ hdiv)
  have hQm : Q ≤ (m + 1) * Q := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right Q (show 1 ≤ m + 1 by omega)
  refine ⟨(m + 1) * Q, hNQ.trans hQm, ?_, hsample⟩
  exact displacement_pos b E _ hb hInf (Nat.mul_pos (Nat.succ_pos m) hQ)

#print axioms weighted_displacement_cofinal_close_return

/-- The irrationality clauses of long-record `thm:257-weighted`: fixed-base irrationality and the
binary-cost all-base hereditary clause. No new analytic target is assumed. -/
theorem divisibilityWeightedClaim : DivisibilityWeightedClaim :=
  divisibilityWeightedClaim_of_mean_target weightedDyadicMeanTarget

/-- FULL short-note `res:mixed-supports`. Uses the nonlinear cover test on
the weighted schedule; does not assume a first-moment bound for the cover
component and does not add individual irrationality premises. -/
theorem mixedSupportClaim : MixedSupportClaim :=
  mixedSupportClaim_of_weighted_mean_target weightedDyadicMeanTarget

end ErdosProblems.Erdos257.PaperCompleteR8
end
