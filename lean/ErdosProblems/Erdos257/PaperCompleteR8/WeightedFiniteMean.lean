import ErdosProblems.Erdos257.PaperCompleteR8.WeightedFiniteEstimates

/-! Finite weighted mean assembly. No mean limit is assumed. -/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Linearity for a finite family of actual observables. -/
theorem progressionMean_finsetSum {ι : Type*} (S : Finset ι)
    (u : ι → ℕ → ℝ) (Q T : ℕ) :
    progressionMean Q T (fun N => ∑ i ∈ S, u i N) =
      ∑ i ∈ S, progressionMean Q T (u i) := by
  unfold progressionMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem dyadicMean_finsetSum {ι : Type*} (S : Finset ι)
    (u : ι → ℕ → ℝ) (Q R M : ℕ) :
    dyadicMean Q R M (fun N => ∑ i ∈ S, u i N) =
      ∑ i ∈ S, dyadicMean Q R M (u i) := by
  unfold dyadicMean
  simp only [progressionMean_finsetSum]
  rw [Finset.sum_comm, Finset.sum_div]

/-- The exact reciprocal column error at the j-th observation scale. -/
def profileErrorSum (B : ℝ) (h : ℕ → ℕ) (F : Finset ℕ) (Q j : ℕ) : ℝ :=
  (1/2 : ℝ)^j * ∑ a ∈ F.filter (fun a => a ≤ Q*2^j), 1/(B^h a-1)

/-- One complete observation scale. The finite cut-off appears only in the
error sum; its dyadic average will be charged to weighted reciprocal mass. -/
theorem progressionMean_frame_le_profile
    (B : ℝ) (hB2 : 2 ≤ B) (Q G j : ℕ) (hQ : 0 < Q) (hG : 0 < G)
    (h : ℕ → ℕ) (hprof : GcdProfile Q G h)
    (F : Finset ℕ) (hF : ∀ a ∈ F, 0 < a) :
    progressionMean Q (2^j) (fun N => ∑ a ∈ F, kernelWeight B a N) ≤
      (∑ a ∈ F, profileWeight B h a) + profileErrorSum B h F Q j +
      ((G:ℝ)*((Q:ℝ)+j)+(Q:ℝ)+1)/(B^G-1) + 4*(1/2 : ℝ)^j := by
  classical
  let T : ℕ := 2^j
  let S := F.filter (fun a => a ≤ Q*T)
  let U := F.filter (fun a => ¬ a ≤ Q*T)
  let D := B^G-1
  have hB : 1 < B := lt_of_lt_of_le (by norm_num) hB2
  have hT : 0 < T := Nat.pow_pos (by decide)
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hD : 0 < D := kernel_den_pos hB hG
  have hSa : ∀ a ∈ S, 0 < a := fun a ha => hF a (Finset.mem_filter.mp ha).1
  have hSQT : ∀ a ∈ S, a ≤ Q*T := fun a ha => (Finset.mem_filter.mp ha).2
  have hW : (∑ a ∈ S, profileWeight B h a) ≤ ∑ a ∈ F, profileWeight B h a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro a ha _
    exact profileWeight_nonneg B hB h a (hprof a (hF a ha)).1
  have hH : (∑ a ∈ S, 1/(a:ℝ)) ≤ (Q:ℝ)+j :=
    (sum_reciprocal_le_harmonicMass S (Q*T) hSQT).trans (harmonicMass_dyadic_le Q j)
  have hcardNat : S.card ≤ Q*T+1 := by
    calc
      S.card ≤ (Finset.range (Q*T+1)).card :=
        Finset.card_le_card (fun a ha => Finset.mem_range.mpr (by have := hSQT a ha; omega))
      _ = _ := Finset.card_range _
  have hcard : (S.card:ℝ) ≤ ((Q:ℝ)+1)*(T:ℝ) := by
    have hc : (S.card:ℝ) ≤ (Q:ℝ)*(T:ℝ)+1 := by exact_mod_cast hcardNat
    have hT1 : (1:ℝ) ≤ T := by exact_mod_cast hT
    nlinarith only [hc,hT1]
  have hhigh : (∑ a ∈ S, (G:ℝ)/((a:ℝ)*D)) ≤
      (G:ℝ)*((Q:ℝ)+j)/D := by
    calc
      _ = ((G:ℝ)/D) * ∑ a ∈ S, 1/(a:ℝ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha; ring
      _ ≤ ((G:ℝ)/D) * ((Q:ℝ)+j) :=
        mul_le_mul_of_nonneg_left hH (div_nonneg (Nat.cast_nonneg G) hD.le)
      _ = _ := by ring
  have hcount : (∑ _a ∈ S, 1/((T:ℝ)*D)) ≤ ((Q:ℝ)+1)/D := by
    rw [Finset.sum_const,nsmul_eq_mul]
    have hh := div_le_div_of_nonneg_right hcard (mul_nonneg hTR.le hD.le)
    have hleft : (S.card:ℝ) * (1/((T:ℝ)*D)) = (S.card:ℝ)/((T:ℝ)*D) := by ring
    have hright : (((Q:ℝ)+1)*(T:ℝ))/((T:ℝ)*D) = ((Q:ℝ)+1)/D := by
      field_simp [hTR.ne',hD.ne']
    rw [hleft]
    exact hh.trans_eq hright
  have herr : (∑ a ∈ S, 1/((T:ℝ)*(B^h a-1))) = profileErrorSum B h F Q j := by
    unfold profileErrorSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [T]
    simp only [Nat.cast_pow,Nat.cast_ofNat,one_div,mul_inv_rev,inv_pow]
    ring
  have hnear : (∑ a ∈ S, progressionMean Q T (kernelWeight B a)) ≤
      (∑ a ∈ F, profileWeight B h a) + profileErrorSum B h F Q j +
      ((G:ℝ)*((Q:ℝ)+j)+(Q:ℝ)+1)/D := by
    have hb := Finset.sum_le_sum (fun a ha =>
      progressionMean_kernel_le_profile B hB Q G T hQ hG hT h hprof a (hSa a ha))
    simp only [Finset.sum_add_distrib] at hb
    rw [herr] at hb
    change (∑ a ∈ S, progressionMean Q T (kernelWeight B a)) ≤ _ at hb
    have hexpand : ((G:ℝ)*((Q:ℝ)+j)+(Q:ℝ)+1)/D =
        (G:ℝ)*((Q:ℝ)+j)/D + ((Q:ℝ)+1)/D := by ring
    rw [hexpand]
    linarith only [hb,hW,hhigh,hcount]
  have hfar : (∑ a ∈ U, progressionMean Q T (kernelWeight B a)) ≤ 4*(1/2:ℝ)^j := by
    rw [← progressionMean_finsetSum]
    have hh := progressionMean_far_conductors_le B hB2 U Q T hQ hT
      (fun a ha => Nat.lt_of_not_ge (Finset.mem_filter.mp ha).2)
    simpa only [T,Nat.cast_pow,Nat.cast_ofNat,one_div,inv_pow,div_eq_mul_inv,one_mul] using hh
  have hsplit : (∑ a ∈ F, progressionMean Q T (kernelWeight B a)) =
      (∑ a ∈ S, progressionMean Q T (kernelWeight B a)) +
      ∑ a ∈ U, progressionMean Q T (kernelWeight B a) :=
    (Finset.sum_filter_add_sum_filter_not F (fun a => a ≤ Q*T)
      (fun a => progressionMean Q T (kernelWeight B a))).symm
  rw [progressionMean_finsetSum,hsplit]
  exact add_le_add hnear hfar

/-- Sum the incomplete-period error across the SAME finite dyadic scales. -/
theorem sum_profileErrorSum_le (B : ℝ) (hB : 1 < B)
    (h : ℕ → ℕ) (F J : Finset ℕ) (Q : ℕ)
    (hF : ∀ a ∈ F, 0 < a) (hh : ∀ a ∈ F, 0 < h a) :
    (∑ j ∈ J, profileErrorSum B h F Q j) ≤
      2*(Q:ℝ) * ∑ a ∈ F, profileWeight B h a := by
  have hnn : ∀ a ∈ F, 0 ≤ 1/(B^h a-1) :=
    fun a ha => one_div_nonneg.mpr (kernel_den_pos hB (hh a ha)).le
  have hobs := dyadic_observation_sum_le J F Q (fun a => 1/(B^h a-1)) hF hnn
  have hw : (∑ a ∈ F, (1/(B^h a-1))/(a:ℝ)) ≤
      ∑ a ∈ F, profileWeight B h a := by
    apply Finset.sum_le_sum
    intro a ha
    have hh1 : (1:ℝ) ≤ h a := by exact_mod_cast (hh a ha)
    have hd : 0 ≤ (a:ℝ)*(B^h a-1) :=
      mul_nonneg (Nat.cast_nonneg a) (kernel_den_pos hB (hh a ha)).le
    have hp := div_le_div_of_nonneg_right hh1 hd
    calc
      (1/(B^h a-1))/(a:ℝ) = 1/((a:ℝ)*(B^h a-1)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (h a:ℝ)/((a:ℝ)*(B^h a-1)) := hp
      _ = profileWeight B h a := rfl
  exact hobs.trans (mul_le_mul_of_nonneg_left hw (by positivity))

/-- Full finite weighted estimate. Its error is independent of the finite
support size. This is the uniform estimate needed before the infinite limit. -/
theorem dyadicMean_finite_frame_le_profile
    (B : ℝ) (hB2 : 2 ≤ B) (Q G M : ℕ)
    (hQ : 0 < Q) (hG : 0 < G) (hM : 0 < M)
    (h : ℕ → ℕ) (hprof : GcdProfile Q G h)
    (F : Finset ℕ) (hF : ∀ a ∈ F, 0 < a) :
    dyadicMean Q M M (fun N => ∑ a ∈ F, kernelWeight B a N) ≤
      (1+2*(Q:ℝ)/M) * (∑ a ∈ F, profileWeight B h a) +
      ((G:ℝ)*((Q:ℝ)+2*(M:ℝ))+(Q:ℝ)+1)/(B^G-1) + 4*(1/2:ℝ)^M := by
  let J := Finset.Ico M (M+M)
  let W := ∑ a ∈ F, profileWeight B h a
  let E := ((G:ℝ)*((Q:ℝ)+2*(M:ℝ))+(Q:ℝ)+1)/(B^G-1)
  have hB : 1 < B := lt_of_lt_of_le (by norm_num) hB2
  have hD : 0 < B^G-1 := kernel_den_pos hB hG
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hcard : J.card=M := by dsimp [J]; rw [Nat.card_Ico]; omega
  have hrow : ∀ j ∈ J,
      progressionMean Q (2^j) (fun N => ∑ a ∈ F, kernelWeight B a N) ≤
        W + profileErrorSum B h F Q j + E + 4*(1/2:ℝ)^M := by
    intro j hj
    have hlow : M ≤ j := (Finset.mem_Ico.mp hj).1
    have hj2 : (j:ℝ) ≤ 2*(M:ℝ) := by
      exact_mod_cast (Nat.le_of_lt (by have := (Finset.mem_Ico.mp hj).2; omega : j < 2*M))
    have hbound := progressionMean_frame_le_profile B hB2 Q G j hQ hG h hprof F hF
    have hh : ((G:ℝ)*((Q:ℝ)+j)+(Q:ℝ)+1)/(B^G-1) ≤ E := by
      apply div_le_div_of_nonneg_right _ hD.le
      have hm := mul_le_mul_of_nonneg_left (add_le_add_left hj2 (Q:ℝ)) (Nat.cast_nonneg G)
      linarith only [hm]
    have hgeo : (1/2:ℝ)^j ≤ (1/2:ℝ)^M :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hlow
    dsimp [W]
    linarith only [hbound,hh,hgeo]
  have hobs := sum_profileErrorSum_le B hB h F J Q hF
    (fun a ha => (hprof a (hF a ha)).1)
  have hsum := Finset.sum_le_sum hrow
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hcard] at hsum
  have hsum' : (∑ j ∈ J, progressionMean Q (2^j)
      (fun N => ∑ a ∈ F, kernelWeight B a N)) ≤
      (M:ℝ)*W + 2*(Q:ℝ)*W + (M:ℝ)*E + (M:ℝ)*(4*(1/2:ℝ)^M) := by
    linarith only [hsum,hobs]
  have hdiv := div_le_div_of_nonneg_right hsum' hMR.le
  have heq : ((M:ℝ)*W + 2*(Q:ℝ)*W + (M:ℝ)*E + (M:ℝ)*(4*(1/2:ℝ)^M))/(M:ℝ) =
      (1+2*(Q:ℝ)/M)*W + E + 4*(1/2:ℝ)^M := by
    field_simp [hMR.ne']
    <;> ring
  exact hdiv.trans_eq heq

end ErdosProblems.Erdos257.PaperCompleteR8
end
