import ErdosProblems.Erdos257.PaperCompleteR8.WeightedPrimeProfile

/-!
# Finite weighted estimates with an explicit observation window

The high-GCD remainder is charged against a dyadic harmonic
bound, not against the cardinality of an unbounded conductor support.
The future-conductor contribution is bounded geometrically before any
infinite interchange. All constants here are deliberately non-sharp.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- A real-base kernel before its first wrap has a uniform binary envelope. -/
theorem kernelWeight_nowrap_binary_envelope (B : ℝ) (hB2 : 2 ≤ B)
    (d N : ℕ) (hNd : N < d) :
    kernelWeight B d N ≤ 2 * (2 : ℝ) ^ N * (1/2 : ℝ) ^ d := by
  have hB : 1 < B := lt_of_lt_of_le (by norm_num) hB2
  have hB0 : 0 < B := lt_trans zero_lt_one hB
  have hd : 0 < d := Nat.zero_lt_of_lt hNd
  have hden : 0 < B ^ d - 1 := kernel_den_pos hB hd
  have hk : 0 < d - N := Nat.sub_pos_of_lt hNd
  have hBk : 0 < B ^ (d - N) := pow_pos hB0 _
  have hBd : (2 : ℝ) ≤ B ^ d :=
    hB2.trans (le_self_pow₀ hB.le hd.ne')
  have hfact : B ^ N * B ^ (d - N) = B ^ d := by
    rw [← pow_add, Nat.add_sub_of_le hNd.le]
  have hfirst : B ^ N / (B ^ d - 1) ≤ 2 / B ^ (d - N) := by
    apply (div_le_div_iff₀ hden hBk).mpr
    rw [hfact]
    linarith only [hBd]
  have hpow : (2 : ℝ) ^ (d - N) ≤ B ^ (d - N) :=
    pow_le_pow_left₀ (by norm_num) hB2 _
  have hsecond : 2 / B ^ (d - N) ≤ 2 / (2 : ℝ) ^ (d - N) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos (by norm_num) _) hpow
  have htwo : (2 : ℝ) ^ N * 2 ^ (d - N) = 2 ^ d := by
    rw [← pow_add, Nat.add_sub_of_le hNd.le]
  have hend : 2 / (2 : ℝ) ^ (d - N) =
      2 * (2 : ℝ) ^ N * (1/2 : ℝ) ^ d := by
    rw [one_div, inv_pow]
    calc
      2 / (2 : ℝ) ^ (d-N) = 2 * (2 : ℝ)^N / ((2 : ℝ)^N * 2^(d-N)) := by
        field_simp
      _ = 2 * (2 : ℝ)^N * ((2 : ℝ)^d)⁻¹ := by rw [htwo]; ring
  rw [kernelWeight, Nat.mod_eq_of_lt hNd]
  exact hfirst.trans (hsecond.trans_eq hend)

/-- The last term controls a finite geometric progression whose ratio is >=2. -/
theorem positive_geometric_sum_le_twice_last (C : ℝ) (hC : 2 ≤ C) (T : ℕ) :
    (∑ m ∈ Finset.range T, C ^ (m + 1)) ≤ 2 * C ^ T := by
  have hC1 : 1 < C := lt_of_lt_of_le (by norm_num) hC
  have hgap : 0 < C - 1 := sub_pos.mpr hC1
  have hCT : 0 ≤ C ^ T := pow_nonneg (le_trans (by norm_num) hC) _
  have hsum : (∑ m ∈ Finset.range T, C ^ (m + 1)) = C * ((C ^ T - 1)/(C - 1)) := by
    simp_rw [pow_succ']
    rw [← Finset.mul_sum, geom_sum_eq hC1.ne']
  rw [hsum, ← mul_div_assoc]
  apply (div_le_iff₀ hgap).mpr
  have hn := mul_nonneg hCT (sub_nonneg.mpr hC)
  nlinarith only [hn, hC]

/-- A finite family of conductors beyond the entire observation prefix costs
at most 4/T, independently of its cardinality. -/
theorem progressionMean_far_conductors_le (B : ℝ) (hB2 : 2 ≤ B)
    (F : Finset ℕ) (Q T : ℕ) (hQ : 0 < Q) (hT : 0 < T)
    (hfar : ∀ a ∈ F, Q * T < a) :
    progressionMean Q T (fun N => ∑ a ∈ F, kernelWeight B a N) ≤ 4 / (T : ℝ) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hgeo := sum_half_pow_le_twice_min F (Q * T + 1)
    (fun a ha => Nat.succ_le_of_lt (hfar a ha))
  have hrow : ∀ m ∈ Finset.range T,
      (∑ a ∈ F, kernelWeight B a ((m + 1)*Q)) ≤
        2 * (2 : ℝ) ^ ((m + 1)*Q) / 2 ^ (Q*T) := by
    intro m hm
    have hmq : (m + 1)*Q ≤ Q*T := by
      have hh := Nat.mul_le_mul_right Q (Nat.succ_le_of_lt (Finset.mem_range.mp hm))
      simpa only [Nat.mul_comm] using hh
    calc
      _ ≤ ∑ a ∈ F, 2 * (2 : ℝ) ^ ((m + 1)*Q) * (1/2 : ℝ) ^ a :=
        Finset.sum_le_sum (fun a ha => kernelWeight_nowrap_binary_envelope B hB2 a _
          (lt_of_le_of_lt hmq (hfar a ha)))
      _ = 2 * (2 : ℝ) ^ ((m + 1)*Q) * ∑ a ∈ F, (1/2 : ℝ) ^ a := by
        rw [Finset.mul_sum]
      _ ≤ 2 * (2 : ℝ) ^ ((m + 1)*Q) * (2 * (1/2 : ℝ) ^ (Q*T+1)) :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = _ := by
        rw [pow_succ, one_div, inv_pow]
        ring
  have hC : (2 : ℝ) ≤ (2 : ℝ) ^ Q := le_self_pow₀ (by norm_num) hQ.ne'
  have hpowSum : (∑ m ∈ Finset.range T, (2 : ℝ) ^ ((m + 1)*Q)) ≤
      2 * (2 : ℝ) ^ (Q*T) := by
    have hh := positive_geometric_sum_le_twice_last ((2 : ℝ)^Q) hC T
    simpa only [← pow_mul, Nat.mul_comm] using hh
  have hsum : (∑ m ∈ Finset.range T, ∑ a ∈ F, kernelWeight B a ((m + 1)*Q)) ≤ 4 := by
    calc
      _ ≤ ∑ m ∈ Finset.range T, 2 * (2 : ℝ) ^ ((m + 1)*Q) / 2 ^ (Q*T) :=
        Finset.sum_le_sum hrow
      _ = 2 * (∑ m ∈ Finset.range T, (2 : ℝ) ^ ((m + 1)*Q)) / 2 ^ (Q*T) := by
        rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ 2 * (2 * (2 : ℝ) ^ (Q*T)) / 2 ^ (Q*T) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowSum (by norm_num)) (by positivity)
      _ = 4 := by field_simp <;> norm_num
  exact div_le_div_of_nonneg_right hsum hT0.le

/-- An elementary harmonic mass, chosen to avoid logarithm APIs. -/
def harmonicMass (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, 1 / ((i + 1 : ℕ) : ℝ)

theorem harmonicMass_le_self (n : ℕ) : harmonicMass n ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hpos : (0 : ℝ) < ((i+1:ℕ):ℝ) := by positivity
      apply (div_le_one hpos).mpr
      exact_mod_cast (Nat.succ_pos i)
    _ = _ := by simp

theorem harmonicMass_double_le (n : ℕ) : harmonicMass (2*n) ≤ harmonicMass n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [harmonicMass]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (∑ i ∈ Finset.range n, 1 / ((n+i+1:ℕ):ℝ)) ≤ 1 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, 1/(n:ℝ) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact one_div_le_one_div_of_le hnR (by exact_mod_cast (by omega : n ≤ n+i+1))
      _ = 1 := by simp [hnR.ne']
  have heq : harmonicMass (2*n) = harmonicMass n +
      ∑ i ∈ Finset.range n, 1 / ((n+i+1:ℕ):ℝ) := by
    rw [show 2*n=n+n by omega, harmonicMass, Finset.sum_range_add]
    rfl
  rw [heq]
  exact add_le_add (le_refl _) ht

theorem harmonicMass_dyadic_le (Q j : ℕ) : harmonicMass (Q*2^j) ≤ (Q:ℝ) + j := by
  induction j with
  | zero => simpa using harmonicMass_le_self Q
  | succ j ih =>
    have heq : Q*2^(j+1)=2*(Q*2^j) := by rw [pow_succ]; ring
    rw [heq]
    have hh := harmonicMass_double_le (Q*2^j)
    push_cast
    linarith only [hh, ih]

/-- Bound a finite reciprocal sum only by the actual observation cutoff. -/
theorem sum_reciprocal_le_harmonicMass (F : Finset ℕ) (T : ℕ)
    (hF : ∀ a ∈ F, a ≤ T) :
    (∑ a ∈ F, 1/(a:ℝ)) ≤ harmonicMass T := by
  have hsub : F ⊆ Finset.range (T+1) := fun a ha => Finset.mem_range.mpr (by
    have := hF a ha; omega)
  have hs : (∑ a ∈ F, 1/(a:ℝ)) ≤ ∑ a ∈ Finset.range (T+1), 1/(a:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun a _ _ => one_div_nonneg.mpr (Nat.cast_nonneg a))
  have heq : (∑ a ∈ Finset.range (T+1), 1/(a:ℝ)) = harmonicMass T := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero]
    rfl
  exact hs.trans_eq heq

/-- The weighted reciprocal conductor mass attached to any positive profile. -/
def profileWeight (B : ℝ) (h : ℕ → ℕ) (a : ℕ) : ℝ :=
  (h a : ℝ) / ((a : ℝ) * (B ^ h a - 1))

theorem profileWeight_nonneg (B : ℝ) (hB : 1 < B) (h : ℕ → ℕ)
    (a : ℕ) (ha : 0 < h a) : 0 ≤ profileWeight B h a :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (kernel_den_pos hB ha).le)

/-- One conductor, with the good and high-GCD terms both exposed. -/
theorem progressionMean_kernel_le_profile (B : ℝ) (hB : 1 < B)
    (Q G T : ℕ) (hQ : 0 < Q) (hG : 0 < G) (hT : 0 < T)
    (h : ℕ → ℕ) (hprof : GcdProfile Q G h) (a : ℕ) (ha : 0 < a) :
    progressionMean Q T (kernelWeight B a) ≤
      profileWeight B h a + 1/((T:ℝ)*(B^h a-1)) +
      (G:ℝ)/((a:ℝ)*(B^G-1)) + 1/((T:ℝ)*(B^G-1)) := by
  let g := Nat.gcd Q a
  have hg : 0 < g := Nat.gcd_pos_of_pos_left a hQ
  have hbase := progressionMean_kernel_le_gcdMean_add_error B hB Q a T hQ ha hT
  have hGD : 0 < B^G-1 := kernel_den_pos hB hG
  obtain ⟨hh, hgood | hbad⟩ := hprof a ha
  · have hle : h a ≤ g := Nat.le_of_dvd hg hgood
    have hr := geom_ratio_antitone B hB (h a) g hh hle
    have hmain : (g:ℝ)/((a:ℝ)*(B^g-1)) ≤ profileWeight B h a := by
      calc
        (g:ℝ)/((a:ℝ)*(B^g-1)) = ((g:ℝ)/(B^g-1))/(a:ℝ) := by simp only [div_div, mul_comm]
        _ ≤ ((h a:ℝ)/(B^h a-1))/(a:ℝ) :=
          div_le_div_of_nonneg_right hr (Nat.cast_nonneg a)
        _ = profileWeight B h a := by simp only [profileWeight, div_div, mul_comm]
    have hden : B^h a-1 ≤ B^g-1 := sub_le_sub_right (pow_le_pow_right₀ hB.le hle) 1
    have herr : 1/((T:ℝ)*(B^g-1)) ≤ 1/((T:ℝ)*(B^h a-1)) := by
      apply one_div_le_one_div_of_le
      · exact mul_pos (by exact_mod_cast hT) (kernel_den_pos hB hh)
      · exact mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg T)
    have h0 : 0 ≤ (G:ℝ)/((a:ℝ)*(B^G-1)) :=
      div_nonneg (Nat.cast_nonneg G) (mul_nonneg (Nat.cast_nonneg a) hGD.le)
    have h1 : 0 ≤ 1/((T:ℝ)*(B^G-1)) :=
      one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg T) hGD.le)
    linarith only [hbase, hmain, herr, h0, h1]
  · have hr := geom_ratio_antitone B hB G g hG hbad
    have hmain : (g:ℝ)/((a:ℝ)*(B^g-1)) ≤ (G:ℝ)/((a:ℝ)*(B^G-1)) := by
      have hb := div_le_div_of_nonneg_right hr (Nat.cast_nonneg a)
      simpa only [div_div, mul_comm] using hb
    have hden : B^G-1 ≤ B^g-1 := sub_le_sub_right (pow_le_pow_right₀ hB.le hbad) 1
    have herr : 1/((T:ℝ)*(B^g-1)) ≤ 1/((T:ℝ)*(B^G-1)) := by
      apply one_div_le_one_div_of_le
      · exact mul_pos (by exact_mod_cast hT) (kernel_den_pos hB hG)
      · exact mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg T)
    have h0 : 0 ≤ profileWeight B h a := profileWeight_nonneg B hB h a hh
    have h1 : 0 ≤ 1/((T:ℝ)*(B^h a-1)) := by
      exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg T) (kernel_den_pos hB hh).le)
    linarith only [hbase, hmain, herr, h0, h1]

end ErdosProblems.Erdos257.PaperCompleteR8
end
