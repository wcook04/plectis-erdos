import ErdosProblems.Erdos257.PaperCompleteR8.WeightedFiniteMean

/-!
# Explicit closure of the weighted observation parameters

There is no asymptotic schedule premise. With Q=L*c^H,
G=2^H and M=4Q, the entire high-GCD/geometric error is bounded by
26*2^(-H), once H >= max 4 (L+c+2). Every inequality uses natural powers.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- The polynomial lower envelope of the binary exponential used below. -/
theorem nat_sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n^2 ≤ 2^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hthree : 3*(4+k) ≤ (4+k)*(4+k) :=
      Nat.mul_le_mul_right (4+k) (by omega : 3 ≤ 4+k)
    have hstep : (4+(k+1))^2 ≤ 2*(4+k)^2 := by nlinarith only [hthree]
    calc
      (4+(k+1))^2 ≤ 2*(4+k)^2 := hstep
      _ ≤ 2*2^(4+k) := Nat.mul_le_mul_left 2 (ih (by omega))
      _ = 2^(4+(k+1)) := by rw [← pow_succ']; congr 1 <;> omega

/-- An intentionally coarse exponential bound for the sampling modulus. -/
theorem samplingModulus_upper (L c H : ℕ) (hH : 1 ≤ H) :
    L*c^H ≤ 2^((L+c)*H) := by
  have hL : L ≤ 2^L := (show L < 2 ^ L from Nat.lt_two_pow_self).le
  have hc : c ≤ 2^c := (show c < 2 ^ c from Nat.lt_two_pow_self).le
  have hprod : L*c^H ≤ 2^L*(2^c)^H :=
    Nat.mul_le_mul hL (Nat.pow_le_pow_left hc H)
  have hidx : L+c*H ≤ (L+c)*H := by
    have hh := Nat.mul_le_mul_left L hH
    nlinarith only [hh]
  calc
    _ ≤ 2^L*(2^c)^H := hprod
    _ = 2^(L+c*H) := by rw [← pow_mul,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hidx

theorem samplingModulus_lower (L c H : ℕ) (hL : 0 < L) (hc : 2 ≤ c) :
    2^H ≤ L*c^H := by
  have hp := Nat.pow_le_pow_left hc H
  have hmul : c^H ≤ L*c^H := by
    have hh := Nat.mul_le_mul_right (c^H) hL
    simpa using hh
  exact hp.trans hmul

/-- The product of a nonempty finite prime set is at least two. -/
theorem primeProduct_ge_two (P : Finset ℕ) (hPn : P.Nonempty)
    (hP : ∀ p ∈ P, Nat.Prime p) : 2 ≤ P.prod id := by
  have hpos : 0 < P.prod id := Finset.prod_pos (fun p hp => (hP p hp).pos)
  obtain ⟨p,hp⟩ := hPn
  exact (hP p hp).two_le.trans (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem id hp))

/-- The finite error from the weighted mean estimate. -/
def weightedScheduleError (B : ℝ) (Q G M : ℕ) : ℝ :=
  ((G:ℝ)*((Q:ℝ)+2*(M:ℝ))+(Q:ℝ)+1)/(B^G-1) + 4*(1/2:ℝ)^M

/-- Quantitative parameter closure: no unquantified limiting onset is used. -/
theorem weightedScheduleError_le (B : ℝ) (hB2 : 2 ≤ B)
    (L c H : ℕ) (hL : 0 < L) (hc : 2 ≤ c)
    (hH4 : 4 ≤ H) (hHC : L+c+2 ≤ H) :
    weightedScheduleError B (L*c^H) (2^H) (4*(L*c^H)) ≤ 26*(1/2:ℝ)^H := by
  let Q : ℕ := L*c^H
  let G : ℕ := 2^H
  let C : ℕ := L+c
  have hQ : 0 < Q := Nat.mul_pos hL (Nat.pow_pos (lt_of_lt_of_le (by decide) hc))
  have hG : 0 < G := Nat.pow_pos (by decide)
  have hB : 1 < B := lt_of_lt_of_le (by norm_num) hB2
  have hden : 0 < B^G-1 := kernel_den_pos hB hG
  have hQbound : Q ≤ 2^(C*H) := samplingModulus_upper L c H (by omega)
  have hGQ : G ≤ Q := samplingModulus_lower L c H hL hc
  have hHG : H ≤ G := (show H < 2 ^ H from Nat.lt_two_pow_self).le
  have hidx : (C+2)*H ≤ G := by
    have hcH : C+2 ≤ H := hHC
    exact (Nat.mul_le_mul_right H hcH).trans (by simpa [pow_two] using nat_sq_le_two_pow hH4)
  have hQR : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hGR : (1:ℝ) ≤ G := by exact_mod_cast hG
  have hGQ1 : (1:ℝ) ≤ (G:ℝ)*(Q:ℝ) := one_le_mul_of_one_le_of_one_le hGR hQR
  have hQGQ : (Q:ℝ) ≤ (G:ℝ)*(Q:ℝ) :=
    le_mul_of_one_le_left (Nat.cast_nonneg Q) hGR
  have hnum : (G:ℝ)*((Q:ℝ)+2*((4*Q:ℕ):ℝ))+(Q:ℝ)+1 ≤
      11*(G:ℝ)*(Q:ℝ) := by push_cast; nlinarith only [hGQ1,hQGQ]
  have htwoG : (2:ℝ) ≤ (2:ℝ)^G := le_self_pow₀ (by norm_num) hG.ne'
  have hbase : (2:ℝ)^G ≤ B^G := pow_le_pow_left₀ (by norm_num) hB2 G
  have hdenLower : (2:ℝ)^G/2 ≤ B^G-1 := by linarith only [htwoG,hbase]
  have hhigh : ((G:ℝ)*((Q:ℝ)+2*((4*Q:ℕ):ℝ))+(Q:ℝ)+1)/(B^G-1) ≤
      22*((G:ℝ)*(Q:ℝ))/(2:ℝ)^G := by
    calc
      _ ≤ (11*(G:ℝ)*(Q:ℝ))/(B^G-1) := div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (11*(G:ℝ)*(Q:ℝ))/((2:ℝ)^G/2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdenLower
      _ = _ := by ring
  have hprod : (G:ℝ)*(Q:ℝ) ≤ (2:ℝ)^((C+1)*H) := by
    have hQr : (Q:ℝ) ≤ (2:ℝ)^(C*H) := by exact_mod_cast hQbound
    have hh := mul_le_mul_of_nonneg_left hQr (Nat.cast_nonneg G)
    have heq : (G:ℝ)*(2:ℝ)^(C*H) = (2:ℝ)^((C+1)*H) := by
      dsimp [G]
      rw [Nat.cast_pow,Nat.cast_ofNat,← pow_add]
      congr 1
      ring
    exact hh.trans_eq heq
  have hratio : (2:ℝ)^((C+1)*H)/(2:ℝ)^G ≤ (1/2:ℝ)^H := by
    rw [one_div,inv_pow,← one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul,← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    have heq : (C+1)*H+H=(C+2)*H := by ring
    rw [heq]
    exact hidx
  have hsmall : ((G:ℝ)*(Q:ℝ))/(2:ℝ)^G ≤ (1/2:ℝ)^H :=
    (div_le_div_of_nonneg_right hprod (by positivity)).trans hratio
  have hfar : (1/2:ℝ)^(4*Q) ≤ (1/2:ℝ)^H :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  change ((G:ℝ)*((Q:ℝ)+2*((4*Q:ℕ):ℝ))+(Q:ℝ)+1)/(B^G-1) +
    4*(1/2:ℝ)^(4*Q) ≤ _
  have heq : 22 * ((G : ℝ) * (Q : ℝ)) / (2 : ℝ)^G =
      22 * (((G : ℝ) * (Q : ℝ)) / (2 : ℝ)^G) := by ring
  rw [heq] at hhigh
  linarith only [hhigh, hsmall, hfar]

/-- Arbitrarily large H with a specified reciprocal binary-power budget. -/
theorem exists_large_half_pow_lt (H₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, H₀ ≤ H ∧ (1/2:ℝ)^H < ε := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (1/ε) (by norm_num : (1:ℝ)<2)
  have hn' : (1/2:ℝ)^n < ε := by
    rw [one_div,inv_pow,← one_div]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2^n)).mpr
    have hh := (div_lt_iff₀ hε).mp hn
    simpa only [mul_comm] using hh
  refine ⟨max H₀ n,le_max_left _ _,?_⟩
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)).trans_lt hn'

end ErdosProblems.Erdos257.PaperCompleteR8
end
