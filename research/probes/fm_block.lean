-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Mathlib

/-! Probe: block sampling of an exponential sum over a subset of an interval, and the
pure real inequalities used around it. Mathlib only. -/

namespace FiberMeanProbe

theorem norm_exp_sub_exp_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  have h1 : Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)
      = Complex.exp ((y : ℂ) * Complex.I) *
          (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    have h2 : (y : ℂ) * Complex.I + Complex.I * ((x - y : ℝ) : ℂ) = (x : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h2]
  rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h3 := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)
  rwa [Real.norm_eq_abs] at h3

theorem step_bound (SP SB G c : ℂ) (nP nB ν ε T K : ℝ)
    (hc : ‖c‖ = 1)
    (h1 : ‖SP - (ν : ℂ) * G‖ ≤ nP * T + K * (ε * ν))
    (h2 : ‖SB - (nB : ℂ) * c‖ ≤ nB * T)
    (h3 : |nB - ν| ≤ ε * ν) :
    ‖SP + SB - (ν : ℂ) * (G + c)‖ ≤ (nP + nB) * T + (K + 1) * (ε * ν) := by
  have key : SP + SB - (ν : ℂ) * (G + c)
      = (SP - (ν : ℂ) * G) + (SB - (nB : ℂ) * c) + (((nB - ν : ℝ) : ℂ) * c) := by
    push_cast
    ring
  have h4 : ‖((nB - ν : ℝ) : ℂ) * c‖ ≤ ε * ν := by
    rw [norm_mul, hc, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact h3
  rw [key]
  calc ‖(SP - (ν : ℂ) * G) + (SB - (nB : ℂ) * c) + (((nB - ν : ℝ) : ℂ) * c)‖
      ≤ ‖SP - (ν : ℂ) * G‖ + ‖SB - (nB : ℂ) * c‖ + ‖((nB - ν : ℝ) : ℂ) * c‖ := norm_add₃_le
    _ ≤ (nP * T + K * (ε * ν)) + nB * T + ε * ν := add_le_add (add_le_add h1 h2) h4
    _ = (nP + nB) * T + (K + 1) * (ε * ν) := by ring

theorem block_one {S : ℕ → Prop} [DecidablePred S] (F : ℕ → ℂ) (q ℓ : ℕ) {T : ℝ}
    (hF : ∀ p : ℕ, q ≤ p → p < q + ℓ → ‖F p - F q‖ ≤ T) :
    ‖∑ p ∈ (Finset.Ico q (q + ℓ)).filter S, F p
        - ((((Finset.Ico q (q + ℓ)).filter S).card : ℝ) : ℂ) * F q‖
      ≤ (((Finset.Ico q (q + ℓ)).filter S).card : ℝ) * T := by
  have hconst : ((((Finset.Ico q (q + ℓ)).filter S).card : ℝ) : ℂ) * F q
      = ∑ p ∈ (Finset.Ico q (q + ℓ)).filter S, F q := by
    rw [Finset.sum_const, nsmul_eq_mul, Complex.ofReal_natCast]
  rw [hconst, ← Finset.sum_sub_distrib]
  calc ‖∑ p ∈ (Finset.Ico q (q + ℓ)).filter S, (F p - F q)‖
      ≤ ∑ p ∈ (Finset.Ico q (q + ℓ)).filter S, ‖F p - F q‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ (Finset.Ico q (q + ℓ)).filter S, T := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1
        exact hF p hp1 hp2
    _ = (((Finset.Ico q (q + ℓ)).filter S).card : ℝ) * T := by
        rw [Finset.sum_const, nsmul_eq_mul]

theorem blocks_approx {S : ℕ → Prop} [DecidablePred S] (F : ℕ → ℂ) (a ℓ : ℕ) {T ν ε : ℝ}
    (hF1 : ∀ p, ‖F p‖ = 1)
    (hF : ∀ p q : ℕ, q ≤ p → p < q + ℓ → ‖F p - F q‖ ≤ T) :
    ∀ K : ℕ, (∀ k < K,
        |(((Finset.Ico (a + k * ℓ) (a + k * ℓ + ℓ)).filter S).card : ℝ) - ν| ≤ ε * ν) →
      ‖∑ p ∈ (Finset.Ico a (a + K * ℓ)).filter S, F p
          - (ν : ℂ) * ∑ k ∈ Finset.range K, F (a + k * ℓ)‖
        ≤ (((Finset.Ico a (a + K * ℓ)).filter S).card : ℝ) * T + K * (ε * ν) := by
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
    intro hblock
    have ih' := ih (fun k hk => hblock k (Nat.lt_succ_of_lt hk))
    have hsplit : a + (K + 1) * ℓ = a + K * ℓ + ℓ := by ring
    have hunion : (Finset.Ico a (a + (K + 1) * ℓ)).filter S =
        (Finset.Ico a (a + K * ℓ)).filter S ∪
          (Finset.Ico (a + K * ℓ) (a + K * ℓ + ℓ)).filter S := by
      rw [hsplit, ← Finset.filter_union,
        Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right _ _) (Nat.le_add_right _ _)]
    have hdisj : Disjoint ((Finset.Ico a (a + K * ℓ)).filter S)
        ((Finset.Ico (a + K * ℓ) (a + K * ℓ + ℓ)).filter S) :=
      Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)
    rw [hunion, Finset.sum_union hdisj, Finset.card_union_of_disjoint hdisj,
      Finset.sum_range_succ]
    have hstep := step_bound
      (∑ p ∈ (Finset.Ico a (a + K * ℓ)).filter S, F p)
      (∑ p ∈ (Finset.Ico (a + K * ℓ) (a + K * ℓ + ℓ)).filter S, F p)
      (∑ k ∈ Finset.range K, F (a + k * ℓ)) (F (a + K * ℓ))
      (((Finset.Ico a (a + K * ℓ)).filter S).card : ℝ)
      (((Finset.Ico (a + K * ℓ) (a + K * ℓ + ℓ)).filter S).card : ℝ)
      ν ε T K (hF1 _) ih'
      (block_one F (a + K * ℓ) ℓ (fun p hp1 hp2 => hF p (a + K * ℓ) hp1 hp2))
      (hblock K (Nat.lt_succ_self K))
    push_cast
    exact hstep

theorem card_blocks_ge {S : ℕ → Prop} [DecidablePred S] (a ℓ : ℕ) {ν ε : ℝ} :
    ∀ K : ℕ, (∀ k < K,
        |(((Finset.Ico (a + k * ℓ) (a + k * ℓ + ℓ)).filter S).card : ℝ) - ν| ≤ ε * ν) →
      (K : ℝ) * ((1 - ε) * ν) ≤ (((Finset.Ico a (a + K * ℓ)).filter S).card : ℝ) := by
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
    intro hblock
    have ih' := ih (fun k hk => hblock k (Nat.lt_succ_of_lt hk))
    have hsplit : a + (K + 1) * ℓ = a + K * ℓ + ℓ := by ring
    have hunion : (Finset.Ico a (a + (K + 1) * ℓ)).filter S =
        (Finset.Ico a (a + K * ℓ)).filter S ∪
          (Finset.Ico (a + K * ℓ) (a + K * ℓ + ℓ)).filter S := by
      rw [hsplit, ← Finset.filter_union,
        Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right _ _) (Nat.le_add_right _ _)]
    have hdisj : Disjoint ((Finset.Ico a (a + K * ℓ)).filter S)
        ((Finset.Ico (a + K * ℓ) (a + K * ℓ + ℓ)).filter S) :=
      Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    have hK := hblock K (Nat.lt_succ_self K)
    rw [abs_le] at hK
    push_cast
    linarith [hK.1]

theorem norm_sum_filter_le_aux {S : ℕ → Prop} [DecidablePred S] (F : ℕ → ℂ) {a b ℓ K : ℕ}
    {T ν ε : ℝ} (hF1 : ∀ p, ‖F p‖ = 1)
    (hF : ∀ p q : ℕ, q ≤ p → p < q + ℓ → ‖F p - F q‖ ≤ T)
    (hab : a + K * ℓ ≤ b) (hb : b ≤ a + K * ℓ + K) (hν : 0 ≤ ν)
    (hblock : ∀ k < K,
      |(((Finset.Ico (a + k * ℓ) (a + k * ℓ + ℓ)).filter S).card : ℝ) - ν| ≤ ε * ν) :
    ‖∑ p ∈ (Finset.Ico a b).filter S, F p‖ ≤
      (((Finset.Ico a (a + K * ℓ)).filter S).card : ℝ) * T + K * (ε * ν)
        + ν * ‖∑ k ∈ Finset.range K, F (a + k * ℓ)‖ + K := by
  have hsplit : (Finset.Ico a b).filter S =
      (Finset.Ico a (a + K * ℓ)).filter S ∪ (Finset.Ico (a + K * ℓ) b).filter S := by
    rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right _ _) hab]
  have hdisj : Disjoint ((Finset.Ico a (a + K * ℓ)).filter S)
      ((Finset.Ico (a + K * ℓ) b).filter S) :=
    Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)
  rw [hsplit, Finset.sum_union hdisj]
  have hmain := blocks_approx (S := S) F a ℓ hF1 hF K hblock
  have hrest : ‖∑ p ∈ (Finset.Ico (a + K * ℓ) b).filter S, F p‖ ≤ K := by
    refine le_trans (norm_sum_le _ _) ?_
    have hsum : ∑ p ∈ (Finset.Ico (a + K * ℓ) b).filter S, ‖F p‖
        = (((Finset.Ico (a + K * ℓ) b).filter S).card : ℝ) := by
      simp only [hF1, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum]
    have hc : ((Finset.Ico (a + K * ℓ) b).filter S).card ≤ K := by
      calc ((Finset.Ico (a + K * ℓ) b).filter S).card
          ≤ (Finset.Ico (a + K * ℓ) b).card := Finset.card_filter_le _ _
        _ = b - (a + K * ℓ) := Nat.card_Ico _ _
        _ ≤ K := by omega
    exact_mod_cast hc
  have hG : ‖(ν : ℂ) * ∑ k ∈ Finset.range K, F (a + k * ℓ)‖
      = ν * ‖∑ k ∈ Finset.range K, F (a + k * ℓ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν]
  have h1 := norm_add_le (∑ p ∈ (Finset.Ico a (a + K * ℓ)).filter S, F p)
    (∑ p ∈ (Finset.Ico (a + K * ℓ) b).filter S, F p)
  have h2 := norm_sub_norm_le (∑ p ∈ (Finset.Ico a (a + K * ℓ)).filter S, F p)
    ((ν : ℂ) * ∑ k ∈ Finset.range K, F (a + k * ℓ))
  rw [hG] at h2
  linarith

theorem norm_geom_exp_le {x : ℝ} (K : ℕ) (h0 : 0 < x) (h1 : x ≤ Real.pi) :
    ‖∑ k ∈ Finset.range K, Complex.exp ((x : ℂ) * Complex.I) ^ k‖ ≤ Real.pi / x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin : 2 / Real.pi * (x / 2) ≤ Real.sin (x / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have hpos : 0 < 2 / Real.pi * (x / 2) := mul_pos (div_pos two_pos hpi) (half_pos h0)
  have hwm1 : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ = ‖2 * Real.sin (x / 2)‖ := by
    have h := Complex.norm_exp_I_mul_ofReal_sub_one x
    rwa [mul_comm Complex.I] at h
  have hlow : 2 * (2 / Real.pi * (x / 2)) ≤ ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ := by
    rw [hwm1, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ 2 * Real.sin (x / 2) by linarith)]
    linarith
  have hne : Complex.exp ((x : ℂ) * Complex.I) ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hlow
    linarith
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖Complex.exp ((x : ℂ) * Complex.I) ^ K - 1‖ ≤ 2 := by
    have e1 : ‖Complex.exp ((x : ℂ) * Complex.I) ^ K‖ = 1 := by
      rw [norm_pow, Complex.norm_exp_ofReal_mul_I, one_pow]
    have e2 := norm_sub_le (Complex.exp ((x : ℂ) * Complex.I) ^ K) 1
    rw [e1, norm_one] at e2
    linarith
  have hden : 0 < ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ := by linarith
  rw [div_le_div_iff₀ hden h0]
  have hpi2 : Real.pi * (2 / Real.pi) = 2 := mul_div_cancel₀ 2 hpi.ne'
  have h2x : 2 * x ≤ Real.pi * ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ := by
    have h3 := mul_le_mul_of_nonneg_left hlow hpi.le
    have h4 : Real.pi * (2 * (2 / Real.pi * (x / 2))) = 2 * x := by
      calc Real.pi * (2 * (2 / Real.pi * (x / 2))) = (Real.pi * (2 / Real.pi)) * x := by ring
        _ = 2 * x := by rw [hpi2]
    linarith
  calc ‖Complex.exp ((x : ℂ) * Complex.I) ^ K - 1‖ * x ≤ 2 * x :=
        mul_le_mul_of_nonneg_right hnum h0.le
    _ ≤ Real.pi * ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ := h2x

theorem sum_exp_arith (θ : ℝ) (a ℓ K : ℕ) :
    ∑ k ∈ Finset.range K, Complex.exp (((θ * ((a + k * ℓ : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((θ * a : ℝ) : ℂ) * Complex.I) *
          ∑ k ∈ Finset.range K, Complex.exp (((θ * ℓ : ℝ) : ℂ) * Complex.I) ^ k := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_sum_filter_exp_le {S : ℕ → Prop} [DecidablePred S] {a b ℓ K : ℕ} {θ ν ε : ℝ}
    (hK : 0 < K) (hθ : 0 < θ) (hθℓ0 : 0 < θ * ℓ) (hθℓ : θ * ℓ ≤ Real.pi) (hν : 0 < ν)
    (hε1 : ε < 1) (hε0 : 0 ≤ ε)
    (hab : a + K * ℓ ≤ b) (hb : b ≤ a + K * ℓ + K)
    (hblock : ∀ k < K,
      |(((Finset.Ico (a + k * ℓ) (a + k * ℓ + ℓ)).filter S).card : ℝ) - ν| ≤ ε * ν) :
    ‖∑ p ∈ (Finset.Ico a b).filter S, Complex.exp (((θ * p : ℝ) : ℂ) * Complex.I)‖ ≤
      (((Finset.Ico a b).filter S).card : ℝ) *
        (θ * ℓ + ε / (1 - ε) + Real.pi / ((1 - ε) * (K * (θ * ℓ))) + 1 / ((1 - ε) * ν)) := by
  have hFvar : ∀ p q : ℕ, q ≤ p → p < q + ℓ →
      ‖Complex.exp (((θ * p : ℝ) : ℂ) * Complex.I) - Complex.exp (((θ * q : ℝ) : ℂ) * Complex.I)‖
        ≤ θ * ℓ := by
    intro p q hqp hpq
    refine le_trans (norm_exp_sub_exp_le _ _) ?_
    have h1 : (q : ℝ) ≤ p := by exact_mod_cast hqp
    have h2 : (p : ℝ) < q + ℓ := by exact_mod_cast hpq
    have h3 : θ * p - θ * q = θ * ((p : ℝ) - q) := by ring
    rw [h3, abs_of_nonneg (mul_nonneg hθ.le (show (0 : ℝ) ≤ (p : ℝ) - q by linarith))]
    exact mul_le_mul_of_nonneg_left (by linarith) hθ.le
  have hmain := norm_sum_filter_le_aux (S := S)
    (fun p : ℕ => Complex.exp (((θ * p : ℝ) : ℂ) * Complex.I))
    (fun p => Complex.norm_exp_ofReal_mul_I _) hFvar hab hb hν.le hblock
  have hgeom : ‖∑ k ∈ Finset.range K,
      Complex.exp (((θ * ((a + k * ℓ : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ Real.pi / (θ * ℓ) := by
    rw [sum_exp_arith, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_geom_exp_le K hθℓ0 hθℓ
  have hcard := card_blocks_ge (S := S) a ℓ K hblock
  have hsub : ((Finset.Ico a (a + K * ℓ)).filter S).card ≤ ((Finset.Ico a b).filter S).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl hab))
  have hN₀N : ((((Finset.Ico a (a + K * ℓ)).filter S).card : ℕ) : ℝ)
      ≤ (((Finset.Ico a b).filter S).card : ℝ) := by exact_mod_cast hsub
  have hD : 0 < 1 - ε := by linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hM : (K : ℝ) * ((1 - ε) * ν) ≤ (((Finset.Ico a b).filter S).card : ℝ) :=
    le_trans hcard hN₀N
  have i1 : ((((Finset.Ico a (a + K * ℓ)).filter S).card : ℕ) : ℝ) * (θ * ℓ)
      ≤ (((Finset.Ico a b).filter S).card : ℝ) * (θ * ℓ) :=
    mul_le_mul_of_nonneg_right hN₀N hθℓ0.le
  have i2 : (K : ℝ) * (ε * ν) ≤ (((Finset.Ico a b).filter S).card : ℝ) * (ε / (1 - ε)) := by
    rw [mul_div_assoc', le_div_iff₀ hD]
    have := mul_le_mul_of_nonneg_left hM hε0
    linarith
  have i3 : ν * (Real.pi / (θ * ℓ))
      ≤ (((Finset.Ico a b).filter S).card : ℝ) * (Real.pi / ((1 - ε) * (K * (θ * ℓ)))) := by
    rw [mul_div_assoc', mul_div_assoc',
      div_le_div_iff₀ hθℓ0 (mul_pos hD (mul_pos hKr hθℓ0))]
    have := mul_le_mul_of_nonneg_left hM (mul_nonneg Real.pi_pos.le hθℓ0.le)
    linarith
  have i4 : (K : ℝ) ≤ (((Finset.Ico a b).filter S).card : ℝ) * (1 / ((1 - ε) * ν)) := by
    rw [mul_one_div, le_div_iff₀ (mul_pos hD hν)]
    linarith
  have i5 : ν * ‖∑ k ∈ Finset.range K,
      Complex.exp (((θ * ((a + k * ℓ : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)‖
        ≤ ν * (Real.pi / (θ * ℓ)) :=
    mul_le_mul_of_nonneg_left hgeom hν.le
  calc ‖∑ p ∈ (Finset.Ico a b).filter S, Complex.exp (((θ * p : ℝ) : ℂ) * Complex.I)‖
      ≤ ((((Finset.Ico a (a + K * ℓ)).filter S).card : ℕ) : ℝ) * (θ * ℓ) + K * (ε * ν)
          + ν * ‖∑ k ∈ Finset.range K,
              Complex.exp (((θ * ((a + k * ℓ : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)‖ + K := hmain
    _ ≤ (((Finset.Ico a b).filter S).card : ℝ) * (θ * ℓ)
          + (((Finset.Ico a b).filter S).card : ℝ) * (ε / (1 - ε))
          + (((Finset.Ico a b).filter S).card : ℝ) * (Real.pi / ((1 - ε) * (K * (θ * ℓ))))
          + (((Finset.Ico a b).filter S).card : ℝ) * (1 / ((1 - ε) * ν)) := by linarith
    _ = (((Finset.Ico a b).filter S).card : ℝ) *
          (θ * ℓ + ε / (1 - ε) + Real.pi / ((1 - ε) * (K * (θ * ℓ))) + 1 / ((1 - ε) * ν)) := by
        ring

theorem final_numeric {x y ν : ℝ} (hx : x ≤ 1 / 1000) (hy : 1000 ≤ y) (hν : 1000 ≤ ν) :
    x + (1 / 1000 : ℝ) / (1 - 1 / 1000) + Real.pi / ((1 - 1 / 1000) * y)
      + 1 / ((1 - 1 / 1000) * ν) ≤ 1 / 100 := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have h1 : (1 / 1000 : ℝ) / (1 - 1 / 1000) ≤ 2 / 1000 := by norm_num
  have hy0 : 0 < (1 - 1 / 1000 : ℝ) * y := by linarith
  have hν0 : 0 < (1 - 1 / 1000 : ℝ) * ν := by linarith
  have h2 : Real.pi / ((1 - 1 / 1000) * y) ≤ 4 / 1000 := by
    rw [div_le_iff₀ hy0]
    linarith
  have h3 : 1 / ((1 - 1 / 1000) * ν) ≤ 2 / 1000 := by
    rw [div_le_iff₀ hν0]
    linarith
  linarith

theorem norm_mean_le_of_blocks {S : ℕ → Prop} [DecidablePred S] {a b ℓ K : ℕ} {θ ν : ℝ}
    (hK : 0 < K) (hθ : 0 < θ) (hθℓ0 : 0 < θ * ℓ) (hθℓ : θ * ℓ ≤ 1 / 1000)
    (hKθℓ : 1000 ≤ K * (θ * ℓ)) (hν : 1000 ≤ ν)
    (hab : a + K * ℓ ≤ b) (hb : b ≤ a + K * ℓ + K)
    (hblock : ∀ k < K,
      |(((Finset.Ico (a + k * ℓ) (a + k * ℓ + ℓ)).filter S).card : ℝ) - ν| ≤ 1 / 1000 * ν) :
    ‖(((Finset.Ico a b).filter S).card : ℂ)⁻¹ *
        ∑ p ∈ (Finset.Ico a b).filter S, Complex.exp (((θ * p - θ : ℝ) : ℂ) * Complex.I)‖
      ≤ 1 / 100 := by
  have hsum : ∑ p ∈ (Finset.Ico a b).filter S, Complex.exp (((θ * p - θ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) *
          ∑ p ∈ (Finset.Ico a b).filter S, Complex.exp (((θ * p : ℝ) : ℂ) * Complex.I) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsum, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_inv,
    Complex.norm_natCast]
  have hmain := norm_sum_filter_exp_le (S := S) (ε := 1 / 1000) hK hθ hθℓ0
    (by linarith [Real.pi_gt_three]) (by linarith) (by norm_num) (by norm_num) hab hb hblock
  have hbound := final_numeric hθℓ hKθℓ hν
  by_cases hN : ((Finset.Ico a b).filter S).card = 0
  · rw [hN]
    norm_num
  · have hN' : ((((Finset.Ico a b).filter S).card : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    calc ((((Finset.Ico a b).filter S).card : ℕ) : ℝ)⁻¹ *
          ‖∑ p ∈ (Finset.Ico a b).filter S, Complex.exp (((θ * p : ℝ) : ℂ) * Complex.I)‖
        ≤ ((((Finset.Ico a b).filter S).card : ℕ) : ℝ)⁻¹ *
            ((((Finset.Ico a b).filter S).card : ℝ) *
              (θ * ℓ + (1 / 1000 : ℝ) / (1 - 1 / 1000)
                + Real.pi / ((1 - 1 / 1000) * (K * (θ * ℓ))) + 1 / ((1 - 1 / 1000) * ν))) :=
          mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = θ * ℓ + (1 / 1000 : ℝ) / (1 - 1 / 1000)
            + Real.pi / ((1 - 1 / 1000) * (K * (θ * ℓ))) + 1 / ((1 - 1 / 1000) * ν) := by
          rw [← mul_assoc, inv_mul_cancel₀ hN', one_mul]
      _ ≤ 1 / 100 := hbound

theorem block_count_core {c₁ c₂ n y₁ ℓ Λ δA : ℝ} (hΛ : 0 < Λ) (hsum : c₁ + n = c₂)
    (h1 : |c₁ * Λ - y₁| ≤ δA) (h2 : |c₂ * Λ - (y₁ + ℓ)| ≤ δA) (hδA : 2 * δA ≤ ℓ / 1000) :
    |n - ℓ / Λ| ≤ 1 / 1000 * (ℓ / Λ) := by
  have hΛ0 : Λ ≠ 0 := hΛ.ne'
  have hn : n = c₂ - c₁ := by linarith
  have key : (n * Λ - ℓ) / Λ = n - ℓ / Λ := by
    rw [sub_div, mul_div_assoc, div_self hΛ0, mul_one]
  have hbound : |n * Λ - ℓ| ≤ ℓ / 1000 := by
    rw [abs_le] at h1 h2 ⊢
    rw [hn]
    constructor
    · nlinarith [h1.1, h1.2, h2.1, h2.2]
    · nlinarith [h1.1, h1.2, h2.1, h2.2]
  rw [← key, abs_div, abs_of_pos hΛ]
  rw [show 1 / 1000 * (ℓ / Λ) = (ℓ / 1000) / Λ by ring]
  exact div_le_div_of_nonneg_right hbound hΛ.le

theorem theta_param_bounds {X m φ W P H ℓ K θ : ℝ} (hX : 0 < X) (hm : 1 ≤ m)
    (hφlo : 1 / 1000 * m ≤ φ) (hφhi : φ ≤ m) (hφ1 : 1 ≤ φ) (hH : 2 ≤ H)
    (hWup : W * m ≤ 2 * X) (hWlo : 99 / 100 * X ≤ W * m) (hW0 : 0 ≤ W)
    (hP0 : 0 < P) (hP32 : 32 * X ≤ P * 67108864) (hP96 : P * 67108864 < 96 * X)
    (hθ : θ * P = Real.pi * (H - 1) * φ)
    (hK : K = H * 34359738368) (hℓK : ℓ * K ≤ W) (hWℓK : W ≤ 2 * (ℓ * K)) :
    0 < θ ∧ θ * ℓ ≤ 1 / 1000 ∧ 1000 ≤ K * (θ * ℓ) := by
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hpi1 : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi2 : 3.14 < Real.pi := Real.pi_gt_d2
  have hnum : 0 < Real.pi * (H - 1) * φ :=
    mul_pos (mul_pos hpi0 (by linarith)) (by linarith)
  have hθ0 : 0 < θ := by
    by_contra hneg
    push_neg at hneg
    have : θ * P ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hP0.le
    linarith
  have hup1 : (H - 1) * φ * W ≤ H * (4194304 * P) := by
    have h1 : (H - 1) * (φ * W) ≤ H * (m * W) :=
      mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right hφhi hW0)
        (mul_nonneg (by linarith) hW0) (by linarith)
    have h2 : H * (m * W) ≤ H * (4194304 * P) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have eW : θ * W * P = Real.pi * ((H - 1) * φ * W) := by
    calc θ * W * P = θ * P * W := by ring
      _ = Real.pi * (H - 1) * φ * W := by rw [hθ]
      _ = Real.pi * ((H - 1) * φ * W) := by ring
  have hθW_up : θ * W ≤ Real.pi * H * 4194304 := by
    have h1 : θ * W * P ≤ Real.pi * H * 4194304 * P := by
      rw [eW]
      have := mul_le_mul_of_nonneg_left hup1 hpi0.le
      linarith
    exact le_of_mul_le_mul_right h1 hP0
  have hlo1 : 99 / 100000 * X ≤ (H - 1) * φ * W := by
    have h1 : 1 * (φ * W) ≤ (H - 1) * (φ * W) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by linarith) hW0)
    have h2 : 1 / 1000 * m * W ≤ φ * W := mul_le_mul_of_nonneg_right hφlo hW0
    linarith
  have hθW_lo : 2000 ≤ θ * W := by
    have h1 : 2000 * P ≤ θ * W * P := by
      rw [eW]
      have h2 : 3.14 * (99 / 100000 * X) ≤ Real.pi * ((H - 1) * φ * W) :=
        mul_le_mul hpi2.le hlo1 (by linarith) hpi0.le
      linarith
    exact le_of_mul_le_mul_right h1 hP0
  refine ⟨hθ0, ?_, ?_⟩
  · have h1 : θ * (ℓ * K) ≤ θ * W := mul_le_mul_of_nonneg_left hℓK hθ0.le
    rw [hK] at h1
    have hH0 : 0 < H := by linarith
    have h2 : θ * ℓ * 34359738368 * H ≤ Real.pi * 4194304 * H := by linarith
    have h3 := le_of_mul_le_mul_right h2 hH0
    linarith
  · have h1 : θ * W ≤ θ * (2 * (ℓ * K)) := mul_le_mul_of_nonneg_left hWℓK hθ0.le
    linarith

theorem discrepancy_core {δ c Y y : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y) (hc : 0 ≤ c)
    (hYy : Y ≤ y) (hy4 : y ≤ 4 * Y)
    (hlo : (1 - δ / 8) * y ≤ c * Real.log y) (hhi : c * Real.log y ≤ (1 + δ / 8) * y)
    (hlogY : 48 / δ ≤ Real.log Y) :
    |c * Real.log Y - y| ≤ δ * Y := by
  have hY0 : 0 < Y := by linarith
  have hy0 : 0 < y := by linarith
  have h48 : 48 ≤ δ * Real.log Y := by
    rw [div_le_iff₀ hδ0] at hlogY
    linarith
  have hlogYy : Real.log Y ≤ Real.log y := Real.log_le_log hY0 hYy
  have hlogy4 : Real.log y ≤ Real.log 4 + Real.log Y := by
    rw [← Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hY0.ne']
    exact Real.log_le_log hy0 hy4
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have h1 : c * Real.log Y ≤ c * Real.log y := mul_le_mul_of_nonneg_left hlogYy hc
  have h9 : δ * y ≤ δ * (4 * Y) := mul_le_mul_of_nonneg_left hy4 hδ0.le
  have hδy : δ * y ≤ 1 * y := mul_le_mul_of_nonneg_right hδ1 hy0.le
  have h2 : c * Real.log Y ≤ 2 * y := by linarith
  have h5 : c * 48 ≤ c * (δ * Real.log Y) := mul_le_mul_of_nonneg_left h48 hc
  have h6 : δ * (c * Real.log Y) ≤ δ * (2 * y) := mul_le_mul_of_nonneg_left h2 hδ0.le
  have h6c : 6 * c ≤ δ * Y := by linarith
  have h7 : c * Real.log y ≤ c * Real.log Y + c * Real.log 4 := by
    have := mul_le_mul_of_nonneg_left hlogy4 hc
    linarith
  have h8 : c * Real.log 4 ≤ c * 3 := mul_le_mul_of_nonneg_left hlog4 hc
  rw [abs_le]
  constructor
  · linarith
  · linarith

theorem count_log_core {δ u N X : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hu3 : 3 ≤ u)
    (hNu : N = u + 1) (hNX : N ≤ X)
    (ha : (1 - δ / 8) * (u * Real.log u) < X)
    (hb : X ≤ (1 + δ / 8) * (N * Real.log N))
    (hd : Real.log (2 * Real.log N) ≤ δ / 8 * Real.log N)
    (he : Real.log X + 1 ≤ δ / 8 * X) :
    (1 - δ) * X ≤ N * Real.log X ∧ N * Real.log X ≤ (1 + δ) * X := by
  have hu0 : 0 < u := by linarith
  have hN0 : 0 < N := by linarith
  have hX0 : 0 < X := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogNX : Real.log N ≤ Real.log X := Real.log_le_log hN0 hNX
  have hlogX : 0 < Real.log X := lt_of_lt_of_le hlogN hlogNX
  have hZ : 0 ≤ N * Real.log X := mul_nonneg hN0.le hlogX.le
  have hNN : N * Real.log N ≤ N * Real.log X := mul_le_mul_of_nonneg_left hlogNX hN0.le
  have hb' : X ≤ (1 + δ / 8) * (N * Real.log X) := by
    have h2 : (1 + δ / 8) * (N * Real.log N) ≤ (1 + δ / 8) * (N * Real.log X) :=
      mul_le_mul_of_nonneg_left hNN (by linarith)
    linarith
  constructor
  · have h1 : (1 - δ) * X ≤ (1 - δ) * ((1 + δ / 8) * (N * Real.log X)) :=
      mul_le_mul_of_nonneg_left hb' (by linarith)
    have h3 : (1 - δ) * (1 + δ / 8) ≤ 1 := by nlinarith [sq_nonneg δ]
    have h4 : (1 - δ) * (1 + δ / 8) * (N * Real.log X) ≤ 1 * (N * Real.log X) :=
      mul_le_mul_of_nonneg_right h3 hZ
    linarith
  · have hNlogN : 0 ≤ N * Real.log N := mul_nonneg hN0.le hlogN.le
    have hX2 : X ≤ 2 * (N * Real.log N) := by
      have : (1 + δ / 8) * (N * Real.log N) ≤ 2 * (N * Real.log N) :=
        mul_le_mul_of_nonneg_right (by linarith) hNlogN
      linarith
    have hL3 : Real.log X ≤ Real.log N + Real.log (2 * Real.log N) := by
      have h1 : Real.log X ≤ Real.log (N * (2 * Real.log N)) :=
        Real.log_le_log hX0 (by linarith)
      rwa [Real.log_mul hN0.ne' (mul_pos two_pos hlogN).ne'] at h1
    have hL5 : N * Real.log X ≤ (1 + δ / 8) * (N * Real.log N) := by
      have h1 : Real.log X ≤ (1 + δ / 8) * Real.log N := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hN0.le
      linarith
    have hL6 : u * Real.log N ≤ u * Real.log u + 1 := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hN0 hu0)
      rw [Real.log_div hN0.ne' hu0.ne'] at h1
      have h2 : u * (Real.log N - Real.log u) ≤ u * (N / u - 1) :=
        mul_le_mul_of_nonneg_left h1 hu0.le
      have h3 : u * (N / u - 1) = N - u := by
        rw [mul_sub, mul_one, mul_div_cancel₀ _ hu0.ne']
      rw [h3] at h2
      linarith
    have hL7 : N * Real.log N ≤ u * Real.log u + 1 + Real.log N := by
      have e : N * Real.log N = u * Real.log N + Real.log N := by
        rw [hNu]
        ring
      linarith
    have hU0 : 0 ≤ u * Real.log u := mul_nonneg hu0.le hlogu.le
    have hL8 : u * Real.log u ≤ (1 + δ / 4) * X := by
      have h1 : 7 / 8 * (u * Real.log u) ≤ (1 - δ / 8) * (u * Real.log u) :=
        mul_le_mul_of_nonneg_right (by linarith) hU0
      have h2 : u * Real.log u ≤ 2 * X := by linarith
      have h3 : δ / 8 * (u * Real.log u) ≤ δ / 8 * (2 * X) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      linarith
    have h1 : N * Real.log N ≤ (1 + δ / 4) * X + δ / 8 * X := by linarith
    have h2 : (1 + δ / 8) * (N * Real.log N) ≤ (1 + δ / 8) * ((1 + δ / 4) * X + δ / 8 * X) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : δ * δ * X ≤ δ * X := by
      have := mul_le_mul_of_nonneg_right hδ1 (mul_nonneg hδ0.le hX0.le)
      linarith
    linarith

end FiberMeanProbe

#print axioms FiberMeanProbe.norm_mean_le_of_blocks
#print axioms FiberMeanProbe.block_count_core
#print axioms FiberMeanProbe.theta_param_bounds
#print axioms FiberMeanProbe.discrepancy_core
#print axioms FiberMeanProbe.count_log_core
