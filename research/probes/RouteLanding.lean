import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate
import ErdosProblems.Erdos249.TypeBReturnV8.PeripheralFiniteBridge

/-!
# Erdős #249: the fibre means from the prime number theorem

`dtw_of_fiberMean_and_centered` (`ErdosProblems.ArgumentGraph.Results.Erdos249`) derives
`DTWPivotResidualDecorrelation` from two clauses: a uniform bound on the fibre means and the
centred correlation. This module proves the first clause, `hmean`, from the prime number theorem
(`fiberMean_le_of_primeNumberTheorem`): at the minimal depth `L = minimalDepth h 26 X`, with
`s = 26` and `η = 1/1000`, for every `h ≥ 1` and all large `X`, every good base `N` has
`‖pivotFiberMean h X L 26 m_N‖ ≤ 1/100`, where `m_N = pivotCofactor N L 26`.

Input. The prime number theorem enters as the hypothesis
`ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem`, that is `p_n / (n log n) → 1`
for the zero-based `n`-th prime `p_n = Nat.nth Nat.Prime n`. Nothing else is assumed.

Proof. Fix `h ≥ 1` and a good base with cofactor `m`, so `0 < m ≤ ⌊√X⌋/2` and `φ(m) ≥ m/1000`.
Put `t = L - 25`, `A = ⌈(X + t)/m⌉` and `B = ⌈(2X + t)/m⌉`.
1. The fibre of `m` is the image of the primes `p` with `X + t ≤ mp < 2X + t`
   (`image_pivotSupplierPrimes_eq_pivotFiber`), so the fibre mean is the mean of
   `pivotPrimePhase h L 26 m p` over the primes of `[A, B)` (`pivotFiberMean_eq_sum_primes`,
   `pivotSupplierPrimes_eq_filter_Ico`).
2. That phase is `e(θ p - θ)` with `e(x) = exp(ix)` and `θ = π (2^h - 1) φ(m) / 2^(L - 26)`
   (`pivotPrimeAngle_eq_affine`).
3. For large `X` the minimal depth has `32X ≤ 2^L < 96X` (`minimalDepth_geometry`), so the phase
   turns through between `2000` and `π 2^(h+22)` radians over `[A, B)`.
4. Cut `[A, B)` into `K = 2^(h+35)` blocks of length `ℓ = ⌊(B - A)/K⌋` and fewer than `K`
   remaining integers. Inside a block the phase moves by at most `θℓ ≤ π/2^13`, so the sum over
   the primes of the blocks is `ν ∑_{k<K} e(θ(A + kℓ))`, with `ν = ℓ / log A`, up to `θℓ` per
   prime and the errors in the block counts (`blocks_approx`). The geometric sum is at most
   `π/(θℓ)` (`norm_geom_exp_le`).
5. The prime number theorem in counting form, `π(x) log x = (1 + o(1)) x`
   (`eventually_count_log_two_sided`), gives `|π(y) log A - y| ≤ δ A` uniformly for
   `A ≤ y ≤ 4A` (`exists_count_log_discrepancy`). With `δ = 1/(8000 K)` every block holds
   `ν (1 ± 1/1000)` primes.
6. The mean is then at most `θℓ + 1/999 + π/(0.999 K θ ℓ) + 1/(0.999 ν)`, and
   `θℓ ≤ 1/1000`, `K θ ℓ ≥ 1000`, `ν ≥ 1000` make this less than `1/100`
   (`norm_mean_le_of_blocks`, `fiberMean_le_at`).
-/

open Filter Topology

namespace ErdosProblems.Erdos249.PaperCompleteR21.FiberMean

/-! ## Exponential sums over an evenly spread set of integers -/

/-- `e(x) = exp(ix)` is `1`-Lipschitz: `‖e(x) - e(y)‖ ≤ |x - y|`. -/
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

/-- One step of the block comparison: the error after `k + 1` blocks from the error after `k`
blocks, the variation of the summand inside the new block, and the error in its count. -/
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

/-- Inside one block `[q, q + ℓ)`, replacing each `F p` by `F q` costs at most `T` per element. -/
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

/-- **Block comparison.** If each block `[a + kℓ, a + kℓ + ℓ)`, `k < K`, holds `ν` elements of `S`
up to `εν`, and `F` moves by at most `T` inside a block, then the sum of `F` over
`S ∩ [a, a + Kℓ)` is `ν ∑_{k<K} F (a + kℓ)` up to `#(S ∩ [a, a + Kℓ)) T + K ε ν`. -/
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

/-- The block counts give `#(S ∩ [a, a + Kℓ)) ≥ K (1 - ε) ν`. -/
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

/-- The sum over `S ∩ [a, b)` with `a + Kℓ ≤ b ≤ a + Kℓ + K`: the block comparison, plus at
most `K` terms in `[a + Kℓ, b)`. -/
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

/-- A geometric sum of `e(x)` with `0 < x ≤ π` has norm at most `π / x`, from
`|e(x) - 1| = 2 sin (x/2)` and Jordan's inequality `sin t ≥ 2t/π` on `[0, π/2]`. -/
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

/-- The sum of `e(θ (a + kℓ))` over `k < K` is `e(θ a)` times a geometric sum in `e(θ ℓ)`. -/
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

/-- **Exponential sums over an evenly spread set.** Under the block hypotheses of
`blocks_approx`, with `N = #(S ∩ [a, b))`,
`‖∑_{p ∈ S ∩ [a, b)} e(θ p)‖ ≤ N (θℓ + ε/(1-ε) + π/((1-ε) K θ ℓ) + 1/((1-ε) ν))`. -/
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

/-- The numerical budget: for `θℓ ≤ 1/1000`, `K θ ℓ ≥ 1000` and `ν ≥ 1000` the bound of
`norm_sum_filter_exp_le` with `ε = 1/1000` is at most `1/100`. -/
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

/-- **The mean of `e(θ p - θ)` over `S ∩ [a, b)` is at most `1/100`**, when every block holds
`ν (1 ± 1/1000)` elements of `S`, `θℓ ≤ 1/1000`, `K θ ℓ ≥ 1000` and `ν ≥ 1000`. -/
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

/-! ## Real inequalities for the parameters -/

/-- One block count: if `|c₁ Λ - y₁| ≤ δA` and `|c₂ Λ - (y₁ + ℓ)| ≤ δA` with `2δA ≤ ℓ/1000`,
then `n = c₂ - c₁` satisfies `|n - ℓ/Λ| ≤ (ℓ/Λ)/1000`. -/
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

/-- The phase speed. With `θ P = π (H - 1) φ`, `H ≥ 2`, `32X ≤ 2^26 P < 96X`, `φ ≥ 1`,
`m/1000 ≤ φ ≤ m`, `(99/100) X ≤ W m ≤ 2X`, `K = 2^35 H` and `ℓK ≤ W ≤ 2ℓK`, one has
`θ > 0`, `θ ℓ ≤ 1/1000` and `K θ ℓ ≥ 1000`: the phase turns through between `2000` and
`π 2^22 H` radians over `W`. -/
theorem theta_param_bounds {X m φ W P H ℓ K θ : ℝ}
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
    have : θ * P ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hP0.le
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

/-- From `π(y) log y = (1 ± δ/8) y` and `log Y ≥ 48/δ`, for `Y ≤ y ≤ 4Y`:
`|π(y) log Y - y| ≤ δ Y`. -/
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

/-- The real-variable core of the counting form of the prime number theorem. Here `N = u + 1`
is the number of primes below `X`, so `p_u < X ≤ p_N`. -/
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

end ErdosProblems.Erdos249.PaperCompleteR21.FiberMean

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos251.PaperR11.PrimeSource (PrimeNumberTheorem)
open ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor

namespace FiberMean

/-! ## Prime counts from the prime number theorem -/

/-- `count p b = count p a + #{x ∈ [a, b) | p x}` for `a ≤ b`. -/
theorem count_add_card_filter_Ico (p : ℕ → Prop) [DecidablePred p] {a b : ℕ} (hab : a ≤ b) :
    Nat.count p a + ((Finset.Ico a b).filter p).card = Nat.count p b := by
  have hdisj : Disjoint ((Finset.range a).filter p) ((Finset.Ico a b).filter p) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 a b
  have hunion : (Finset.range a).filter p ∪ (Finset.Ico a b).filter p
      = (Finset.range b).filter p := by
    rw [← Finset.filter_union, Finset.range_eq_Ico,
      Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a) hab]
  have h1 : Nat.count p a = ((Finset.range a).filter p).card := Nat.count_eq_card_filter_range p a
  have h2 : Nat.count p b = ((Finset.range b).filter p).card := Nat.count_eq_card_filter_range p b
  rw [h1, h2, ← hunion, Finset.card_union_of_disjoint hdisj]

/-- **The prime number theorem in counting form.** For `0 < δ ≤ 1`, for all large `x`,
`(1 - δ) x ≤ π(x) log x ≤ (1 + δ) x`, where `π(x) = Nat.count Nat.Prime x` counts the primes
below `x`. The upper bound uses `log x ≤ (1 + δ/8) log π(x)`. -/
theorem eventually_count_log_two_sided (hPNT : PrimeNumberTheorem) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∀ᶠ x : ℕ in atTop,
      (1 - δ) * (x : ℝ) ≤ (Nat.count Nat.Prime x : ℝ) * Real.log x ∧
      (Nat.count Nat.Prime x : ℝ) * Real.log x ≤ (1 + δ) * x := by
  have hδ8 : 0 < δ / 8 := by positivity
  obtain ⟨K, hK2, hK⟩ := nthPrime_two_sided hPNT hδ8
  have hll : ∀ᶠ n : ℕ in atTop, Real.log (2 * Real.log (n : ℝ)) ≤ δ / 8 * Real.log n :=
    tendsto_natCast_atTop_atTop.eventually (eventually_log_two_mul_log_le hδ8)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hll
  have hsm : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) + 1 ≤ δ / 8 * (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_log_add_le hδ8 1)
  have hinf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime
  filter_upwards [hsm, eventually_gt_atTop (Nat.nth Nat.Prime (K + n₀ + 5))] with x hsm hx
  have hnK : K + n₀ + 5 < Nat.count Nat.Prime x := (Nat.lt_nth_iff_count_lt hinf).mpr hx
  have hF2 : x ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime x) := Nat.le_nth_count hinf x
  have hF1 : Nat.nth Nat.Prime (Nat.count Nat.Prime x - 1) < x :=
    Nat.nth_lt_of_lt_count (by omega)
  have hnx : Nat.count Nat.Prime x ≤ x := Nat.count_le _
  generalize Nat.count Nat.Prime x = n at hnK hF2 hF1 hnx ⊢
  obtain ⟨hu1, -⟩ := hK (n - 1) (by omega)
  obtain ⟨-, hn2⟩ := hK n (by omega)
  have hun : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  exact count_log_core hδ0 hδ1 (u := ((n - 1 : ℕ) : ℝ)) (N := (n : ℝ)) (X := (x : ℝ))
    (by exact_mod_cast (show 3 ≤ n - 1 by omega)) hun.symm (by exact_mod_cast hnx)
    (lt_of_le_of_lt hu1 (by exact_mod_cast hF1)) (le_trans (by exact_mod_cast hF2) hn2)
    (hn₀ n (by omega)) hsm

/-- **Prime counts at scale `Y`.** For `0 < δ ≤ 1` there is `Y₀` such that
`|π(y) log Y - y| ≤ δ Y` whenever `Y₀ ≤ Y ≤ y ≤ 4Y`. -/
theorem exists_count_log_discrepancy (hPNT : PrimeNumberTheorem) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y → ∀ y : ℕ, Y ≤ y → y ≤ 4 * Y →
      |(Nat.count Nat.Prime y : ℝ) * Real.log (Y : ℝ) - (y : ℝ)| ≤ δ * (Y : ℝ) := by
  have hδ8 : 0 < δ / 8 := by positivity
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (eventually_count_log_two_sided hPNT hδ8 (by linarith))
  have hlog : ∀ᶠ Y : ℕ in atTop, 48 / δ ≤ Real.log (Y : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp hlog
  refine ⟨max (max X₁ X₂) 1, fun Y hY y hYy hy4 => ?_⟩
  have hY1 : X₁ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hY2 : X₂ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hY3 : 1 ≤ Y := le_trans (le_max_right _ _) hY
  obtain ⟨hlo, hhi⟩ := hX₁ y (le_trans hY1 hYy)
  exact discrepancy_core hδ0 hδ1 (by exact_mod_cast hY3) (Nat.cast_nonneg _)
    (by exact_mod_cast hYy) (by exact_mod_cast hy4) hlo hhi (hX₂ Y hY2)

/-! ## The minimal depth -/

/-- **The minimal depth.** For `h ≥ 1` and `X ≥ max(2^(h+22), 4h + 64)` the minimal admissible depth
`L = minimalDepth h 26 X` has `h + 26 ≤ L`, `32X ≤ 2^L < 96X` and `L ≤ h + 36 + log₂ X`. The
upper bound `2^L < 96X` holds because `L - 1` is not admissible. -/
theorem minimalDepth_geometry {h X : ℕ} (hh : 0 < h) (hX1 : 2 ^ (h + 22) ≤ X)
    (hX2 : 4 * h + 64 ≤ X) :
    h + 26 ≤ minimalDepth h 26 X ∧
    32 * X ≤ 2 ^ minimalDepth h 26 X ∧
    2 ^ minimalDepth h 26 X < 96 * X ∧
    minimalDepth h 26 X ≤ h + 36 + Nat.log 2 X := by
  obtain ⟨hA1, hA2⟩ := minimalDepth_admissible h 26 X
  have hle := minimalDepth_le (admissibleDepth_witness h 26 X)
  have hpos : 0 < minimalDepth h 26 X := by omega
  have hmin : ¬ AdmissibleDepth h 26 X (minimalDepth h 26 X - 1) :=
    Nat.find_min (exists_admissibleDepth h 26 X) (Nat.sub_lt hpos Nat.one_pos)
  have hlog : 4 * Nat.log 2 X ≤ X := four_mul_log_two_le (by omega)
  have hP : 0 < 2 ^ (h + 21) := pow_pos (by norm_num) _
  have h2 : 2 ^ (h + 26) = 32 * 2 ^ (h + 21) := by ring
  have h3 : 2 ^ (h + 22) = 2 * 2 ^ (h + 21) := by ring
  generalize minimalDepth h 26 X = L at hA1 hA2 hle hpos hmin ⊢
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  simp only [AdmissibleDepth, Nat.add_sub_cancel, not_and, not_le] at hmin
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
  have h27 : h + 27 ≤ k + 1 := by
    by_contra hcon
    have hk : k + 1 = h + 26 := by omega
    rw [hk] at hA2
    omega
  have hcase := hmin (by omega)
  refine ⟨by omega, by omega, ?_, by omega⟩
  rw [hpow]
  omega

/-! ## A fibre is a set of primes, and its phase is affine in the prime -/

/-- At the base `mp - t` of a supplier prime `p` of `m`, the pivot phase is
`pivotPrimePhase h L s m p`. -/
theorem pivotPhaseAt_baseOfPrime (h : ℕ) {X L s m p : ℕ} (hm : 0 < m)
    (hmsmall : m ≤ Nat.sqrt X / 2) (hp : p ∈ pivotSupplierPrimes X L s m) :
    pivotPhaseAt h (pivotBaseOfPrime L s m p) L s = pivotPrimePhase h L s m p := by
  obtain ⟨_, hpp, hlo, _⟩ := Finset.mem_filter.mp hp
  have ht1 : 1 ≤ pivotOffset L s := by unfold pivotOffset; omega
  have hmp : m < p := by
    by_contra hcon
    have h1 : m * p ≤ m * m := Nat.mul_le_mul_left m (by omega)
    have h2 : m ≤ Nat.sqrt X := le_trans hmsmall (Nat.div_le_self _ _)
    have h3 : m * m ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul h2 h2
    have h4 := Nat.sqrt_le X
    omega
  have ht_le : pivotOffset L s ≤ m * p := by omega
  have harg : pivotArgument (pivotBaseOfPrime L s m p) L s = m * p := by
    simp only [pivotArgument, pivotBaseOfPrime]
    exact Nat.sub_add_cancel ht_le
  have hpivot := pivotPrime_eq_of_argument_eq_mul_prime hm hpp hmp harg
  have hcof := pivotCofactor_eq_of_argument_eq_mul_prime hm hpp hmp harg
  unfold pivotPhaseAt
  rw [hpivot, hcof]

/-- **A fibre mean is a mean over primes.** For `0 < m ≤ ⌊√X⌋/2`, the fibre mean of `m` is the
mean of `pivotPrimePhase h L s m p` over the supplier primes `p` of `m`. -/
theorem pivotFiberMean_eq_sum_primes (h : ℕ) {X L s m : ℕ} (hm : 0 < m)
    (hmsmall : m ≤ Nat.sqrt X / 2) :
    pivotFiberMean h X L s m =
      ((pivotSupplierPrimes X L s m).card : ℂ)⁻¹ *
        ∑ p ∈ pivotSupplierPrimes X L s m, pivotPrimePhase h L s m p := by
  have hinj : Set.InjOn (pivotBaseOfPrime L s m) (pivotSupplierPrimes X L s m : Set ℕ) :=
    fun p hp q hq heq => pivotBaseOfPrime_injective_on_supplierPrimes hm
      (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hq) heq
  rw [pivotFiberMean, ← image_pivotSupplierPrimes_eq_pivotFiber (L := L) (s := s) hm hmsmall,
    Finset.card_image_of_injOn hinj, Finset.sum_image hinj]
  congr 1
  exact Finset.sum_congr rfl (fun p hp => pivotPhaseAt_baseOfPrime h hm hmsmall hp)

/-- The supplier primes of `m` are the primes of `[⌈(X + t)/m⌉, ⌈(2X + t)/m⌉)`,
`t = pivotOffset L s`. -/
theorem pivotSupplierPrimes_eq_filter_Ico {X L s m : ℕ} (hm : 0 < m) :
    pivotSupplierPrimes X L s m =
      (Finset.Ico ((X + pivotOffset L s + m - 1) / m)
        ((2 * X + pivotOffset L s + m - 1) / m)).filter Nat.Prime := by
  ext p
  simp only [pivotSupplierPrimes, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  have h1 := Nat.div_le_iff_le_mul_add_pred (a := X + pivotOffset L s + m - 1) (c := p) hm
  have h2 := Nat.div_le_iff_le_mul_add_pred (a := 2 * X + pivotOffset L s + m - 1) (c := p) hm
  have hp : p ≤ m * p := Nat.le_mul_of_pos_left p hm
  constructor
  · rintro ⟨_, hpp, hlo, hhi⟩
    refine ⟨⟨h1.mpr (by omega), ?_⟩, hpp⟩
    by_contra hcon
    have := h2.mp (not_lt.mp hcon)
    omega
  · rintro ⟨⟨hlo, hhi⟩, hpp⟩
    have hlo' := h1.mp hlo
    have hhi' : m * p < 2 * X + pivotOffset L s := by
      by_contra hcon
      exact absurd (h2.mpr (by omega)) (not_le.mpr hhi)
    exact ⟨by omega, hpp, by omega, hhi'⟩

/-- At `s = 26` the pivot angle is affine in the prime: `θ p - θ` with
`θ = π (2^h - 1) φ(m) / 2^(L - 26)`. -/
theorem pivotPrimeAngle_eq_affine {h L m p : ℕ} {θ : ℝ}
    (hθ : θ = Real.pi * ((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) / (2 : ℝ) ^ (L - 26)) :
    pivotPrimeAngle h L 26 m p = θ * p - θ := by
  rw [pivotPrimeAngle, hθ]
  ring

/-- `⌈(X + t)/m⌉ ≥ 2⌊√X⌋` when `0 < m ≤ ⌊√X⌋/2`. -/
theorem two_sqrt_le_ceil {X t m : ℕ} (hm : 0 < m) (hmsmall : m ≤ Nat.sqrt X / 2) :
    2 * Nat.sqrt X ≤ (X + t + m - 1) / m := by
  rw [Nat.le_div_iff_mul_le hm]
  have h1 : Nat.sqrt X * (2 * m) ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul_left _ (by omega)
  have h2 : 2 * Nat.sqrt X * m = Nat.sqrt X * (2 * m) := by ring
  have h3 := Nat.sqrt_le X
  omega

/-! ## The fibre mean at one large `X` -/

/-- **One fibre at one large `X`.** The fibre mean of a cofactor `m ≤ ⌊√X⌋/2` with
`φ(m) ≥ m/1000` is at most `1/100`, given the bounds on the depth `L`, a lower bound on `⌊√X⌋`,
and prime counts `|π(y) log A - y| ≤ δ A` on `[A, 4A]`, `A = ⌈(X + t)/m⌉`, with
`δ = 1/(8000 · 2^(h+35))`. -/
theorem fiberMean_le_at {h X m L A B : ℕ} {δ : ℝ} (hh : 0 < h) (hm : 0 < m)
    (hmsmall : m ≤ Nat.sqrt X / 2)
    (hgood : (1 / 1000 : ℝ) * (m : ℝ) ≤ (Nat.totient m : ℝ))
    (hL26 : h + 26 ≤ L) (hL32 : 32 * X ≤ 2 ^ L) (hL96 : 2 ^ L < 96 * X)
    (hLlog : L ≤ h + 36 + Nat.log 2 X) (hX2 : 4 * h + 64 ≤ X)
    (hS : 2 ^ (h + 35) + 100 ≤ Nat.sqrt X)
    (hA : A = (X + pivotOffset L 26 + m - 1) / m)
    (hB : B = (2 * X + pivotOffset L 26 + m - 1) / m)
    (hδ : δ * (8000 * (2 : ℝ) ^ (h + 35)) = 1) (hδ0 : 0 ≤ δ)
    (hcount : ∀ y : ℕ, A ≤ y → y ≤ 4 * A →
      |(Nat.count Nat.Prime y : ℝ) * Real.log (A : ℝ) - (y : ℝ)| ≤ δ * (A : ℝ))
    (hlogA : 4000 * (2 : ℝ) ^ (h + 35) * Real.log (A : ℝ) ≤ (A : ℝ)) :
    ‖pivotFiberMean h X L 26 m‖ ≤ 1 / 100 := by
  have hK0 : 0 < 2 ^ (h + 35) := pow_pos (by norm_num) _
  have ht1 : 1 ≤ pivotOffset L 26 := by unfold pivotOffset; omega
  have ht2 : pivotOffset L 26 ≤ h + 11 + Nat.log 2 X := by unfold pivotOffset; omega
  have hlog4 : 4 * Nat.log 2 X ≤ X := four_mul_log_two_le (by omega)
  have hSS : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
  have h2m : 2 * m ≤ Nat.sqrt X := by omega
  have hS100 : 100 * Nat.sqrt X ≤ X := by
    have : 100 * Nat.sqrt X ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul_right _ (by omega)
    omega
  have hA1 : A * m ≤ X + pivotOffset L 26 + m - 1 := by
    rw [hA]; exact Nat.div_mul_le_self _ _
  have hA2 : X + pivotOffset L 26 ≤ A * m := by
    have := Nat.lt_div_mul_add (a := X + pivotOffset L 26 + m - 1) hm
    rw [← hA] at this
    omega
  have hB1 : B * m ≤ 2 * X + pivotOffset L 26 + m - 1 := by
    rw [hB]; exact Nat.div_mul_le_self _ _
  have hB2 : 2 * X + pivotOffset L 26 ≤ B * m := by
    have := Nat.lt_div_mul_add (a := 2 * X + pivotOffset L 26 + m - 1) hm
    rw [← hB] at this
    omega
  have hAB : A ≤ B := Nat.le_of_mul_le_mul_right (by omega : A * m ≤ B * m) hm
  obtain ⟨W, hW⟩ : ∃ W, B = A + W := ⟨B - A, by omega⟩
  have hWm : B * m = A * m + W * m := by rw [hW]; ring
  have hWup : W * m + 1 ≤ X + m := by omega
  have hWlo : X + 1 ≤ W * m + m := by omega
  have hA2S : 2 * Nat.sqrt X ≤ A := by
    apply Nat.le_of_mul_le_mul_right _ hm
    have h1 : Nat.sqrt X * (2 * m) ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul_left _ h2m
    have h2 : 2 * Nat.sqrt X * m = Nat.sqrt X * (2 * m) := by ring
    omega
  have hA2W : A ≤ 2 * W := by
    apply Nat.le_of_mul_le_mul_right _ hm
    have h2 : 2 * W * m = 2 * (W * m) := by ring
    omega
  have hW3A : W ≤ 3 * A := by
    apply Nat.le_of_mul_le_mul_right _ hm
    have h2 : 3 * A * m = 3 * (A * m) := by ring
    omega
  have hKW : 2 ^ (h + 35) ≤ W := by omega
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = W / 2 ^ (h + 35) := ⟨_, rfl⟩
  have hℓK : ℓ * 2 ^ (h + 35) ≤ W := by rw [hℓ]; exact Nat.div_mul_le_self _ _
  have hℓK' : W < ℓ * 2 ^ (h + 35) + 2 ^ (h + 35) := by
    rw [hℓ]; exact Nat.lt_div_mul_add hK0
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Nat.le_div_iff_mul_le hK0]; omega
  have hKℓ : 2 ^ (h + 35) ≤ ℓ * 2 ^ (h + 35) := Nat.le_mul_of_pos_left _ hℓ1
  have hcomm : 2 ^ (h + 35) * ℓ = ℓ * 2 ^ (h + 35) := Nat.mul_comm _ _
  have hA4 : A ≤ 4 * (ℓ * 2 ^ (h + 35)) := by omega
  have hab : A + 2 ^ (h + 35) * ℓ ≤ B := by omega
  have hbb : B ≤ A + 2 ^ (h + 35) * ℓ + 2 ^ (h + 35) := by omega
  -- real facts
  have hφhi : (Nat.totient m : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hφpos : 0 < Nat.totient m := Nat.totient_pos.mpr hm
  have hφ1 : (1 : ℝ) ≤ Nat.totient m := by exact_mod_cast (show 1 ≤ Nat.totient m by omega)
  have hH : (2 : ℝ) ≤ (2 : ℝ) ^ h := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ h by omega)
    rwa [pow_one] at this
  have hWupR : (W : ℝ) * m ≤ 2 * X := by
    have : W * m ≤ 2 * X := by omega
    exact_mod_cast this
  have hWloR : 99 / 100 * (X : ℝ) ≤ (W : ℝ) * m := by
    have : 99 * X ≤ 100 * (W * m) := by omega
    have h' : (99 : ℝ) * X ≤ 100 * ((W : ℝ) * m) := by exact_mod_cast this
    linarith
  have hP0 : (0 : ℝ) < (2 : ℝ) ^ (L - 26) := by positivity
  have hP26 : (2 : ℝ) ^ (L - 26) * 67108864 = (2 : ℝ) ^ L := by
    rw [show (67108864 : ℝ) = 2 ^ 26 by norm_num, ← pow_add,
      Nat.sub_add_cancel (by omega : 26 ≤ L)]
  have hL32R : 32 * (X : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hL32
  have hL96R : (2 : ℝ) ^ L < 96 * (X : ℝ) := by exact_mod_cast hL96
  have hKR : ((2 ^ (h + 35) : ℕ) : ℝ) = (2 : ℝ) ^ h * 34359738368 := by
    push_cast
    ring
  have hℓKR : (ℓ : ℝ) * ((2 ^ (h + 35) : ℕ) : ℝ) ≤ W := by exact_mod_cast hℓK
  have hWℓKR : (W : ℝ) ≤ 2 * ((ℓ : ℝ) * ((2 ^ (h + 35) : ℕ) : ℝ)) := by
    have : W ≤ 2 * (ℓ * 2 ^ (h + 35)) := by omega
    exact_mod_cast this
  obtain ⟨hθ0, hθℓ, hKθℓ⟩ := theta_param_bounds
    (θ := Real.pi * ((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) / (2 : ℝ) ^ (L - 26))
    hgood hφhi hφ1 hH hWupR hWloR (Nat.cast_nonneg W) hP0 (by linarith) (by linarith)
    (div_mul_cancel₀ _ hP0.ne') hKR hℓKR hWℓKR
  have hθℓ0 : 0 < Real.pi * ((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) / (2 : ℝ) ^ (L - 26)
      * (ℓ : ℝ) := mul_pos hθ0 (by exact_mod_cast (show 0 < ℓ by omega))
  have hlogA0 : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hν : 1000 ≤ (ℓ : ℝ) / Real.log (A : ℝ) := by
    rw [le_div_iff₀ hlogA0]
    have h1 : (A : ℝ) ≤ 4 * ((ℓ : ℝ) * (2 : ℝ) ^ (h + 35)) := by exact_mod_cast hA4
    have hKpos : (0 : ℝ) < 4 * (2 : ℝ) ^ (h + 35) := by positivity
    have h2 : 4 * (2 : ℝ) ^ (h + 35) * (1000 * Real.log (A : ℝ))
        ≤ 4 * (2 : ℝ) ^ (h + 35) * (ℓ : ℝ) := by linarith
    exact le_of_mul_le_mul_left h2 hKpos
  have hblock : ∀ k < 2 ^ (h + 35),
      |(((Finset.Ico (A + k * ℓ) (A + k * ℓ + ℓ)).filter Nat.Prime).card : ℝ)
          - (ℓ : ℝ) / Real.log (A : ℝ)| ≤ 1 / 1000 * ((ℓ : ℝ) / Real.log (A : ℝ)) := by
    intro k hk
    have hk1 : A + k * ℓ + ℓ ≤ A + 2 ^ (h + 35) * ℓ := by
      have h1 : (k + 1) * ℓ ≤ 2 ^ (h + 35) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
      have h2 : (k + 1) * ℓ = k * ℓ + ℓ := by ring
      omega
    have hy1 := hcount (A + k * ℓ) (by omega) (by omega)
    have hy2 := hcount (A + k * ℓ + ℓ) (by omega) (by omega)
    have hsplit := count_add_card_filter_Ico Nat.Prime
      (show A + k * ℓ ≤ A + k * ℓ + ℓ by omega)
    have hsplitR : (Nat.count Nat.Prime (A + k * ℓ) : ℝ)
        + (((Finset.Ico (A + k * ℓ) (A + k * ℓ + ℓ)).filter Nat.Prime).card : ℝ)
        = (Nat.count Nat.Prime (A + k * ℓ + ℓ) : ℝ) := by exact_mod_cast hsplit
    have e : (((A + k * ℓ + ℓ : ℕ) : ℝ)) = ((A + k * ℓ : ℕ) : ℝ) + (ℓ : ℝ) :=
      Nat.cast_add _ _
    have hy2' : |(Nat.count Nat.Prime (A + k * ℓ + ℓ) : ℝ) * Real.log (A : ℝ)
        - (((A + k * ℓ : ℕ) : ℝ) + (ℓ : ℝ))| ≤ δ * (A : ℝ) := by
      rw [← e]
      exact hy2
    refine block_count_core hlogA0 hsplitR hy1 hy2' ?_
    have h1 : (A : ℝ) ≤ 4 * ((ℓ : ℝ) * (2 : ℝ) ^ (h + 35)) := by exact_mod_cast hA4
    have h4 : δ * (A : ℝ) ≤ δ * (4 * ((ℓ : ℝ) * (2 : ℝ) ^ (h + 35))) :=
      mul_le_mul_of_nonneg_left h1 hδ0
    have h5 : δ * (8000 * (2 : ℝ) ^ (h + 35)) * (ℓ : ℝ) = 1 * (ℓ : ℝ) := by rw [hδ]
    linarith
  rw [pivotFiberMean_eq_sum_primes h hm hmsmall, pivotSupplierPrimes_eq_filter_Ico hm,
    ← hA, ← hB]
  have hphase : ∀ p : ℕ, pivotPrimePhase h L 26 m p =
      Complex.exp (((Real.pi * ((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) / (2 : ℝ) ^ (L - 26)
          * (p : ℝ)
        - Real.pi * ((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) / (2 : ℝ) ^ (L - 26) : ℝ) : ℂ)
          * Complex.I) := by
    intro p
    rw [pivotPrimePhase, pivotPrimeAngle_eq_affine (h := h) (L := L) (m := m) (p := p) rfl]
  simp only [hphase]
  exact norm_mean_le_of_blocks hK0 hθ0 hθℓ0 hθℓ hKθℓ hν hab hbb hblock

end FiberMean

open FiberMean

/-- **The fibre means are small, from the prime number theorem.** At the minimal depth with
`s = 26` and `η = 1/1000`, for every `h ≥ 1` and all large `X`, every good base `N` has
`‖pivotFiberMean h X L 26 m_N‖ ≤ 1/100`. This is the `hmean` hypothesis of
`dtw_of_fiberMean_and_centered`. -/
theorem fiberMean_le_of_primeNumberTheorem (hPNT : PrimeNumberTheorem) :
    ∀ h : ℕ, 0 < h → ∀ᶠ X : ℕ in Filter.atTop,
      ∀ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        ‖pivotFiberMean h X (minimalDepth h 26 X) 26
            (pivotCofactor N (minimalDepth h 26 X) 26)‖ ≤ (1 / 100 : ℝ) := by
  intro h hh
  have hδ0 : (0 : ℝ) < 1 / (8000 * (2 : ℝ) ^ (h + 35)) := by positivity
  have hδ1 : 1 / (8000 * (2 : ℝ) ^ (h + 35)) ≤ 1 := by
    rw [div_le_one (show (0 : ℝ) < 8000 * (2 : ℝ) ^ (h + 35) by positivity)]
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (h + 35) := one_le_pow₀ (by norm_num)
    linarith
  obtain ⟨Y₀, hY₀⟩ := exists_count_log_discrepancy hPNT hδ0 hδ1
  have hc : (0 : ℝ) < 1 / (4000 * (2 : ℝ) ^ (h + 35)) := by positivity
  have hev : ∀ᶠ A : ℕ in atTop,
      Real.log (A : ℝ) + 0 ≤ 1 / (4000 * (2 : ℝ) ^ (h + 35)) * (A : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_log_add_le hc 0)
  have hA₂ : ∀ᶠ A : ℕ in atTop, 4000 * (2 : ℝ) ^ (h + 35) * Real.log (A : ℝ) ≤ (A : ℝ) := by
    filter_upwards [hev] with A hA
    have hK0 : (0 : ℝ) < 4000 * (2 : ℝ) ^ (h + 35) := by positivity
    have h1 : Real.log (A : ℝ) ≤ 1 / (4000 * (2 : ℝ) ^ (h + 35)) * A := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hK0.le
    have h3 : 4000 * (2 : ℝ) ^ (h + 35) * (1 / (4000 * (2 : ℝ) ^ (h + 35)) * (A : ℝ))
        = A := by
      rw [← mul_assoc, mul_one_div_cancel hK0.ne', one_mul]
    linarith
  obtain ⟨A₂, hA₂'⟩ := eventually_atTop.mp hA₂
  filter_upwards [eventually_ge_atTop (2 ^ (h + 22)), eventually_ge_atTop (4 * h + 64),
    eventually_ge_atTop ((Y₀ + A₂ + 2 ^ (h + 35) + 100) * (Y₀ + A₂ + 2 ^ (h + 35) + 100))]
    with X hX1 hX2 hX3
  intro N hN
  have hNsup : N ∈ pivotSupplierBases X (minimalDepth h 26 X) 26 := (Finset.mem_filter.mp hN).1
  have hgood : (1 / 1000 : ℝ) * (pivotCofactor N (minimalDepth h 26 X) 26 : ℝ)
      ≤ (Nat.totient (pivotCofactor N (minimalDepth h 26 X) 26) : ℝ) :=
    (Finset.mem_filter.mp hN).2
  obtain ⟨hm0, hmM⟩ := pivotCofactor_pos_le hNsup
  obtain ⟨hL26, hL32, hL96, hLlog⟩ := minimalDepth_geometry hh hX1 hX2
  have hK0 : 0 < 2 ^ (h + 35) := pow_pos (by norm_num) _
  have hS : Y₀ + A₂ + 2 ^ (h + 35) + 100 ≤ Nat.sqrt X := Nat.le_sqrt.mpr hX3
  have hA2S := two_sqrt_le_ceil (t := pivotOffset (minimalDepth h 26 X) 26) hm0 hmM
  have hδ : 1 / (8000 * (2 : ℝ) ^ (h + 35)) * (8000 * (2 : ℝ) ^ (h + 35)) = 1 :=
    one_div_mul_cancel (by positivity)
  exact fiberMean_le_at hh hm0 hmM hgood hL26 hL32 hL96 hLlog hX2 (by omega) rfl rfl hδ hδ0.le
    (hY₀ _ (by omega)) (hA₂' _ (by omega))

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.FiberMean.norm_mean_le_of_blocks
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.FiberMean.exists_count_log_discrepancy
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.FiberMean.minimalDepth_geometry
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.FiberMean.pivotFiberMean_eq_sum_primes
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.fiberMean_le_of_primeNumberTheorem


/-!
# Erdős #249: the pivot decorrelation from two of its clauses

`DTWPivotResidualDecorrelation` (`FirstHarmonicPivot`, demand `G064` of the demand ledger)
asks, for every `h`, for parameters at which the two depth conditions and the four clauses of
`PivotBudgetAt` hold together, and it implies the irrationality of `∑ φ(n) / 2 ^ n`. The finite
bridge `pivotBudgetAt_of_peripheral_estimates` reduces three of the clauses to a uniform
fibre-mean bound, a count of bad bases and a count of non-supplier bases.

At the minimal depth, with `s = 26` and `η = 1/1000`, two proofs that do not mention the
decorrelation supply most of this. `prop_dickman` gives the two depth conditions and, for all
large `X`, fewer than `8X/25` non-supplier bases, with no hypothesis. The argument graph's
frontier of `prop_badcof` showed that its proof uses the prime number theorem only through a
dyadic prime count, which Chebyshev's bound supplies:
`excluded_budget_one_thousandth_of_chebyshev` gives fewer than `X/100` bad bases for all large
`X`, with no hypothesis. The two theorems below state what remains: the fibre means and the
centred correlation.
-/

open Filter

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor

/-- The bad-base clause, read off the excluded-cofactor count. -/
theorem card_pivotBadBases_le_of_count (h X : ℕ)
    (hcount : ((((pivotSupplierBases X (minimalDepth h 26 X) 26).filter
        (fun N => pivotCofactor N (minimalDepth h 26 X) 26
          ∈ excludedCofactorSet (1 / 1000))).card : ℕ) : ℝ) < (1 / 100 : ℝ) * X) :
    ((pivotBadBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card : ℝ)
      ≤ (1 / 100 : ℝ) * X := by
  rw [← filter_excluded_eq_pivotBadBases]
  exact hcount.le

/-- **The decorrelation from its fibre-mean and centred clauses.** At the minimal depth, with
`s = 26` and `η = 1/1000`, `prop_dickman` supplies the depth conditions and the non-supplier
count and `excluded_budget_one_thousandth_of_chebyshev` the bad-base count. -/
theorem dtw_of_fiberMean_and_centered
    (hmean : ∀ h : ℕ, 0 < h → ∀ᶠ X : ℕ in atTop,
      ∀ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        ‖pivotFiberMean h X (minimalDepth h 26 X) 26
            (pivotCofactor N (minimalDepth h 26 X) 26)‖ ≤ (1 / 100 : ℝ))
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    DTWPivotResidualDecorrelation := by
  intro h hh
  refine ⟨26, by norm_num, (1 / 1000 : ℝ), by norm_num, by norm_num, ?_⟩
  intro X₀
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp (hmean h hh)
  obtain ⟨A₂, hA₂⟩ := eventually_atTop.mp (excluded_budget_one_thousandth_of_chebyshev h 26)
  obtain ⟨A₃, hA₃⟩ := eventually_atTop.mp (prop_dickman h 26).2.2.2.2.2
  obtain ⟨X, hX, hc⟩ := hcentered h hh (max X₀ (max A₁ (max A₂ A₃)))
  simp only [max_le_iff] at hX
  obtain ⟨⟨hX₀, hXA₁, hXA₂, hXA₃⟩, hX1⟩ := hX
  have hadm : h ≤ minimalDepth h 26 X - 26 ∧
      16 * (2 * X + h + minimalDepth h 26 X + 2) ≤ 2 ^ minimalDepth h 26 X :=
    ((prop_dickman h 26).1 X).1
  refine ⟨X, minimalDepth h 26 X, max_le hX₀ hX1, hadm.1, hadm.2, ?_⟩
  refine pivotBudgetAt_of_peripheral_estimates h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)
    hc (hA₁ X hXA₁) ?_ ?_
  · exact card_pivotBadBases_le_of_count h X (hA₂ X hXA₂).1
  · have hnon := (hA₃ X hXA₃).2
    simpa [filter_not_mem_pivotSupplierBases] using hnon.le

/-- **The irrationality of `∑ φ(n) / 2 ^ n` from the fibre means and the centred
correlation**, at the minimal depth with `s = 26` and `η = 1/1000`. -/
theorem irrational_totient_series_of_fiberMean_and_centered
    (hmean : ∀ h : ℕ, 0 < h → ∀ᶠ X : ℕ in atTop,
      ∀ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        ‖pivotFiberMean h X (minimalDepth h 26 X) 26
            (pivotCofactor N (minimalDepth h 26 X) 26)‖ ≤ (1 / 100 : ℝ))
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotResidualDecorrelation
    (dtw_of_fiberMean_and_centered hmean hcentered)

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dtw_of_fiberMean_and_centered
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_fiberMean_and_centered


/-!
# Erdős #249: the first-harmonic route, given the prime number theorem

`Results/Erdos249.lean` reduces `DTWPivotResidualDecorrelation`, at the minimal depth with
`s = 26` and `η = 1/1000`, to two clauses: a uniform bound on the fibre means and the centred
correlation. `fiberMean_le_of_primeNumberTheorem` proves the first from the prime number
theorem.

The second is the first-harmonic gap on the good bases. There the first harmonic factors as the
residual times the pivot phase, so its sum over the good bases is the centred correlation plus
the fibre-mean contribution (`goodBase_sum_eq_centered_add_mean`). With every fibre mean at most
`1/100` the two conditions differ by at most `X/100` either way: the good-base gap at `11X/20`
gives the centred clause (`centered_re_le_of_goodBase_gap`), and the centred clause gives the
good-base gap at `57X/100` (`goodBase_gap_of_centered_re_le`).

Hence, given the prime number theorem, the irrationality of `∑ φ(n)/2^n` follows once, for every
`h ≥ 1`, there are arbitrarily large `X` at which the real part of the first harmonic summed over
the good bases is at most `11X/20`
(`irrational_totient_series_of_primeNumberTheorem_and_goodBase_gap`). The non-supplier and bad
bases, about a third of `[X, 2X)`, are handled unconditionally by `prop_dickman` and Chebyshev's
bound.
-/

open Filter

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos251.PaperR11.PrimeSource (PrimeNumberTheorem)
open Finset

/-- The good-base first harmonic is the centred correlation plus the fibre-mean
contribution. -/
theorem goodBase_sum_eq_centered_add_mean (h X L s : ℕ) (η : ℝ) :
    (∑ N ∈ pivotGoodBases X L s η, windowFirstExp h N L) =
      pivotCenteredCorrelation h X L s η + pivotFiberMeanContribution h X L s η := by
  rw [pivotCenteredCorrelation, pivotFiberMeanContribution, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _
  rw [windowFirstExp_eq_pivotResidualAt_mul_phase]
  ring

/-- With fibre means at most `1/100`, the good-base gap at `11X/20` gives the centred
clause. -/
theorem centered_re_le_of_goodBase_gap {h X L s : ℕ} {η : ℝ}
    (hmean : ∀ N ∈ pivotGoodBases X L s η,
      ‖pivotFiberMean h X L s (pivotCofactor N L s)‖ ≤ (1 / 100 : ℝ))
    (hgap : (∑ N ∈ pivotGoodBases X L s η, windowFirstExp h N L).re ≤ (11 / 20 : ℝ) * X) :
    (pivotCenteredCorrelation h X L s η).re ≤ (14 / 25 : ℝ) * X := by
  have hsplit := congrArg Complex.re (goodBase_sum_eq_centered_add_mean h X L s η)
  rw [Complex.add_re] at hsplit
  have hfm := norm_pivotFiberMeanContribution_le_of_uniform h X L s η (1 / 100)
    (by norm_num) hmean
  have hre := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) hfm)).1
  linarith

/-- Conversely the centred clause gives the good-base gap at `57X/100`: on the good bases the
centred clause asks for nothing beyond the first-harmonic gap. -/
theorem goodBase_gap_of_centered_re_le {h X L s : ℕ} {η : ℝ}
    (hmean : ∀ N ∈ pivotGoodBases X L s η,
      ‖pivotFiberMean h X L s (pivotCofactor N L s)‖ ≤ (1 / 100 : ℝ))
    (hc : (pivotCenteredCorrelation h X L s η).re ≤ (14 / 25 : ℝ) * X) :
    (∑ N ∈ pivotGoodBases X L s η, windowFirstExp h N L).re ≤ (57 / 100 : ℝ) * X := by
  have hsplit := congrArg Complex.re (goodBase_sum_eq_centered_add_mean h X L s η)
  rw [Complex.add_re] at hsplit
  have hfm := norm_pivotFiberMeanContribution_le_of_uniform h X L s η (1 / 100)
    (by norm_num) hmean
  have hre := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) hfm)).2
  linarith

/-- At the minimal depth with `s = 26` and `η = 1/1000`: eventual fibre means and a cofinal
good-base gap at `11X/20` give the cofinal centred clause of `dtw_of_fiberMean_and_centered`. -/
theorem centered_of_fiberMean_and_goodBase_gap
    (hmean : ∀ h : ℕ, 0 < h → ∀ᶠ X : ℕ in atTop,
      ∀ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        ‖pivotFiberMean h X (minimalDepth h 26 X) 26
            (pivotCofactor N (minimalDepth h 26 X) 26)‖ ≤ (1 / 100 : ℝ))
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (11 / 20 : ℝ) * X) :
    ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X := by
  intro h hh A
  obtain ⟨A₁, hA₁⟩ := eventually_atTop.mp (hmean h hh)
  obtain ⟨X, hX, hg⟩ := hgap h hh (max A A₁)
  have hmax : max (max A A₁) 1 ≤ X := hX
  refine ⟨X, le_trans (max_le_max (le_max_left A A₁) le_rfl) hmax, ?_⟩
  have hA₁X : A₁ ≤ X := le_trans (le_trans (le_max_right A A₁) (le_max_left _ _)) hmax
  exact centered_re_le_of_goodBase_gap (hA₁ X hA₁X) hg

/-- **The decorrelation from the prime number theorem and the centred clause.** -/
theorem dtw_of_primeNumberTheorem_and_centered (hPNT : PrimeNumberTheorem)
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    DTWPivotResidualDecorrelation :=
  dtw_of_fiberMean_and_centered (fiberMean_le_of_primeNumberTheorem hPNT) hcentered

/-- **The irrationality of `∑ φ(n) / 2 ^ n` from the prime number theorem and the centred
clause.** -/
theorem irrational_totient_series_of_primeNumberTheorem_and_centered (hPNT : PrimeNumberTheorem)
    (hcentered : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (pivotCenteredCorrelation h X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).re
        ≤ (14 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_pivotResidualDecorrelation
    (dtw_of_primeNumberTheorem_and_centered hPNT hcentered)

/-- **The irrationality of `∑ φ(n) / 2 ^ n` from the prime number theorem and a first-harmonic
gap on the good bases**: for every `h ≥ 1`, arbitrarily large `X` at which the real part of the
first harmonic summed over the good bases is at most `11X/20`. -/
theorem irrational_totient_series_of_primeNumberTheorem_and_goodBase_gap
    (hPNT : PrimeNumberTheorem)
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (11 / 20 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_primeNumberTheorem_and_centered hPNT
    (centered_of_fiberMean_and_goodBase_gap (fiberMean_le_of_primeNumberTheorem hPNT) hgap)

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.goodBase_sum_eq_centered_add_mean
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.centered_re_le_of_goodBase_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.goodBase_gap_of_centered_re_le
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.dtw_of_primeNumberTheorem_and_centered
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_primeNumberTheorem_and_goodBase_gap
