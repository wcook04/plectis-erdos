import ErdosProblems.Erdos251.PrimeGapDyadicTail

/-!
# Bounded perturbations of dyadic digit series

For a natural-digit dyadic series with sum `S`, every positive integer `M`,
every cutoff `K`, and every real `r` satisfying `S < r < S + M / 2^K`, binary
digits `δ_n` can be chosen so that

    Σ_{n ≥ 0} (g_n + M δ_n) / 2^{n+1} = r,

with `δ_n = 0` for `n < K`. The construction takes the binary expansion of
`(r-S)/M`: its first `K` digits vanish, and its finite floor telescope converges
to that number. Density of the rationals then supplies a rational perturbed
series, including when the original digits are the consecutive prime gaps.

Each modified gap is between `g_n` and `g_n + M`, agrees with `g_n` modulo
`M`, and leaves the prescribed initial segment unchanged. Consequently a
property preserved under all these perturbations cannot, by itself, imply
irrationality. The modified digits need not be prime gaps; the theorem makes
no assertion about the rationality of the original prime-gap series.
-/

open Filter Topology Finset

namespace ErdosProblems.Erdos251

/-! ## Binary digits of a real number -/

/-- The `n`th binary digit (after the point) of `D`: `⌊2^{n+1} D⌋ - 2⌊2^n D⌋`. -/
noncomputable def binaryDigit (D : ℝ) (n : ℕ) : ℤ :=
  ⌊(2 : ℝ) ^ (n + 1) * D⌋ - 2 * ⌊(2 : ℝ) ^ n * D⌋

theorem binaryDigit_nonneg (D : ℝ) (n : ℕ) : 0 ≤ binaryDigit D n := by
  unfold binaryDigit
  have h : (2 : ℤ) * ⌊(2 : ℝ) ^ n * D⌋ ≤ ⌊(2 : ℝ) ^ (n + 1) * D⌋ := by
    rw [Int.le_floor]
    push_cast
    have e : (2 : ℝ) ^ (n + 1) * D = 2 * ((2 : ℝ) ^ n * D) := by ring
    rw [e]
    linarith [Int.floor_le ((2 : ℝ) ^ n * D)]
  omega

theorem binaryDigit_le_one (D : ℝ) (n : ℕ) : binaryDigit D n ≤ 1 := by
  unfold binaryDigit
  have h : ⌊(2 : ℝ) ^ (n + 1) * D⌋ < 2 * ⌊(2 : ℝ) ^ n * D⌋ + 2 := by
    rw [Int.floor_lt]
    push_cast
    have e : (2 : ℝ) ^ (n + 1) * D = 2 * ((2 : ℝ) ^ n * D) := by ring
    rw [e]
    linarith [Int.lt_floor_add_one ((2 : ℝ) ^ n * D)]
  omega

/-- The finite telescope: `Σ_{n<N} δ_n/2^{n+1} = ⌊2^N D⌋/2^N - ⌊D⌋`. -/
theorem sum_binaryDigit_div (D : ℝ) (N : ℕ) :
    ∑ n ∈ range N, (binaryDigit D n : ℝ) / 2 ^ (n + 1)
      = (⌊(2 : ℝ) ^ N * D⌋ : ℝ) / 2 ^ N - (⌊D⌋ : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    unfold binaryDigit
    push_cast
    field_simp
    ring

theorem tendsto_floor_pow_mul_div (D : ℝ) :
    Tendsto (fun N : ℕ => (⌊(2 : ℝ) ^ N * D⌋ : ℝ) / 2 ^ N) atTop (𝓝 D) := by
  have hlow : ∀ N : ℕ, D - 1 / 2 ^ N ≤ (⌊(2 : ℝ) ^ N * D⌋ : ℝ) / 2 ^ N := by
    intro N
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    rw [le_div_iff₀ h2]
    have e : (D - 1 / 2 ^ N) * 2 ^ N = 2 ^ N * D - 1 := by
      rw [sub_mul, one_div, inv_mul_cancel₀ h2.ne']
      ring
    rw [e]
    linarith [Int.lt_floor_add_one ((2 : ℝ) ^ N * D)]
  have hup : ∀ N : ℕ, (⌊(2 : ℝ) ^ N * D⌋ : ℝ) / 2 ^ N ≤ D := by
    intro N
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    rw [div_le_iff₀ h2]
    have e : D * 2 ^ N = 2 ^ N * D := by ring
    rw [e]
    exact Int.floor_le ((2 : ℝ) ^ N * D)
  have h0 : Tendsto (fun N : ℕ => ((1 : ℝ) / 2) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / 2 ^ N) atTop (𝓝 0) := by
    simpa [one_div_pow] using h0
  have hlim : Tendsto (fun N : ℕ => D - 1 / (2 : ℝ) ^ N) atTop (𝓝 D) := by
    simpa using tendsto_const_nhds.sub h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup

/-- `Σ_{n ≥ 0} δ_n / 2^{n+1} = D` for `0 ≤ D < 1`. -/
theorem hasSum_binaryDigit (D : ℝ) (h0 : 0 ≤ D) (h1 : D < 1) :
    HasSum (fun n : ℕ => (binaryDigit D n : ℝ) / 2 ^ (n + 1)) D := by
  have hnn : ∀ n : ℕ, 0 ≤ (binaryDigit D n : ℝ) / 2 ^ (n + 1) := fun n =>
    div_nonneg (by exact_mod_cast binaryDigit_nonneg D n) (by positivity)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hfl : ⌊D⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  simp_rw [sum_binaryDigit_div, hfl]
  simpa using tendsto_floor_pow_mul_div D

/-! ## The perturbation -/

/-- **Bounded-perturbation countermodel, general form.**  If the natural-digit
dyadic series `Σ g_n/2^{n+1}` has sum `S`, then for every `M ≥ 1`, every real
`r` with `S < r < S + M/2^K`, there are digits `δ_n ∈ {0,1}`, vanishing for
`n < K`, with `Σ (g_n + M δ_n)/2^{n+1} = r`. -/
theorem exists_bounded_perturbation {g : ℕ → ℕ} {S : ℝ}
    (hS : HasSum (fun n => (g n : ℝ) / 2 ^ (n + 1)) S) (M : ℕ) (hM : 0 < M)
    (r : ℝ) (hr₁ : S < r) (K : ℕ) (hK : r < S + M / 2 ^ K) :
    ∃ δ : ℕ → ℕ, (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((g n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have hrs : (r - S) * 2 ^ K < M := by
    have : r - S < M / 2 ^ K := by linarith
    exact (lt_div_iff₀ h2K).mp this
  have hr₂ : r < S + M := by
    have hK1 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
    nlinarith
  set D : ℝ := (r - S) / M with hD
  have hD0 : 0 ≤ D := div_nonneg (by linarith) hMpos.le
  have hD1 : D < 1 := by rw [hD, div_lt_one hMpos]; linarith
  have hfloor : ∀ m, m ≤ K → ⌊(2 : ℝ) ^ m * D⌋ = 0 := by
    intro m hm
    rw [Int.floor_eq_zero_iff]
    refine ⟨mul_nonneg (by positivity) hD0, ?_⟩
    have h2m : (2 : ℝ) ^ m ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hm
    have hlt : (2 : ℝ) ^ K * D < 1 := by
      rw [hD, mul_div_assoc', div_lt_one hMpos]
      linarith
    calc (2 : ℝ) ^ m * D ≤ 2 ^ K * D := mul_le_mul_of_nonneg_right h2m hD0
      _ < 1 := hlt
  refine ⟨fun n => (binaryDigit D n).toNat, ?_, ?_, ?_⟩
  · intro n
    show (binaryDigit D n).toNat ≤ 1
    have := binaryDigit_le_one D n
    have := binaryDigit_nonneg D n
    omega
  · intro n hn
    show (binaryDigit D n).toNat = 0
    simp [binaryDigit, hfloor (n + 1) (by omega), hfloor n (by omega)]
  · have hcast : ∀ n, (((binaryDigit D n).toNat : ℕ) : ℝ) = (binaryDigit D n : ℝ) := by
      intro n
      have := binaryDigit_nonneg D n
      exact_mod_cast Int.toNat_of_nonneg this
    have h1 := hasSum_binaryDigit D hD0 hD1
    convert hS.add (h1.mul_left (M : ℝ)) using 1
    · funext n
      push_cast
      rw [hcast]
      ring
    · have hMD : (M : ℝ) * D = r - S := by
        rw [hD]
        field_simp
      linarith

/-! ## Rational targets and the invariant-property obstruction -/

/-- Any convergent natural-digit dyadic series admits a rational bounded
perturbation preserving the first `K` digits. -/
theorem exists_rational_bounded_perturbation {g : ℕ → ℕ} {S : ℝ}
    (hS : HasSum (fun n => (g n : ℝ) / 2 ^ (n + 1)) S)
    (M : ℕ) (hM : 0 < M) (K : ℕ) :
    ∃ (δ : ℕ → ℕ) (r : ℚ), (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((g n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hlt : S < S + M / 2 ^ K := by
    have : (0 : ℝ) < M / 2 ^ K := by positivity
    linarith
  obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn hlt
  obtain ⟨δ, h1, h2, h3⟩ := exists_bounded_perturbation hS M hM r hr₁ K hr₂
  exact ⟨δ, r, h1, h2, h3⟩

/-- If a property holds for every allowed bounded perturbation of one
convergent digit series after a fixed prefix, it cannot force irrationality.
The zero perturbation already includes the original series in this hypothesis. -/
theorem not_forall_irrational_of_bounded_perturbation_invariant
    {P : (ℕ → ℕ) → Prop} {g : ℕ → ℕ} {S : ℝ}
    (hS : HasSum (fun n => (g n : ℝ) / 2 ^ (n + 1)) S)
    (M : ℕ) (hM : 0 < M) (K : ℕ)
    (hP : ∀ δ : ℕ → ℕ, (∀ n, δ n ≤ 1) → (∀ n < K, δ n = 0) →
      P (fun n => g n + M * δ n)) :
    ¬ ∀ a : ℕ → ℕ, P a →
      Irrational (∑' n : ℕ, (a n : ℝ) / 2 ^ (n + 1)) := by
  intro hI
  obtain ⟨δ, r, h1, h2, hsum⟩ := exists_rational_bounded_perturbation hS M hM K
  have hirr := hI (fun n => g n + M * δ n) (hP δ h1 h2)
  rw [hsum.tsum_eq] at hirr
  exact Rat.not_irrational r hirr

/-! ## The actual prime gaps -/

/-- **Bounded-perturbation countermodel for the prime-gap series.**  For every
`M ≥ 1` and every `K`, there are digits `δ_n ∈ {0,1}`, zero for `n < K`, and a
rational `r` with `Σ (g_n + M δ_n)/2^{n+1} = r`, where `g_n` are the actual
consecutive prime gaps.  The perturbed gaps satisfy `g_n ≤ g_n + M δ_n ≤ g_n + M`
and `g_n + M δ_n ≡ g_n (mod M)` at every index. -/
theorem exists_rational_bounded_perturbation_primeGap (M : ℕ) (hM : 0 < M) (K : ℕ) :
    ∃ (δ : ℕ → ℕ) (r : ℚ), (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((primeGap0 n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  have hS : HasSum (fun n => (primeGap0 n : ℝ) / 2 ^ (n + 1))
      (∑' n, primeGapDyadicTerm n) := by
    have := summable_primeGapDyadicTerm.hasSum
    simpa [primeGapDyadicTerm] using this
  exact exists_rational_bounded_perturbation hS M hM K

/-- The perturbed prime-gap series is rational. -/
theorem not_irrational_bounded_perturbation_primeGap (M : ℕ) (hM : 0 < M) (K : ℕ) :
    ∃ δ : ℕ → ℕ, (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      ¬ Irrational (∑' n, ((primeGap0 n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) := by
  obtain ⟨δ, r, h1, h2, h3⟩ := exists_rational_bounded_perturbation_primeGap M hM K
  refine ⟨δ, h1, h2, ?_⟩
  rw [h3.tsum_eq]
  exact Rat.not_irrational r

/-- Pointwise form of the perturbation bounds, for the record: every perturbed
gap lies in `[g_n, g_n + M]` and is congruent to `g_n` modulo `M`. -/
theorem perturbed_gap_bounds (M : ℕ) (δ : ℕ → ℕ) (hδ : ∀ n, δ n ≤ 1) (n : ℕ) :
    primeGap0 n ≤ primeGap0 n + M * δ n ∧ primeGap0 n + M * δ n ≤ primeGap0 n + M ∧
      (primeGap0 n + M * δ n) % M = primeGap0 n % M := by
  refine ⟨Nat.le_add_right _ _, ?_, ?_⟩
  · have := hδ n
    nlinarith
  · simp [Nat.add_mul_mod_self_left]

#print axioms hasSum_binaryDigit
#print axioms exists_bounded_perturbation
#print axioms exists_rational_bounded_perturbation
#print axioms not_forall_irrational_of_bounded_perturbation_invariant
#print axioms exists_rational_bounded_perturbation_primeGap
#print axioms not_irrational_bounded_perturbation_primeGap

end ErdosProblems.Erdos251
