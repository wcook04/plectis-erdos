import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate

/-!
# Kernel probe: the `η = 1/1000` excluded-cofactor budget without the prime number theorem

Scratch file for the kernel-probe workflow.  The declarations below are the
additions proposed for `ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate`,
written in the namespaces and under the `open`s they would have there.

The prime number theorem enters `excluded_budget_one_thousandth` only through the
dyadic prime count `#{p prime : a < p ≤ 2a + 1} · log a ≤ (1 + ε) a`.  Chebyshev's
elementary bound gives the same count with `log 4` in place of `1`: the primes
`p` with `a + 1 < p ≤ 2a + 1` divide `C(2a + 1, a) ≤ 4 ^ a`
(`prod_primes_dyadic_le_four_pow`), so
`#{p prime : a < p ≤ 2a + 1} · log a ≤ a log 4 + log a` for every `a`
(`card_primes_dyadic_mul_log_le`).  The chain `fibre_card_le`,
`card_excluded_le_harmonic`, `excluded_final_arith` is linear in the dyadic
constant, so a constant `K` there gives the excluded count `(K D + o(1)) X`
(`eventually_card_excluded_le_of_upper_of_dyadic`; the prime number theorem is the
case `K = 1`), and the `X/100` budget whenever `K D < 1/100`
(`eventually_excluded_budget_of_upper_of_dyadic`).  With `K = log 4` and the
elementary density bound `D = 3/1000`, `K D ≤ 9/1000 < 1/100`
(`excluded_budget_one_thousandth_of_chebyshev`).
-/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos251.PaperR11.PrimeSource (PrimeNumberTheorem)
open Finset Filter Topology

open ExcludedCofactor

/-! ## The budget at `η = 1/1000` without the prime number theorem

The prime number theorem enters `excluded_budget_one_thousandth` only through the
dyadic count `eventually_card_primes_dyadic_le`.  Chebyshev's bound gives that count
with `log 4` in place of `1`: the primes `p` with `a + 1 < p ≤ 2a + 1` divide
`C(2a + 1, a) ≤ 4 ^ a` (`prod_primes_dyadic_le_four_pow`), so
`#{p prime : a < p ≤ 2a + 1} · log a ≤ a log 4 + log a` for every `a`
(`card_primes_dyadic_mul_log_le`).  Steps 2 to 4 of the proof are linear in the
constant of the dyadic count, so a constant `K` gives the excluded count
`(K D + o(1)) X` (`eventually_card_excluded_le_of_upper_of_dyadic`) and the `X/100`
budget whenever `K D < 1/100` (`eventually_excluded_budget_of_upper_of_dyadic`).
At `η = 1/1000`, `log 4 · 3/1000 ≤ 9/1000 < 1/100`
(`excluded_budget_one_thousandth_of_chebyshev`). -/

namespace ExcludedCofactor

/-- Chebyshev's product bound: the primes `p` with `a + 2 ≤ p ≤ 2a + 1` divide the
binomial coefficient `C(2a + 1, a + 1) = C(2a + 1, a) ≤ 4 ^ a`, so their product is
at most `4 ^ a` (Mathlib's `primorial_add_le` and `Nat.choose_middle_le_pow`). -/
theorem prod_primes_dyadic_le_four_pow (a : ℕ) :
    ∏ p ∈ (Ico (a + 2) (2 * a + 2)).filter Nat.Prime, p ≤ 4 ^ a := by
  have hle := primorial_add_le (m := a + 1) (n := a) (by omega)
  rw [primorial_add (a + 1) a, show a + 1 + 1 = a + 2 by omega,
    show a + 1 + a + 1 = 2 * a + 2 by omega, Nat.choose_symm_add,
    show a + 1 + a = 2 * a + 1 by omega] at hle
  exact le_trans (Nat.le_of_mul_le_mul_left hle (primorial_pos _)) (Nat.choose_middle_le_pow a)

/-- The dyadic prime count from Chebyshev's bound, for every `a`:
`#{p prime : a < p ≤ 2a + 1} · log a ≤ a log 4 + log a`.  The primes above `a + 1`
number at most `a log 4 / log (a + 2)` by `prod_primes_dyadic_le_four_pow`, and
`a + 1` is the one other candidate. -/
theorem card_primes_dyadic_mul_log_le (a : ℕ) :
    ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) * Real.log a
      ≤ a * Real.log 4 + Real.log a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hsub : (Ioc a (2 * a + 1)).filter Nat.Prime
      ⊆ insert (a + 1) ((Ico (a + 2) (2 * a + 2)).filter Nat.Prime) := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hap, hp2⟩ := Finset.mem_Ioc.mp hpI
    by_cases hpa : p = a + 1
    · exact Finset.mem_insert.mpr (Or.inl hpa)
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hpp⟩)
  have hcard : ((Ioc a (2 * a + 1)).filter Nat.Prime).card
      ≤ ((Ico (a + 2) (2 * a + 2)).filter Nat.Prime).card + 1 :=
    le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
  have hpow : (a + 2) ^ ((Ico (a + 2) (2 * a + 2)).filter Nat.Prime).card ≤ 4 ^ a := by
    refine le_trans (Finset.pow_card_le_prod _ (fun p => p) (a + 2) ?_)
      (prod_primes_dyadic_le_four_pow a)
    intro p hp
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
  have hpowR : ((a : ℝ) + 2) ^ ((Ico (a + 2) (2 * a + 2)).filter Nat.Prime).card
      ≤ (4 : ℝ) ^ a := by
    exact_mod_cast hpow
  have hlogP := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow, Real.log_pow] at hlogP
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hloga0 : 0 ≤ Real.log a := Real.log_nonneg haR
  have hloga2 : Real.log a ≤ Real.log ((a : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hcardR : ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ)
      ≤ (((Ico (a + 2) (2 * a + 2)).filter Nat.Prime).card : ℝ) + 1 := by
    exact_mod_cast hcard
  have h1 := mul_le_mul_of_nonneg_right hcardR hloga0
  have h2 := mul_le_mul_of_nonneg_left hloga2
    (Nat.cast_nonneg (α := ℝ) ((Ico (a + 2) (2 * a + 2)).filter Nat.Prime).card)
  linarith

/-- **Dyadic prime count from Chebyshev's bound.**  For every `ε > 0`, for all
large `a`, `#{p prime : a < p ≤ 2a + 1} · log a ≤ (log 4 + ε) a`.  This is
`eventually_card_primes_dyadic_le` with `log 4` in place of `1` and no hypothesis. -/
theorem eventually_card_primes_dyadic_le_log_four {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℕ in atTop,
      ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) * Real.log a
        ≤ (Real.log 4 + ε) * a := by
  have hsm : ∀ᶠ a : ℕ in atTop, Real.log (a : ℝ) + 0 ≤ ε * (a : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_log_add_le hε 0)
  filter_upwards [hsm] with a ha
  have := card_primes_dyadic_mul_log_le a
  linarith

/-- `1 ≤ log 4`, since `e < 4`. -/
theorem one_le_log_four : 1 ≤ Real.log 4 := by
  have h := Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ 4 by linarith [Real.exp_one_lt_d9])
  rwa [Real.log_exp] at h

/-- `excluded_final_arith` with a general leading constant `K > 0` in place of
`1 + e`: with `t ≤ eX`, `8C ≤ e log X`, `S ≤ 2K(X + t)/log X · T`, `T ≥ 0` and
`T ≤ (D + e)(log X)/2 + C`, one gets `S ≤ K (D + ε) X`. -/
theorem excluded_final_arith_const {X t S T D C e ε Λ K : ℝ} (hX : 0 < X) (hΛ : 0 < Λ)
    (he0 : 0 < e) (he1 : e ≤ 1) (he8 : 8 * e ≤ ε) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (hC0 : 0 ≤ C)
    (hK : 0 < K) (hT0 : 0 ≤ T) (ht0 : 0 ≤ t) (hXt : t ≤ e * X) (hC : 8 * C ≤ e * Λ)
    (hS : S ≤ (2 * K * (X + t) / Λ) * T)
    (hT : T ≤ (D + e) * (Λ / 2) + C) :
    S ≤ K * (D + ε) * X := by
  -- `S / K ≤ 2(X + t)/Λ · T ≤ 2(1 + e)(X + t)/Λ · T`, then `excluded_final_arith`
  have hW0 : 0 ≤ (X + t) / Λ * T := mul_nonneg (div_nonneg (by linarith) hΛ.le) hT0
  have hSK : S / K ≤ (2 * (1 + e) * (X + t) / Λ) * T := by
    rw [div_le_iff₀ hK]
    have e1 : (2 * K * (X + t) / Λ) * T = 2 * ((X + t) / Λ * T) * K := by ring
    have e2 : (2 * (1 + e) * (X + t) / Λ) * T * K
        = 2 * ((X + t) / Λ * T) * K + 2 * e * ((X + t) / Λ * T) * K := by ring
    have h3 : 0 ≤ 2 * e * ((X + t) / Λ * T) * K :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two he0.le) hW0) hK.le
    linarith
  have hfin := excluded_final_arith hX hΛ he0 he1 he8 hD0 hD1 hC0 ht0 hXt hC hSK hT
  rw [div_le_iff₀ hK] at hfin
  calc S ≤ (D + ε) * X * K := hfin
    _ = K * (D + ε) * X := by ring

/-- **The excluded-cofactor estimate from a dyadic prime count with constant `K`.**
If `#{p prime : a < p ≤ 2a + 1} · log a ≤ (K + ε) a` for every `ε > 0` and all
large `a`, and `B(η)` has upper density at most `D ∈ [0, 1]`, then for every
`ε > 0`, for all large `X`, `#{N ∈ 𝒜 : m_N ∈ B(η)} ≤ (K D + ε) X`.  The prime
number theorem gives the dyadic count with `K = 1` (`eventually_card_primes_dyadic_le`),
and then this is the bound of `eventually_card_excluded_le_of_upper`; Chebyshev's
bound gives it with `K = log 4` (`eventually_card_primes_dyadic_le_log_four`). -/
theorem eventually_card_excluded_le_of_upper_of_dyadic (h s : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (hdy : ∀ ε : ℝ, 0 < ε → ∀ᶠ a : ℕ in atTop,
      ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) * Real.log a ≤ (K + ε) * a)
    {η D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (hup : UpperDensityLE (excludedCofactorSet η) D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        ≤ (K * D + ε) * X := by
  have hK9 : 0 < 8 * K + 9 := by linarith
  obtain ⟨e, he0, he1, heK⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e * (8 * K + 9) ≤ ε :=
    ⟨min 1 (ε / (8 * K + 9)), lt_min (by norm_num) (div_pos hε hK9), min_le_left _ _,
      (le_div_iff₀ hK9).mp (min_le_right _ _)⟩
  obtain ⟨C, hC0, hCbound⟩ := upper_density_harmonic_bound _ hD0 hup he0
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp (hdy e he0)
  have hA₀' : ∀ a ≥ A₀, ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) * Real.log a
      ≤ (1 + (K + e - 1)) * a := by
    intro a ha
    rw [show (1 + (K + e - 1) : ℝ) = K + e by ring]
    exact hA₀ a ha
  have hE2 : ∀ᶠ X : ℕ in atTop, A₀ ≤ Nat.sqrt X := by
    filter_upwards [eventually_ge_atTop (A₀ * A₀)] with X hX
    exact Nat.le_sqrt.mpr hX
  have hE3 := eventually_minimalOffset_le h s he0
  have hE4 : ∀ᶠ X : ℕ in atTop, 8 * C ≤ e * Real.log X := by
    have hlog : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually_ge_atTop (8 * C / e)] with X hX
    rw [div_le_iff₀ he0] at hX
    linarith
  filter_upwards [hE2, hE3, hE4, eventually_ge_atTop 16] with X hX2 hX3 hX4 hX16
  have hX16R : (16 : ℝ) ≤ X := by exact_mod_cast hX16
  have hXpos : (0 : ℝ) < X := by linarith
  have hΛ : 0 < Real.log X := Real.log_pos (by linarith)
  have hS := card_excluded_le_harmonic (L := minimalDepth h s X) (s := s) η
    (show (0 : ℝ) ≤ K + e - 1 by linarith) hX16 hX2 hA₀'
  rw [show (1 + (K + e - 1) : ℝ) = K + e by ring] at hS
  have hT : ∑ m ∈ (Icc 1 (Nat.sqrt X / 2)).filter (· ∈ excludedCofactorSet η), (1 : ℝ) / m
      ≤ (D + e) * (Real.log X / 2) + C := by
    have hb := hCbound (Nat.sqrt X / 2)
    have hl := log_sqrt_half_succ_le hX16
    have := mul_le_mul_of_nonneg_left hl (show 0 ≤ D + e by linarith)
    linarith
  have hT0 : 0 ≤ ∑ m ∈ (Icc 1 (Nat.sqrt X / 2)).filter (· ∈ excludedCofactorSet η),
      (1 : ℝ) / m := Finset.sum_nonneg fun m _ => by positivity
  have hX3' : ((pivotOffset (minimalDepth h s X) s : ℕ) : ℝ) ≤ e * X := hX3
  have hfin := excluded_final_arith_const (ε := 8 * e) hXpos hΛ he0 he1 le_rfl hD0 hD1 hC0
    (show (0 : ℝ) < K + e by linarith) hT0 (Nat.cast_nonneg _) hX3' hX4 hS hT
  -- `(K + e)(D + 8e) ≤ K D + e (8K + 9) ≤ K D + ε`
  have p1 : e * D ≤ e * 1 := mul_le_mul_of_nonneg_left hD1 he0.le
  have p2 : e * e ≤ e * 1 := mul_le_mul_of_nonneg_left he1 he0.le
  have hcoef : (K + e) * (D + 8 * e) ≤ K * D + ε := by linarith
  exact le_trans hfin (mul_le_mul_of_nonneg_right hcoef hXpos.le)

/-- The budget consequence from a dyadic prime count with constant `K` and an upper
density bound `D` with `K D < 1/100`: for all large `X` the count is `< X/100`, and
the excluded-cofactor contribution `∑_{N ∈ 𝒜 ∖ 𝒢} E(h, N, L)` has norm at most
`X/100`.  With `K = 1` this is the conclusion of `eventually_excluded_budget_of_upper`. -/
theorem eventually_excluded_budget_of_upper_of_dyadic (h s : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (hdy : ∀ ε : ℝ, 0 < ε → ∀ᶠ a : ℕ in atTop,
      ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) * Real.log a ≤ (K + ε) * a)
    {η D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (hup : UpperDensityLE (excludedCofactorSet η) D)
    (hKD : K * D < 1 / 100) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ) < (1 / 100 : ℝ) * X ∧
      ‖pivotBadContribution h X (minimalDepth h s X) s η‖ ≤ (1 / 100 : ℝ) * X := by
  have hε : 0 < (1 / 100 - K * D) / 2 := by linarith
  filter_upwards [eventually_card_excluded_le_of_upper_of_dyadic h s hK hdy hD0 hD1 hup hε,
    eventually_gt_atTop 0] with X hX hX0
  have hX0R : (0 : ℝ) < X := by exact_mod_cast hX0
  have hlt : ((((pivotSupplierBases X (minimalDepth h s X) s).filter
      (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
        : ℕ) : ℝ) < (1 / 100 : ℝ) * X := by
    have : (K * D + (1 / 100 - K * D) / 2) * (X : ℝ) < (1 / 100 : ℝ) * X :=
      mul_lt_mul_of_pos_right (by linarith) hX0R
    linarith
  refine ⟨hlt, ?_⟩
  have hnorm : ‖pivotBadContribution h X (minimalDepth h s X) s η‖
      ≤ ((pivotBadBases X (minimalDepth h s X) s η).card : ℝ) := by
    unfold pivotBadContribution
    calc ‖∑ N ∈ pivotBadBases X (minimalDepth h s X) s η, windowFirstExp h N (minimalDepth h s X)‖
        ≤ ∑ N ∈ pivotBadBases X (minimalDepth h s X) s η,
            ‖windowFirstExp h N (minimalDepth h s X)‖ := norm_sum_le _ _
      _ = ((pivotBadBases X (minimalDepth h s X) s η).card : ℝ) := by
          simp [norm_windowFirstExp]
  rw [← filter_excluded_eq_pivotBadBases] at hnorm
  linarith

end ExcludedCofactor

/-- **The explicit choice `η = 1/1000`, with no input.**  Chebyshev's bound
replaces the prime number theorem in `excluded_budget_one_thousandth`: it gives the
dyadic prime count with constant `log 4` (`eventually_card_primes_dyadic_le_log_four`),
`B(1/1000)` has upper density at most `3/1000` (`excludedCofactorSet_upperDensityLE`),
and `log 4 · 3/1000 ≤ 9/1000 < 1/100`.  So for all large `X` the excluded-cofactor
count is `< X/100` and the excluded-cofactor contribution meets its `X/100` budget. -/
theorem excluded_budget_one_thousandth_of_chebyshev (h s : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s
            ∈ excludedCofactorSet (1 / 1000))).card : ℕ) : ℝ) < (1 / 100 : ℝ) * X ∧
      ‖pivotBadContribution h X (minimalDepth h s X) s (1 / 1000)‖ ≤ (1 / 100 : ℝ) * X :=
  eventually_excluded_budget_of_upper_of_dyadic h s one_le_log_four
    (fun _ε hε => eventually_card_primes_dyadic_le_log_four hε) (D := 3 * (1 / 1000))
    (by norm_num) (by norm_num) (excludedCofactorSet_upperDensityLE (by norm_num))
    (by
      have h4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith)

/-! Probe-only checks, not proposed for the library. -/

/-- The prime number theorem is the case `K = 1` of the general estimate: this
reproduces `eventually_card_excluded_le_of_upper`, with `1 * D` for `D`. -/
example (hPNT : PrimeNumberTheorem) (h s : ℕ) {η D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hup : UpperDensityLE (excludedCofactorSet η) D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        ≤ (1 * D + ε) * X :=
  eventually_card_excluded_le_of_upper_of_dyadic h s le_rfl
    (fun _ε hε => eventually_card_primes_dyadic_le hPNT hε) hD0 hD1 hup hε

/-- The Chebyshev instance of the general estimate: for any `η` whose `B(η)` has
upper density at most `D`, the excluded count is `(D log 4 + o(1)) X`. -/
example (h s : ℕ) {η D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hup : UpperDensityLE (excludedCofactorSet η) D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        ≤ (Real.log 4 * D + ε) * X :=
  eventually_card_excluded_le_of_upper_of_dyadic h s one_le_log_four
    (fun _ε hε => eventually_card_primes_dyadic_le_log_four hε) hD0 hD1 hup hε

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.excluded_budget_one_thousandth_of_chebyshev
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.eventually_excluded_budget_of_upper_of_dyadic
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.eventually_card_excluded_le_of_upper_of_dyadic
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.eventually_card_primes_dyadic_le_log_four
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.card_primes_dyadic_mul_log_le
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.prod_primes_dyadic_le_four_pow
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.excluded_final_arith_const
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.one_le_log_four
