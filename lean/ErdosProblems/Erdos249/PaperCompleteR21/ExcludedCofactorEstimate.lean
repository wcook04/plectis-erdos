import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorDensity
import ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCount
import ErdosProblems.Erdos251.ActualPrimePaperR11

/-! `prop:badcof` of the long #249 paper ("The excluded-cofactor estimate",
`paper/reasoning-parts/erdos249/a249_front.tex`), and the assembled
proposition `prop_badcof`.

The paper's statement: fix `h, s` and use the minimal admissible depth `L`, so
`t = L - s + 1 = O_{h,s}(log X)`.  For `η ∈ (0, 1)` let
`B(η) = {m ≥ 1 : φ(m) < η m}`, with natural density `D(η)` (cited to
Schoenberg).  Then `#{N ∈ 𝒜 : m_N ∈ B(η)} ≤ (D(η) + o(1)) X`, so a single `η`
with `D(η) < 1/200` meets the `X/100` budget for all large `X`.

Dictionary, with the development's own objects as in `prop_dickman`:

* `L = minimalDepth h s X`, `t = minimalOffset h s X = pivotOffset L s`;
* `𝒜 = pivotSupplierBases X L s` and `m_N = pivotCofactor N L s`;
* `B(η) = excludedCofactorSet η` (in `ExcludedCofactorDensity`); the set
  `{N ∈ 𝒜 : m_N ∈ B(η)}` equals `pivotBadBases X L s η` (`𝒜 ∖ 𝒢`), whose
  contribution `pivotBadContribution` carries the `X/100` budget of
  `PivotBudgetAt`;
* "`B(η)` has natural density `D`" is `HasNaturalDensity (excludedCofactorSet η) D`,
  that is `#(B(η) ∩ [1, x]) / x → D`.

Inputs.  The prime number theorem enters as a hypothesis, through the
repository's single PNT input
`ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem`
(`p_n / (n log n) → 1` for the zero-based `n`-th prime).  The existence of
`D(η)` (Schoenberg's theorem) enters only as the density hypothesis of
`prop_badcof`.  Nothing else is assumed.

Proof, following the paper.
1. PNT gives, uniformly in the start point, the dyadic count
   `#{p prime : a < p ≤ 2a + 1} · log a ≤ (1 + ε) a` for all large `a`
   (`eventually_card_primes_dyadic_le`), from `p_n ∼ n log n` at the indices of
   the first prime above `a` and the last prime up to `2a + 1`.
2. The fibre of a cofactor `m ≤ ⌊√X⌋/2` is the image of the primes `p` with
   `X + t ≤ mp < 2X + t` (`image_pivotSupplierPrimes_eq_pivotFiber`).  These lie in
   `(a, 2a + 1]` with `a = ⌊(X + t - 1)/m⌋ ≥ 2⌊√X⌋ ≥ √X`, so the fibre has at
   most `2(1 + ε)(X + t)/(m log X)` elements (`fibre_card_le`).  The paper's
   endpoint term `O(1)` is absorbed by counting over `(a, 2a + 1]`.
3. Partial summation from the density gives
   `∑_{m ≤ M, m ∈ B(η)} 1/m ≤ (D + ε) log (M + 1) + C_ε`
   (`upper_density_harmonic_bound`), and `log (⌊√X⌋/2 + 1) ≤ (log X)/2`.
4. Multiplying, with `t = O(log X)`, gives at most `(D + 8ε) X`
   (`excluded_final_arith`).

The argument only uses the upper half of the density, so it is run from an
upper density bound (`eventually_card_excluded_le_of_upper`).  Combined with
the elementary bound `#(B(η) ∩ [1, x]) < 3ηx` of the remark after the proof,
this proves the remark's explicit choice `η = 1/1000` with the prime number
theorem as the only input (`excluded_budget_one_thousandth`). -/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos251.PaperR11.PrimeSource (PrimeNumberTheorem)
open Finset Filter Topology

namespace ExcludedCofactor

/-! ## The prime number theorem gives the dyadic prime count -/

/-- The named PNT input, unfolded: `p_n / (n log n) → 1` for the zero-based
`n`-th prime `p_n = Nat.nth Nat.Prime n`. -/
theorem nthPrime_div_tendsto (hPNT : PrimeNumberTheorem) :
    Tendsto (fun n : ℕ => ((Nat.nth Nat.Prime n : ℕ) : ℝ) / ((n : ℝ) * Real.log n))
      atTop (𝓝 1) :=
  hPNT

/-- Two-sided form: `(1 - δ) n log n ≤ p_n ≤ (1 + δ) n log n` for large `n`. -/
theorem nthPrime_two_sided (hPNT : PrimeNumberTheorem) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ n : ℕ, K ≤ n →
      (1 - δ) * ((n : ℝ) * Real.log n) ≤ (Nat.nth Nat.Prime n : ℝ) ∧
      (Nat.nth Nat.Prime n : ℝ) ≤ (1 + δ) * ((n : ℝ) * Real.log n) := by
  have hev : ∀ᶠ n : ℕ in atTop,
      ((Nat.nth Nat.Prime n : ℕ) : ℝ) / ((n : ℝ) * Real.log n) ∈ Set.Ioo (1 - δ) (1 + δ) :=
    nthPrime_div_tendsto hPNT (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop 2))
  refine ⟨max K 2, le_max_right _ _, fun n hn => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hK n (le_trans (le_max_left _ _) hn)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h3
  have hpos : 0 < (n : ℝ) * Real.log n :=
    mul_pos (by linarith) (Real.log_pos (by linarith))
  rw [lt_div_iff₀ hpos] at h1
  rw [div_lt_iff₀ hpos] at h2
  exact ⟨h1.le, h2.le⟩

/-- `log (2 log x) ≤ δ log x` for large `x`. -/
theorem eventually_log_two_mul_log_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log (2 * Real.log x) ≤ δ * Real.log x := by
  have hlo := Real.isLittleO_log_id_atTop.def (show 0 < δ / 2 by positivity)
  have htend : Tendsto (fun x : ℝ => 2 * Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop two_pos
  filter_upwards [htend.eventually hlo, eventually_ge_atTop 1] with x hx hx1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  simp only [id, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.log x)] at hx
  calc Real.log (2 * Real.log x) ≤ |Real.log (2 * Real.log x)| := le_abs_self _
    _ ≤ δ / 2 * (2 * Real.log x) := hx
    _ = δ * Real.log x := by ring

/-- `log x + C ≤ c x` for large `x`, for any `c > 0`. -/
theorem eventually_log_add_le {c : ℝ} (hc : 0 < c) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.log x + C ≤ c * x := by
  have hlo := Real.isLittleO_log_id_atTop.def (show 0 < c / 2 by positivity)
  filter_upwards [hlo, eventually_ge_atTop 1, eventually_ge_atTop (2 * C / c)]
    with x hx hx1 hxC
  simp only [id, Real.norm_eq_abs] at hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [abs_of_nonneg hlog0, abs_of_nonneg (by linarith)] at hx
  rw [div_le_iff₀ hc] at hxC
  linarith

/-- The index of the first prime `> a` has logarithm at least `(1 - δ) log a`. -/
theorem log_index_lower {a v δ : ℝ} (ha : 3 ≤ a) (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2)
    (hv2 : 2 ≤ v) (hva : v ≤ a + 1)
    (hv : (1 - δ) * (a + 1) ≤ v * Real.log v)
    (hll : Real.log (2 * Real.log (a + 1)) ≤ δ * Real.log (a + 1)) :
    (1 - δ) * Real.log a ≤ Real.log v := by
  have hv0 : 0 < v := by linarith
  have ha1 : 0 < a + 1 := by linarith
  have hlogA : 0 < Real.log (a + 1) := Real.log_pos (by linarith)
  have hlogaA : Real.log a ≤ Real.log (a + 1) := Real.log_le_log (by linarith) (by linarith)
  have hVhalf : (a + 1) / 2 ≤ v * Real.log v := by
    have : 0 ≤ (1 / 2 - δ) * (a + 1) := mul_nonneg (by linarith) ha1.le
    linarith
  have hlogva : Real.log v ≤ Real.log (a + 1) := Real.log_le_log hv0 hva
  have hvA : (a + 1) / 2 ≤ v * Real.log (a + 1) :=
    le_trans hVhalf (mul_le_mul_of_nonneg_left hlogva hv0.le)
  have hvlow : (a + 1) / (2 * Real.log (a + 1)) ≤ v := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hlog_low : Real.log ((a + 1) / (2 * Real.log (a + 1))) ≤ Real.log v :=
    Real.log_le_log (by positivity) hvlow
  rw [Real.log_div ha1.ne' (by positivity)] at hlog_low
  have := mul_le_mul_of_nonneg_left hlogaA (show (0 : ℝ) ≤ 1 - δ by linarith)
  linarith

/-- The real-variable core of the dyadic prime count.  Here `u, v` stand for the
indices of the last prime `≤ 2a + 1` and the first prime `> a`. -/
theorem dyadic_count_real_core {a u v δ ε : ℝ} (ha : 3 ≤ a) (hδ0 : 0 < δ)
    (hδ12 : δ ≤ 1 / 2) (hδε : 24 * δ ≤ ε) (hv2 : 2 ≤ v) (hvu : v ≤ u) (hva : v ≤ a + 1)
    (hu : (1 - δ) * (u * Real.log u) ≤ 2 * a + 1)
    (hv : a + 1 ≤ (1 + δ) * (v * Real.log v))
    (hll : Real.log (2 * Real.log (a + 1)) ≤ δ * Real.log (a + 1))
    (hsmall : Real.log a + 4 ≤ ε / 2 * a) :
    (u - v + 1) * Real.log a ≤ (1 + ε) * a := by
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := by linarith
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  have hloguv : Real.log v ≤ Real.log u := Real.log_le_log hv0 hvu
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  -- `(u - v) log v ≤ u log u - v log v`
  have hS2 : (u - v) * Real.log v ≤ u * Real.log u - v * Real.log v := by
    have := mul_le_mul_of_nonneg_left hloguv hu0.le
    linarith
  -- `u log u ≤ (1 + 2δ)(2a + 1)`
  have hU0 : 0 ≤ u * Real.log u := mul_nonneg hu0.le (le_trans hlogv.le hloguv)
  have hS3 : u * Real.log u ≤ (1 + 2 * δ) * (2 * a + 1) := by
    have hk : 0 ≤ δ * (1 - 2 * δ) * (u * Real.log u) :=
      mul_nonneg (mul_nonneg hδ0.le (by linarith)) hU0
    have := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 1 + 2 * δ by linarith)
    linarith
  -- `(1 - δ)(a + 1) ≤ v log v`
  have hV0 : 0 ≤ v * Real.log v := mul_nonneg hv0.le hlogv.le
  have hS4 : (1 - δ) * (a + 1) ≤ v * Real.log v := by
    have h1 := mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 1 - δ by linarith)
    have h2 : 0 ≤ δ * δ * (v * Real.log v) := mul_nonneg (mul_nonneg hδ0.le hδ0.le) hV0
    linarith
  -- `log v ≥ (1 - δ) log a`
  have hS6 := log_index_lower ha hδ0 hδ12 hv2 hva hS4 hll
  -- `(u - v) log a ≤ (1 + 2δ) W` with `W = (1 + 2δ)(2a + 1) - (1 - δ)(a + 1)`
  have huv : 0 ≤ u - v := by linarith
  have hZ0 : 0 ≤ (u - v) * Real.log a := mul_nonneg huv hloga.le
  have hS7 : (1 - δ) * ((u - v) * Real.log a) ≤
      (1 + 2 * δ) * (2 * a + 1) - (1 - δ) * (a + 1) := by
    have := mul_le_mul_of_nonneg_left hS6 huv
    linarith
  have hS8 : (u - v) * Real.log a ≤
      (1 + 2 * δ) * ((1 + 2 * δ) * (2 * a + 1) - (1 - δ) * (a + 1)) := by
    have hk : 0 ≤ δ * (1 - 2 * δ) * ((u - v) * Real.log a) :=
      mul_nonneg (mul_nonneg hδ0.le (by linarith)) hZ0
    have := mul_le_mul_of_nonneg_left hS7 (show (0 : ℝ) ≤ 1 + 2 * δ by linarith)
    linarith
  -- the constants
  have hδδ' : δ * δ ≤ δ * (1 / 2) := mul_le_mul_of_nonneg_left hδ12 hδ0.le
  have hδa : δ * δ * a ≤ δ * (1 / 2) * a := mul_le_mul_of_nonneg_right hδδ' (by linarith)
  have h12 : 12 * δ * a ≤ ε / 2 * a := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- **Dyadic prime count from PNT.**  For every `ε > 0`, for all large `a`,
`#{p prime : a < p ≤ 2a + 1} · log a ≤ (1 + ε) a`. -/
theorem eventually_card_primes_dyadic_le (hPNT : PrimeNumberTheorem) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℕ in atTop,
      ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) * Real.log a ≤ (1 + ε) * a := by
  set δ : ℝ := min (1 / 2) (ε / 24) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ12 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : 24 * δ ≤ ε := by
    have := min_le_right (1 / 2 : ℝ) (ε / 24)
    linarith
  obtain ⟨K, hK2, hK⟩ := nthPrime_two_sided hPNT hδ0
  have hshift : Tendsto (fun a : ℕ => (a : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hll : ∀ᶠ a : ℕ in atTop,
      Real.log (2 * Real.log ((a : ℝ) + 1)) ≤ δ * Real.log ((a : ℝ) + 1) :=
    hshift.eventually (eventually_log_two_mul_log_le hδ0)
  have hsm : ∀ᶠ a : ℕ in atTop, Real.log (a : ℝ) + 4 ≤ ε / 2 * (a : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_log_add_le (by positivity) 4)
  filter_upwards [hll, hsm, eventually_ge_atTop (Nat.nth Nat.Prime K), eventually_ge_atTop 3]
    with a hll hsm hanth ha3
  have hinf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime
  have ha3R : (3 : ℝ) ≤ a := by exact_mod_cast ha3
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
  -- indices: `j` primes are `≤ a`, `k` primes are `≤ 2a + 1`
  set j := Nat.count Nat.Prime (a + 1) with hj
  set k := Nat.count Nat.Prime (2 * a + 2) with hk
  have hcard : ((Ioc a (2 * a + 1)).filter Nat.Prime).card ≤ k - j := by
    have hmaps : Set.MapsTo (Nat.count Nat.Prime)
        (((Ioc a (2 * a + 1)).filter Nat.Prime : Finset ℕ) : Set ℕ) ((Ico j k : Finset ℕ) : Set ℕ) := by
      intro p hp
      obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      obtain ⟨hap, hp2⟩ := Finset.mem_Ioc.mp hpI
      exact Finset.mem_coe.mpr (Finset.mem_Ico.mpr
        ⟨Nat.count_monotone _ (by omega), Nat.count_strict_mono hpp (by omega)⟩)
    have hinj : Set.InjOn (Nat.count Nat.Prime)
        (((Ioc a (2 * a + 1)).filter Nat.Prime : Finset ℕ) : Set ℕ) := by
      intro p hp q hq hpq
      exact Nat.count_injective (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
        (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2 hpq
    have := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa using this
  rcases Nat.lt_or_ge j k with hjk | hjk
  swap
  · have h0 : ((Ioc a (2 * a + 1)).filter Nat.Prime).card = 0 := by omega
    rw [h0]
    simp only [Nat.cast_zero, zero_mul]
    positivity
  have hjK : K < j := (Nat.lt_nth_iff_count_lt hinf).mpr (by omega)
  have hu_lt : Nat.nth Nat.Prime (k - 1) < 2 * a + 2 :=
    (Nat.lt_nth_iff_count_lt hinf).mp (by omega)
  have hv_ge : a + 1 ≤ Nat.nth Nat.Prime j := (Nat.count_le_iff_le_nth hinf).mp le_rfl
  have hva : j ≤ a + 1 := by rw [hj]; exact Nat.count_le _
  obtain ⟨hu1, _⟩ := hK (k - 1) (by omega)
  obtain ⟨_, hv2⟩ := hK j (by omega)
  have hcore := dyadic_count_real_core (a := (a : ℝ)) (u := ((k - 1 : ℕ) : ℝ)) (v := (j : ℝ))
    (δ := δ) (ε := ε) ha3R hδ0 hδ12 hδε
    (by exact_mod_cast (show 2 ≤ j by omega))
    (by exact_mod_cast (show j ≤ k - 1 by omega))
    (by exact_mod_cast hva)
    (by
      have : ((Nat.nth Nat.Prime (k - 1) : ℕ) : ℝ) ≤ 2 * (a : ℝ) + 1 := by
        exact_mod_cast (show Nat.nth Nat.Prime (k - 1) ≤ 2 * a + 1 by omega)
      linarith)
    (by
      have : (a : ℝ) + 1 ≤ ((Nat.nth Nat.Prime j : ℕ) : ℝ) := by exact_mod_cast hv_ge
      linarith)
    hll hsm
  have hcardR : ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) + j
      ≤ ((k - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show ((Ioc a (2 * a + 1)).filter Nat.Prime).card + j ≤ (k - 1) + 1 by omega)
  calc ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) * Real.log a
      ≤ (((k - 1 : ℕ) : ℝ) - j + 1) * Real.log a :=
        mul_le_mul_of_nonneg_right (by linarith) hloga.le
    _ ≤ (1 + ε) * a := hcore

/-! ## One cofactor fibre injects into the primes of a dyadic interval -/

/-- On the assigned set, the cofactor satisfies `1 ≤ m_N ≤ ⌊√X⌋ / 2`. -/
theorem pivotCofactor_pos_le {X L s N : ℕ} (hN : N ∈ pivotSupplierBases X L s) :
    0 < pivotCofactor N L s ∧ pivotCofactor N L s ≤ Nat.sqrt X / 2 := by
  have hs := (Finset.mem_filter.mp hN).2
  change (pivotPrime N L s).Prime ∧
    pivotCofactor N L s * pivotPrime N L s = pivotArgument N L s ∧
    0 < pivotCofactor N L s ∧
    pivotCofactor N L s ≤ Nat.sqrt X / 2 ∧
    2 * Nat.sqrt X < pivotPrime N L s at hs
  exact ⟨hs.2.2.1, hs.2.2.2.1⟩

/-- The fibre of cofactor `m` has at most as many elements as there are primes
`p` with `a < p ≤ 2a + 1`, where `a = ⌊(X + t - 1)/m⌋`: the fibre is the image of
the primes with `X + t ≤ mp < 2X + t` (`image_pivotSupplierPrimes_eq_pivotFiber`). -/
theorem pivotFiber_card_le_card_primes {X L s m : ℕ} (hm : 0 < m)
    (hmM : m ≤ Nat.sqrt X / 2) :
    (pivotFiber X L s m).card ≤
      ((Ioc ((X + pivotOffset L s - 1) / m)
          (2 * ((X + pivotOffset L s - 1) / m) + 1)).filter Nat.Prime).card := by
  rw [← image_pivotSupplierPrimes_eq_pivotFiber hm hmM]
  refine le_trans Finset.card_image_le (Finset.card_le_card ?_)
  intro p hp
  obtain ⟨_, hpp, hlow, hup⟩ := Finset.mem_filter.mp hp
  have ht1 : 1 ≤ pivotOffset L s := by simp [pivotOffset]
  set t := pivotOffset L s with htdef
  set c := X + t - 1 with hcdef
  have hc1 : c < m * p := by omega
  have hc2 : m * p < 2 * c + 1 := by omega
  have hdiv : c < m * (c / m + 1) := Nat.lt_mul_div_succ c hm
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hpp⟩
  · rw [Nat.div_lt_iff_lt_mul hm]
    rw [Nat.mul_comm] at hc1
    exact hc1
  · by_contra hcon
    have hp' : 2 * (c / m) + 2 ≤ p := by omega
    have key : m * (2 * (c / m) + 2) ≤ m * p := Nat.mul_le_mul_left m hp'
    have key2 : m * (2 * (c / m) + 2) = 2 * (m * (c / m + 1)) := by ring
    omega

/-! ## The excluded-cofactor set is the development's `pivotBadBases` -/

/-- `{N ∈ 𝒜 : m_N ∈ B(η)}` is the index set `𝒜 ∖ 𝒢` of the excluded-cofactor
contribution in the four-term decomposition. -/
theorem filter_excluded_eq_pivotBadBases (X L s : ℕ) (η : ℝ) :
    (pivotSupplierBases X L s).filter (fun N => pivotCofactor N L s ∈ excludedCofactorSet η)
      = pivotBadBases X L s η := by
  ext N
  simp only [pivotBadBases, Finset.mem_filter, mem_excludedCofactorSet, pivotGoodCofactor, not_le]
  constructor
  · rintro ⟨hN, _, hlt⟩
    exact ⟨hN, hlt⟩
  · rintro ⟨hN, hlt⟩
    exact ⟨hN, (pivotCofactor_pos_le hN).1, hlt⟩

/-! ## Assembly -/

/-- `t = o(X)` at the minimal admissible depth, in the form `t ≤ e X` eventually. -/
theorem eventually_minimalOffset_le (h s : ℕ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ X : ℕ in atTop, ((minimalOffset h s X : ℕ) : ℝ) ≤ e * X := by
  have hsm : ∀ᶠ X : ℕ in atTop, Real.log (X : ℝ) + ((h : ℝ) + 11) / 2 ≤ e / 2 * (X : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_log_add_le (by positivity) _)
  filter_upwards [hsm, eventually_ge_atTop 1] with X hX hX1
  have hoff := minimalOffset_le h s X
  have hpow : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
  have hpowR : ((2 : ℝ) ^ Nat.log 2 X) ≤ X := by exact_mod_cast hpow
  have hlogpow : (Nat.log 2 X : ℝ) * Real.log 2 ≤ Real.log X := by
    have h := Real.log_le_log (by positivity) hpowR
    rw [Real.log_pow] at h
    exact h
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hk0 : (0 : ℝ) ≤ Nat.log 2 X := Nat.cast_nonneg _
  have hk : (Nat.log 2 X : ℝ) ≤ 2 * Real.log X := by nlinarith
  have hoffR : ((minimalOffset h s X : ℕ) : ℝ) ≤ (h : ℝ) + Nat.log 2 X + 11 := by
    exact_mod_cast hoff
  linarith

/-- Splitting `{N ∈ 𝒜 : m_N ∈ B(η)}` by the cofactor `m_N ∈ B(η) ∩ [1, ⌊√X⌋/2]`. -/
theorem card_excluded_le_sum_fibre (X L s : ℕ) (η : ℝ) :
    ((pivotSupplierBases X L s).filter
        (fun N => pivotCofactor N L s ∈ excludedCofactorSet η)).card
      ≤ ∑ m ∈ (Icc 1 (Nat.sqrt X / 2)).filter (· ∈ excludedCofactorSet η),
          (pivotFiber X L s m).card := by
  have hmaps : Set.MapsTo (fun N => pivotCofactor N L s)
      (((pivotSupplierBases X L s).filter
        (fun N => pivotCofactor N L s ∈ excludedCofactorSet η) : Finset ℕ) : Set ℕ)
      (((Icc 1 (Nat.sqrt X / 2)).filter (· ∈ excludedCofactorSet η) : Finset ℕ) : Set ℕ) := by
    intro N hN
    obtain ⟨hNA, hNB⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hN)
    obtain ⟨hm0, hmM⟩ := pivotCofactor_pos_le hNA
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm0, hmM⟩, hNB⟩)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_le_sum
  intro m _
  apply Finset.card_le_card
  intro N hN
  obtain ⟨hNS, hNm⟩ := Finset.mem_filter.mp hN
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hNS).1, hNm⟩

/-- One cofactor fibre, via the dyadic prime count: for `m ≤ ⌊√X⌋/2` the primes
lie above `a = ⌊(X + t - 1)/m⌋ ≥ 2⌊√X⌋ ≥ √X`, so `log a ≥ (log X)/2` and the
fibre has at most `2(1 + e)(X + t)/(m log X)` elements. -/
theorem fibre_card_le {X L s m A₀ : ℕ} {e : ℝ} (he : 0 ≤ e) (hX16 : 16 ≤ X)
    (hm0 : 0 < m) (hmM : m ≤ Nat.sqrt X / 2) (hA : A₀ ≤ Nat.sqrt X)
    (hA₀ : ∀ a ≥ A₀, ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) * Real.log a
      ≤ (1 + e) * a) :
    ((pivotFiber X L s m).card : ℝ)
      ≤ (2 * (1 + e) * ((X : ℝ) + pivotOffset L s) / Real.log X) * (1 / (m : ℝ)) := by
  have hfib := pivotFiber_card_le_card_primes (L := L) (s := s) hm0 hmM
  have hX16R : (16 : ℝ) ≤ X := by exact_mod_cast hX16
  have hXpos : (0 : ℝ) < X := by linarith
  have hΛ : 0 < Real.log X := Real.log_pos (by linarith)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hsq4 : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have ht1 : 1 ≤ pivotOffset L s := by simp [pivotOffset]
  -- `a = ⌊(X + t - 1)/m⌋ ≥ 2 ⌊√X⌋`
  have hM0 : 0 < Nat.sqrt X / 2 := by omega
  have h2M : 2 * Nat.sqrt X * (Nat.sqrt X / 2) ≤ X := by
    have hsq : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    have h2 : 2 * (Nat.sqrt X / 2) ≤ Nat.sqrt X := by omega
    calc 2 * Nat.sqrt X * (Nat.sqrt X / 2) = Nat.sqrt X * (2 * (Nat.sqrt X / 2)) := by ring
      _ ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul_left _ h2
      _ ≤ X := hsq
  have hXM : 2 * Nat.sqrt X ≤ X / (Nat.sqrt X / 2) := (Nat.le_div_iff_mul_le hM0).mpr h2M
  have hMm : X / (Nat.sqrt X / 2) ≤ X / m := Nat.div_le_div_left hmM hm0
  have hXc : X / m ≤ (X + pivotOffset L s - 1) / m := Nat.div_le_div_right (by omega)
  have ha_ge : 2 * Nat.sqrt X ≤ (X + pivotOffset L s - 1) / m :=
    le_trans hXM (le_trans hMm hXc)
  have hcount := hA₀ ((X + pivotOffset L s - 1) / m) (by omega)
  -- real bounds on `a`
  have hsqrtX : Real.sqrt X ≤ 2 * ((Nat.sqrt X : ℕ) : ℝ) := by
    have h1 := Real.real_sqrt_lt_nat_sqrt_succ (a := X)
    have h2 : (1 : ℝ) ≤ ((Nat.sqrt X : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ Nat.sqrt X by omega)
    linarith
  have haR : Real.sqrt X ≤ (((X + pivotOffset L s - 1) / m : ℕ) : ℝ) := by
    have : ((2 * Nat.sqrt X : ℕ) : ℝ) ≤ (((X + pivotOffset L s - 1) / m : ℕ) : ℝ) := by
      exact_mod_cast ha_ge
    push_cast at this
    linarith
  have hloga : Real.log X / 2 ≤ Real.log (((X + pivotOffset L s - 1) / m : ℕ) : ℝ) := by
    rw [← Real.log_sqrt hXpos.le]
    exact Real.log_le_log (Real.sqrt_pos.mpr hXpos) haR
  have haXt : (((X + pivotOffset L s - 1) / m : ℕ) : ℝ) * m ≤ (X : ℝ) + pivotOffset L s := by
    have h1 : (X + pivotOffset L s - 1) / m * m ≤ X + pivotOffset L s - 1 :=
      Nat.div_mul_le_self _ _
    have h2 : (X + pivotOffset L s - 1) / m * m ≤ X + pivotOffset L s := by omega
    exact_mod_cast h2
  have hfibR : ((pivotFiber X L s m).card : ℝ) ≤
      ((((Ioc ((X + pivotOffset L s - 1) / m)
        (2 * ((X + pivotOffset L s - 1) / m) + 1)).filter Nat.Prime).card : ℕ) : ℝ) := by
    exact_mod_cast hfib
  generalize ((((Ioc ((X + pivotOffset L s - 1) / m)
    (2 * ((X + pivotOffset L s - 1) / m) + 1)).filter Nat.Prime).card : ℕ) : ℝ) = P
    at hfibR hcount
  generalize (((X + pivotOffset L s - 1) / m : ℕ) : ℝ) = a at hloga haXt hcount
  have hP0 : 0 ≤ P := le_trans (Nat.cast_nonneg _) hfibR
  have h1 : P * (Real.log X / 2) ≤ (1 + e) * a :=
    le_trans (mul_le_mul_of_nonneg_left hloga hP0) hcount
  rw [div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
  have hfm : ((pivotFiber X L s m).card : ℝ) * (Real.log X * m) ≤ P * (Real.log X * m) :=
    mul_le_mul_of_nonneg_right hfibR (by positivity)
  have h2 : P * (Real.log X / 2) * m ≤ (1 + e) * a * m := mul_le_mul_of_nonneg_right h1 hmR.le
  have h3 : (1 + e) * (a * m) ≤ (1 + e) * ((X : ℝ) + pivotOffset L s) :=
    mul_le_mul_of_nonneg_left haXt (by linarith)
  linarith

/-- Steps A to D of the paper's proof: the count is at most
`2(1 + e)(X + t)/log X · ∑_{m ≤ ⌊√X⌋/2, m ∈ B(η)} 1/m`. -/
theorem card_excluded_le_harmonic {X L s A₀ : ℕ} {e : ℝ} (η : ℝ) (he : 0 ≤ e) (hX16 : 16 ≤ X)
    (hA : A₀ ≤ Nat.sqrt X)
    (hA₀ : ∀ a ≥ A₀, ((((Ioc a (2 * a + 1)).filter Nat.Prime).card : ℕ) : ℝ) * Real.log a
      ≤ (1 + e) * a) :
    ((((pivotSupplierBases X L s).filter
        (fun N => pivotCofactor N L s ∈ excludedCofactorSet η)).card : ℕ) : ℝ)
      ≤ (2 * (1 + e) * ((X : ℝ) + pivotOffset L s) / Real.log X)
        * ∑ m ∈ (Icc 1 (Nat.sqrt X / 2)).filter (· ∈ excludedCofactorSet η), (1 : ℝ) / m := by
  have hA' := card_excluded_le_sum_fibre X L s η
  calc ((((pivotSupplierBases X L s).filter
        (fun N => pivotCofactor N L s ∈ excludedCofactorSet η)).card : ℕ) : ℝ)
      ≤ ∑ m ∈ (Icc 1 (Nat.sqrt X / 2)).filter (· ∈ excludedCofactorSet η),
          ((pivotFiber X L s m).card : ℝ) := by exact_mod_cast hA'
    _ ≤ ∑ m ∈ (Icc 1 (Nat.sqrt X / 2)).filter (· ∈ excludedCofactorSet η),
          (2 * (1 + e) * ((X : ℝ) + pivotOffset L s) / Real.log X) * (1 / (m : ℝ)) := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨hmI, _⟩ := Finset.mem_filter.mp hm
        obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hmI
        exact fibre_card_le he hX16 hm1 hmM hA hA₀
    _ = _ := by rw [Finset.mul_sum]

/-- `log (⌊√X⌋/2 + 1) ≤ (log X)/2` for `X ≥ 16`. -/
theorem log_sqrt_half_succ_le {X : ℕ} (hX16 : 16 ≤ X) :
    Real.log (((Nat.sqrt X / 2 : ℕ) : ℝ) + 1) ≤ Real.log X / 2 := by
  have hX16R : (16 : ℝ) ≤ X := by exact_mod_cast hX16
  have hXpos : (0 : ℝ) < X := by linarith
  have hsq4 : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hM1 : ((Nat.sqrt X / 2 : ℕ) : ℝ) + 1 ≤ Real.sqrt X := by
    have h1 : Nat.sqrt X / 2 + 1 ≤ Nat.sqrt X := by omega
    have h2 : (((Nat.sqrt X / 2 : ℕ) : ℝ) + 1) ≤ ((Nat.sqrt X : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith [Real.nat_sqrt_le_real_sqrt (a := X)]
  rw [← Real.log_sqrt hXpos.le]
  exact Real.log_le_log (by positivity) hM1

/-- Steps E to G of the paper's proof, as pure real arithmetic: with `t ≤ eX`,
`8C ≤ e log X`, `S ≤ 2(1+e)(X+t)/log X · T` and `T ≤ (D+e)(log X)/2 + C`,
one gets `S ≤ (D + 8e) X ≤ (D + ε) X`. -/
theorem excluded_final_arith {X t S T D C e ε Λ : ℝ} (hX : 0 < X) (hΛ : 0 < Λ)
    (he0 : 0 < e) (he1 : e ≤ 1) (he8 : 8 * e ≤ ε) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (hC0 : 0 ≤ C)
    (ht0 : 0 ≤ t) (hXt : t ≤ e * X) (hC : 8 * C ≤ e * Λ)
    (hS : S ≤ (2 * (1 + e) * (X + t) / Λ) * T)
    (hT : T ≤ (D + e) * (Λ / 2) + C) :
    S ≤ (D + ε) * X := by
  have hK0 : 0 ≤ 2 * (1 + e) * (X + t) / Λ := by positivity
  have hKΛ : 2 * (1 + e) * (X + t) / Λ * Λ = 2 * (1 + e) * (X + t) := by
    field_simp
  generalize hKdef : 2 * (1 + e) * (X + t) / Λ = K at hK0 hKΛ hS
  have h1 : S ≤ K * ((D + e) * (Λ / 2) + C) := le_trans hS (mul_le_mul_of_nonneg_left hT hK0)
  have h2 : K * ((D + e) * (Λ / 2)) = (1 + e) * (X + t) * (D + e) := by
    have : K * ((D + e) * (Λ / 2)) = (K * Λ) * (D + e) / 2 := by ring
    rw [this, hKΛ]
    ring
  have heX : e * X ≤ X := mul_le_of_le_one_left hX.le he1
  have h3 : K * C ≤ e * X := by
    have hKCΛ : K * C * Λ = 2 * (1 + e) * (X + t) * C := by
      calc K * C * Λ = (K * Λ) * C := by ring
        _ = 2 * (1 + e) * (X + t) * C := by rw [hKΛ]
    have hle : 2 * (1 + e) * (X + t) * C ≤ e * X * Λ := by
      have hA : (1 + e) * (X + t) ≤ 2 * (2 * X) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
      have hB : 2 * ((1 + e) * (X + t)) * C ≤ 2 * (2 * (2 * X)) * C :=
        mul_le_mul_of_nonneg_right (by linarith) hC0
      have hC' : 8 * C * X ≤ e * Λ * X := mul_le_mul_of_nonneg_right hC hX.le
      linarith
    have : K * C * Λ ≤ e * X * Λ := by rw [hKCΛ]; exact hle
    exact le_of_mul_le_mul_right this hΛ
  have h4 : (1 + e) * (X + t) * (D + e) ≤ (D + 7 * e) * X := by
    have hDe : 0 ≤ (1 + e) * (D + e) := mul_nonneg (by linarith) (by linarith)
    have hm : (1 + e) * (D + e) * t ≤ (1 + e) * (D + e) * (e * X) :=
      mul_le_mul_of_nonneg_left hXt hDe
    have p1 : e * D * X ≤ e * 1 * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1 he0.le) hX.le
    have p2 : e * e * X ≤ e * 1 * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 he0.le) hX.le
    have p3 : e * e * D * X ≤ e * e * 1 * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1 (mul_nonneg he0.le he0.le)) hX.le
    have p4 : e * e * e * X ≤ e * e * 1 * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 (mul_nonneg he0.le he0.le)) hX.le
    linarith
  have h5 : (D + 7 * e) * X + e * X ≤ (D + ε) * X := by
    have := mul_le_mul_of_nonneg_right (show D + 8 * e ≤ D + ε by linarith) hX.le
    linarith
  linarith

/-- **The excluded-cofactor estimate from an upper density bound.**  If `B(η)`
has upper density at most `D ∈ [0, 1]`, then for every `ε > 0`, for all large
`X`, `#{N ∈ 𝒜 : m_N ∈ B(η)} ≤ (D + ε) X`.  This is the paper's argument; only
the upper half of the density is used. -/
theorem eventually_card_excluded_le_of_upper (hPNT : PrimeNumberTheorem) (h s : ℕ)
    {η D : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (hup : UpperDensityLE (excludedCofactorSet η) D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        ≤ (D + ε) * X := by
  set e : ℝ := min 1 (ε / 8) with hedef
  have he0 : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have he8 : 8 * e ≤ ε := by
    have := min_le_right (1 : ℝ) (ε / 8)
    linarith
  obtain ⟨C, hC0, hCbound⟩ := upper_density_harmonic_bound _ hD0 hup he0
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp (eventually_card_primes_dyadic_le hPNT he0)
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
  have hS := card_excluded_le_harmonic (L := minimalDepth h s X) (s := s) η he0.le hX16 hX2 hA₀
  have hT : ∑ m ∈ (Icc 1 (Nat.sqrt X / 2)).filter (· ∈ excludedCofactorSet η), (1 : ℝ) / m
      ≤ (D + e) * (Real.log X / 2) + C := by
    have hb := hCbound (Nat.sqrt X / 2)
    have hl := log_sqrt_half_succ_le hX16
    have := mul_le_mul_of_nonneg_left hl (show 0 ≤ D + e by linarith)
    linarith
  have hX3' : ((pivotOffset (minimalDepth h s X) s : ℕ) : ℝ) ≤ e * X := hX3
  exact excluded_final_arith hXpos hΛ he0 he1 he8 hD0 hD1 hC0 (Nat.cast_nonneg _) hX3' hX4 hS hT

/-- **The excluded-cofactor estimate, `o(1)` form.**  If `B(η)` has natural
density `D`, then for every `ε > 0`, for all large `X`,
`#{N ∈ 𝒜 : m_N ∈ B(η)} ≤ (D + ε) X`. -/
theorem eventually_card_excluded_le (hPNT : PrimeNumberTheorem) (h s : ℕ) {η D : ℝ}
    (hD : HasNaturalDensity (excludedCofactorSet η) D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        ≤ (D + ε) * X :=
  eventually_card_excluded_le_of_upper hPNT h s hD.nonneg hD.le_one hD.upperDensityLE hε

/-- The budget consequence from an upper density bound `D < 1/100`: for all
large `X` the count is `< X/100`, and the excluded-cofactor contribution
`∑_{N ∈ 𝒜 ∖ 𝒢} E(h, N, L)` has norm at most `X/100`. -/
theorem eventually_excluded_budget_of_upper (hPNT : PrimeNumberTheorem) (h s : ℕ) {η D : ℝ}
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (hup : UpperDensityLE (excludedCofactorSet η) D)
    (hD100 : D < 1 / 100) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ) < (1 / 100 : ℝ) * X ∧
      ‖pivotBadContribution h X (minimalDepth h s X) s η‖ ≤ (1 / 100 : ℝ) * X := by
  have hε : 0 < (1 / 100 - D) / 2 := by linarith
  filter_upwards [eventually_card_excluded_le_of_upper hPNT h s hD0 hD1 hup hε,
    eventually_gt_atTop 0] with X hX hX0
  have hX0R : (0 : ℝ) < X := by exact_mod_cast hX0
  have hlt : ((((pivotSupplierBases X (minimalDepth h s X) s).filter
      (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
        : ℕ) : ℝ) < (1 / 100 : ℝ) * X := by
    have : (D + (1 / 100 - D) / 2) * (X : ℝ) < (1 / 100 : ℝ) * X :=
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

/-- The budget consequence from a natural density `D < 1/100`. -/
theorem eventually_excluded_budget (hPNT : PrimeNumberTheorem) (h s : ℕ) {η D : ℝ}
    (hD : HasNaturalDensity (excludedCofactorSet η) D) (hD100 : D < 1 / 100) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ) < (1 / 100 : ℝ) * X ∧
      ‖pivotBadContribution h X (minimalDepth h s X) s η‖ ≤ (1 / 100 : ℝ) * X :=
  eventually_excluded_budget_of_upper hPNT h s hD.nonneg hD.le_one hD.upperDensityLE hD100

end ExcludedCofactor

open ExcludedCofactor

/-- **`prop:badcof`** of the long #249 paper ("The excluded-cofactor estimate"),
with the prime number theorem as the one named input and the natural density
`D = D(η)` of `B(η)` as a hypothesis (the paper cites Schoenberg for its
existence).  For fixed `h, s`, with `L = minimalDepth h s X` the minimal
admissible depth, `t = minimalOffset h s X = L - s + 1`,
`𝒜 = pivotSupplierBases X L s`, `m_N = pivotCofactor N L s` and
`B(η) = excludedCofactorSet η`, the four conjuncts are:

1. `t = O_{h,s}(log X)`, explicitly `t ≤ h + ⌊log₂ X⌋ + 11` (the paper's "thus",
   from `prop_dickman`);
2. `{N ∈ 𝒜 : m_N ∈ B(η)}` is the development's excluded-cofactor index set
   `pivotBadBases X L s η`, that is `𝒜 ∖ 𝒢`;
3. `#{N ∈ 𝒜 : m_N ∈ B(η)} ≤ (D(η) + o(1)) X`, the `o(1)` written as: for every
   `ε > 0`, for all large `X`, the count is at most `(D + ε) X`;
4. if `D(η) < 1/200`, then for all large `X` the count is `< X/100` and the
   excluded-cofactor contribution meets its budget
   `‖∑_{N ∈ 𝒜 ∖ 𝒢} E(h, N, L)‖ ≤ X/100`, the third clause of `PivotBudgetAt`.
   Here `η` is fixed before the threshold in `X`.

The paper's range `0 < η < 1` is not needed, and `D(η) < 1/100` already suffices
for conjunct 4 (`eventually_excluded_budget`).  For the explicit choice
`η = 1/1000` the density hypothesis can be dropped altogether
(`excluded_budget_one_thousandth`). -/
theorem prop_badcof (hPNT : ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem)
    (h s : ℕ) (η D : ℝ) (hD : HasNaturalDensity (excludedCofactorSet η) D) :
    (∀ X : ℕ, minimalOffset h s X ≤ h + Nat.log 2 X + 11) ∧
    (∀ X : ℕ, (pivotSupplierBases X (minimalDepth h s X) s).filter
        (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)
      = pivotBadBases X (minimalDepth h s X) s η) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        ≤ (D + ε) * X) ∧
    (D < 1 / 200 → ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        < (1 / 100 : ℝ) * X ∧
      ‖pivotBadContribution h X (minimalDepth h s X) s η‖ ≤ (1 / 100 : ℝ) * X) :=
  ⟨minimalOffset_le h s, fun X => filter_excluded_eq_pivotBadBases X _ s η,
    fun _ε hε => eventually_card_excluded_le hPNT h s hD hε,
    fun hD200 => eventually_excluded_budget hPNT h s hD (by linarith)⟩

/-- **The explicit choice `η = 1/1000`** of the remark after `prop:badcof`, with
the prime number theorem as the only input.  The elementary bound
`#(B(η) ∩ [1, x]) < 3ηx` (`excludedCofactorSet_upperDensityLE`) replaces the
cited existence of `D(η)`: `B(1/1000)` has upper density at most `3/1000`, so for
all large `X` the excluded-cofactor count is `< X/100` and the excluded-cofactor
contribution meets its `X/100` budget. -/
theorem excluded_budget_one_thousandth
    (hPNT : ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem) (h s : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s
            ∈ excludedCofactorSet (1 / 1000))).card : ℕ) : ℝ) < (1 / 100 : ℝ) * X ∧
      ‖pivotBadContribution h X (minimalDepth h s X) s (1 / 1000)‖ ≤ (1 / 100 : ℝ) * X :=
  eventually_excluded_budget_of_upper hPNT h s (D := 3 * (1 / 1000)) (by norm_num) (by norm_num)
    (excludedCofactorSet_upperDensityLE (by norm_num)) (by norm_num)

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.excluded_budget_one_thousandth
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.prop_badcof
