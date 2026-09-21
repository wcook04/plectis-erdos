import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveTowerBlocks

/-!
# The nonprimitive coefficient-one lower boundary


This module performs the growing-block selection and the logarithmic
composition, rather than taking the needed block as a hypothesis. The
canonical corollary derives all growth budgets from the original series.
It proves the subcritical part, not the strict primitive amplification
which is needed for the inclusive coefficient-one endpoint.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter PaperCompleteR7
open scoped BigOperators Topology

/-- One explicit Archimedean choice controls all later quadratic budgets.
The finite prefix and the fixed log-log scaling shift occur in `F`. -/
theorem eventual_quadratic_budget (c : ℝ) (d e F : ℕ)
    (hc0 : 0 ≤ c) (hslack : c * d < e) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      c * ((d : ℝ) * (k : ℝ) ^ 2 + k + F) ≤ (e : ℝ) * (k : ℝ) ^ 2 := by
  let δ : ℝ := e - c * d
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (max (1 : ℝ) (c * ((F : ℝ) + 1) / δ))
  refine ⟨K, fun k hk ↦ ?_⟩
  have hKk : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : 1 ≤ (k : ℝ) := ((le_max_left _ _).trans hK.le).trans hKk
  have hq : c * ((F : ℝ) + 1) / δ ≤ (k : ℝ) :=
    ((le_max_right _ _).trans hK.le).trans hKk
  have hq' := (div_le_iff₀ hδ).1 hq
  have hmul := mul_le_mul_of_nonneg_right hq' (show (0 : ℝ) ≤ k by positivity)
  have hFk : (k : ℝ) + F ≤ ((F : ℝ) + 1) * k := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ F by positivity) (sub_nonneg.mpr hk1)]
  have hsmall := mul_le_mul_of_nonneg_left hFk hc0
  dsimp [δ] at hmul
  nlinarith

/-- There is no eventual record cap of coefficient less than one on an
unbounded exact orbit with the stated, explicit growth estimates. -/
theorem no_subcritical_record_cap
    (a U D : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (hUpos : ∀ n, 0 < U n) (hDpos : ∀ n, 0 < D n)
    (hU : ∀ n, U (n + 1) + D n = a n * U n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hlower : ∃ N : ℕ, ∀ k, 2 * binaryTower k ≤ a (N + k))
    (hrecord : ∃ K : ℕ, ∀ n, runningMax U n ≤ 2 ^ (K + n))
    (hden : ∃ L : ℕ, ∀ n, D n ≤ binaryTower (n + L))
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n)
    (g : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ¬ ∃ T : ℕ, ∀ n, T ≤ n → runningMax U n < U (n + 1) →
      ((U (n + 1) - runningMax U n : ℕ) : ℝ) ≤
        c * recordLogLog (g * runningMax U n : ℕ) := by
  rintro ⟨T, hcap⟩
  obtain ⟨N, hN⟩ := hlower
  obtain ⟨K, hK⟩ := hrecord
  obtain ⟨L, hL⟩ := hden
  obtain ⟨k₀, hk₀⟩ := eventual_quadratic_budget c 1 1 (N + L + g + 2) hc0
    (by simpa only [Nat.cast_one, mul_one] using hc1)
  let t := max 5 (max (K + N) (T + k₀))
  let k := 2 ^ t
  let B := k ^ 2
  let J := N + k
  let M := J + B
  let A : Fin B → ℕ := fun i ↦ a (J + i)
  have ht5 : 5 ≤ t := le_max_left _ _
  have htK : K + N ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have htT : T + k₀ ≤ t := (le_max_right _ _).trans (le_max_right _ _)
  have htk : t ≤ k := by have := index_succ_le_two_pow t; dsimp [k]; omega
  have hKN : K + N ≤ k := htK.trans htk
  have hk₀k : k₀ ≤ k := by omega
  have hTM : T ≤ M := by dsimp [M, J, B]; omega
  have hB : 0 < B := by dsimp [B, k]; positivity
  have hApos : ∀ i, 0 < A i := fun i ↦ hapos _
  have hAlower : ∀ i, 2 * binaryTower k ≤ A i := by
    intro i
    exact (hN k).trans (ha.monotone (by dsimp [J]; omega))
  have hpair : ∀ i j : Fin B, i ≠ j → Nat.gcd (A i) (A j) ≤ runningMax U M := by
    intro i j hij
    apply multiplier_gcd_le_terminal_record a U D hU hD hUpos
    · intro heq
      apply hij
      apply Fin.ext
      dsimp [A, J] at heq
      omega
    · dsimp [M]; have := i.isLt; omega
    · dsimp [M]; have := j.isLt; omega
  have hlarge : ∀ i, max B (runningMax U M) * (runningMax U M) ^ (B - 1) < A i :=
    square_block_core_size U K N t ht5 hKN (hK M) A hAlower
  have hUI : ∀ n, (U (n + 1) : ℤ) = (a n : ℤ) * U n - (1 : ℤ) * D n := by
    intro n
    have hh : (U (n + 1) : ℤ) + D n = (a n : ℤ) * U n := by exact_mod_cast hU n
    linarith
  have hDI : ∀ n, (D (n + 1) : ℤ) = (a n : ℤ) * D n := by
    intro n
    exact_mod_cast hD n
  obtain ⟨x, P, hPx, hxP, hPA, hRx, hfence⟩ :=
    coprime_core_record_fence U (fun n ↦ (D n : ℤ)) (fun n ↦ (a n : ℤ))
      (fun _ ↦ 1) M B (runningMax U M) hB A hApos hUI hDI hpair hlarge
      (fun i n hn ↦ Int.natCast_dvd_natCast.mpr (multiplier_block_old a D hD J B i n hn))
  have hPD : P ≤ D M := hPA.trans (multiplier_block_product_le_denominator a D hD hDpos J B)
  have hPtower : P ≤ binaryTower (M + L) := hPD.trans (hL M)
  have hBtower : B ≤ binaryTower (M + L) :=
    (show B ≤ M + L by dsimp [M]; omega).trans (index_le_binaryTower (M + L))
  have hheight := scaled_crt_height_logLog g P B (M + L) hPtower hBtower
  have hbudget : c * (M + L + g + 2 : ℕ) ≤ (B : ℝ) := by
    have hh := hk₀ k hk₀k
    dsimp [M, J, B]
    push_cast
    push_cast at hh
    nlinarith
  have hbounded : ∀ n, U n < x + B := by
    apply hfence
    intro n hn hR hnew
    have hfirst := hcap n (hTM.trans hn) hnew
    have hRheight : recordLogLog (g * runningMax U n : ℕ) ≤
        recordLogLog (g * (2 * P + B) : ℕ) :=
      recordLogLog_nat_mul_mono g (by omega)
    have hfinal : ((U (n + 1) - runningMax U n : ℕ) : ℝ) ≤ (B : ℝ) :=
      hfirst.trans ((mul_le_mul_of_nonneg_left (hRheight.trans hheight) hc0).trans hbudget)
    exact_mod_cast hfinal
  obtain ⟨n, hn⟩ := hunbounded (x + B)
  exact (not_lt_of_ge hn) (hbounded n)

/-- The lower-bound conclusion is cofinal in the original index, not merely
an assertion about a newly chosen subsequence of records. -/
theorem cofinal_record_exceeds_subcritical_logLog
    (a U D : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (hUpos : ∀ n, 0 < U n) (hDpos : ∀ n, 0 < D n)
    (hU : ∀ n, U (n + 1) + D n = a n * U n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hlower : ∃ N : ℕ, ∀ k, 2 * binaryTower k ≤ a (N + k))
    (hrecord : ∃ K : ℕ, ∀ n, runningMax U n ≤ 2 ^ (K + n))
    (hden : ∃ L : ℕ, ∀ n, D n ≤ binaryTower (n + L))
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n)
    (g : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (T : ℕ) :
    ∃ n, T ≤ n ∧ runningMax U n < U (n + 1) ∧
      c * recordLogLog (g * runningMax U n : ℕ) <
        ((U (n + 1) - runningMax U n : ℕ) : ℝ) := by
  by_contra hnot
  apply no_subcritical_record_cap a U D ha hapos hUpos hDpos hU hD
    hlower hrecord hden hunbounded g c hc0 hc1
  refine ⟨T, fun n hn hnew ↦ ?_⟩
  by_contra hh
  exact hnot ⟨n, hn, hnew, lt_of_not_ge hh⟩

/-- Canonical specialisation: neither a block supplier nor a denominator
or numerator growth bound is assumed in addition to the actual series. -/
theorem canonical_cofinal_subcritical_record
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ canonicalNaturalNumerator a p q n)
    (g : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (T : ℕ) :
    ∃ n, T ≤ n ∧ runningMax (canonicalNaturalNumerator a p q) n <
      canonicalNaturalNumerator a p q (n + 1) ∧
      c * recordLogLog (g * runningMax (canonicalNaturalNumerator a p q) n : ℕ) <
        ((canonicalNaturalNumerator a p q (n + 1) -
          runningMax (canonicalNaturalNumerator a p q) n : ℕ) : ℝ) := by
  obtain ⟨hU, hD, hstep, hden, htail⟩ := canonical_integer_tail a hapos p q hq hs
  apply cofinal_record_exceeds_subcritical_logLog a (canonicalNaturalNumerator a p q)
    (canonicalDenominator a q) ha hapos hU hD hstep hden
    ?_ (canonical_runningMax_binary_exponent a ha hapos p q hq hs hgrowth)
    (canonical_denominator_binaryTower_bound a ha hapos q hgrowth)
    hunbounded g c hc0 hc1 T
  obtain ⟨N, A, hN, hA, hb⟩ := quadratic_double_exponential_bounds a ha hapos hgrowth
  exact ⟨N, fun k ↦ (hb k).1⟩

end ErdosProblems.Erdos243.PaperCompleteR11
