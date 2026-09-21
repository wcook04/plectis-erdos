import Erdos249257.HalfGreedyFatalGap
import ErdosProblems.Erdos257.PaperCompleteR20.GeneralTargetGap

/-!
Paper-form restatements of four asserted environments of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`:

* `thm:fatal-absorbing` (line 2482) — a fatal rank is absorbing, and infinitely
  many omitted positive ranks force membership;
* `thm:straddle-closed-set` (line 2590) — straddling finite supports at every
  depth are exactly membership;
* `lem:fatal-gap-exclusion` (line 3272) — a certified strict gap excludes every
  representation, not only the continuations of the displayed prefix;
* `thm:sharp-fatal-gap` (line 3561) — the `2u ≤ 3a` sufficient test, its
  relation to the dyadic test, and the strictness data.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21
open Erdos249257 Erdos249257.HalfGreedyFatalGap

/-! ## `thm:fatal-absorbing` -/

/-- Long `thm:fatal-absorbing`.  `r n x` is `greedyMersenneRemainder x n` and
`R n` is `mersenneTail n`.  Both asserted clauses: once `r n > R n`, every later
rank is selected and every later state is again fatal; consequently infinitely
many omitted positive ranks give `x ∈ 𝒜`. -/
theorem fatal_absorbing {x : ℝ} (hx : 0 ≤ x) :
    (∀ n : ℕ, mersenneTail n < greedyMersenneRemainder x n →
        (∀ k : ℕ, n + k + 1 ∈ greedyMersenneSupport x) ∧
          ∀ k : ℕ, mersenneTail (n + k) < greedyMersenneRemainder x (n + k)) ∧
      ((greedyMersenneSkippedSupport x).Infinite → x ∈ mersenneAchievementSet) :=
  ⟨fun _ hfatal =>
      ⟨fun k => mem_greedyMersenneSupport_of_fatalAt_add_succ hfatal k,
        fun k => greedyMersenneFatalAt_add hfatal k⟩,
    fun hinf => mem_mersenneAchievementSet_of_greedySkippedSupport_infinite hx hinf⟩

/-! ## `thm:straddle-closed-set` -/

/-- Long `thm:straddle-closed-set`, both directions.  `X_D(2)` is
`positiveMersenneSupportValue ↑D` and `R_d` is `mersenneTail d`; the supports at
different depths are unrelated. -/
theorem straddle_all_depths_iff_mem (t : ℝ) :
    (∀ d : ℕ, ∃ D : Finset ℕ, (∀ n ∈ D, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑D : Set ℕ) ≤ t ∧
        t ≤ positiveMersenneSupportValue (↑D : Set ℕ) + mersenneTail d) ↔
      t ∈ mersenneAchievementSet := by
  classical
  constructor
  · intro h
    refine mem_mersenneAchievementSet_of_straddle_all_depths ?_
    intro d
    obtain ⟨D, hb, hlo, hhi⟩ := h d
    exact ⟨D, hb, hlo, hhi⟩
  · rintro ⟨A, hA0, rfl⟩ d
    refine ⟨(Finset.range (d + 1)).filter (fun n => n ∈ A), ?_, ?_, ?_⟩
    · intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      refine ⟨?_, by omega⟩
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact absurd hn.2 hA0
      · exact hpos
    · have hp : mersenneSupportPrefix A d
          = positiveMersenneSupportValue
              (↑((Finset.range (d + 1)).filter (fun n => n ∈ A)) : Set ℕ) := by
        refine mersenneSupportPrefix_eq_coe_finset ?_ ?_
        · intro n hn
          rw [Finset.mem_filter, Finset.mem_range] at hn
          refine ⟨?_, by omega⟩
          rcases Nat.eq_zero_or_pos n with rfl | hpos
          · exact absurd hn.2 hA0
          · exact hpos
        · intro n hn hnd
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
      have he := positiveMersenneSupportValue_eq_prefix_add_suffix A d
      change positiveMersenneSupportValue A
          = mersenneSupportPrefix A d + positiveMersenneSupportSuffix A d at he
      rw [hp] at he
      have := positiveMersenneSupportSuffix_nonneg A d
      linarith
    · have hp : mersenneSupportPrefix A d
          = positiveMersenneSupportValue
              (↑((Finset.range (d + 1)).filter (fun n => n ∈ A)) : Set ℕ) := by
        refine mersenneSupportPrefix_eq_coe_finset ?_ ?_
        · intro n hn
          rw [Finset.mem_filter, Finset.mem_range] at hn
          refine ⟨?_, by omega⟩
          rcases Nat.eq_zero_or_pos n with rfl | hpos
          · exact absurd hn.2 hA0
          · exact hpos
        · intro n hn hnd
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
      have he := positiveMersenneSupportValue_eq_prefix_add_suffix A d
      change positiveMersenneSupportValue A
          = mersenneSupportPrefix A d + positiveMersenneSupportSuffix A d at he
      rw [hp] at he
      have := positiveMersenneSupportSuffix_le_tail A d
      linarith

/-- Long `thm:straddle-closed-set`, the two inputs named in the environment for
the limiting support: compactness of `𝒜` and `R_d → 0`. -/
theorem straddle_limiting_support_inputs :
    IsCompact mersenneAchievementSet ∧
      Filter.Tendsto mersenneTail Filter.atTop (nhds 0) :=
  ⟨isCompact_mersenneAchievementSet, tendsto_mersenneTail_zero⟩

/-! ## `lem:fatal-gap-exclusion` -/

/-- Long `lem:fatal-gap-exclusion`, the displayed endpoint computation: for a
support agreeing with `u` through rank `d`, omitting `d+1` leaves value at most
the lower endpoint `X_u(2) + R_{d+1}`, while including it gives value at least
the upper endpoint `X_u(2) + w_{d+1}`. -/
theorem fatal_gap_endpoint_bounds {A : Set ℕ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hagree : ∀ n : ℕ, 0 < n → n ≤ d → (n ∈ A ↔ n ∈ u)) :
    (d + 1 ∉ A →
        positiveMersenneSupportValue A
          ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)) ∧
      (d + 1 ∈ A →
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)
          ≤ positiveMersenneSupportValue A) := by
  have hp : mersenneSupportPrefix A d = positiveMersenneSupportValue (↑u : Set ℕ) :=
    mersenneSupportPrefix_eq_coe_finset hu hagree
  have hsplit := positiveMersenneSupportValue_eq_prefix_add_suffix A (d + 1)
  change positiveMersenneSupportValue A
      = mersenneSupportPrefix A (d + 1) + positiveMersenneSupportSuffix A (d + 1)
    at hsplit
  have hnn := positiveMersenneSupportSuffix_nonneg A (d + 1)
  have hle := positiveMersenneSupportSuffix_le_tail A (d + 1)
  constructor
  · intro hnot
    have hsucc := mersenneSupportPrefix_succ A d
    rw [hp, Set.indicator_of_notMem hnot] at hsucc
    linarith
  · intro hmem
    have hsucc := mersenneSupportPrefix_succ A d
    rw [hp, Set.indicator_of_mem hmem] at hsucc
    linarith

/-- Long `lem:fatal-gap-exclusion`, the disjointness of the containing intervals
of distinct length-`d` prefixes: a target in both intervals forces the two
prefixes to agree. -/
theorem depth_prefix_interval_disjoint {t : ℝ} {u v : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d) (hv : ∀ n ∈ v, 0 < n ∧ n ≤ d)
    (hut : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d)
    (hvt : positiveMersenneSupportValue (↑v : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑v : Set ℕ) + mersenneTail d) :
    u = v := by
  have ha := PaperCompleteR20.straddle_agrees_greedy
    (IsStraddlePrefix.mk hu hut.1 hut.2)
  have hb := PaperCompleteR20.straddle_agrees_greedy
    (IsStraddlePrefix.mk hv hvt.1 hvt.2)
  ext n
  by_cases hn : 0 < n ∧ n ≤ d
  · rw [ha n hn.1 hn.2, ← hb n hn.1 hn.2]
  · exact ⟨fun h => absurd (hu n h) hn, fun h => absurd (hv n h) hn⟩

/-- Long `lem:fatal-gap-exclusion`: the displayed gap lies inside the containing
interval of its own prefix `u`. -/
theorem fatal_gap_within_prefix_interval {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d := by
  have htail := mersenneTail_eq_weight_add d
  have hnn := mersenneTail_nonneg (d + 1)
  exact ⟨by linarith, by linarith⟩

/-- Long `lem:fatal-gap-exclusion`.  A strict gap over the finite prefix `u`
excludes *every* positive support, not merely those agreeing with `u` through
rank `d`: the conclusion quantifies over all `A` with `0 ∉ A`. -/
theorem fatal_gap_excludes_every_representation {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    ∀ A : Set ℕ, 0 ∉ A → positiveMersenneSupportValue A ≠ t := by
  intro A hA0 hval
  refine PaperCompleteR20.internal_gap_excludes_membership (x := t)
    ⟨u, d + 1, by omega, fun n hn => ⟨(hu n hn).1, by have := (hu n hn).2; omega⟩,
      hlo, hhi⟩ ⟨A, hA0, hval.symm⟩

/-! ## `thm:sharp-fatal-gap`

Throughout, `ρ = u / (2 L)` and the subtraction-free parity relation
`2^k u + a = 2 L + u` is the paper's `a = 2L - (2^k - 1) u`. -/

/-- The skip condition: `0 < a` is exactly `ρ < w_k`. -/
theorem skipPositive_iff_lt_weight {k u L a : ℕ} (hk : 1 ≤ k) (hu : 0 < u)
    (hL : 0 < L) (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    0 < a ↔ (u : ℝ) / (2 * L) < mersenneWeight k := by
  have hpow : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hL0 : (0 : ℝ) < 2 * L := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    linarith
  have hden : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by linarith
  have hcast : (2 : ℝ) ^ k * u + a = 2 * L + u := by exact_mod_cast hdecomp
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  rw [mersenneWeight, div_lt_div_iff₀ hL0 hden]
  constructor
  · intro ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    nlinarith
  · intro hlt
    have ha0 : (0 : ℝ) < a := by nlinarith
    exact_mod_cast ha0

/-- The same equivalence in the paper's second phrasing: `0 < a` says exactly
that the greedy rule skips the weight `w_k`. -/
theorem skipPositive_iff_greedy_skips {k u L a : ℕ} (hk : 1 ≤ k) (hu : 0 < u)
    (hL : 0 < L) (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    0 < a ↔ ¬ (mersenneWeight k ≤ (u : ℝ) / (2 * L)) := by
  rw [skipPositive_iff_lt_weight hk hu hL hdecomp]
  exact not_le.symm

/-- The dyadic sufficient test `ρ ≤ 2^{-k}` is exactly `u ≤ a`. -/
theorem dyadic_test_iff_le {k u L a : ℕ} (hk : 1 ≤ k) (hu : 0 < u) (hL : 0 < L)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    (u : ℝ) / (2 * L) ≤ 1 / 2 ^ k ↔ u ≤ a := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hL0 : (0 : ℝ) < 2 * L := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    linarith
  have hcast : (2 : ℝ) ^ k * u + a = 2 * L + u := by exact_mod_cast hdecomp
  rw [div_le_div_iff₀ hL0 hpow]
  constructor
  · intro h
    have : (u : ℝ) ≤ a := by nlinarith
    exact_mod_cast this
  · intro h
    have : (u : ℝ) ≤ a := by exact_mod_cast h
    nlinarith

/-- The paper's displayed comparison series, literally:
`2^{-k} + (3·4^k)^{-1} + (7·8^k)^{-1} < R_k`. -/
theorem three_channel_lt_mersenneTail (k : ℕ) :
    (1 : ℝ) / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k) < mersenneTail k := by
  have h4 : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
  have h8 : ((2 : ℝ) ^ k) ^ 3 = (8 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm k 3, pow_mul]; norm_num
  have h := mersenneTailLB3_lt_mersenneTail k
  unfold mersenneTailLB3 at h
  rwa [h4, h8] at h

/-- The weaker sufficient condition `2u ≤ 3a` places the skipped residual
strictly below the remaining tail mass `R_k`. -/
theorem sharp_test_skipSafe {k u L a : ℕ} (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTail k :=
  skipSafe_actualTail_of_two_mul_le_three_mul hk hu ha hdecomp hsharp

/-- Containment: the dyadic test implies the sharp test. -/
theorem dyadic_test_contained_in_sharp {u a : ℕ} (h : u ≤ a) : 2 * u ≤ 3 * a := by
  omega

/-- Strict containment of the two sufficient tests on valid rational data:
`(k, u, L, a) = (2, 7, 13, 5)` satisfies the parity relation and `2u ≤ 3a`,
fails `u ≤ a`, and gives `1/4 < 7/26 < R_2`. -/
theorem sharp_strict_containment :
    (2 : ℕ) ^ 2 * 7 + 5 = 2 * 13 + 7 ∧ 2 * 7 ≤ 3 * 5 ∧ ¬ (7 ≤ 5) ∧
      (1 : ℝ) / 2 ^ 2 < (7 : ℝ) / (2 * 13) ∧ (7 : ℝ) / (2 * 13) < mersenneTail 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h := sharp_test_skipSafe (k := 2) (u := 7) (L := 13) (a := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  norm_num
  exact h

/-- The scalar pair `(u, a) = (3, 2)` does not arise from an integral `L` under
the parity relation: `2^k·3 + 2` is even for `k ≥ 1` while `2L + 3` is odd. -/
theorem three_two_not_realisable (k L : ℕ) (hk : 1 ≤ k) :
    2 ^ k * 3 + 2 ≠ 2 * L + 3 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h : 2 ^ (1 + m) = 2 * 2 ^ m := by rw [pow_add, pow_one]
  rw [h]
  omega

/-- Unit numerators are nonfatal at a skipped step, since then `a ≥ 1`. -/
theorem unit_numerator_nonfatal {k L a : ℕ} (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTail k :=
  unitNumerator_skipSafe_actualTail hk ha hdecomp

/-- Conversely a fatal step requires `3a < 2u`, hence `u ≥ 2`, and `u ≥ 3` when
`u` is odd. -/
theorem fatal_forces_numerator {k u L a : ℕ} (hk : 1 ≤ k) (hu : 0 < u)
    (ha : 0 < a) (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hfatal : mersenneTail k < (u : ℝ) / (2 * L)) :
    3 * a < 2 * u ∧ 2 ≤ u ∧ (Odd u → 3 ≤ u) := by
  have h3 := three_mul_lt_two_mul_of_actualTail_fatal hk hu ha hdecomp hfatal
  exact ⟨h3, by omega,
    fun hodd => three_le_of_actualTail_fatal_of_odd hk hu ha hodd hdecomp hfatal⟩

/-- Every clause of long `thm:sharp-fatal-gap`, assembled. -/
theorem paper_sharp_fatal_gap :
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ (u : ℝ) / (2 * L) < mersenneWeight k)) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ ¬ (mersenneWeight k ≤ (u : ℝ) / (2 * L)))) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k ↔ u ≤ a)) ∧
    (∀ k : ℕ, (1 : ℝ) / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        2 * u ≤ 3 * a → (u : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ u a : ℕ, u ≤ a → 2 * u ≤ 3 * a) ∧
    ((2 : ℕ) ^ 2 * 7 + 5 = 2 * 13 + 7 ∧ 2 * 7 ≤ 3 * 5 ∧ ¬ (7 ≤ 5) ∧
      (1 : ℝ) / 2 ^ 2 < (7 : ℝ) / (2 * 13) ∧ (7 : ℝ) / (2 * 13) < mersenneTail 2) ∧
    (∀ k L : ℕ, 1 ≤ k → 2 ^ k * 3 + 2 ≠ 2 * L + 3) ∧
    (∀ k L a : ℕ, 1 ≤ k → 0 < a → 2 ^ k * 1 + a = 2 * L + 1 →
        (1 : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        mersenneTail k < (u : ℝ) / (2 * L) →
        3 * a < 2 * u ∧ 2 ≤ u ∧ (Odd u → 3 ≤ u)) :=
  ⟨fun _ _ _ _ hk hu hL hd => skipPositive_iff_lt_weight hk hu hL hd,
    fun _ _ _ _ hk hu hL hd => skipPositive_iff_greedy_skips hk hu hL hd,
    fun _ _ _ _ hk hu hL hd => dyadic_test_iff_le hk hu hL hd,
    three_channel_lt_mersenneTail,
    fun _ _ _ _ hk hu ha hd hs => sharp_test_skipSafe hk hu ha hd hs,
    fun _ _ h => dyadic_test_contained_in_sharp h,
    sharp_strict_containment,
    fun _ _ hk => three_two_not_realisable _ _ hk,
    fun _ _ _ hk ha hd => unit_numerator_nonfatal hk ha hd,
    fun _ _ _ _ hk hu ha hd hf => fatal_forces_numerator hk hu ha hd hf⟩

#print axioms fatal_absorbing
#print axioms straddle_all_depths_iff_mem
#print axioms straddle_limiting_support_inputs
#print axioms fatal_gap_excludes_every_representation
#print axioms fatal_gap_endpoint_bounds
#print axioms depth_prefix_interval_disjoint
#print axioms fatal_gap_within_prefix_interval
#print axioms paper_sharp_fatal_gap
end ErdosProblems.Erdos257.PaperCompleteR21
