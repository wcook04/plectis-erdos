import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Erdős 243: window avoidance for a family of pairwise coprime moduli

This file formalises two propositions of the long note
`paper/reasoning-parts/erdos243/core.tex`.

* `long243:res:coprimalitycap` ("an elementary interval bound"), both clauses.
  Clause (i) is `exists_avoiding_in_window`: for pairwise coprime moduli
  `m 0 < m 1 < ⋯`, all at least `2`, with `θ = ∑ᵢ 1/mᵢ < 1`, every window
  `[x, x+L)` with `x ≥ 1`, `L ≥ 1` and `L > k/(1-θ)`, where `k = #{i : mᵢ ≤ x+L}`,
  contains an integer divisible by no `mᵢ`.
  Clause (ii) is `exists_slow_rise_avoiding_sequence`: under the additional
  scale `ℓ(mᵢ) = i + O(1)`, for each `ε > 0` there are an index `T` and a
  strictly increasing sequence `(uₙ)` of positive integers with `mᵢ ∤ uₙ` for
  every `i ≥ T` and every `n`, and `u_{n+1} - uₙ ≤ (1+ε) ℓ(uₙ)` eventually.
  Here `ℓ x = log₂ log₂ max(4, x)` is `ellScale`.

* `long243:res:variablerise` ("small increases when the prime moduli are
  sparse"), `exists_sparse_prime_coprime_sequence`: there are strictly
  increasing primes `pᵢ` and a strictly increasing sequence `uₙ → ∞` of
  positive integers coprime to every `pᵢ` with
  `u_{n+1} - uₙ = O(√(log log (uₙ + e^e))) = o(log log (uₙ + 3))`.

The arguments follow the note.  The window count is the elementary inclusion
`#[x, x+L) ≤ Σ_{mᵢ ≤ x+L} #(multiples of mᵢ in the window) ≤ Lθ + k < L`, and
the sequences are produced by iterating that window step from a starting point
beyond an explicit threshold.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open scoped BigOperators Topology

/-! ### Counting multiples in a window -/

/-- A window of length `L` contains at most `L/d + 1` multiples of `d`. -/
private lemma card_filter_dvd_Ico_mul_le (d x L : ℕ) (hd : 0 < d) :
    ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)).card * d ≤ L + d := by
  rcases Finset.eq_empty_or_nonempty ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)) with h | h
  · rw [h]; simp
  have hcF : ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)).min' h
      ∈ (Finset.Ico x (x + L)).filter (fun n => d ∣ n) :=
    Finset.min'_mem _ h
  have hMF : ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)).max' h
      ∈ (Finset.Ico x (x + L)).filter (fun n => d ∣ n) :=
    Finset.max'_mem _ h
  set c := ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)).min' h with hcdef
  set M := ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)).max' h with hMdef
  have hcdvd : d ∣ c := (Finset.mem_filter.mp hcF).2
  have hcx : x ≤ c := (Finset.mem_Ico.mp (Finset.mem_filter.mp hcF).1).1
  have hMlt : M < x + L := (Finset.mem_Ico.mp (Finset.mem_filter.mp hMF).1).2
  have hcM : c ≤ M := Finset.min'_le _ M hMF
  have hcard : ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)).card ≤ (M - c) / d + 1 := by
    have key : ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)).card
        ≤ (Finset.range ((M - c) / d + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun n => (n - c) / d) ?_ ?_
      · intro n hn
        have hn' : n ∈ (Finset.Ico x (x + L)).filter (fun n => d ∣ n) := Finset.mem_coe.mp hn
        have hnM : n ≤ M := Finset.le_max' _ n hn'
        have hcn : c ≤ n := Finset.min'_le _ n hn'
        exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)))
      · intro n1 h1 n2 h2 heq
        have h1' : n1 ∈ (Finset.Ico x (x + L)).filter (fun n => d ∣ n) := Finset.mem_coe.mp h1
        have h2' : n2 ∈ (Finset.Ico x (x + L)).filter (fun n => d ∣ n) := Finset.mem_coe.mp h2
        have hd1 : d ∣ n1 - c := Nat.dvd_sub (Finset.mem_filter.mp h1').2 hcdvd
        have hd2 : d ∣ n2 - c := Nat.dvd_sub (Finset.mem_filter.mp h2').2 hcdvd
        have e1 : (n1 - c) / d * d = n1 - c := Nat.div_mul_cancel hd1
        have e2 : (n2 - c) / d * d = n2 - c := Nat.div_mul_cancel hd2
        have hc1 : c ≤ n1 := Finset.min'_le _ n1 h1'
        have hc2 : c ≤ n2 := Finset.min'_le _ n2 h2'
        have heq' : (n1 - c) / d = (n2 - c) / d := heq
        have hsub : n1 - c = n2 - c := by rw [← e1, ← e2, heq']
        omega
    simpa using key
  have hstep : ((M - c) / d + 1) * d = (M - c) / d * d + d := by ring
  have hdiv : (M - c) / d * d ≤ M - c := Nat.div_mul_le_self _ _
  calc ((Finset.Ico x (x + L)).filter (fun n => d ∣ n)).card * d
      ≤ ((M - c) / d + 1) * d := Nat.mul_le_mul hcard (le_refl d)
    _ = (M - c) / d * d + d := hstep
    _ ≤ (M - c) + d := by omega
    _ ≤ L + d := by omega

/-! ### The index set of small moduli -/

/-- The indices of the moduli not exceeding `z`.  For a strictly increasing family
this finite set is the `k` of `long243:res:coprimalitycap`. -/
private def modIdx (m : ℕ → ℕ) (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter (fun i => m i ≤ z)

private lemma mem_modIdx {m : ℕ → ℕ} (hmono : StrictMono m) (z i : ℕ) :
    i ∈ modIdx m z ↔ m i ≤ z := by
  constructor
  · intro hi
    exact (Finset.mem_filter.mp hi).2
  · intro hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hi⟩
    have hle : i ≤ m i := hmono.le_apply
    omega

private lemma ncard_setOf_le_eq {m : ℕ → ℕ} (hmono : StrictMono m) (z : ℕ) :
    ({i | m i ≤ z} : Set ℕ).ncard = (modIdx m z).card := by
  have hset : ({i | m i ≤ z} : Set ℕ) = ↑(modIdx m z) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_modIdx hmono]
  rw [hset, Set.ncard_coe_finset]

/-! ### Clause (i): the elementary window bound -/

private lemma exists_window_avoiding_aux
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    {x L : ℕ} (hx : 1 ≤ x)
    (hkL : (((modIdx m (x + L)).card : ℝ)) / (1 - θ) < (L : ℝ)) :
    ∃ n, x ≤ n ∧ n < x + L ∧ ∀ i, ¬ m i ∣ n := by
  by_contra hcon
  push_neg at hcon
  have hθ0 : 0 ≤ θ := by
    rw [← hθ]
    exact tsum_nonneg (fun i => by positivity)
  have hone : (0 : ℝ) < 1 - θ := by linarith
  have hWcard : (Finset.Ico x (x + L)).card = L := by
    rw [Nat.card_Ico]; omega
  have hcover : Finset.Ico x (x + L)
      ⊆ (modIdx m (x + L)).biUnion
          (fun i => (Finset.Ico x (x + L)).filter (fun n => m i ∣ n)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
    obtain ⟨i, hi⟩ := hcon n hn1 hn2
    have hpos : 0 < n := by omega
    have hmin : m i ≤ x + L := by
      have := Nat.le_of_dvd hpos hi
      omega
    exact Finset.mem_biUnion.mpr ⟨i, (mem_modIdx hmono _ i).mpr hmin,
      Finset.mem_filter.mpr ⟨hn, hi⟩⟩
  have hLsumNat : L ≤ ∑ i ∈ modIdx m (x + L),
      ((Finset.Ico x (x + L)).filter (fun n => m i ∣ n)).card := by
    calc L = (Finset.Ico x (x + L)).card := hWcard.symm
      _ ≤ ((modIdx m (x + L)).biUnion
            (fun i => (Finset.Ico x (x + L)).filter (fun n => m i ∣ n))).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ i ∈ modIdx m (x + L),
            ((Finset.Ico x (x + L)).filter (fun n => m i ∣ n)).card :=
          Finset.card_biUnion_le
  have hLsum : (L : ℝ) ≤ ∑ i ∈ modIdx m (x + L),
      (((Finset.Ico x (x + L)).filter (fun n => m i ∣ n)).card : ℝ) := by
    exact_mod_cast hLsumNat
  have hterm : ∀ i ∈ modIdx m (x + L),
      (((Finset.Ico x (x + L)).filter (fun n => m i ∣ n)).card : ℝ)
        ≤ (L : ℝ) * (1 / (m i : ℝ)) + 1 := by
    intro i _
    have hmi : 0 < m i := lt_of_lt_of_le (by norm_num) (hm2 i)
    have hmiR : (0 : ℝ) < (m i : ℝ) := by exact_mod_cast hmi
    have hbase := card_filter_dvd_Ico_mul_le (m i) x L hmi
    have hR : (((Finset.Ico x (x + L)).filter (fun n => m i ∣ n)).card : ℝ) * (m i : ℝ)
        ≤ (L : ℝ) + (m i : ℝ) := by exact_mod_cast hbase
    have hkey : ((L : ℝ) + (m i : ℝ)) / (m i : ℝ) = (L : ℝ) * (1 / (m i : ℝ)) + 1 := by
      field_simp
    rw [← hkey, le_div_iff₀ hmiR]
    exact hR
  have hsum1 : ∑ i ∈ modIdx m (x + L),
      (((Finset.Ico x (x + L)).filter (fun n => m i ∣ n)).card : ℝ)
        ≤ ∑ i ∈ modIdx m (x + L), ((L : ℝ) * (1 / (m i : ℝ)) + 1) :=
    Finset.sum_le_sum hterm
  have hsum2 : ∑ i ∈ modIdx m (x + L), ((L : ℝ) * (1 / (m i : ℝ)) + 1)
      = (L : ℝ) * (∑ i ∈ modIdx m (x + L), (1 : ℝ) / (m i : ℝ))
        + ((modIdx m (x + L)).card : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hpartial : (∑ i ∈ modIdx m (x + L), (1 : ℝ) / (m i : ℝ)) ≤ θ := by
    rw [← hθ]
    exact hsum.sum_le_tsum _ (fun i _ => by positivity)
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hsum3 : (L : ℝ) * (∑ i ∈ modIdx m (x + L), (1 : ℝ) / (m i : ℝ)) ≤ (L : ℝ) * θ :=
    mul_le_mul_of_nonneg_left hpartial hLnn
  have hklt : ((modIdx m (x + L)).card : ℝ) < (L : ℝ) * (1 - θ) := by
    rw [div_lt_iff₀ hone] at hkL
    linarith
  have hexp : (L : ℝ) * (1 - θ) = (L : ℝ) - (L : ℝ) * θ := by ring
  linarith

/-- Clause (i) of `long243:res:coprimalitycap`: for pairwise coprime moduli
`m 0 < m 1 < ⋯`, all at least `2`, with `θ = ∑ᵢ 1/mᵢ < 1`, every window
`[x, x+L)` with `x ≥ 1`, `L ≥ 1` and `L > k/(1-θ)`, where `k = #{i : mᵢ ≤ x+L}`,
contains an integer divisible by no `mᵢ`. -/
theorem exists_avoiding_in_window
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    {x L : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L)
    (hkL : ((({i | m i ≤ x + L} : Set ℕ).ncard : ℝ)) / (1 - θ) < (L : ℝ)) :
    ∃ n, x ≤ n ∧ n < x + L ∧ ∀ i, ¬ m i ∣ n := by
  refine exists_window_avoiding_aux hmono hm2 hsum hθ hθ1 hx ?_
  rwa [ncard_setOf_le_eq hmono] at hkL

/-! ### Iterating the window step -/

private lemma exists_iterate_seq
    {Adm : ℕ → Prop} {Lf : ℕ → ℕ} {y₀ : ℕ}
    (hbase : ∃ w, y₀ ≤ w ∧ Adm w)
    (hstep : ∀ y, y₀ ≤ y → ∃ z, y < z ∧ z ≤ y + Lf y ∧ Adm z) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ (∀ n, y₀ ≤ u n) ∧ (∀ n, Adm (u n)) ∧
      (∀ n, u (n + 1) ≤ u n + Lf (u n)) := by
  obtain ⟨w, hw0, hw1⟩ := hbase
  have hnext : ∀ y : {y : ℕ // y₀ ≤ y ∧ Adm y},
      ∃ z : {z : ℕ // y₀ ≤ z ∧ Adm z},
        (y : ℕ) < (z : ℕ) ∧ (z : ℕ) ≤ (y : ℕ) + Lf (y : ℕ) := by
    rintro ⟨y, hy0, hy1⟩
    obtain ⟨z, hz1, hz2, hz3⟩ := hstep y hy0
    exact ⟨⟨z, le_trans hy0 hz1.le, hz3⟩, hz1, hz2⟩
  choose F hF1 hF2 using hnext
  refine ⟨fun n => ((F^[n] (⟨w, hw0, hw1⟩ : {y : ℕ // y₀ ≤ y ∧ Adm y})) : ℕ), ?_,
    fun n => (F^[n] (⟨w, hw0, hw1⟩ : {y : ℕ // y₀ ≤ y ∧ Adm y})).2.1,
    fun n => (F^[n] (⟨w, hw0, hw1⟩ : {y : ℕ // y₀ ≤ y ∧ Adm y})).2.2, ?_⟩
  · refine strictMono_nat_of_lt_succ (fun n => ?_)
    simp only [Function.iterate_succ_apply']
    exact hF1 _
  · intro n
    simp only [Function.iterate_succ_apply']
    exact hF2 _

private lemma exists_avoiding_seq_of_window
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    {Lf : ℕ → ℕ} {y₀ : ℕ} (hy₀ : 1 ≤ y₀)
    (hwin : ∀ y, y₀ ≤ y →
      (((modIdx m (y + 1 + Lf y)).card : ℝ)) / (1 - θ) < (Lf y : ℝ)) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ (∀ n, y₀ ≤ u n) ∧ (∀ n i, ¬ m i ∣ u n) ∧
      (∀ n, u (n + 1) ≤ u n + Lf (u n)) := by
  have hstep : ∀ y, y₀ ≤ y → ∃ z, y < z ∧ z ≤ y + Lf y ∧ ∀ i, ¬ m i ∣ z := by
    intro y hy
    have hx : 1 ≤ y + 1 := by omega
    obtain ⟨n, hn1, hn2, hn3⟩ :=
      exists_window_avoiding_aux hmono hm2 hsum hθ hθ1 hx (hwin y hy)
    exact ⟨n, by omega, by omega, hn3⟩
  have hbase : ∃ w, y₀ ≤ w ∧ ∀ i, ¬ m i ∣ w := by
    obtain ⟨z, hz1, hz2, hz3⟩ := hstep y₀ le_rfl
    exact ⟨z, by omega, hz3⟩
  exact exists_iterate_seq hbase hstep

/-! ### The scale `ℓ x = log₂ log₂ max(4, x)` -/

/-- `ℓ x = log₂ log₂ max(4, x)`, the scale of the long #243 note. -/
def ellScale (x : ℝ) : ℝ := Real.logb 2 (Real.logb 2 (max 4 x))

private lemma log_two_pos' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

private lemma logb_two_two : Real.logb 2 (2 : ℝ) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
  rw [Real.logb]
  field_simp

private lemma logb_two_four : Real.logb 2 (4 : ℝ) = 2 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos'
  have h4 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
  rw [Real.logb, h4, Real.log_pow]
  push_cast
  field_simp

private lemma two_le_inner (x : ℝ) : 2 ≤ Real.logb 2 (max 4 x) := by
  calc (2 : ℝ) = Real.logb 2 4 := logb_two_four.symm
    _ ≤ Real.logb 2 (max 4 x) :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num) (le_max_left _ _)

/-- The scale is at least `1`. -/
lemma one_le_ellScale (x : ℝ) : 1 ≤ ellScale x := by
  have h := two_le_inner x
  calc (1 : ℝ) = Real.logb 2 2 := logb_two_two.symm
    _ ≤ Real.logb 2 (Real.logb 2 (max 4 x)) :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num) h

/-- The scale is monotone. -/
lemma ellScale_mono {x y : ℝ} (h : x ≤ y) : ellScale x ≤ ellScale y := by
  have hin : Real.logb 2 (max 4 x) ≤ Real.logb 2 (max 4 y) :=
    Real.logb_le_logb_of_le (by norm_num)
      (lt_of_lt_of_le (by norm_num) (le_max_left (4 : ℝ) x)) (max_le_max le_rfl h)
  exact Real.logb_le_logb_of_le (by norm_num)
    (lt_of_lt_of_le (by norm_num) (two_le_inner x)) hin

/-- Squaring the argument raises the scale by at most one. -/
private lemma ellScale_le_add_one {y z : ℝ} (hy : 4 ≤ y) (hz : z ≤ y ^ 2) :
    ellScale z ≤ ellScale y + 1 := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hmaxy : max 4 y = y := max_eq_right hy
  have hmaxz : max 4 z ≤ y ^ 2 := by
    refine max_le ?_ hz
    nlinarith
  have hlogy : (2 : ℝ) ≤ Real.logb 2 y := by
    have h := two_le_inner y; rwa [hmaxy] at h
  have hsq : Real.logb 2 (y ^ 2) = 2 * Real.logb 2 y := by
    rw [Real.logb_pow]; norm_num
  have h1 : Real.logb 2 (max 4 z) ≤ 2 * Real.logb 2 y := by
    have hle := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (lt_of_lt_of_le (by norm_num) (le_max_left (4 : ℝ) z)) hmaxz
    rwa [hsq] at hle
  have h2 : Real.logb 2 (Real.logb 2 (max 4 z)) ≤ Real.logb 2 (2 * Real.logb 2 y) :=
    Real.logb_le_logb_of_le (by norm_num)
      (lt_of_lt_of_le (by norm_num) (two_le_inner z)) h1
  have h3 : Real.logb 2 (2 * Real.logb 2 y) = 1 + Real.logb 2 (Real.logb 2 y) := by
    rw [Real.logb_mul (by norm_num) (by linarith), logb_two_two]
  have helly : ellScale y = Real.logb 2 (Real.logb 2 y) := by rw [ellScale, hmaxy]
  have hellz : ellScale z = Real.logb 2 (Real.logb 2 (max 4 z)) := rfl
  rw [hellz, helly]
  linarith

private lemma log_le_half {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / 2 := by
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hne : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht)
  have h2 : Real.log t = Real.log (Real.sqrt t) + Real.log (Real.sqrt t) := by
    rw [← Real.log_mul hne hne, hsq]
  nlinarith [sq_nonneg (Real.sqrt t - 2)]

private lemma logb_two_le_self {t : ℝ} (ht : 0 < t) : Real.logb 2 t ≤ t := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hpos : (0 : ℝ) < Real.log 2 := by linarith
  have h1 : Real.log t ≤ t / 2 := log_le_half ht
  have hmul : t * (0.6931471803 : ℝ) ≤ t * Real.log 2 :=
    mul_le_mul_of_nonneg_left (le_of_lt hlog2) (le_of_lt ht)
  rw [Real.logb, div_le_iff₀ hpos]
  linarith

private lemma ellScale_le_self {y : ℝ} (hy : 4 ≤ y) : ellScale y ≤ y := by
  have hmaxy : max 4 y = y := max_eq_right hy
  have hinner : (2 : ℝ) ≤ Real.logb 2 y := by
    have h := two_le_inner y; rwa [hmaxy] at h
  have h1 : Real.logb 2 y ≤ y := logb_two_le_self (by linarith)
  have h2 : Real.logb 2 (Real.logb 2 y) ≤ Real.logb 2 y := logb_two_le_self (by linarith)
  have helly : ellScale y = Real.logb 2 (Real.logb 2 y) := by rw [ellScale, hmaxy]
  rw [helly]
  linarith

private lemma logb_two_pow (k : ℕ) : Real.logb 2 ((2 : ℝ) ^ k) = (k : ℝ) := by
  rw [Real.logb_pow, logb_two_two, mul_one]

private lemma ellScale_two_pow_two_pow {n : ℕ} (hn : 1 ≤ n) :
    ellScale ((2 : ℝ) ^ (2 ^ n)) = (n : ℝ) := by
  have hnat : (4 : ℕ) ≤ 2 ^ (2 ^ n) := by
    have h2 : (2 : ℕ) ≤ 2 ^ n := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 ^ n) := Nat.pow_le_pow_right (by norm_num) h2
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (2 ^ n) := by exact_mod_cast hnat
  rw [ellScale, max_eq_right h4, logb_two_pow]
  push_cast
  rw [logb_two_pow]

private lemma exists_ellScale_ge (M : ℝ) :
    ∃ N : ℕ, ∀ y : ℕ, N ≤ y → M ≤ ellScale (y : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_ge M
  refine ⟨2 ^ (2 ^ (n + 1)), fun y hy => ?_⟩
  have h1 : ellScale ((2 : ℝ) ^ (2 ^ (n + 1))) = ((n : ℝ) + 1) := by
    have h := ellScale_two_pow_two_pow (n := n + 1) (by omega)
    push_cast at h
    exact h
  have h2 : ((2 : ℝ) ^ (2 ^ (n + 1))) ≤ (y : ℝ) := by
    have hc : ((2 ^ (2 ^ (n + 1)) : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    push_cast at hc
    exact hc
  have h3 := ellScale_mono h2
  rw [h1] at h3
  linarith

/-! ### Clause (ii): a slowly rising sequence avoiding a tail of the family -/

private lemma card_shift_le
    {m : ℕ → ℕ} (hmono : StrictMono m) {C : ℝ}
    (hC : ∀ i, |ellScale (m i : ℝ) - (i : ℝ)| ≤ C) (hC0 : 0 ≤ C) (T z : ℕ) :
    (((modIdx (fun j => m (j + T)) z).card : ℝ)) ≤ ellScale (z : ℝ) + C + 2 := by
  have hmono' : StrictMono (fun j => m (j + T)) := by
    intro a b hab
    exact hmono (by omega)
  have hX : (0 : ℝ) ≤ ellScale (z : ℝ) + C := by
    have := one_le_ellScale (z : ℝ); linarith
  have hsubset : modIdx (fun j => m (j + T)) z
      ⊆ Finset.range (⌈ellScale (z : ℝ) + C⌉₊ + 1) := by
    intro j hj
    have hjz : m (j + T) ≤ z := (mem_modIdx hmono' z j).mp hj
    have hcast : ((m (j + T) : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast hjz
    have hell : ellScale ((m (j + T) : ℕ) : ℝ) ≤ ellScale (z : ℝ) := ellScale_mono hcast
    have habs := hC (j + T)
    rw [abs_le] at habs
    have hlow := habs.1
    push_cast at hlow
    have hT0 : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
    have hjle : (j : ℝ) ≤ ellScale (z : ℝ) + C := by linarith
    have hceil : (j : ℝ) ≤ (⌈ellScale (z : ℝ) + C⌉₊ : ℝ) := le_trans hjle (Nat.le_ceil _)
    have hjnat : j ≤ ⌈ellScale (z : ℝ) + C⌉₊ := by exact_mod_cast hceil
    exact Finset.mem_range.mpr (by omega)
  have hcard : (modIdx (fun j => m (j + T)) z).card ≤ ⌈ellScale (z : ℝ) + C⌉₊ + 1 := by
    have h := Finset.card_le_card hsubset
    simpa using h
  have hcardR : (((modIdx (fun j => m (j + T)) z).card : ℝ))
      ≤ ((⌈ellScale (z : ℝ) + C⌉₊ : ℝ) + 1) := by exact_mod_cast hcard
  have hceil2 : (⌈ellScale (z : ℝ) + C⌉₊ : ℝ) < ellScale (z : ℝ) + C + 1 :=
    Nat.ceil_lt_add_one hX
  linarith

/-- Clause (ii) of `long243:res:coprimalitycap`.  If in addition
`ℓ(mᵢ) = i + O(1)`, then for every `ε > 0` there are an index `T` and a
strictly increasing sequence `(uₙ)` of positive integers such that `mᵢ ∤ uₙ`
for every `i ≥ T` and every `n`, and `u_{n+1} - uₙ ≤ (1+ε) ℓ(uₙ)` eventually. -/
theorem exists_slow_rise_avoiding_sequence
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    (hscale : ∃ C : ℝ, ∀ i, |ellScale (m i : ℝ) - (i : ℝ)| ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : ℕ) (u : ℕ → ℕ), StrictMono u ∧ (∀ n, 0 < u n) ∧
      (∀ i, T ≤ i → ∀ n, ¬ m i ∣ u n) ∧
      ∀ᶠ n in atTop, ((u (n + 1) : ℝ) - (u n : ℝ)) ≤ (1 + ε) * ellScale (u n : ℝ) := by
  obtain ⟨C, hC⟩ := hscale
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    have h1 := one_le_ellScale ((m 0 : ℕ) : ℝ)
    rw [abs_le] at h0
    have h2 := h0.2
    push_cast at h2
    linarith
  have hεpos : (0 : ℝ) < 1 + ε := by linarith
  have hδ₀ : (0 : ℝ) < ε / (1 + ε) := by positivity
  have htail : Tendsto (fun T => ∑' k, (1 : ℝ) / (m (k + T) : ℝ)) atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun i => (1 : ℝ) / (m i : ℝ))
  obtain ⟨T, hT⟩ := (htail.eventually (gt_mem_nhds hδ₀)).exists
  have hmono' : StrictMono (fun j => m (j + T)) := by
    intro a b hab; exact hmono (by omega)
  have hm2' : ∀ j, 2 ≤ (fun j => m (j + T)) j := fun j => hm2 _
  have hsum' : Summable fun j => (1 : ℝ) / ((fun j => m (j + T)) j : ℝ) :=
    (summable_nat_add_iff (f := fun i => (1 : ℝ) / (m i : ℝ)) T).mpr hsum
  have hθ'0 : 0 ≤ ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ) :=
    tsum_nonneg (fun j => by positivity)
  have hθ'lt : (∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) < ε / (1 + ε) := hT
  have hθ'1 : (∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) < 1 := by
    have hlt1 : ε / (1 + ε) < 1 := by
      rw [div_lt_one hεpos]; linarith
    linarith
  have hone' : (0 : ℝ) < 1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ) := by linarith
  -- pick ρ strictly between (1-θ')⁻¹ and 1+ε
  have hlt : 1 / (1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) < 1 + ε := by
    rw [div_lt_iff₀ hone']
    have h1 : (∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) * (1 + ε) < ε := by
      have h := hθ'lt
      rw [lt_div_iff₀ hεpos] at h
      exact h
    nlinarith
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_between hlt
  have hδ : 0 < ρ * (1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) - 1 := by
    rw [div_lt_iff₀ hone'] at hρ1
    linarith
  have hρpos : (0 : ℝ) < ρ := by nlinarith
  have hη : (0 : ℝ) < 1 + ε - ρ := by linarith
  obtain ⟨N₁, hN₁⟩ := exists_ellScale_ge
    ((C + 3) / (ρ * (1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) - 1) + 1)
  obtain ⟨N₂, hN₂⟩ := exists_ellScale_ge (1 / (1 + ε - ρ))
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ℕ → ℕ, ∀ y : ℕ, Lf y = ⌈ρ * ellScale (y : ℝ)⌉₊ :=
    ⟨_, fun _ => rfl⟩
  have hLfle : ∀ y : ℕ, (Lf y : ℝ) ≤ ρ * ellScale (y : ℝ) + 1 := by
    intro y
    have hnn : (0 : ℝ) ≤ ρ * ellScale (y : ℝ) := by
      have := one_le_ellScale (y : ℝ); nlinarith
    rw [hLf y]
    exact le_of_lt (Nat.ceil_lt_add_one hnn)
  have hLfge : ∀ y : ℕ, ρ * ellScale (y : ℝ) ≤ (Lf y : ℝ) := by
    intro y; rw [hLf y]; exact Nat.le_ceil _
  refine ?_
  obtain ⟨y₀, hy₀def⟩ : ∃ y₀ : ℕ, y₀ = max (max 4 (⌈ρ⌉₊ + 3)) (max N₁ N₂) := ⟨_, rfl⟩
  have hy₀1 : 1 ≤ y₀ := by
    have h4 : 4 ≤ y₀ := by rw [hy₀def]; omega
    omega
  have hkey : ∀ y : ℕ, y₀ ≤ y →
      (4 : ℝ) ≤ (y : ℝ) ∧
      (C + 3) / (ρ * (1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) - 1) + 1
        ≤ ellScale (y : ℝ) ∧
      1 / (1 + ε - ρ) ≤ ellScale (y : ℝ) ∧
      ((y : ℝ) + 1 + (Lf y : ℝ)) ≤ (y : ℝ) ^ 2 := by
    intro y hy
    rw [hy₀def] at hy
    have h4 : 4 ≤ y := by omega
    have hrho3 : ⌈ρ⌉₊ + 3 ≤ y := by omega
    have hN1 : N₁ ≤ y := by omega
    have hN2 : N₂ ≤ y := by omega
    have h4R : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast h4
    have hrhoR : ρ + 3 ≤ (y : ℝ) := by
      have h1 : (ρ : ℝ) ≤ (⌈ρ⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈ρ⌉₊ + 3 : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hrho3
      push_cast at h2
      linarith
    have hells : ellScale (y : ℝ) ≤ (y : ℝ) := ellScale_le_self h4R
    have hb : (Lf y : ℝ) ≤ ρ * (y : ℝ) + 1 := by
      have h1 : ρ * ellScale (y : ℝ) ≤ ρ * (y : ℝ) :=
        mul_le_mul_of_nonneg_left hells (le_of_lt hρpos)
      have h2 := hLfle y
      linarith
    have hsquare : ((y : ℝ) + 1 + (Lf y : ℝ)) ≤ (y : ℝ) ^ 2 := by nlinarith
    exact ⟨h4R, hN₁ y hN1, hN₂ y hN2, hsquare⟩
  have hwin : ∀ y, y₀ ≤ y →
      (((modIdx (fun j => m (j + T)) (y + 1 + Lf y)).card : ℝ))
        / (1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) < (Lf y : ℝ) := by
    intro y hy
    obtain ⟨h4R, hEll1, hEll2, hsquare⟩ := hkey y hy
    have hellpos : 1 ≤ ellScale (y : ℝ) := one_le_ellScale _
    have hcast : ((y + 1 + Lf y : ℕ) : ℝ) = (y : ℝ) + 1 + (Lf y : ℝ) := by push_cast; ring
    have hk := card_shift_le hmono hC hC0 T (y + 1 + Lf y)
    have hup : ellScale (((y + 1 + Lf y : ℕ) : ℝ)) ≤ ellScale (y : ℝ) + 1 := by
      rw [hcast]
      exact ellScale_le_add_one h4R hsquare
    have hkle : (((modIdx (fun j => m (j + T)) (y + 1 + Lf y)).card : ℝ))
        ≤ ellScale (y : ℝ) + C + 3 := by linarith
    have hδell : C + 3
        < (ρ * (1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) - 1) * ellScale (y : ℝ) := by
      have h1 : (C + 3) / (ρ * (1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) - 1)
          < ellScale (y : ℝ) := by linarith
      rw [div_lt_iff₀ hδ] at h1
      linarith
    rw [div_lt_iff₀ hone']
    have hexpand : ρ * ellScale (y : ℝ)
        * (1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ))
        ≤ (Lf y : ℝ) * (1 - ∑' j, (1 : ℝ) / ((fun j => m (j + T)) j : ℝ)) :=
      mul_le_mul_of_nonneg_right (hLfge y) (le_of_lt hone')
    nlinarith
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ :=
    exists_avoiding_seq_of_window hmono' hm2' hsum' rfl hθ'1 hy₀1 hwin
  refine ⟨T, u, hu1, fun n => lt_of_lt_of_le (by omega) (hu2 n), ?_, ?_⟩
  · intro i hi n hdvd
    have heq : m ((i - T) + T) = m i := by congr 1; omega
    exact hu3 n (i - T) (by simpa [heq] using hdvd)
  · refine Filter.Eventually.of_forall (fun n => ?_)
    have hyn : y₀ ≤ u n := hu2 n
    obtain ⟨h4R, hEll1, hEll2, _⟩ := hkey (u n) hyn
    have hgap : (u (n + 1) : ℝ) ≤ (u n : ℝ) + (Lf (u n) : ℝ) := by
      have hc : ((u (n + 1) : ℕ) : ℝ) ≤ ((u n + Lf (u n) : ℕ) : ℝ) := by exact_mod_cast hu4 n
      push_cast at hc
      exact hc
    have hL := hLfle (u n)
    have hηell : 1 ≤ ellScale ((u n : ℕ) : ℝ) * (1 + ε - ρ) := by
      have h1 : 1 / (1 + ε - ρ) ≤ ellScale ((u n : ℕ) : ℝ) := hEll2
      rw [div_le_iff₀ hη] at h1
      linarith
    nlinarith

/-! ### Sparse prime moduli -/

private def primeBound (i : ℕ) : ℕ :=
  max ⌈Real.exp (Real.exp (((i : ℝ) + 2) ^ 2))⌉₊ (2 ^ (i + 4))

private def sparsePrimeStep (b prev : ℕ) : ℕ :=
  (Nat.exists_infinite_primes (max b prev + 1)).choose

private lemma sparsePrimeStep_spec (b prev : ℕ) :
    max b prev < sparsePrimeStep b prev ∧ Nat.Prime (sparsePrimeStep b prev) := by
  obtain ⟨h1, h2⟩ : max b prev + 1 ≤ sparsePrimeStep b prev
      ∧ Nat.Prime (sparsePrimeStep b prev) :=
    (Nat.exists_infinite_primes (max b prev + 1)).choose_spec
  exact ⟨by omega, h2⟩

private def sparsePrime : ℕ → ℕ
  | 0 => sparsePrimeStep (primeBound 0) 0
  | (i + 1) => sparsePrimeStep (primeBound (i + 1)) (sparsePrime i)

private lemma sparsePrime_prime (i : ℕ) : Nat.Prime (sparsePrime i) := by
  cases i with
  | zero => exact (sparsePrimeStep_spec (primeBound 0) 0).2
  | succ k => exact (sparsePrimeStep_spec (primeBound (k + 1)) (sparsePrime k)).2

private lemma primeBound_lt_sparsePrime (i : ℕ) : primeBound i < sparsePrime i := by
  cases i with
  | zero =>
      have h : max (primeBound 0) 0 < sparsePrimeStep (primeBound 0) 0 :=
        (sparsePrimeStep_spec (primeBound 0) 0).1
      have heq : sparsePrime 0 = sparsePrimeStep (primeBound 0) 0 := rfl
      omega
  | succ k =>
      have h : max (primeBound (k + 1)) (sparsePrime k)
          < sparsePrimeStep (primeBound (k + 1)) (sparsePrime k) :=
        (sparsePrimeStep_spec (primeBound (k + 1)) (sparsePrime k)).1
      have heq : sparsePrime (k + 1) = sparsePrimeStep (primeBound (k + 1)) (sparsePrime k) := rfl
      omega

private lemma sparsePrime_strictMono : StrictMono sparsePrime := by
  refine strictMono_nat_of_lt_succ (fun i => ?_)
  have h : max (primeBound (i + 1)) (sparsePrime i)
      < sparsePrimeStep (primeBound (i + 1)) (sparsePrime i) :=
    (sparsePrimeStep_spec (primeBound (i + 1)) (sparsePrime i)).1
  have heq : sparsePrime (i + 1) = sparsePrimeStep (primeBound (i + 1)) (sparsePrime i) := rfl
  omega

private lemma two_pow_lt_sparsePrime (i : ℕ) : 2 ^ (i + 4) < sparsePrime i := by
  have h := primeBound_lt_sparsePrime i
  have h2 : 2 ^ (i + 4) ≤ primeBound i := le_max_right _ _
  omega

private lemma expexp_lt_sparsePrime (i : ℕ) :
    Real.exp (Real.exp (((i : ℝ) + 2) ^ 2)) < (sparsePrime i : ℝ) := by
  have h1 : Real.exp (Real.exp (((i : ℝ) + 2) ^ 2))
      ≤ (⌈Real.exp (Real.exp (((i : ℝ) + 2) ^ 2))⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ⌈Real.exp (Real.exp (((i : ℝ) + 2) ^ 2))⌉₊ ≤ primeBound i := le_max_left _ _
  have h3 := primeBound_lt_sparsePrime i
  have h4 : ((⌈Real.exp (Real.exp (((i : ℝ) + 2) ^ 2))⌉₊ : ℕ) : ℝ) < (sparsePrime i : ℝ) := by
    have hlt : (⌈Real.exp (Real.exp (((i : ℝ) + 2) ^ 2))⌉₊ : ℕ) < sparsePrime i := by omega
    exact_mod_cast hlt
  linarith

private lemma sparsePrime_two_le (i : ℕ) : 2 ≤ sparsePrime i := (sparsePrime_prime i).two_le

private lemma sparsePrime_coprime (i j : ℕ) (hij : i ≠ j) :
    Nat.Coprime (sparsePrime i) (sparsePrime j) := by
  rw [Nat.coprime_primes (sparsePrime_prime i) (sparsePrime_prime j)]
  exact fun h => hij (sparsePrime_strictMono.injective h)

private lemma sparse_recip_le (i : ℕ) :
    (1 : ℝ) / (sparsePrime i : ℝ) ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ i := by
  have h := two_pow_lt_sparsePrime i
  have hR : ((2 : ℝ) ^ (i + 4)) < (sparsePrime i : ℝ) := by exact_mod_cast h
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (i + 4) := by positivity
  have hkey : (1 : ℝ) / (sparsePrime i : ℝ) ≤ 1 / ((2 : ℝ) ^ (i + 4)) :=
    one_div_le_one_div_of_le hpos (le_of_lt hR)
  have hval : (1 : ℝ) / ((2 : ℝ) ^ (i + 4)) = (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ i := by
    have h1 : (1 / 2 : ℝ) ^ i = 1 / (2 : ℝ) ^ i := by rw [div_pow, one_pow]
    have h2 : ((2 : ℝ)) ^ (i + 4) = (2 : ℝ) ^ i * 16 := by rw [pow_add]; norm_num
    have hne : ((2 : ℝ) ^ i) ≠ 0 := by positivity
    rw [h1, h2]
    field_simp
    all_goals ring
  linarith [hkey, hval.le, hval.ge]

private lemma sparse_geom_summable : Summable (fun i : ℕ => (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ i) :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

private lemma sparse_summable : Summable (fun i : ℕ => (1 : ℝ) / (sparsePrime i : ℝ)) :=
  Summable.of_nonneg_of_le (fun i => by positivity) sparse_recip_le sparse_geom_summable

private lemma sparse_theta_le : ∑' i, (1 : ℝ) / (sparsePrime i : ℝ) ≤ 1 / 8 := by
  have h1 : ∑' i, (1 : ℝ) / (sparsePrime i : ℝ)
      ≤ ∑' i : ℕ, (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ i :=
    sparse_summable.tsum_le_tsum sparse_recip_le sparse_geom_summable
  have h2 : ∑' i : ℕ, (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ i = 1 / 8 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  linarith

/-! ### Elementary real estimates for the sparse construction -/

private lemma expexp_ge_seven : (7 : ℝ) ≤ Real.exp (Real.exp 1) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h1 : Real.exp 2 ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr he
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  nlinarith

private lemma expexp_le_twentyone : Real.exp (Real.exp 1) ≤ 21 := by
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; linarith
  have h1 : Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr he
  have h2 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h4 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  nlinarith

private lemma one_le_loglog {t : ℝ} (ht : Real.exp (Real.exp 1) ≤ t) :
    1 ≤ Real.log (Real.log t) := by
  have h0 : (0 : ℝ) < Real.exp (Real.exp 1) := Real.exp_pos _
  have h1 : Real.exp 1 ≤ Real.log t := by
    have h := Real.log_le_log h0 ht
    rwa [Real.log_exp] at h
  have h2 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h3 := Real.log_le_log h2 h1
  rwa [Real.log_exp] at h3

private lemma loglog_le_self {t : ℝ} (ht : 1 < t) : Real.log (Real.log t) ≤ t := by
  have htpos : (0 : ℝ) < t := by linarith
  have hlogpos : (0 : ℝ) < Real.log t := Real.log_pos ht
  have h1 : Real.log t ≤ t / 2 := log_le_half htpos
  have h2 : Real.log (Real.log t) ≤ Real.log t / 2 := log_le_half hlogpos
  linarith

/-- If `z ≤ t ^ 2` then `log log z ≤ log log t + 1`. -/
private lemma loglog_square_le {t z : ℝ} (ht : 1 < t) (hz : 1 < z) (hzt : z ≤ t ^ 2) :
    Real.log (Real.log z) ≤ Real.log (Real.log t) + 1 := by
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos ht
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz
  have hzpos : (0 : ℝ) < z := by linarith
  have h1 : Real.log z ≤ 2 * Real.log t := by
    have h := Real.log_le_log hzpos hzt
    rwa [show Real.log (t ^ 2) = 2 * Real.log t by rw [Real.log_pow]; norm_num] at h
  have h2 : Real.log (Real.log z) ≤ Real.log (2 * Real.log t) := Real.log_le_log hlogz h1
  have h3 : Real.log (2 * Real.log t) = Real.log 2 + Real.log (Real.log t) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hlogt)]
  have h4 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  linarith

private lemma sqrt_add_one_le {a : ℝ} (ha : 0 ≤ a) : Real.sqrt (a + 1) ≤ Real.sqrt a + 1 := by
  have h2 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have h0 : (0 : ℝ) ≤ Real.sqrt a + 1 := by linarith
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsq : a + 1 ≤ (Real.sqrt a + 1) ^ 2 := by nlinarith
  calc Real.sqrt (a + 1) ≤ Real.sqrt ((Real.sqrt a + 1) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt a + 1 := Real.sqrt_sq h0

private lemma sparse_card_le (z : ℕ) :
    (((modIdx sparsePrime z).card : ℝ)) ≤ Real.sqrt (Real.log (Real.log (z : ℝ))) := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log (Real.log (z : ℝ))) := Real.sqrt_nonneg _
  have hsubset : modIdx sparsePrime z
      ⊆ Finset.range ⌈Real.sqrt (Real.log (Real.log (z : ℝ))) - 2⌉₊ := by
    intro i hi
    have hiz : sparsePrime i ≤ z := (mem_modIdx sparsePrime_strictMono z i).mp hi
    have hizR : (sparsePrime i : ℝ) ≤ (z : ℝ) := by exact_mod_cast hiz
    have hexp := expexp_lt_sparsePrime i
    have hlt : Real.exp (Real.exp (((i : ℝ) + 2) ^ 2)) < (z : ℝ) := by linarith
    have hstep1 : Real.exp (((i : ℝ) + 2) ^ 2) < Real.log (z : ℝ) := by
      have h := Real.log_lt_log (Real.exp_pos _) hlt
      rwa [Real.log_exp] at h
    have hstep2 : ((i : ℝ) + 2) ^ 2 < Real.log (Real.log (z : ℝ)) := by
      have h := Real.log_lt_log (Real.exp_pos _) hstep1
      rwa [Real.log_exp] at h
    have hnn : (0 : ℝ) ≤ Real.log (Real.log (z : ℝ)) := by
      nlinarith [sq_nonneg ((i : ℝ) + 2)]
    have hsq : Real.sqrt (Real.log (Real.log (z : ℝ))) ^ 2 = Real.log (Real.log (z : ℝ)) :=
      Real.sq_sqrt hnn
    have hilt : (i : ℝ) + 2 < Real.sqrt (Real.log (Real.log (z : ℝ))) := by
      by_contra hcon
      push_neg at hcon
      have hi0 : (0 : ℝ) ≤ (i : ℝ) + 2 := by positivity
      nlinarith
    have hceil : (i : ℝ) < (⌈Real.sqrt (Real.log (Real.log (z : ℝ))) - 2⌉₊ : ℝ) := by
      have h2 : Real.sqrt (Real.log (Real.log (z : ℝ))) - 2
          ≤ (⌈Real.sqrt (Real.log (Real.log (z : ℝ))) - 2⌉₊ : ℝ) := Nat.le_ceil _
      linarith
    exact Finset.mem_range.mpr (by exact_mod_cast hceil)
  have hcard : (modIdx sparsePrime z).card
      ≤ ⌈Real.sqrt (Real.log (Real.log (z : ℝ))) - 2⌉₊ := by
    have h := Finset.card_le_card hsubset
    simpa using h
  have hcardR : (((modIdx sparsePrime z).card : ℝ))
      ≤ (⌈Real.sqrt (Real.log (Real.log (z : ℝ))) - 2⌉₊ : ℝ) := by exact_mod_cast hcard
  by_cases hle : Real.sqrt (Real.log (Real.log (z : ℝ))) ≤ 2
  · have hz : ⌈Real.sqrt (Real.log (Real.log (z : ℝ))) - 2⌉₊ = 0 :=
      Nat.ceil_eq_zero.mpr (by linarith)
    rw [hz] at hcardR
    push_cast at hcardR
    linarith
  · have hgt : (2 : ℝ) < Real.sqrt (Real.log (Real.log (z : ℝ))) := not_le.mp hle
    have hc : (⌈Real.sqrt (Real.log (Real.log (z : ℝ))) - 2⌉₊ : ℝ)
        < (Real.sqrt (Real.log (Real.log (z : ℝ))) - 2) + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    linarith

/-! ### The window length for the sparse prime family -/

private def bigL (x : ℕ) : ℕ :=
  ⌈4 * Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 8⌉₊

private lemma bigL_ge (x : ℕ) :
    4 * Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 8 ≤ (bigL x : ℝ) :=
  Nat.le_ceil _

private lemma bigL_le (x : ℕ) :
    (bigL x : ℝ)
      ≤ 4 * Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 9 := by
  have hnn : (0 : ℝ)
      ≤ 4 * Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 8 := by
    have := Real.sqrt_nonneg (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1))))
    linarith
  have h : ((bigL x : ℕ) : ℝ)
      < 4 * Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 8 + 1 :=
    Nat.ceil_lt_add_one hnn
  linarith

private lemma bigL_ge_eight (x : ℕ) : (8 : ℝ) ≤ (bigL x : ℝ) := by
  have h := bigL_ge x
  have := Real.sqrt_nonneg (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1))))
  linarith

/-- The window condition of clause (i) holds for the sparse prime family with the
window length `bigL`. -/
private lemma sparse_window (x : ℕ) :
    (((modIdx sparsePrime (x + bigL x)).card : ℝ))
        / (1 - ∑' i, (1 : ℝ) / (sparsePrime i : ℝ)) < (bigL x : ℝ) := by
  have hθ0 : (0 : ℝ) ≤ ∑' i, (1 : ℝ) / (sparsePrime i : ℝ) :=
    tsum_nonneg (fun i => by positivity)
  have hθle : (∑' i, (1 : ℝ) / (sparsePrime i : ℝ)) ≤ 1 / 8 := sparse_theta_le
  have hone : (0 : ℝ) < 1 - ∑' i, (1 : ℝ) / (sparsePrime i : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := Nat.cast_nonneg x
  have hee7 := expexp_ge_seven
  have ht7 : (7 : ℝ) ≤ (x : ℝ) + Real.exp (Real.exp 1) := by linarith
  have htee : Real.exp (Real.exp 1) ≤ (x : ℝ) + Real.exp (Real.exp 1) := by linarith
  have hA1 : 1 ≤ Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) := by
    have h1 : 1 ≤ Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1))) := one_le_loglog htee
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_one] at h2
  have hLge := bigL_ge x
  have hLle := bigL_le x
  -- the window fits inside `t ^ 2`
  have hloglogle : Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))
      ≤ (x : ℝ) + Real.exp (Real.exp 1) := loglog_le_self (by linarith)
  have hAhalf : Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1))))
      ≤ ((x : ℝ) + Real.exp (Real.exp 1)) / 2 := by
    have h2 : Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))
        ≤ (((x : ℝ) + Real.exp (Real.exp 1)) / 2) ^ 2 := by nlinarith
    calc Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1))))
        ≤ Real.sqrt ((((x : ℝ) + Real.exp (Real.exp 1)) / 2) ^ 2) := Real.sqrt_le_sqrt h2
      _ = ((x : ℝ) + Real.exp (Real.exp 1)) / 2 := Real.sqrt_sq (by linarith)
  have hcastz : ((x + bigL x : ℕ) : ℝ) = (x : ℝ) + (bigL x : ℝ) := by push_cast; ring
  have hwin2 : ((x + bigL x : ℕ) : ℝ) ≤ ((x : ℝ) + Real.exp (Real.exp 1)) ^ 2 := by
    rw [hcastz]; nlinarith
  have h8 := bigL_ge_eight x
  have hzgt1 : (1 : ℝ) < ((x + bigL x : ℕ) : ℝ) := by rw [hcastz]; linarith
  have hll : Real.log (Real.log ((x + bigL x : ℕ) : ℝ))
      ≤ Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1))) + 1 :=
    loglog_square_le (by linarith) hzgt1 hwin2
  have hknn : (0 : ℝ) ≤ Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1))) := by
    linarith [one_le_loglog htee]
  have hk : (((modIdx sparsePrime (x + bigL x)).card : ℝ))
      ≤ Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 1 := by
    have h1 := sparse_card_le (x + bigL x)
    have h2 : Real.sqrt (Real.log (Real.log ((x + bigL x : ℕ) : ℝ)))
        ≤ Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1))) + 1) :=
      Real.sqrt_le_sqrt hll
    have h3 : Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1))) + 1)
        ≤ Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 1 :=
      sqrt_add_one_le hknn
    linarith
  rw [div_lt_iff₀ hone]
  have hmul : (4 * Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 8)
      * (1 - ∑' i, (1 : ℝ) / (sparsePrime i : ℝ))
      ≤ (bigL x : ℝ) * (1 - ∑' i, (1 : ℝ) / (sparsePrime i : ℝ)) :=
    mul_le_mul_of_nonneg_right hLge (le_of_lt hone)
  have hmul2 : (4 * Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 8)
      * (7 / 8 : ℝ)
      ≤ (4 * Real.sqrt (Real.log (Real.log ((x : ℝ) + Real.exp (Real.exp 1)))) + 8)
        * (1 - ∑' i, (1 : ℝ) / (sparsePrime i : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- `long243:res:variablerise`: there are strictly increasing primes `pᵢ` and a
strictly increasing sequence `uₙ → ∞` of positive integers, coprime to every
`pᵢ`, with `u_{n+1} - uₙ = O(√(log log (uₙ + e^e))) = o(log log (uₙ + 3))`. -/
theorem exists_sparse_prime_coprime_sequence :
    ∃ (p : ℕ → ℕ) (u : ℕ → ℕ),
      StrictMono p ∧ (∀ i, Nat.Prime (p i)) ∧
      StrictMono u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop atTop ∧
      (∀ i n, Nat.Coprime (u n) (p i)) ∧
      (∃ Cst : ℝ, ∀ n, ((u (n + 1) : ℝ) - (u n : ℝ))
          ≤ Cst * Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))))) ∧
      Tendsto (fun n => ((u (n + 1) : ℝ) - (u n : ℝ))
          / Real.log (Real.log ((u n : ℝ) + 3))) atTop (𝓝 0) := by
  have hθ1 : (∑' i, (1 : ℝ) / (sparsePrime i : ℝ)) < 1 :=
    lt_of_le_of_lt sparse_theta_le (by norm_num)
  have hwin : ∀ y, 1 ≤ y →
      (((modIdx sparsePrime (y + 1 + bigL (y + 1))).card : ℝ))
        / (1 - ∑' i, (1 : ℝ) / (sparsePrime i : ℝ)) < (bigL (y + 1) : ℝ) := by
    intro y _
    exact sparse_window (y + 1)
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ :=
    exists_avoiding_seq_of_window sparsePrime_strictMono sparsePrime_two_le
      sparse_summable rfl hθ1 (le_refl 1) hwin
  have hutop : Tendsto u atTop atTop :=
    tendsto_atTop_mono (fun n => hu1.le_apply) tendsto_id
  -- the gap bound with constant 17, valid at every index
  have hgap17 : ∀ n, ((u (n + 1) : ℝ) - (u n : ℝ))
      ≤ 17 * Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1)))) := by
    intro n
    have hu0 : (0 : ℝ) ≤ (u n : ℝ) := Nat.cast_nonneg _
    have hee7 := expexp_ge_seven
    have htee : Real.exp (Real.exp 1) ≤ (u n : ℝ) + Real.exp (Real.exp 1) := by linarith
    have ht7 : (7 : ℝ) ≤ (u n : ℝ) + Real.exp (Real.exp 1) := by linarith
    have hA1 : 1 ≤ Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1)))) := by
      have h1 : 1 ≤ Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))) :=
        one_le_loglog htee
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at h2
    have hgap : (u (n + 1) : ℝ) ≤ (u n : ℝ) + (bigL (u n + 1) : ℝ) := by
      have hc : ((u (n + 1) : ℕ) : ℝ) ≤ ((u n + bigL (u n + 1) : ℕ) : ℝ) := by
        exact_mod_cast hu4 n
      push_cast at hc
      exact hc
    have hcast' : ((u n + 1 : ℕ) : ℝ) + Real.exp (Real.exp 1)
        = ((u n : ℝ) + Real.exp (Real.exp 1)) + 1 := by push_cast; ring
    have ht'gt1 : (1 : ℝ) < ((u n : ℝ) + Real.exp (Real.exp 1)) + 1 := by linarith
    have ht'sq : ((u n : ℝ) + Real.exp (Real.exp 1)) + 1
        ≤ ((u n : ℝ) + Real.exp (Real.exp 1)) ^ 2 := by nlinarith
    have hll : Real.log (Real.log (((u n : ℝ) + Real.exp (Real.exp 1)) + 1))
        ≤ Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))) + 1 :=
      loglog_square_le (by linarith) ht'gt1 ht'sq
    have hknn : (0 : ℝ) ≤ Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))) := by
      linarith [one_le_loglog htee]
    have hA' : Real.sqrt (Real.log (Real.log (((u n : ℝ) + Real.exp (Real.exp 1)) + 1)))
        ≤ Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1)))) + 1 := by
      have h2 : Real.sqrt (Real.log (Real.log (((u n : ℝ) + Real.exp (Real.exp 1)) + 1)))
          ≤ Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))) + 1) :=
        Real.sqrt_le_sqrt hll
      have h3 := sqrt_add_one_le hknn
      linarith
    have hLle := bigL_le (u n + 1)
    rw [hcast'] at hLle
    linarith
  refine ⟨sparsePrime, u, sparsePrime_strictMono, sparsePrime_prime, hu1,
    fun n => lt_of_lt_of_le Nat.zero_lt_one (hu2 n), hutop, ?_, ⟨17, hgap17⟩, ?_⟩
  · intro i n
    have hnd : ¬ sparsePrime i ∣ u n := hu3 n i
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (sparsePrime_prime i)).mpr hnd)
  · -- the `o(log log (uₙ + 3))` clause
    have hB : Tendsto (fun n => Real.log (Real.log ((u n : ℝ) + 3))) atTop atTop := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun n : ℕ => ((u n : ℝ) + 3)) atTop atTop := by
        refine tendsto_atTop_mono (fun n => ?_) hnat
        have : (n : ℝ) ≤ (u n : ℝ) := by exact_mod_cast hu1.le_apply
        linarith
      exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)
    have hsqrtB : Tendsto (fun n => Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))
        atTop atTop := Real.tendsto_sqrt_atTop.comp hB
    have hzero : Tendsto (fun n =>
        (17 : ℝ) * (Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))⁻¹
          + (17 : ℝ) * (Real.log (Real.log ((u n : ℝ) + 3)))⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))⁻¹)
          atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hsqrtB
      have h2 : Tendsto (fun n => (Real.log (Real.log ((u n : ℝ) + 3)))⁻¹)
          atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hB
      simpa using (h1.const_mul (17 : ℝ)).add (h2.const_mul (17 : ℝ))
    refine squeeze_zero' ?_ ?_ hzero
    · filter_upwards [hB.eventually_ge_atTop 1] with n hn
      show (0 : ℝ) ≤ ((u (n + 1) : ℝ) - (u n : ℝ)) / Real.log (Real.log ((u n : ℝ) + 3))
      have hnum : (0 : ℝ) ≤ (u (n + 1) : ℝ) - (u n : ℝ) := by
        have hlt := hu1 (Nat.lt_succ_self n)
        have hle : (u n : ℝ) ≤ (u (n + 1) : ℝ) := by exact_mod_cast le_of_lt hlt
        linarith
      have hden : (0 : ℝ) < Real.log (Real.log ((u n : ℝ) + 3)) := by linarith
      positivity
    · filter_upwards [hB.eventually_ge_atTop 1, hutop.eventually_ge_atTop 2] with n hn hun
      show ((u (n + 1) : ℝ) - (u n : ℝ)) / Real.log (Real.log ((u n : ℝ) + 3))
          ≤ (17 : ℝ) * (Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))⁻¹
            + (17 : ℝ) * (Real.log (Real.log ((u n : ℝ) + 3)))⁻¹
      have hBpos : (0 : ℝ) < Real.log (Real.log ((u n : ℝ) + 3)) := by linarith
      have hunR : (2 : ℝ) ≤ (u n : ℝ) := by exact_mod_cast hun
      have hee21 := expexp_le_twentyone
      have hee7 := expexp_ge_seven
      have htee : Real.exp (Real.exp 1) ≤ (u n : ℝ) + Real.exp (Real.exp 1) := by linarith
      have hcmp : (u n : ℝ) + Real.exp (Real.exp 1) ≤ ((u n : ℝ) + 3) ^ 2 := by nlinarith
      have htgt1 : (1 : ℝ) < (u n : ℝ) + Real.exp (Real.exp 1) := by linarith
      have hu3gt1 : (1 : ℝ) < (u n : ℝ) + 3 := by linarith
      have hBt : Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1)))
          ≤ Real.log (Real.log ((u n : ℝ) + 3)) + 1 :=
        loglog_square_le hu3gt1 htgt1 hcmp
      have hAB : Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))))
          ≤ Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))) + 1 := by
        have h2 : Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))))
            ≤ Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3)) + 1) := Real.sqrt_le_sqrt hBt
        have h3 := sqrt_add_one_le (le_of_lt hBpos)
        linarith
      have hsB : (0 : ℝ) < Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))) :=
        Real.sqrt_pos.mpr hBpos
      have hsBsq : Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3)))
          * Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3)))
          = Real.log (Real.log ((u n : ℝ) + 3)) := Real.mul_self_sqrt (le_of_lt hBpos)
      have hkey : (Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))⁻¹
          * Real.log (Real.log ((u n : ℝ) + 3))
          = Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))) := by
        calc (Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))⁻¹
              * Real.log (Real.log ((u n : ℝ) + 3))
            = (Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))⁻¹
              * (Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3)))
                * Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3)))) := by rw [hsBsq]
          _ = Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))) := by
              rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsB), one_mul]
      have hB' : (Real.log (Real.log ((u n : ℝ) + 3)))⁻¹
          * Real.log (Real.log ((u n : ℝ) + 3)) = 1 := inv_mul_cancel₀ (ne_of_gt hBpos)
      have hexpand : ((17 : ℝ) * (Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))⁻¹
            + (17 : ℝ) * (Real.log (Real.log ((u n : ℝ) + 3)))⁻¹)
          * Real.log (Real.log ((u n : ℝ) + 3))
          = 17 * Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))) + 17 := by
        calc ((17 : ℝ) * (Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))⁻¹
              + (17 : ℝ) * (Real.log (Real.log ((u n : ℝ) + 3)))⁻¹)
              * Real.log (Real.log ((u n : ℝ) + 3))
            = 17 * ((Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))))⁻¹
                * Real.log (Real.log ((u n : ℝ) + 3)))
              + 17 * ((Real.log (Real.log ((u n : ℝ) + 3)))⁻¹
                * Real.log (Real.log ((u n : ℝ) + 3))) := by ring
          _ = 17 * Real.sqrt (Real.log (Real.log ((u n : ℝ) + 3))) + 17 := by
              rw [hkey, hB']; ring
      rw [div_le_iff₀ hBpos, hexpand]
      have := hgap17 n
      linarith

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exists_avoiding_in_window
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exists_slow_rise_avoiding_sequence
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exists_sparse_prime_coprime_sequence

end ErdosProblems.Erdos243.PaperCompleteR21
