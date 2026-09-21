import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field

/-! Paper-form restatement of the long #249 paper's lacunary comparison
environment `thm:lacunary` ("The block norm condition is stronger in the class
`0 ≤ c(n) ≤ n`").

The environment asserts, for `c(n) = 1` when `n = k!` for some `k ≥ 1` and
`c(n) = 0` otherwise, and `β = ∑_{n≥1} c(n)/2^n = ∑_{k≥1} 2^{-k!}`:

* `0 ≤ c(n) ≤ n` for all `n ≥ 1`  (`lacCoef_bounds`);
* the two indexings of `β` agree  (`lacBeta_eq_factorial_series`);
* `β` is irrational  (`irrational_lacBeta`);
* for every `h ≥ 1` and every `X ≥ 81(h+5)`,
  `∑_{N=X}^{2X-1} cos(2π·2^N(2^h-1)β) > (9/10)X`  (`lacunary_block_cos_gap`);
* consequently the full-block norm condition of `defn:fh`, transcribed to the
  coefficient sequence `c`, fails for `β` at every scale `X ≥ 81(h+5)` and at
  every admissible depth `L`  (`lacunary_block_norm_fails`), even though `β`
  is irrational.

Here `D_c(h,N,L) = ∑_{j<L}(c(N+h+1+j) - c(N+1+j))·2^{L-1-j}` and
`E_c(h,N,L) = e((D_c mod 2^L)/2^L)` are the paper's `D` and `E` with the
totient replaced by `c`, matching `Erdos249257.TotientTailPeriodKiller.
windowDiscrepancy` and `Erdos249257.windowFirstExp` clause for clause. -/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Finset
open scoped Nat

/-! ### The comparison coefficients `c` -/

/-- The paper's comparison coefficients: `c(n) = 1` when `n = k!` for some
`k ≥ 1`, and `c(n) = 0` otherwise. -/
noncomputable def lacCoef (n : ℕ) : ℤ :=
  @ite ℤ (∃ k : ℕ, 1 ≤ k ∧ n = k !) (Classical.propDecidable _) 1 0

theorem lacCoef_nonneg (n : ℕ) : 0 ≤ lacCoef n := by
  unfold lacCoef; split <;> norm_num

theorem lacCoef_le_one (n : ℕ) : lacCoef n ≤ 1 := by
  unfold lacCoef; split <;> norm_num

theorem lacCoef_factorial {k : ℕ} (hk : 1 ≤ k) : lacCoef (k !) = 1 := by
  unfold lacCoef; rw [if_pos ⟨k, hk, rfl⟩]

theorem lacCoef_ne_zero_iff {n : ℕ} : lacCoef n ≠ 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ n = k ! := by
  unfold lacCoef
  by_cases h : ∃ k : ℕ, 1 ≤ k ∧ n = Nat.factorial k
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => one_ne_zero⟩
  · rw [if_neg h]
    exact ⟨fun h0 => absurd rfl h0, fun hx => absurd hx h⟩

theorem lacCoef_zero : lacCoef 0 = 0 := by
  unfold lacCoef
  rw [if_neg]
  rintro ⟨k, _, h0⟩
  have := Nat.factorial_pos k
  omega

/-- **Clause (a).** The comparison coefficients lie in the paper's class
`0 ≤ c(n) ≤ n` on `n ≥ 1`. -/
theorem lacCoef_bounds {n : ℕ} (hn : 1 ≤ n) : 0 ≤ lacCoef n ∧ lacCoef n ≤ (n : ℤ) :=
  ⟨lacCoef_nonneg n, (lacCoef_le_one n).trans (by exact_mod_cast hn)⟩

/-! ### The comparison constant `β` -/

/-- `β = ∑_{n ≥ 1} c(n)/2ⁿ` (the `n = 0` term vanishes since `k! ≥ 1`). -/
noncomputable def lacBeta : ℝ := ∑' n : ℕ, (lacCoef n : ℝ) / 2 ^ n

theorem summable_lacCoef_div : Summable (fun n : ℕ => (lacCoef n : ℝ) / 2 ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) summable_geometric_two
  · refine div_nonneg ?_ (by positivity)
    exact_mod_cast lacCoef_nonneg n
  · have h1 : (lacCoef n : ℝ) ≤ 1 := by exact_mod_cast lacCoef_le_one n
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_le_iff₀ h2]
    have h3 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    rw [h3]
    exact h1

/-- The paper's second indexing of `β`: `β = ∑_{k ≥ 1} 2^{-k!}`. -/
theorem lacBeta_eq_factorial_series : lacBeta = ∑' k : ℕ, (1 : ℝ) / 2 ^ ((k + 1)!) := by
  have hmono : StrictMono (fun k : ℕ => (k + 1)!) := fun a b hab =>
    (Nat.factorial_lt (Nat.succ_pos a)).mpr (by omega)
  have hsupp : Function.support (fun n : ℕ => (lacCoef n : ℝ) / 2 ^ n)
      ⊆ Set.range (fun k : ℕ => (k + 1)!) := by
    intro n hn
    rw [Function.mem_support] at hn
    have hc : lacCoef n ≠ 0 := by
      intro h0
      apply hn
      rw [h0]; norm_num
    obtain ⟨k, hk, rfl⟩ := lacCoef_ne_zero_iff.mp hc
    refine ⟨k - 1, ?_⟩
    have hkk : k - 1 + 1 = k := Nat.sub_add_cancel hk
    simp [hkk]
  rw [lacBeta, ← hmono.injective.tsum_eq hsupp]
  refine tsum_congr fun k => ?_
  rw [lacCoef_factorial (by omega : 1 ≤ k + 1)]
  norm_num

theorem lacBeta_eq_remainder : lacBeta = LiouvilleNumber.remainder 2 0 := by
  rw [lacBeta_eq_factorial_series]
  unfold LiouvilleNumber.remainder
  exact tsum_congr fun k => by norm_num

theorem liouvilleNumber_two_eq : liouvilleNumber (2 : ℝ) = 1 / 2 + lacBeta := by
  have h := LiouvilleNumber.partialSum_add_remainder (m := (2 : ℝ)) (by norm_num) 0
  have hps : LiouvilleNumber.partialSum (2 : ℝ) 0 = 1 / 2 := by
    unfold LiouvilleNumber.partialSum
    norm_num
  rw [← h, hps, lacBeta_eq_remainder]

/-- **Clause (b).** `β` is irrational. -/
theorem irrational_lacBeta : Irrational lacBeta := by
  have hirr : Irrational (liouvilleNumber ((2 : ℕ) : ℝ)) :=
    (liouville_liouvilleNumber (le_refl 2)).irrational
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hcast] at hirr
  rintro ⟨q, hq⟩
  refine hirr ⟨1 / 2 + q, ?_⟩
  rw [liouvilleNumber_two_eq, ← hq]
  push_cast
  ring

/-! ### The least factorial above `N` -/

theorem lacIdx_exists (N : ℕ) : ∃ n : ℕ, N < (n + 1)! :=
  ⟨N, lt_of_lt_of_le (Nat.lt_succ_self N) (Nat.self_le_factorial (N + 1))⟩

/-- `lacIdx N + 1` is the least `k ≥ 1` with `k! > N`. -/
def lacIdx (N : ℕ) : ℕ := Nat.find (lacIdx_exists N)

theorem lt_factorial_lacIdx (N : ℕ) : N < (lacIdx N + 1)! := Nat.find_spec (lacIdx_exists N)

theorem factorial_le_of_lt_lacIdx {N j : ℕ} (hj : j < lacIdx N) : (j + 1)! ≤ N :=
  not_lt.mp (Nat.find_min (lacIdx_exists N) hj)

/-! ### The exact split of `2^N β` into an integer and a small tail -/

theorem lacBeta_split (K : ℕ) :
    lacBeta = (∑ i ∈ Finset.Ico 1 (K + 1), (1 : ℝ) / 2 ^ (i !))
      + LiouvilleNumber.remainder 2 K := by
  have h := LiouvilleNumber.partialSum_add_remainder (m := (2 : ℝ)) (by norm_num) K
  have hps : LiouvilleNumber.partialSum (2 : ℝ) K
      = 1 / 2 + ∑ i ∈ Finset.Ico 1 (K + 1), (1 : ℝ) / 2 ^ (i !) := by
    unfold LiouvilleNumber.partialSum
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos K)]
    norm_num
  have h2 := liouvilleNumber_two_eq
  rw [hps] at h
  linarith

/-- The integer part of `2^N β`: the terms `k! ≤ N`. -/
def lacInt (N : ℕ) : ℕ := ∑ i ∈ Finset.Ico 1 (lacIdx N + 1), 2 ^ (N - i !)

theorem two_pow_mul_lacBeta (N : ℕ) :
    2 ^ N * lacBeta = (lacInt N : ℝ) + 2 ^ N * LiouvilleNumber.remainder 2 (lacIdx N) := by
  rw [lacBeta_split (lacIdx N), mul_add]
  congr 1
  rw [Finset.mul_sum, lacInt]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_Ico.mp hi
  have hfac : (i)! ≤ N := by
    have hlt : i - 1 < lacIdx N := by omega
    have h2 := factorial_le_of_lt_lacIdx hlt
    rwa [Nat.sub_add_cancel hi'.1] at h2
  have hne : ((2 : ℝ) ^ (i !)) ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ N = 2 ^ (i !) * 2 ^ (N - i !) := by
    rw [← pow_add, Nat.add_sub_cancel' hfac]
  rw [hpow]
  field_simp

theorem lacRemainder_pos (K : ℕ) : 0 < LiouvilleNumber.remainder 2 K :=
  LiouvilleNumber.remainder_pos (by norm_num) K

theorem lacRemainder_lt (K : ℕ) :
    LiouvilleNumber.remainder 2 K < 2 / 2 ^ ((K + 1)!) := by
  have h := LiouvilleNumber.remainder_lt' (m := (2 : ℝ)) K (by norm_num)
  have h2 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
  rw [h2, mul_one_div] at h
  exact h

/-! ### The phase estimate at a good `N` -/

/-- If `x` differs from a natural number by at most `1/16`, its first-harmonic
cosine is at least `cos(π/8)`. -/
theorem cos_ge_of_near {x : ℝ} {M : ℕ} (hx0 : 0 ≤ x - M) (hx1 : x - M ≤ 1 / 16) :
    Real.cos (Real.pi / 8) ≤ Real.cos (2 * Real.pi * x) := by
  have hcos : Real.cos (2 * Real.pi * x) = Real.cos (2 * Real.pi * (x - M)) := by
    rw [show 2 * Real.pi * x = 2 * Real.pi * (x - (M : ℝ)) + (M : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_add_nat_mul_two_pi _ _
  rw [hcos]
  refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

theorem two_le_two_pow {h : ℕ} (hh : 1 ≤ h) : (2 : ℝ) ≤ 2 ^ h := by
  have hn : (2 : ℕ) ≤ 2 ^ h := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  exact_mod_cast hn

/-- **The good-`N` estimate.**  If the least factorial above `N` exceeds
`N + h + 5`, the phase `2^N(2^h-1)β` is within `1/16` of an integer, so its
cosine is at least `cos(π/8)`. -/
theorem cos_lacPhase_ge {h N : ℕ} (hh : 1 ≤ h)
    (hgood : N + h + 5 ≤ (lacIdx N + 1)!) :
    Real.cos (Real.pi / 8)
      ≤ Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)) := by
  have hRpos : 0 < LiouvilleNumber.remainder 2 (lacIdx N) := lacRemainder_pos (lacIdx N)
  have hRlt : LiouvilleNumber.remainder 2 (lacIdx N) < 2 / 2 ^ ((lacIdx N + 1)!) :=
    lacRemainder_lt (lacIdx N)
  have hsplit := two_pow_mul_lacBeta N
  have h2h : (2 : ℝ) ≤ 2 ^ h := two_le_two_pow hh
  have hANpos : (0 : ℝ) < 2 ^ N := by positivity
  have hcastM : (((2 ^ h - 1) * lacInt N : ℕ) : ℝ) = ((2 : ℝ) ^ h - 1) * (lacInt N : ℝ) := by
    have h1 : (1 : ℕ) ≤ 2 ^ h := Nat.one_le_two_pow
    rw [Nat.cast_mul, Nat.cast_sub h1]
    push_cast
    ring
  have hphase : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta
      - (((2 ^ h - 1) * lacInt N : ℕ) : ℝ)
      = ((2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ N * LiouvilleNumber.remainder 2 (lacIdx N)) := by
    rw [hcastM]
    have hx : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta
        = ((2 : ℝ) ^ h - 1) * ((2 : ℝ) ^ N * lacBeta) := by ring
    rw [hx, hsplit]
    ring
  refine cos_ge_of_near (M := (2 ^ h - 1) * lacInt N) ?_ ?_
  · rw [hphase]
    have := mul_pos hANpos hRpos
    nlinarith
  · rw [hphase]
    have hKfac : (2 : ℝ) ^ (N + h + 5) ≤ 2 ^ ((lacIdx N + 1)!) := by
      have hn : (2 : ℕ) ^ (N + h + 5) ≤ 2 ^ ((lacIdx N + 1)!) :=
        Nat.pow_le_pow_right (by norm_num) hgood
      exact_mod_cast hn
    have hpow : (2 : ℝ) ^ (N + h + 5) = 2 ^ N * 2 ^ h * 32 := by
      rw [pow_add, pow_add]; norm_num
    have hRmul : LiouvilleNumber.remainder 2 (lacIdx N) * ((2 : ℝ) ^ N * 2 ^ h * 32) < 2 := by
      have h1 : LiouvilleNumber.remainder 2 (lacIdx N) * ((2 : ℝ) ^ N * 2 ^ h * 32)
          ≤ LiouvilleNumber.remainder 2 (lacIdx N) * 2 ^ ((lacIdx N + 1)!) := by
        refine mul_le_mul_of_nonneg_left ?_ hRpos.le
        rw [← hpow]; exact hKfac
      have h2 : LiouvilleNumber.remainder 2 (lacIdx N) * (2 : ℝ) ^ ((lacIdx N + 1)!) < 2 := by
        rw [← lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ ((lacIdx N + 1)!))]
        exact hRlt
      linarith
    have hprod : (0 : ℝ) < (2 : ℝ) ^ N * LiouvilleNumber.remainder 2 (lacIdx N) :=
      mul_pos hANpos hRpos
    nlinarith [hRmul, hprod]

/-! ### The exceptional indices in a dyadic block -/

/-- Two exceptional indices in `[X, 2X)` share the same least factorial above
them: consecutive relevant factorials differ by a factor at least `3`. -/
theorem lacIdx_not_lt_of_bad {h X N N' : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X)
    (hN : X ≤ N) (hN'2 : N' < 2 * X)
    (hb' : (lacIdx N' + 1)! < N' + h + 5) :
    ¬ lacIdx N < lacIdx N' := by
  intro hlt
  have h1 : N < (lacIdx N + 1)! := lt_factorial_lacIdx N
  have hKge : X + 1 ≤ (lacIdx N + 1)! := by omega
  have hK2 : 2 ≤ lacIdx N + 1 := by
    by_contra hc
    have hK1 : lacIdx N + 1 = 1 := by omega
    rw [hK1, Nat.factorial_one] at hKge
    omega
  have h5 : 3 * (lacIdx N + 1)! ≤ (lacIdx N + 1 + 1)! := by
    have hfs : (lacIdx N + 1 + 1)! = (lacIdx N + 1 + 1) * (lacIdx N + 1)! :=
      Nat.factorial_succ (lacIdx N + 1)
    rw [hfs]
    exact Nat.mul_le_mul (by omega) (le_refl _)
  have h3 : (lacIdx N + 1 + 1)! ≤ (lacIdx N' + 1)! := Nat.factorial_le (by omega)
  omega

theorem card_lacBad_le {h X : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X) :
    ((Finset.Ico X (2 * X)).filter (fun N => (lacIdx N + 1)! < N + h + 5)).card ≤ h + 5 := by
  rcases ((Finset.Ico X (2 * X)).filter
      (fun N => (lacIdx N + 1)! < N + h + 5)).eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  obtain ⟨N₀, hN₀⟩ := hne
  have hN₀' := Finset.mem_filter.mp hN₀
  have hN₀mem := Finset.mem_Ico.mp hN₀'.1
  have hsub : ((Finset.Ico X (2 * X)).filter (fun N => (lacIdx N + 1)! < N + h + 5))
      ⊆ Finset.Ico ((lacIdx N₀ + 1)! - (h + 4)) ((lacIdx N₀ + 1)!) := by
    intro N hN
    have hN' := Finset.mem_filter.mp hN
    have hNmem := Finset.mem_Ico.mp hN'.1
    have hle1 : ¬ lacIdx N < lacIdx N₀ :=
      lacIdx_not_lt_of_bad hh hX hNmem.1 hN₀mem.2 hN₀'.2
    have hle2 : ¬ lacIdx N₀ < lacIdx N :=
      lacIdx_not_lt_of_bad hh hX hN₀mem.1 hNmem.2 hN'.2
    have heq : lacIdx N = lacIdx N₀ := by omega
    have h1 : N < (lacIdx N + 1)! := lt_factorial_lacIdx N
    have h2 : (lacIdx N + 1)! < N + h + 5 := hN'.2
    rw [heq] at h1 h2
    rw [Finset.mem_Ico]
    omega
  calc ((Finset.Ico X (2 * X)).filter (fun N => (lacIdx N + 1)! < N + h + 5)).card
      ≤ (Finset.Ico ((lacIdx N₀ + 1)! - (h + 4)) ((lacIdx N₀ + 1)!)).card :=
        Finset.card_le_card hsub
    _ = (lacIdx N₀ + 1)! - ((lacIdx N₀ + 1)! - (h + 4)) := Nat.card_Ico _ _
    _ ≤ h + 5 := by omega

/-! ### `cos(π/8) > 9238/10000` -/

theorem cos_pi_div_eight_gt : (9238 / 10000 : ℝ) < Real.cos (Real.pi / 8) := by
  rw [Real.cos_pi_div_eight]
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2gt : (7071 / 5000 : ℝ) < Real.sqrt 2 := by nlinarith
  have hs : (0 : ℝ) ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hssq : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have h1 : ((9238 : ℝ) / 5000) ^ 2 < 2 + Real.sqrt 2 := by nlinarith
  have hgt : (9238 / 5000 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by nlinarith
  linarith

/-! ### Clause (c): the block cosine sum -/

/-- **Clause (c).**  For every `h ≥ 1` and every `X ≥ 81(h+5)`,
`∑_{N=X}^{2X-1} cos(2π·2^N(2^h-1)β) > (9/10)X`. -/
theorem lacunary_block_cos_gap {h X : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X) :
    (9 / 10 : ℝ) * X
      < ∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)) := by
  have hcardS : (Finset.Ico X (2 * X)).card = X := by
    rw [Nat.card_Ico]; omega
  have hsplit :
      (∑ N ∈ (Finset.Ico X (2 * X)).filter (fun N => (lacIdx N + 1)! < N + h + 5),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)))
        + (∑ N ∈ (Finset.Ico X (2 * X)).filter
            (fun N => ¬ ((lacIdx N + 1)! < N + h + 5)),
            Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)))
      = ∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)) :=
    Finset.sum_filter_add_sum_filter_not (Finset.Ico X (2 * X))
      (fun N => (lacIdx N + 1)! < N + h + 5) _
  have hbadbound : ∀ N ∈ (Finset.Ico X (2 * X)).filter (fun N => (lacIdx N + 1)! < N + h + 5),
      (-1 : ℝ) ≤ Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)) :=
    fun N _ => Real.neg_one_le_cos _
  have hgoodbound : ∀ N ∈ (Finset.Ico X (2 * X)).filter
      (fun N => ¬ ((lacIdx N + 1)! < N + h + 5)),
      (9238 / 10000 : ℝ)
        ≤ Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)) := by
    intro N hN
    have hmem := Finset.mem_filter.mp hN
    have hgood : N + h + 5 ≤ (lacIdx N + 1)! := by
      have hnp : ¬ ((lacIdx N + 1)! < N + h + 5) := hmem.2
      omega
    exact le_of_lt (lt_of_lt_of_le cos_pi_div_eight_gt (cos_lacPhase_ge hh hgood))
  have hB := Finset.card_nsmul_le_sum
    ((Finset.Ico X (2 * X)).filter (fun N => (lacIdx N + 1)! < N + h + 5))
    (fun N => Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)))
    (-1) hbadbound
  have hG := Finset.card_nsmul_le_sum
    ((Finset.Ico X (2 * X)).filter (fun N => ¬ ((lacIdx N + 1)! < N + h + 5)))
    (fun N => Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)))
    (9238 / 10000) hgoodbound
  rw [nsmul_eq_mul] at hB hG
  have hcards :
      ((Finset.Ico X (2 * X)).filter (fun N => (lacIdx N + 1)! < N + h + 5)).card
        + ((Finset.Ico X (2 * X)).filter (fun N => ¬ ((lacIdx N + 1)! < N + h + 5))).card
      = X := by
    rw [Finset.card_filter_add_card_filter_not]
    exact hcardS
  have hbad5 : ((Finset.Ico X (2 * X)).filter
      (fun N => (lacIdx N + 1)! < N + h + 5)).card ≤ h + 5 := card_lacBad_le hh hX
  have hXR : (81 : ℝ) * ((h : ℝ) + 5) ≤ (X : ℝ) := by exact_mod_cast hX
  have hbad5R : ((((Finset.Ico X (2 * X)).filter
      (fun N => (lacIdx N + 1)! < N + h + 5)).card : ℕ) : ℝ) ≤ (h : ℝ) + 5 := by
    exact_mod_cast hbad5
  have hcardsR : ((((Finset.Ico X (2 * X)).filter
        (fun N => (lacIdx N + 1)! < N + h + 5)).card : ℕ) : ℝ)
      + ((((Finset.Ico X (2 * X)).filter
        (fun N => ¬ ((lacIdx N + 1)! < N + h + 5))).card : ℕ) : ℝ) = (X : ℝ) := by
    exact_mod_cast hcards
  have hb0 : (0 : ℝ) ≤ ((((Finset.Ico X (2 * X)).filter
      (fun N => (lacIdx N + 1)! < N + h + 5)).card : ℕ) : ℝ) := by positivity
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  linarith

/-! ### Clause (d): the block norm condition fails for `β` -/

/-- The paper's window discrepancy `D(h,N,L)` with the totient replaced by the
comparison coefficients `c`. -/
noncomputable def lacDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (lacCoef (N + h + 1 + j) - lacCoef (N + 1 + j)) * 2 ^ (L - 1 - j)

/-- The angle of the paper's `E(h,N,L)` for the comparison coefficients. -/
noncomputable def lacFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi * (((lacDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))

/-- The paper's `E(h,N,L) = e((D mod 2^L)/2^L)` for the comparison
coefficients. -/
noncomputable def lacFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((lacFirstAngle h N L : ℂ) * Complex.I)

/-- The scaled tail `T(M) = ∑_{j ≥ 0} c(M+1+j)·2^{-(j+1)}` of `2^M β`. -/
noncomputable def lacScaledTail (M : ℕ) : ℝ :=
  ∑' j : ℕ, (lacCoef (j + (M + 1)) : ℝ) / 2 ^ (j + 1)

/-- The integer head of `2^M β`. -/
noncomputable def lacHead (M : ℕ) : ℤ :=
  ∑ n ∈ Finset.range (M + 1), lacCoef n * 2 ^ (M - n)

theorem summable_lacTailTerm (M : ℕ) :
    Summable (fun j : ℕ => (lacCoef (j + (M + 1)) : ℝ) / 2 ^ (j + 1)) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) summable_geometric_two
  · refine div_nonneg ?_ (by positivity)
    exact_mod_cast lacCoef_nonneg _
  · have h1 : (lacCoef (j + (M + 1)) : ℝ) ≤ 1 := by exact_mod_cast lacCoef_le_one _
    have h2 : (0 : ℝ) < 2 ^ (j + 1) := by positivity
    rw [div_le_iff₀ h2]
    have h3 : ((1 : ℝ) / 2) ^ j * 2 ^ (j + 1) = 2 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
    rw [h3]
    linarith

theorem two_pow_mul_lacBeta_eq (M : ℕ) :
    (2 : ℝ) ^ M * lacBeta = ((lacHead M : ℤ) : ℝ) + lacScaledTail M := by
  have hs := summable_lacCoef_div.sum_add_tsum_nat_add (M + 1)
  rw [lacBeta, ← hs, mul_add]
  congr 1
  · rw [Finset.mul_sum, lacHead]
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ M := by have := Finset.mem_range.mp hn; omega
    have hne : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    have hpow : (2 : ℝ) ^ M = 2 ^ n * 2 ^ (M - n) := by
      rw [← pow_add, Nat.add_sub_cancel' hn']
    rw [hpow]
    field_simp
  · rw [lacScaledTail, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    have hne : ((2 : ℝ) ^ M) ≠ 0 := by positivity
    have hpow : (2 : ℝ) ^ (i + (M + 1)) = 2 ^ M * 2 ^ (i + 1) := by
      rw [← pow_add, show M + (i + 1) = i + (M + 1) from by omega]
    rw [hpow]
    field_simp

theorem lacScaledTail_sub_partial (M L : ℕ) :
    0 ≤ lacScaledTail M - ∑ j ∈ Finset.range L, (lacCoef (j + (M + 1)) : ℝ) / 2 ^ (j + 1) ∧
      lacScaledTail M - ∑ j ∈ Finset.range L, (lacCoef (j + (M + 1)) : ℝ) / 2 ^ (j + 1)
        ≤ 1 / 2 ^ L := by
  have hs := (summable_lacTailTerm M).sum_add_tsum_nat_add L
  have hkey : lacScaledTail M
      - ∑ j ∈ Finset.range L, (lacCoef (j + (M + 1)) : ℝ) / 2 ^ (j + 1)
      = ∑' i : ℕ, (lacCoef (i + L + (M + 1)) : ℝ) / 2 ^ (i + L + 1) := by
    rw [lacScaledTail, ← hs]
    ring
  have hcomp : ∀ i : ℕ, (lacCoef (i + L + (M + 1)) : ℝ) / 2 ^ (i + L + 1)
      ≤ ((1 : ℝ) / 2) ^ (L + 1) * ((1 : ℝ) / 2) ^ i := by
    intro i
    have h1 : (lacCoef (i + L + (M + 1)) : ℝ) ≤ 1 := by exact_mod_cast lacCoef_le_one _
    have h2 : (0 : ℝ) < 2 ^ (i + L + 1) := by positivity
    rw [div_le_iff₀ h2]
    have h3 : ((1 : ℝ) / 2) ^ (L + 1) * ((1 : ℝ) / 2) ^ i * 2 ^ (i + L + 1) = 1 := by
      rw [← pow_add, show L + 1 + i = i + L + 1 from by omega, ← mul_pow]
      norm_num
    rw [h3]
    exact h1
  have hgeo : Summable (fun i : ℕ => ((1 : ℝ) / 2) ^ (L + 1) * ((1 : ℝ) / 2) ^ i) :=
    summable_geometric_two.mul_left _
  have htail : Summable (fun i : ℕ => (lacCoef (i + L + (M + 1)) : ℝ) / 2 ^ (i + L + 1)) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) hcomp hgeo
    refine div_nonneg ?_ (by positivity)
    exact_mod_cast lacCoef_nonneg _
  rw [hkey]
  refine ⟨tsum_nonneg fun i => div_nonneg (by exact_mod_cast lacCoef_nonneg _) (by positivity), ?_⟩
  calc ∑' i : ℕ, (lacCoef (i + L + (M + 1)) : ℝ) / 2 ^ (i + L + 1)
      ≤ ∑' i : ℕ, ((1 : ℝ) / 2) ^ (L + 1) * ((1 : ℝ) / 2) ^ i :=
        Summable.tsum_le_tsum hcomp htail hgeo
    _ = ((1 : ℝ) / 2) ^ (L + 1) * 2 := by rw [tsum_mul_left, tsum_geometric_two]
    _ = 1 / 2 ^ L := by
        rw [div_pow, one_pow, pow_succ]
        have h2L : (0 : ℝ) < 2 ^ L := by positivity
        field_simp

theorem lacDiscrepancy_div_eq (h N L : ℕ) :
    ((lacDiscrepancy h N L : ℤ) : ℝ) / 2 ^ L
      = (∑ j ∈ Finset.range L, (lacCoef (j + (N + h + 1)) : ℝ) / 2 ^ (j + 1))
        - ∑ j ∈ Finset.range L, (lacCoef (j + (N + 1)) : ℝ) / 2 ^ (j + 1) := by
  rw [lacDiscrepancy]
  push_cast
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjL : j < L := Finset.mem_range.mp hj
  have hne : ((2 : ℝ) ^ (L - 1 - j)) ≠ 0 := by positivity
  have hne2 : ((2 : ℝ) ^ (j + 1)) ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ L = 2 ^ (L - 1 - j) * 2 ^ (j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [show N + h + 1 + j = j + (N + h + 1) from by omega,
      show N + 1 + j = j + (N + 1) from by omega, hpow]
  field_simp

theorem cos_emod_eq (D : ℤ) (L : ℕ) :
    Real.cos (2 * Real.pi * (((D % (2 ^ L : ℤ) : ℤ) : ℝ) / (((2 ^ L : ℤ) : ℤ) : ℝ)))
      = Real.cos (2 * Real.pi * ((D : ℝ) / (2 : ℝ) ^ L)) := by
  have hPR : (((2 ^ L : ℤ) : ℤ) : ℝ) = (2 : ℝ) ^ L := by push_cast; ring
  have hPne : ((2 : ℝ) ^ L) ≠ 0 := by positivity
  have h1 : ((D % (2 ^ L : ℤ) : ℤ) : ℝ)
      = (D : ℝ) - ((2 : ℝ) ^ L) * ((D / (2 ^ L : ℤ) : ℤ) : ℝ) := by
    rw [Int.emod_def]
    push_cast
    ring
  rw [hPR, h1]
  have hq : ((D : ℝ) - ((2 : ℝ) ^ L) * ((D / (2 ^ L : ℤ) : ℤ) : ℝ)) / (2 : ℝ) ^ L
      = (D : ℝ) / (2 : ℝ) ^ L - ((D / (2 ^ L : ℤ) : ℤ) : ℝ) := by
    field_simp
  rw [hq, show 2 * Real.pi * ((D : ℝ) / (2 : ℝ) ^ L - ((D / (2 ^ L : ℤ) : ℤ) : ℝ))
      = 2 * Real.pi * ((D : ℝ) / (2 : ℝ) ^ L)
        - ((D / (2 ^ L : ℤ) : ℤ) : ℝ) * (2 * Real.pi) from by ring]
  exact Real.cos_sub_int_mul_two_pi _ _

/-- **The truncation transfer.**  The finite residue test at depth `L` sees the
exact phase `2^N(2^h-1)β` up to `2π·2^{-L}`. -/
theorem lacFirstExp_re_ge (h N L : ℕ) :
    Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta))
        - 2 * Real.pi / 2 ^ L
      ≤ (lacFirstExp h N L).re := by
  have hre : (lacFirstExp h N L).re = Real.cos (lacFirstAngle h N L) := by
    rw [lacFirstExp, Complex.exp_ofReal_mul_I_re]
  have hang : Real.cos (lacFirstAngle h N L)
      = Real.cos (2 * Real.pi * (((lacDiscrepancy h N L : ℤ) : ℝ) / (2 : ℝ) ^ L)) := by
    rw [lacFirstAngle]
    exact cos_emod_eq _ _
  obtain ⟨hA0, hA1⟩ := lacScaledTail_sub_partial (N + h) L
  obtain ⟨hB0, hB1⟩ := lacScaledTail_sub_partial N L
  have hD := lacDiscrepancy_div_eq h N L
  have hNh := two_pow_mul_lacBeta_eq (N + h)
  have hNN := two_pow_mul_lacBeta_eq N
  have hgamma : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta
      = ((lacHead (N + h) : ℤ) : ℝ) - ((lacHead N : ℤ) : ℝ)
        + (lacScaledTail (N + h) - lacScaledTail N) := by
    have hpow : (2 : ℝ) ^ (N + h) = 2 ^ N * 2 ^ h := pow_add 2 N h
    have h1 : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta
        = (2 : ℝ) ^ (N + h) * lacBeta - (2 : ℝ) ^ N * lacBeta := by rw [hpow]; ring
    rw [h1, hNh, hNN]
    ring
  set A := ∑ j ∈ Finset.range L, (lacCoef (j + (N + h + 1)) : ℝ) / 2 ^ (j + 1) with hAdef
  set B := ∑ j ∈ Finset.range L, (lacCoef (j + (N + 1)) : ℝ) / 2 ^ (j + 1) with hBdef
  set G := (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta with hGdef
  set E := (lacScaledTail (N + h) - A) - (lacScaledTail N - B) with hEdef
  have hstep : ((lacDiscrepancy h N L : ℤ) : ℝ) / (2 : ℝ) ^ L
      = G - (((lacHead (N + h) - lacHead N : ℤ)) : ℝ) - E := by
    rw [hD, hEdef, hgamma]
    push_cast
    ring
  have hcos2 : Real.cos (2 * Real.pi * (((lacDiscrepancy h N L : ℤ) : ℝ) / (2 : ℝ) ^ L))
      = Real.cos (2 * Real.pi * (G - E)) := by
    rw [hstep, show 2 * Real.pi * (G - (((lacHead (N + h) - lacHead N : ℤ)) : ℝ) - E)
        = 2 * Real.pi * (G - E) - (((lacHead (N + h) - lacHead N : ℤ)) : ℝ) * (2 * Real.pi)
        from by ring]
    exact Real.cos_sub_int_mul_two_pi _ _
  have hlip := Real.abs_cos_sub_cos_le (2 * Real.pi * (G - E)) (2 * Real.pi * G)
  have habs : |2 * Real.pi * (G - E) - 2 * Real.pi * G| ≤ 2 * Real.pi / 2 ^ L := by
    have heq : 2 * Real.pi * (G - E) - 2 * Real.pi * G = -(2 * Real.pi) * E := by ring
    have hd : |E| ≤ 1 / 2 ^ L := by
      rw [abs_le, hEdef]
      constructor <;> linarith
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [heq, abs_mul, abs_neg, abs_of_pos h2pi]
    calc 2 * Real.pi * |E| ≤ 2 * Real.pi * (1 / 2 ^ L) :=
          mul_le_mul_of_nonneg_left hd h2pi.le
      _ = 2 * Real.pi / 2 ^ L := by ring
  have hcomb := abs_le.mp (hlip.trans habs)
  rw [hre, hang, hcos2]
  linarith [hcomb.1, hcomb.2]

/-- **Clause (d).**  The full-block norm condition of `defn:fh`, transcribed to
the comparison coefficients `c`, fails for `β` at every scale `X ≥ 81(h+5)` and
at every admissible depth `L`: the block sum of `E(h,N,L)` has norm strictly
greater than `21X/25`. -/
theorem lacunary_block_norm_fails {h X L : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) :
    (21 / 25 : ℝ) * X < ‖∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L‖ := by
  have hgap := lacunary_block_cos_gap hh hX
  have hre : (∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L).re
      = ∑ N ∈ Finset.Ico X (2 * X), (lacFirstExp h N L).re := by
    simp [Complex.re_sum]
  have hlow : ∑ N ∈ Finset.Ico X (2 * X),
      (Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta))
        - 2 * Real.pi / 2 ^ L)
      ≤ ∑ N ∈ Finset.Ico X (2 * X), (lacFirstExp h N L).re :=
    Finset.sum_le_sum fun N _ => lacFirstExp_re_ge h N L
  have hc : (Finset.Ico X (2 * X)).card = X := by rw [Nat.card_Ico]; omega
  have hsplit : ∑ N ∈ Finset.Ico X (2 * X),
      (Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta))
        - 2 * Real.pi / 2 ^ L)
      = (∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta)))
        - (X : ℝ) * (2 * Real.pi / 2 ^ L) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hc, nsmul_eq_mul]
  rw [hsplit] at hlow
  have hroomR : (32 : ℝ) * X < (2 : ℝ) ^ L := by
    have hn : 32 * X < 2 ^ L := by omega
    exact_mod_cast hn
  have h2Lpos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hXL : (X : ℝ) / (2 : ℝ) ^ L < 1 / 32 := by
    rw [div_lt_div_iff₀ h2Lpos (by norm_num : (0 : ℝ) < 32)]
    linarith
  have hpi := Real.pi_pos
  have hsmall : (X : ℝ) * (2 * Real.pi / 2 ^ L) < Real.pi / 16 := by
    have heq : (X : ℝ) * (2 * Real.pi / 2 ^ L) = 2 * Real.pi * ((X : ℝ) / 2 ^ L) := by ring
    rw [heq]
    nlinarith [hXL, hpi]
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hXR : (81 : ℝ) * ((h : ℝ) + 5) ≤ (X : ℝ) := by exact_mod_cast hX
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  calc (21 / 25 : ℝ) * X < ∑ N ∈ Finset.Ico X (2 * X), (lacFirstExp h N L).re := by linarith
    _ = (∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L).re := hre.symm
    _ ≤ ‖∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L‖ := Complex.re_le_norm _

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lacCoef_bounds
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lacBeta_eq_factorial_series
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_lacBeta
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.cos_pi_div_eight_gt
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_cos_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_norm_fails
