import ErdosProblems.Erdos243.PaperCompleteR21.ReducedDenominatorPrimePowers
import ErdosProblems.Erdos243.ProtectedEpochEnergy

/-!
# Erdős 243: two convergence criteria for large record jumps

This file proves `long243:res:energycriterion`
(`paper/reasoning-parts/erdos243/core.tex`, line 2144):

> Under the standing hypotheses, the sum
> `𝓔 = ∑_{n record} (1_{d_n ≥ 3} u_n^{-1/2} + (d_n - 2)_+ u_n^{-1})`
> is finite if and only if the sequence is eventually Sylvester; and
> `∑_{n record} (d_n - 2)_+ u_n^{-1/2}` is finite if and only if the sequence is
> eventually Sylvester.

The standing hypotheses and the objects `u`, `v`, `w`, `h`, `R`, `H` of
§`long243:sec:records` are the ones transcribed by
`PaperCompleteR21.StandingOrbit` (`ReducedDenominatorPrimePowers.lean`).  A
*record step* is `R n < u (n+1)` and the jump is `d n = u (n+1) - u n`
(core.tex:1630).  The two series are `StandingOrbit.energy` and
`StandingOrbit.energySqrt`; since both are nonnegative, "the sum is finite" is
`Summable`.

The proof is the paper's, with the two inputs the first pass lacked now
available:

* `StandingOrbit.oddPrimePower_supply_nat` (`ReducedDenominatorPrimePowers.lean`)
  is the unconditional `long243:res:oddpowersupply`; it is used at `A = 3`.
* `ErdosProblems.Erdos243.protected_epoch_energy_integer`
  (`ProtectedEpochEnergy.lean`) is the checked integer form of
  `long243:res:epochenergy`.

`energy_window_real_bound` is the paper's real-valued division of the counting
inequality by `L = pQ/2`, carrying its two displayed constant estimates
`8p/L = 16/Q ≤ 1` and `(8p+8)/√L ≤ 8√2(1+1/p) < 16`;
`exists_late_energy_window` assembles one arbitrarily late window contributing
at least `1/16`; and `StandingOrbit.energy_le_two_energySqrt` is the paper's
term-by-term comparison
`1_{d≥3} u^{-1/2} + (d-2)_+ u^{-1} ≤ 2 (d-2)_+ u^{-1/2}`.

The converse direction uses that a Sylvester tail has `u n = 1` eventually, so
there are no late records at all.  The "not eventually Sylvester implies
`u n → ∞`" step of the paper is obtained here in the equivalent bounded form:
a bounded `u` has an eventually constant running maximum, so
`long243:res:unitrecord` applies and the tail is Sylvester.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open ErdosProblems.Erdos243
open scoped BigOperators Topology

/-! ## 1. Two elementary facts -/

/-- A monotone sequence of naturals with an upper bound is eventually constant. -/
theorem monotone_bounded_eventually_const {f : ℕ → ℕ} (hmono : Monotone f) {M : ℕ}
    (hM : ∀ n, f n ≤ M) : ∃ N, ∀ n, N ≤ n → f n = f N := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ j : ℕ, ∃ n, j ≤ f n := by
    intro j
    induction j with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ j ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, hm, hne⟩ := hcon n
        have hle : f n ≤ f m := hmono hm
        exact ⟨m, by omega⟩
  obtain ⟨n, hn⟩ := key (M + 1)
  have := hM n
  omega

/-- **The real-valued division of the counting inequality.**

This is the displayed step in the proof of `long243:res:energycriterion`.  With
`P = p Q`, `L = P / 2`, `Q = p ^ k ≥ 16` and `Q ≥ p ≥ 3`, the paper's two
constant estimates are `8p / L = 16 / Q ≤ 1` (here `hP16`) and
`(8p + 8) / √L ≤ 8 √2 (1 + 1/p) < 16` (here `hPsq`, since `L ≥ p² / 2`).
Dividing `P ≤ (8p+8) K + 4 X + 8p` by `L` therefore gives
`1 ≤ 16 K / √L + 4 X / L`, i.e. `1/16 ≤ K / √L + X / L`. -/
theorem energy_window_real_bound {pr P K X : ℝ}
    (hpr : 3 ≤ pr) (hPsq : pr * pr ≤ P) (hP16 : 16 * pr ≤ P)
    (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hineq : P ≤ (8 * pr + 8) * K + 4 * X + 8 * pr) :
    (1 : ℝ) / 16 ≤ K / Real.sqrt (P / 2) + X / (P / 2) := by
  have hPpos : 0 < P := by nlinarith
  have hLpos : (0 : ℝ) < P / 2 := by linarith
  have hsLpos : 0 < Real.sqrt (P / 2) := Real.sqrt_pos.mpr hLpos
  have hsq : Real.sqrt (P / 2) * Real.sqrt (P / 2) = P / 2 := Real.mul_self_sqrt hLpos.le
  have hb : 8 * pr + 8 ≤ 16 * Real.sqrt (P / 2) := by
    have h1 : ((8 * pr + 8) / 16) ^ 2 ≤ P / 2 := by
      nlinarith [hPsq, hpr, sq_nonneg (pr - 3)]
    have h2 : (8 * pr + 8) / 16 ≤ Real.sqrt (P / 2) := by
      have h3 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by linarith)] at h3
    linarith
  have h8p : 8 * pr ≤ P / 2 := by linarith
  have hmain : P / 2 ≤ (8 * pr + 8) * K + 4 * X := by linarith
  have hfin : P / 2 ≤ 16 * (K * Real.sqrt (P / 2) + X) := by
    nlinarith [mul_le_mul_of_nonneg_right hb hK, hX]
  have hKeq : K / Real.sqrt (P / 2) = K * Real.sqrt (P / 2) / (P / 2) := by
    rw [div_eq_div_iff (ne_of_gt hsLpos) (ne_of_gt hLpos)]
    calc K * (P / 2) = K * (Real.sqrt (P / 2) * Real.sqrt (P / 2)) := by rw [hsq]
    _ = K * Real.sqrt (P / 2) * Real.sqrt (P / 2) := by ring
  rw [hKeq, ← add_div, le_div_iff₀ hLpos]
  linarith

/-! ## 2. Records, jumps and the two series -/

namespace StandingOrbit

variable (O : StandingOrbit)

theorem R_eq (n : ℕ) : O.R n = runningMax O.u n := rfl

/-- `n` is a **record step**: the reduced numerator sets a new maximum at
`n + 1`, i.e. `R n < u (n+1)` (core.tex, §`long243:sec:records`). -/
def IsRecord (n : ℕ) : Prop := O.R n < O.u (n + 1)

/-- The paper's jump `d n = u (n+1) - u n` at a strict rise (core.tex:1630). -/
def jump (n : ℕ) : ℕ := O.u (n + 1) - O.u n

/-- The term of the paper's first series:
`1_{d_n ≥ 3} u_n^{-1/2} + (d_n - 2)_+ u_n^{-1}` at a record step, and `0`
elsewhere. -/
def energy (n : ℕ) : ℝ :=
  if O.R n < O.u (n + 1) then
    (if 3 ≤ O.jump n then 1 / Real.sqrt ((O.u n : ℝ)) else 0)
      + ((O.jump n - 2 : ℕ) : ℝ) / (O.u n : ℝ)
  else 0

/-- The term of the paper's second series: `(d_n - 2)_+ u_n^{-1/2}` at a record
step, and `0` elsewhere. -/
def energySqrt (n : ℕ) : ℝ :=
  if O.R n < O.u (n + 1) then ((O.jump n - 2 : ℕ) : ℝ) / Real.sqrt ((O.u n : ℝ))
  else 0

theorem energy_nonneg (n : ℕ) : 0 ≤ O.energy n := by
  rw [energy]
  split
  · have h1 : (0 : ℝ) ≤ if 3 ≤ O.jump n then 1 / Real.sqrt ((O.u n : ℝ)) else 0 := by
      split
      · exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
      · exact le_rfl
    have h2 : (0 : ℝ) ≤ ((O.jump n - 2 : ℕ) : ℝ) / (O.u n : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  · exact le_rfl

theorem energySqrt_nonneg (n : ℕ) : 0 ≤ O.energySqrt n := by
  rw [energySqrt]
  split
  · exact div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  · exact le_rfl

/-- **The paper's term-by-term comparison.**  At a record,
`1_{d ≥ 3} u^{-1/2} + (d-2)_+ u^{-1} ≤ 2 (d-2)_+ u^{-1/2}`. -/
theorem energy_le_two_energySqrt (n : ℕ) : O.energy n ≤ 2 * O.energySqrt n := by
  rw [energy, energySqrt]
  by_cases hrec : O.R n < O.u (n + 1)
  · rw [if_pos hrec, if_pos hrec]
    have hun : (1 : ℕ) ≤ O.u n := O.u_pos n
    have hU : (1 : ℝ) ≤ (O.u n : ℝ) := by exact_mod_cast hun
    have hUpos : (0 : ℝ) < (O.u n : ℝ) := by linarith
    have hspos : 0 < Real.sqrt ((O.u n : ℝ)) := Real.sqrt_pos.mpr hUpos
    have hS1 : (1 : ℝ) ≤ Real.sqrt ((O.u n : ℝ)) := by
      have h := Real.sqrt_le_sqrt hU
      rwa [Real.sqrt_one] at h
    have hSsq : Real.sqrt ((O.u n : ℝ)) * Real.sqrt ((O.u n : ℝ)) = (O.u n : ℝ) :=
      Real.mul_self_sqrt hUpos.le
    have hSU : Real.sqrt ((O.u n : ℝ)) ≤ (O.u n : ℝ) := by nlinarith
    by_cases hj : 3 ≤ O.jump n
    · rw [if_pos hj]
      have hD1 : (1 : ℝ) ≤ ((O.jump n - 2 : ℕ) : ℝ) := by
        have : 1 ≤ O.jump n - 2 := by omega
        exact_mod_cast this
      have e1 : (1 : ℝ) / Real.sqrt ((O.u n : ℝ))
          ≤ ((O.jump n - 2 : ℕ) : ℝ) / Real.sqrt ((O.u n : ℝ)) := by
        rw [div_le_div_iff₀ hspos hspos]
        nlinarith
      have e2 : ((O.jump n - 2 : ℕ) : ℝ) / (O.u n : ℝ)
          ≤ ((O.jump n - 2 : ℕ) : ℝ) / Real.sqrt ((O.u n : ℝ)) := by
        rw [div_le_div_iff₀ hUpos hspos]
        nlinarith
      linarith
    · rw [if_neg hj]
      have hd0 : O.jump n - 2 = 0 := by omega
      rw [hd0]
      norm_num
  · rw [if_neg hrec, if_neg hrec]
    norm_num

/-! ### A Sylvester tail has no late records -/

theorem no_late_record_of_eventual_sylvester
    (hrec : ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) :
    ∃ N, ∀ n, N ≤ n → ¬ O.R n < O.u (n + 1) := by
  obtain ⟨N, hN⟩ := O.u_eq_one_of_eventual_sylvester hrec
  refine ⟨N, fun n hn hlt ↦ ?_⟩
  have h1 : O.u (n + 1) = 1 := hN (n + 1) (by omega)
  have h2 : O.u n ≤ O.R n := le_runningMax O.u (le_refl n)
  have h3 : 1 ≤ O.u n := O.u_pos n
  omega

theorem energy_summable_of_eventual_sylvester
    (hrec : ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) :
    Summable O.energy := by
  obtain ⟨N, hN⟩ := O.no_late_record_of_eventual_sylvester hrec
  refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn ↦ ?_)
  have hge : N ≤ n := by
    simp only [Finset.mem_range, not_lt] at hn
    exact hn
  rw [energy, if_neg (hN n hge)]

theorem energySqrt_summable_of_eventual_sylvester
    (hrec : ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) :
    Summable O.energySqrt := by
  obtain ⟨N, hN⟩ := O.no_late_record_of_eventual_sylvester hrec
  refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn ↦ ?_)
  have hge : N ≤ n := by
    simp only [Finset.mem_range, not_lt] at hn
    exact hn
  rw [energySqrt, if_neg (hN n hge)]

/-! ### A bounded reduced numerator forces the Sylvester recurrence -/

/-- If `u` is bounded then `R = runningMax u` is eventually constant, so the
unit record-increment hypothesis of `long243:res:unitrecord` holds and the tail
is Sylvester.  This is the contrapositive of the paper's
"not eventually Sylvester, hence `u n → ∞`". -/
theorem sylvesterNext_of_u_bounded (hb : ∃ M, ∀ n, O.u n ≤ M) :
    ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  obtain ⟨M, hM⟩ := hb
  have hmono : Monotone O.R := by
    apply monotone_nat_of_le_succ
    intro n
    show runningMax O.u n ≤ max (runningMax O.u n) (O.u (n + 1))
    exact le_max_left _ _
  have hbdd : ∀ n, O.R n ≤ M := by
    intro n
    have h : runningMax O.u n < M + 1 :=
      runningMax_lt O.u (fun j _ ↦ by have := hM j; omega)
    have h2 : O.R n = runningMax O.u n := rfl
    omega
  obtain ⟨N, hN⟩ := monotone_bounded_eventually_const hmono hbdd
  refine O.unitRecordIncrement_sylvesterNext ⟨N, fun n hn ↦ ?_⟩
  have h1 : O.R n = O.R N := hN n hn
  have h2 : O.R (n + 1) = O.R N := hN (n + 1) (by omega)
  omega

/-! ## 3. One arbitrarily late window contributes at least `1/16` -/

/-- **The paper's window estimate.**  If the reduced numerator is unbounded then
for every `S` there are `S ≤ s < τ` and a finite set `J ⊆ [s, τ)` of record
steps with `d_n ≥ 3` whose energy contribution is at least `1/16`.

The prime power comes from `long243:res:oddpowersupply` at `A = 3`, the set `J`
and the counting inequality from `long243:res:epochenergy`, and the passage to
the real series from `energy_window_real_bound`. -/
theorem exists_late_energy_window (hunb : ∀ M : ℕ, ∃ n, M < O.u n) (S : ℕ) :
    ∃ (s τ : ℕ) (J : Finset ℕ), S ≤ s ∧ s < τ ∧ (∀ n ∈ J, s ≤ n ∧ n < τ) ∧
      (1 : ℝ) / 16 ≤ ∑ n ∈ J, O.energy n := by
  classical
  obtain ⟨N₁, hN₁⟩ := O.redErr_vanishing 2
  obtain ⟨N₂, hN₂⟩ := O.oddPrimePower_supply_nat 3
  obtain ⟨s, hsS, hsN₁, hsN₂⟩ : ∃ s, S ≤ s ∧ N₁ ≤ s ∧ N₂ ≤ s :=
    ⟨max S (max N₁ N₂), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨p, k, hp, hp2, hk, hdvd, hlt⟩ := hN₂ s hsN₂
  -- `p ≥ 3`, `Q = p ^ k ≥ 28`, `p ≤ Q`.
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hH1 : 1 ≤ O.Hmax s := O.one_le_Hmax s
  have hbase : 27 ≤ (O.Hmax s + 2) ^ 3 := by
    have h3 : (3 : ℕ) ≤ O.Hmax s + 2 := by omega
    calc (27 : ℕ) = 3 ^ 3 := by norm_num
    _ ≤ (O.Hmax s + 2) ^ 3 := Nat.pow_le_pow_left h3 3
  have hQ16 : 16 ≤ p ^ k := by omega
  have hpQk : p ≤ p ^ k := by
    calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k := Nat.pow_le_pow_right (by omega) hk
  -- `4 R s < p Q`.
  have hcube : 4 * (O.Hmax s + 2) ≤ (O.Hmax s + 2) ^ 3 := by
    have h3 : (3 : ℕ) ≤ O.Hmax s + 2 := by omega
    have h2 : 9 * (O.Hmax s + 2) ≤ ((O.Hmax s + 2) * (O.Hmax s + 2)) * (O.Hmax s + 2) :=
      Nat.mul_le_mul_right (O.Hmax s + 2) (Nat.mul_le_mul h3 h3)
    have h4 : ((O.Hmax s + 2) * (O.Hmax s + 2)) * (O.Hmax s + 2) = (O.Hmax s + 2) ^ 3 := by
      ring
    omega
  have hRH : O.R s ≤ O.Hmax s := O.R_le_Hmax s
  have hRr : O.R s = runningMax O.u s := rfl
  have hPle : p ^ k ≤ p * p ^ k := Nat.le_mul_of_pos_left _ (by omega)
  have hRs : 4 * runningMax O.u s < p * p ^ k := by omega
  -- The orbit reaches `pQ / 2`, and `τ` is the first index after `s` where it does.
  obtain ⟨t, ht⟩ := hunb (max (p * p ^ k) (runningMax O.u s))
  have hts : s < t := by
    by_contra hcon
    have h1 : O.u t ≤ runningMax O.u s := le_runningMax O.u (by omega)
    have h2 := le_max_right (p * p ^ k) (runningMax O.u s)
    omega
  have htu : p * p ^ k ≤ 2 * O.u t := by
    have h2 := le_max_left (p * p ^ k) (runningMax O.u s)
    omega
  have hne : {m : ℕ | s < m ∧ p * p ^ k ≤ 2 * O.u m}.Nonempty := ⟨t, hts, htu⟩
  have hmem : sInf {m : ℕ | s < m ∧ p * p ^ k ≤ 2 * O.u m}
      ∈ {m : ℕ | s < m ∧ p * p ^ k ≤ 2 * O.u m} := Nat.sInf_mem hne
  obtain ⟨hsτ, hτu⟩ := hmem
  have hbefore : ∀ n, s ≤ n → n < sInf {m : ℕ | s < m ∧ p * p ^ k ≤ 2 * O.u m} →
      2 * O.u n < p * p ^ k := by
    intro n hn1 hn2
    rcases Nat.lt_or_ge s n with hlt' | hge'
    · by_contra hcon
      have hin : n ∈ {m : ℕ | s < m ∧ p * p ^ k ≤ 2 * O.u m} := ⟨hlt', by omega⟩
      have := Nat.sInf_le hin
      omega
    · have hns : n = s := by omega
      have h1 : O.u n ≤ runningMax O.u s := by
        rw [hns]; exact le_runningMax O.u (le_refl s)
      omega
  -- The centring bound `2 w n ≤ 3 u n` from `2 |ẽ n| < u n`.
  have hslow : ∀ n, s ≤ n → 2 * O.w n ≤ 3 * O.u n := by
    intro n hn
    have h1 : 2 * (O.redErr n).natAbs < O.u n := hN₁ n (by omega)
    have h2 : (O.w n : ℤ) = (O.u n : ℤ) - O.redErr n := O.w_eq_sub_redErr n
    omega
  obtain ⟨J, hJ, hineq⟩ :=
    protected_epoch_energy_integer O.a O.u O.v O.w O.canc p k s
      (sInf {m : ℕ | s < m ∧ p * p ^ k ≤ 2 * O.u m}) hp (hp.odd_of_ne_two hp2) hk
      (fun n _ ↦ O.coprime_u_v n) (fun n _ ↦ O.v_pos n) (fun n _ ↦ O.w_add_v n)
      (fun n _ ↦ O.w_pos n) (fun n _ ↦ O.num_step n) (fun n _ ↦ O.den_step n)
      hslow hdvd hQ16 hRs hsτ hτu
  refine ⟨s, sInf {m : ℕ | s < m ∧ p * p ^ k ≤ 2 * O.u m}, J, hsS, hsτ,
    fun n hn ↦ ⟨(hJ n hn).1, (hJ n hn).2.1⟩, ?_⟩
  -- The real-valued division.
  have hPnat : 0 < p * p ^ k := by
    have hpp : 0 < p := by omega
    positivity
  have hterm : ∀ n ∈ J,
      1 / Real.sqrt (((p * p ^ k : ℕ) : ℝ) / 2)
        + ((O.u (n + 1) - O.u n - 2 : ℕ) : ℝ) / (((p * p ^ k : ℕ) : ℝ) / 2)
      ≤ O.energy n := by
    intro n hn
    obtain ⟨hns, hnτ, hrec, hjump, -⟩ := hJ n hn
    have hun0 : 0 < O.u n := O.u_pos n
    have hUpos : (0 : ℝ) < (O.u n : ℝ) := by exact_mod_cast hun0
    have hcount := hbefore n hns hnτ
    have hunL : (O.u n : ℝ) ≤ ((p * p ^ k : ℕ) : ℝ) / 2 := by
      have hcast : ((2 * O.u n : ℕ) : ℝ) ≤ ((p * p ^ k : ℕ) : ℝ) := by
        exact_mod_cast le_of_lt hcount
      push_cast at hcast ⊢
      linarith
    have hLpos : (0 : ℝ) < ((p * p ^ k : ℕ) : ℝ) / 2 := by linarith
    have hspos : 0 < Real.sqrt ((O.u n : ℝ)) := Real.sqrt_pos.mpr hUpos
    have hsLpos : 0 < Real.sqrt (((p * p ^ k : ℕ) : ℝ) / 2) := Real.sqrt_pos.mpr hLpos
    have hsle : Real.sqrt ((O.u n : ℝ)) ≤ Real.sqrt (((p * p ^ k : ℕ) : ℝ) / 2) :=
      Real.sqrt_le_sqrt hunL
    have hrec' : O.R n < O.u (n + 1) := hrec
    have hjump3 : 3 ≤ O.jump n := by
      rw [jump]; omega
    rw [energy, if_pos hrec', if_pos hjump3, jump]
    have e1 : 1 / Real.sqrt (((p * p ^ k : ℕ) : ℝ) / 2) ≤ 1 / Real.sqrt ((O.u n : ℝ)) := by
      rw [div_le_div_iff₀ hsLpos hspos]
      nlinarith
    have e2 : ((O.u (n + 1) - O.u n - 2 : ℕ) : ℝ) / (((p * p ^ k : ℕ) : ℝ) / 2)
        ≤ ((O.u (n + 1) - O.u n - 2 : ℕ) : ℝ) / (O.u n : ℝ) := by
      rw [div_le_div_iff₀ hLpos hUpos]
      nlinarith [Nat.cast_nonneg (α := ℝ) (O.u (n + 1) - O.u n - 2)]
    linarith
  have hsplit : ∑ n ∈ J, (1 / Real.sqrt (((p * p ^ k : ℕ) : ℝ) / 2)
        + ((O.u (n + 1) - O.u n - 2 : ℕ) : ℝ) / (((p * p ^ k : ℕ) : ℝ) / 2))
      = (J.card : ℝ) * (1 / Real.sqrt (((p * p ^ k : ℕ) : ℝ) / 2))
        + (∑ n ∈ J, ((O.u (n + 1) - O.u n - 2 : ℕ) : ℝ)) / (((p * p ^ k : ℕ) : ℝ) / 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_div]
  have hlow := Finset.sum_le_sum hterm
  rw [hsplit] at hlow
  -- the paper's inequality, in real form
  have hreal : (1 : ℝ) / 16
      ≤ (J.card : ℝ) / Real.sqrt (((p * p ^ k : ℕ) : ℝ) / 2)
        + ((∑ n ∈ J, (O.u (n + 1) - O.u n - 2) : ℕ) : ℝ) / (((p * p ^ k : ℕ) : ℝ) / 2) := by
    refine energy_window_real_bound (pr := (p : ℝ)) (P := ((p * p ^ k : ℕ) : ℝ))
      (by exact_mod_cast hp3) ?_ ?_ (by positivity) (by positivity) ?_
    · have : (p * p : ℕ) ≤ p * p ^ k := Nat.mul_le_mul_left p hpQk
      have hc : ((p * p : ℕ) : ℝ) ≤ ((p * p ^ k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hc ⊢
      linarith
    · have : (16 * p : ℕ) ≤ p * p ^ k := by
        calc (16 * p : ℕ) = p * 16 := by ring
        _ ≤ p * p ^ k := Nat.mul_le_mul_left p hQ16
      have hc : ((16 * p : ℕ) : ℝ) ≤ ((p * p ^ k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hc ⊢
      linarith
    · have hc : ((p * p ^ k : ℕ) : ℝ)
          ≤ (((8 * p + 8) * J.card + 4 * ∑ n ∈ J, (O.u (n + 1) - O.u n - 2) + 8 * p : ℕ) : ℝ) := by
        exact_mod_cast hineq
      push_cast at hc ⊢
      linarith
  have hcast : ((∑ n ∈ J, (O.u (n + 1) - O.u n - 2) : ℕ) : ℝ)
      = ∑ n ∈ J, ((O.u (n + 1) - O.u n - 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at hreal
  have hmulform : (J.card : ℝ) * (1 / Real.sqrt (((p * p ^ k : ℕ) : ℝ) / 2))
      = (J.card : ℝ) / Real.sqrt (((p * p ^ k : ℕ) : ℝ) / 2) := by ring
  rw [hmulform] at hlow
  linarith

/-! ## 4. `long243:res:energycriterion` -/

/-- **`long243:res:energycriterion`, first series.**

`𝓔 = ∑_{n record} (1_{d_n ≥ 3} u_n^{-1/2} + (d_n - 2)_+ u_n^{-1})` is finite if
and only if the sequence is eventually Sylvester. -/
theorem energy_summable_iff :
    Summable O.energy ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  constructor
  · intro hsum
    by_contra hnot
    have hunb : ∀ M : ℕ, ∃ n, M < O.u n := by
      intro M
      by_contra hcon
      push_neg at hcon
      exact hnot (O.sylvesterNext_of_u_bounded ⟨M, hcon⟩)
    have hnn : ∀ n, 0 ≤ O.energy n := O.energy_nonneg
    obtain ⟨S, hS⟩ : ∃ S, (∑' n, O.energy n) - (∑ n ∈ Finset.range S, O.energy n) < 1 / 16 := by
      obtain ⟨S, hSS⟩ :=
        Metric.tendsto_atTop.mp hsum.hasSum.tendsto_sum_nat (1 / 16) (by norm_num)
      refine ⟨S, ?_⟩
      have h := hSS S le_rfl
      rw [Real.dist_eq] at h
      have h2 := abs_lt.mp h
      linarith [h2.1, h2.2]
    obtain ⟨s, τ, J, hsS, hsτ, hJrange, hJlb⟩ := O.exists_late_energy_window hunb S
    have hsub : J ⊆ Finset.Ico s τ := fun n hn ↦ Finset.mem_Ico.mpr (hJrange n hn)
    have hup : ∑ n ∈ J, O.energy n ≤ ∑ n ∈ Finset.Ico s τ, O.energy n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ ↦ hnn n)
    have hcons : ∑ n ∈ Finset.Ico 0 s, O.energy n + ∑ n ∈ Finset.Ico s τ, O.energy n
        = ∑ n ∈ Finset.Ico 0 τ, O.energy n :=
      Finset.sum_Ico_consecutive _ (Nat.zero_le s) (le_of_lt hsτ)
    rw [← Finset.range_eq_Ico] at hcons
    have hrangeτ : ∑ n ∈ Finset.range τ, O.energy n ≤ ∑' n, O.energy n :=
      Summable.sum_le_tsum _ (fun i _ ↦ hnn i) hsum
    have hrangeS : ∑ n ∈ Finset.range S, O.energy n ≤ ∑ n ∈ Finset.range s, O.energy n :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn ↦ Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) hsS))
        (fun n _ _ ↦ hnn n)
    linarith
  · exact O.energy_summable_of_eventual_sylvester

/-- **`long243:res:energycriterion`, second series.**

`∑_{n record} (d_n - 2)_+ u_n^{-1/2}` is finite if and only if the sequence is
eventually Sylvester. -/
theorem energySqrt_summable_iff :
    Summable O.energySqrt ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  constructor
  · intro hsum
    refine O.energy_summable_iff.mp ?_
    refine Summable.of_nonneg_of_le O.energy_nonneg O.energy_le_two_energySqrt ?_
    exact hsum.mul_left 2
  · exact O.energySqrt_summable_of_eventual_sylvester

/-- **`long243:res:energycriterion` in full**: both series are finite exactly
when the sequence is eventually Sylvester, so in particular they are finite
together. -/
theorem energy_criterion :
    (Summable O.energy ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ∧
      (Summable O.energySqrt ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) :=
  ⟨O.energy_summable_iff, O.energySqrt_summable_iff⟩

end StandingOrbit

end ErdosProblems.Erdos243.PaperCompleteR21

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_summable_iff
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt_summable_iff
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_criterion
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_le_two_energySqrt
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.exists_late_energy_window
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.energy_window_real_bound
