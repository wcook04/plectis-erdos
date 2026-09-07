import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Erdős #249: prefix 2-adic denominator exclusion and control rigidity

This module lands the clean elementary core of the 2026-09-05 eight-return
Type B batch for `S = ∑_{n≥1} φ(n)/2ⁿ` (Erdős #249).  Four independent desks
produced statements whose mathematical content is *elementary integer
arithmetic*; those are exactly the statements collected here, each fully
proved and free of `sorry`.

## The prefix integer

`totientPrefix n = ∑_{i<n} 2^{n-1-i} φ(i+1) = ∑_{i≤n} φ(i) 2^{n-i}` is the
integer prefix `P_n` of `2ⁿ·S`, so that `2ⁿ S = P_n + R_n` with
`R_n = ∑_{j≥1} φ(n+j)/2^j` the local totient tail.

**Correspondence with the shared machinery.**  The shared library carries the
same object as `TotientTailPeriodKiller.totientPrefix N = ∑_{n ∈ range (N+1)}
φ(n)·2^{N-n}`, together with `two_pow_mul_totient_series_eq :
2^N · S = totientPrefix N + totientTail N` and the block identity
`2^H R_c = totientBlock (H, c) + R_{c+H}` in `CyclotomicAnchoredKill`.  That
library is named `Erdos257PeriodNoncollapse` in the private authoring root and
`Erdos249257` in the public build root, so a direct import cannot compile in
both; this module therefore re-defines `totientPrefix` locally and *proves*
the correspondence in `totientPrefix_eq_corpusForm` rather than asserting it.
The tail is carried abstractly as `prefixTail S n = 2ⁿ·S - P_n`, which equals
`totientTail n` on the nose once `S` is the binary totient series.

## Contents

* `prefix_twoAdic_denominator_exclusion` (desk E, claim E10) — the only
  non-vacuous dyadic window form.  A single 2-adic valuation of the prefix
  integer excludes a whole rectangle of candidate denominators.
* `prefix_twoAdic_denominator_lower_bound`,
  `prefix_twoAdic_odd_denominator_floor` — the `R_n ≤ n+2` corollaries.
* `termwise_dyadic_window_vacuous` (desk E, claim E8) — the *termwise* dyadic
  window argument excludes no denominator at all.
* `even_law_and_eventual_congruence_forces_totient` (desk B) — exact doubling
  identities plus eventual congruence modulo every integer force `g = φ`.
* `one_prime_law_and_little_o_forces_totient` (desk A) — one prime law plus an
  `o(n)` error forces `g = φ`.
* `smooth_shift_padicValNat` (desk D, r08 Lemma 3) — the smooth-shift
  coordinate: `p^a ∣ N` freezes `v_p` on the whole window `0 < m < p^a`.
* `topBand_prime_layer_cancellation_unique` (desk E, claim E2) — the rank-one
  top band admits at most one cancellable layer.

Everything is elementary: `φ(n) ≤ n`, integer divisibility, and `Int.le_of_dvd`.
-/

namespace ErdosProblems.Erdos249

open Finset

/-! ## The totient prefix integer -/

/-- The integer prefix `P_n = ∑_{i<n} 2^{n-1-i} φ(i+1)` of `2ⁿ·S`, where
`S = ∑_{n≥1} φ(n)/2ⁿ` is the Erdős #249 constant. -/
def totientPrefix (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * Nat.totient (i + 1)

@[simp] theorem totientPrefix_zero : totientPrefix 0 = 0 := by
  simp [totientPrefix]

/-- The defining recurrence `P_{n+1} = 2 P_n + φ(n+1)`. -/
theorem totientPrefix_succ (n : ℕ) :
    totientPrefix (n + 1) = 2 * totientPrefix n + Nat.totient (n + 1) := by
  unfold totientPrefix
  rw [Finset.sum_range_succ]
  have hlast : (2 : ℕ) ^ (n + 1 - 1 - n) * Nat.totient (n + 1) = Nat.totient (n + 1) := by
    simp
  rw [hlast, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  have hexp : n + 1 - 1 - i = (n - 1 - i) + 1 := by omega
  rw [hexp, pow_succ]
  ring

/-- **Correspondence with the shared machinery.**  The local definition agrees
with `TotientTailPeriodKiller.totientPrefix N = ∑_{n ∈ range (N+1)} φ(n) 2^{N-n}`
of the shared library (`Erdos257PeriodNoncollapse` privately, `Erdos249257`
publicly).  This is the machine-checked form of the docstring claim above. -/
theorem totientPrefix_eq_corpusForm (n : ℕ) :
    totientPrefix n = ∑ i ∈ Finset.range (n + 1), Nat.totient i * 2 ^ (n - i) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.totient_zero, zero_mul, add_zero]
  unfold totientPrefix
  refine Finset.sum_congr rfl fun i _ => ?_
  have hexp : n - (i + 1) = n - 1 - i := by omega
  rw [hexp, Nat.mul_comm]

/-- The abstract local tail `R_n = 2ⁿ·S - P_n`.  When `S` is the binary totient
series this is exactly `TotientTailPeriodKiller.totientTail n`, by the shared
library's shift identity `two_pow_mul_totient_series_eq`. -/
noncomputable def prefixTail (S : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * S - (totientPrefix n : ℝ)

/-! ## Desk E, claim E10: the prefix 2-adic denominator exclusion -/

/-- Under `S = a / (2^c v)` and `c ≤ n`, the rescaled tail `v·R_n` is the
integer `2^{n-c} a - v P_n`.  This is the whole content of the exclusion: the
tail is not merely bounded, it is an integer once multiplied by the odd part of
the denominator. -/
theorem oddPart_mul_prefixTail_eq_intCast
    {S : ℝ} {a : ℤ} {c v n : ℕ} (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hcn : c ≤ n) :
    (v : ℝ) * prefixTail S n
      = (((2 : ℤ) ^ (n - c) * a - (v : ℤ) * (totientPrefix n : ℤ) : ℤ) : ℝ) := by
  have hv0 : (v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hvpos.ne'
  have h2c : ((2 : ℝ) ^ c) ≠ 0 := by positivity
  have hsplit : (2 : ℝ) ^ n = 2 ^ (n - c) * 2 ^ c := by
    rw [← pow_add]
    congr 1
    omega
  simp only [prefixTail, hS, hsplit]
  push_cast
  field_simp

set_option linter.unusedVariables false in
/-- **Desk E, claim E10 — the prefix 2-adic denominator exclusion.**
If `S = a/(2^c v)` with `v > 0` odd, the local tail `R_n = 2ⁿ S - P_n` is
positive, `c + t ≤ n`, and `2^t ∣ P_n`, then `2^t ≤ v · R_n`.

Reason: `v R_n = 2^{n-c} a - v P_n` is an integer, it is positive, and `2^t`
divides it (it divides `2^{n-c}` because `t ≤ n - c`, and it divides `v P_n`
by hypothesis).  A positive integer divisible by `2^t` is at least `2^t`.

This is the *non-termwise* form of the dyadic window argument, and it is the
only non-vacuous one: compare `termwise_dyadic_window_vacuous` below.

The oddness of `v` is the canonical normalisation `S = a/(2^c v)` with `v` odd
(it is what makes `2^t ∣ v P_n ↔ 2^t ∣ P_n`); this direction of the argument
does not consume it, so it is recorded but unused. -/
theorem prefix_twoAdic_denominator_exclusion
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * prefixTail S n := by
  have hcn : c ≤ n := by omega
  have heq := oddPart_mul_prefixTail_eq_intCast hvpos hS hcn
  set m : ℤ := (2 : ℤ) ^ (n - c) * a - (v : ℤ) * (totientPrefix n : ℤ) with hmdef
  have hvR : (0 : ℝ) < (v : ℝ) * prefixTail S n := by
    have : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hvpos
    exact mul_pos this hpos
  have hmpos : 0 < m := by
    have hcast : (0 : ℝ) < (m : ℝ) := heq ▸ hvR
    exact_mod_cast hcast
  have hdvd1 : (2 : ℤ) ^ t ∣ (2 : ℤ) ^ (n - c) * a :=
    Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
  have hdvd2 : (2 : ℤ) ^ t ∣ (v : ℤ) * (totientPrefix n : ℤ) := by
    have h : ((2 ^ t : ℕ) : ℤ) ∣ ((totientPrefix n : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hdvd
    push_cast at h
    exact Dvd.dvd.mul_left h _
  have hdvdm : (2 : ℤ) ^ t ∣ m := dvd_sub hdvd1 hdvd2
  have hle : (2 : ℤ) ^ t ≤ m := Int.le_of_dvd hmpos hdvdm
  have hcast : (2 : ℝ) ^ t ≤ (m : ℝ) := by exact_mod_cast hle
  rw [heq]
  exact hcast

/-- **Corollary of E10 with the canonical tail bound `R_n ≤ n + 2`.**
A single 2-adic valuation `2^t ∣ P_n` excludes every denominator `2^c v`
with `c + t ≤ n` and `v · (n+2) < 2^t`. -/
theorem prefix_twoAdic_denominator_lower_bound
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * ((n : ℝ) + 2) := by
  have h := prefix_twoAdic_denominator_exclusion hvodd hvpos hS hpos hct hdvd
  have hv : (0 : ℝ) ≤ (v : ℝ) := by positivity
  have hmono : (v : ℝ) * prefixTail S n ≤ (v : ℝ) * ((n : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left htail hv
  linarith

/-- The same exclusion read as a lower bound on the odd part of the
denominator: `v ≥ 2^t / (n + 2)`. -/
theorem prefix_twoAdic_odd_denominator_floor
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t / ((n : ℝ) + 2) ≤ (v : ℝ) := by
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h := prefix_twoAdic_denominator_lower_bound hvodd hvpos hS hpos htail hct hdvd
  rw [div_le_iff₀ hden]
  linarith

/-- `P_3 = 4·φ(1) + 2·φ(2) + φ(3) = 8`, for the non-vacuity witness below. -/
theorem totientPrefix_three : totientPrefix 3 = 8 := by
  simp [totientPrefix, Finset.sum_range_succ, Nat.totient_prime (by norm_num : Nat.Prime 3)]

/-- **Non-vacuity of the E10 hypothesis bundle.**  A guard that cannot fire is
not a guard, so we exhibit a tuple satisfying every hypothesis of
`prefix_twoAdic_denominator_exclusion` simultaneously: `S = 9`, `a = 9`,
`c = 0`, `v = 1`, `n = 3`, `t = 3`, where `P_3 = 8` and `R_3 = 8·9 - 8 = 64`,
and the conclusion reads `8 ≤ 64`. -/
example : (2 : ℝ) ^ 3 ≤ ((1 : ℕ) : ℝ) * prefixTail 9 3 := by
  refine prefix_twoAdic_denominator_exclusion (S := 9) (a := 9) (c := 0) (v := 1) (n := 3)
    (t := 3) (by decide) (by norm_num) (by norm_num) ?_ (by omega) ?_
  · rw [prefixTail, totientPrefix_three]
    norm_num
  · rw [totientPrefix_three]
    norm_num

/-! ## Desk E, claim E8: the termwise dyadic window is vacuous -/

set_option linter.unusedVariables false in
/-- **Desk E, claim E8 — the termwise dyadic window excludes no denominator.**
The termwise hypothesis `2^t ∣ φ(N+t)` can never beat the size budget
`v·(N+t+2)`, because `2^t ≤ φ(N+t) < N+t`.  So the termwise form of the dyadic
window argument is unconditionally vacuous, for every `t ≥ 1`, every `N` with
`N + t ≥ 2`, and every `v ≥ 1`.  (This corrects the conductor's first
accounting, which claimed a residual regime `v < 2^c`.)

The hypothesis `1 ≤ t` is recorded because it is the intended regime; the
size arithmetic does not consume it. -/
theorem termwise_dyadic_window_vacuous
    {N t v : ℕ} (ht : 1 ≤ t) (hNt : 2 ≤ N + t) (hv : 1 ≤ v)
    (hdvd : 2 ^ t ∣ Nat.totient (N + t)) :
    2 ^ t ≤ v * (N + t + 2) := by
  have hphipos : 0 < Nat.totient (N + t) := Nat.totient_pos.mpr (by omega)
  have hle : 2 ^ t ≤ Nat.totient (N + t) := Nat.le_of_dvd hphipos hdvd
  have hlt : Nat.totient (N + t) < N + t := Nat.totient_lt _ (by omega)
  calc 2 ^ t ≤ Nat.totient (N + t) := hle
    _ ≤ N + t + 2 := by omega
    _ ≤ v * (N + t + 2) := Nat.le_mul_of_pos_left _ (by omega)

/-! ## Rational-control rigidity: the defect sequence -/

/-- The defect of a candidate integer coefficient sequence against `φ`. -/
def totientDefect (g : ℕ → ℤ) (n : ℕ) : ℤ := g n - (Nat.totient n : ℤ)

theorem totientDefect_eq_zero_iff {g : ℕ → ℤ} {n : ℕ} :
    totientDefect g n = 0 ↔ g n = (Nat.totient n : ℤ) := by
  simp [totientDefect, sub_eq_zero]

/-- `φ(2m) = φ(m)` for odd `m`. -/
theorem totient_two_mul_of_odd {m : ℕ} (hm : Odd m) :
    Nat.totient (2 * m) = Nat.totient m := by
  rw [Nat.totient_mul (Nat.coprime_two_left.mpr hm), Nat.totient_two, one_mul]

/-- `φ(2m) = 2 φ(m)` for even `m`. -/
theorem totient_two_mul_of_even {m : ℕ} (hm : Even m) :
    Nat.totient (2 * m) = 2 * Nat.totient m := by
  obtain ⟨r, hr⟩ := hm
  exact Nat.totient_mul_of_prime_of_dvd Nat.prime_two ⟨r, by omega⟩

/-! ### Desk B: the exact even laws plus eventual congruence force `φ` -/

/-- **Desk B's rigidity theorem.**  Let `g : ℕ → ℤ` obey the two exact doubling
identities of the totient — `g(2m) = g(m)` for odd `m ≥ 1` and
`g(2m) = 2 g(m)` for even `m ≥ 2` — and suppose that for every modulus `q ≥ 1`
the difference `g - φ` is eventually divisible by `q`.  Then `g = φ` on `n ≥ 1`.

Mechanism: the defect `δ = g - φ` inherits the law `δ(2^{a+1} m) = 2^a δ(m)`
for odd `m`, because `φ` satisfies both identities exactly.  If `δ(m) ≠ 0` for
some odd `m`, pick an odd prime `q > |δ(m)|`; eventual divisibility gives
`q ∣ 2^a δ(m)` for large `a`, hence `q ∣ δ(m)`, hence `q ≤ |δ(m)|` — a
contradiction.  So `δ` vanishes on odd arguments, and the doubling laws
propagate that to every `n ≥ 1`.

This strictly supersedes the batch's `o(n)`-error and fixed-modulus variants:
the hypothesis here is only *eventual* congruence, with no rate at all. -/
theorem even_law_and_eventual_congruence_forces_totient
    {g : ℕ → ℤ}
    (hodd : ∀ m : ℕ, Odd m → 1 ≤ m → g (2 * m) = g m)
    (heven : ∀ m : ℕ, Even m → 2 ≤ m → g (2 * m) = 2 * g m)
    (hcong : ∀ q : ℕ, 1 ≤ q → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (q : ℤ) ∣ totientDefect g n)
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  -- the defect inherits both doubling laws
  have hdodd : ∀ m : ℕ, Odd m → 1 ≤ m →
      totientDefect g (2 * m) = totientDefect g m := by
    intro m hm hm1
    simp only [totientDefect, hodd m hm hm1, totient_two_mul_of_odd hm]
  have hdeven : ∀ m : ℕ, Even m → 2 ≤ m →
      totientDefect g (2 * m) = 2 * totientDefect g m := by
    intro m hm hm2
    simp only [totientDefect, heven m hm hm2, totient_two_mul_of_even hm]
    push_cast
    ring
  -- the power law on odd arguments
  have hpow : ∀ m : ℕ, Odd m → 1 ≤ m → ∀ a : ℕ,
      totientDefect g (2 ^ (a + 1) * m) = 2 ^ a * totientDefect g m := by
    intro m hm hm1 a
    induction a with
    | zero => simpa using hdodd m hm hm1
    | succ a ih =>
        have hk1 : 2 ≤ 2 ^ (a + 1) * m := by
          have h1 : (2 : ℕ) ^ 1 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          have := Nat.le_mul_of_pos_right (2 ^ (a + 1)) hm1
          omega
        have hke : Even (2 ^ (a + 1) * m) := by
          refine ⟨2 ^ a * m, ?_⟩
          have : (2 : ℕ) ^ (a + 1) = 2 ^ a * 2 := by ring
          rw [this]
          ring
        have hrw : (2 : ℕ) ^ (a + 1 + 1) * m = 2 * (2 ^ (a + 1) * m) := by ring
        rw [hrw, hdeven _ hke hk1, ih]
        ring
  -- the defect vanishes on odd arguments
  have hoddzero : ∀ m : ℕ, Odd m → 1 ≤ m → totientDefect g m = 0 := by
    intro m hm hm1
    by_contra hne
    obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes ((totientDefect g m).natAbs + 3)
    obtain ⟨N, hN⟩ := hcong q (by omega)
    have hbig : N ≤ 2 ^ (N + 1) * m := by
      have h1 : N < 2 ^ N := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ N ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : 2 ^ (N + 1) ≤ 2 ^ (N + 1) * m := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hdvd : (q : ℤ) ∣ totientDefect g (2 ^ (N + 1) * m) := hN _ hbig
    rw [hpow m hm hm1 N] at hdvd
    have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    rcases (hqZ.dvd_mul).mp hdvd with hcase | hcase
    · have h2 : (q : ℤ) ∣ (2 : ℤ) := hqZ.dvd_of_dvd_pow hcase
      have h2' : q ∣ 2 := by exact_mod_cast h2
      have := Nat.le_of_dvd (by omega) h2'
      omega
    · have habs : q ∣ (totientDefect g m).natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr hcase
        simpa using this
      have hpos : 0 < (totientDefect g m).natAbs := Int.natAbs_pos.mpr hne
      have := Nat.le_of_dvd hpos habs
      omega
  -- propagate to every positive argument, by induction on a bound
  have hall : ∀ B : ℕ, ∀ k : ℕ, k ≤ B → 1 ≤ k → totientDefect g k = 0 := by
    intro B
    induction B with
    | zero => intro k hk hk1; omega
    | succ B ih =>
        intro k hk hk1
        rcases Nat.even_or_odd k with hke | hko
        · obtain ⟨r, hr⟩ := hke
          have hr1 : 1 ≤ r := by omega
          have hk2 : k = 2 * r := by omega
          have hrB : r ≤ B := by omega
          rcases Nat.even_or_odd r with hre | hro
          · have hr2 : 2 ≤ r := by obtain ⟨s, hs⟩ := hre; omega
            rw [hk2, hdeven r hre hr2, ih r hrB hr1]
            ring
          · rw [hk2, hdodd r hro hr1]
            exact hoddzero r hro hr1
        · exact hoddzero k hko hk1
  exact totientDefect_eq_zero_iff.mp (hall n n le_rfl hn)

/-! ### Desk A: one prime law plus an `o(n)` error forces `φ` -/

/-- `φ(p n) = p φ(n)` when `p` is prime and `p ∣ n`. -/
theorem totient_prime_mul_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) :
    (Nat.totient (p * n) : ℤ) = (p : ℤ) * (Nat.totient n : ℤ) := by
  rw [Nat.totient_mul_of_prime_of_dvd hp h]
  push_cast
  ring

/-- `φ(p n) = (p-1) φ(n)` when `p` is prime and `p ∤ n`. -/
theorem totient_prime_mul_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    (Nat.totient (p * n) : ℤ) = ((p : ℤ) - 1) * (Nat.totient n : ℤ) := by
  rw [Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd hp).mpr h), Nat.totient_prime hp]
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have : 1 ≤ p := hp.one_lt.le
    push_cast [Nat.cast_sub this]
    ring
  push_cast [hcast]
  ring

/-- **Desk A's sharpening.**  Let `p` be prime and let `g : ℕ → ℤ` satisfy the
exact `p`-laws of the totient — `g(pn) = (p-1) g(n)` when `p ∤ n` and
`g(pn) = p g(n)` when `p ∣ n` — together with the error bound
`∀ ε > 0, ∃ N, ∀ n ≥ N, |g(n) - φ(n)| ≤ ε n`.  Then `g = φ` on `n ≥ 1`.

Mechanism: the defect satisfies `δ(p^a n) = p^a δ(n)` whenever `p ∣ n`, so
dividing the error bound by `p^a n` and taking `a` large forces `|δ(n)| ≤ ε n`
for every `ε > 0`, hence `δ(n) = 0` on multiples of `p`; the `p ∤ n` law then
transfers this to every `n ≥ 1` because `p - 1 ≠ 0`.

Only ONE prime law is used.  This is the exact boundary of the batch's
rational controls: for every *finite* set of primes there is a rational-valued
control obeying the exact laws at all of them, so the theorem is sharp in the
sense that the `o(n)` error hypothesis is what does the work. -/
theorem one_prime_law_and_little_o_forces_totient
    {p : ℕ} (hp : p.Prime) {g : ℕ → ℤ}
    (hlaw_not_dvd : ∀ n : ℕ, 1 ≤ n → ¬ p ∣ n → g (p * n) = ((p : ℤ) - 1) * g n)
    (hlaw_dvd : ∀ n : ℕ, 1 ≤ n → p ∣ n → g (p * n) = (p : ℤ) * g n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(g n : ℝ) - (Nat.totient n : ℝ)| ≤ ε * (n : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  have hp2 : 2 ≤ p := hp.two_le
  -- the defect inherits the p-laws
  have hd_dvd : ∀ k : ℕ, 1 ≤ k → p ∣ k →
      totientDefect g (p * k) = (p : ℤ) * totientDefect g k := by
    intro k hk1 hk
    simp only [totientDefect, hlaw_dvd k hk1 hk, totient_prime_mul_of_dvd hp hk]
    ring
  have hd_not_dvd : ∀ k : ℕ, 1 ≤ k → ¬ p ∣ k →
      totientDefect g (p * k) = ((p : ℤ) - 1) * totientDefect g k := by
    intro k hk1 hk
    simp only [totientDefect, hlaw_not_dvd k hk1 hk, totient_prime_mul_of_not_dvd hp hk]
    ring
  -- the power law on multiples of p
  have hpow : ∀ k : ℕ, 1 ≤ k → p ∣ k → ∀ a : ℕ,
      totientDefect g (p ^ a * k) = (p : ℤ) ^ a * totientDefect g k := by
    intro k hk1 hk a
    induction a with
    | zero => simp
    | succ a ih =>
        have hk1' : 1 ≤ p ^ a * k := by
          have h1 : 0 < p ^ a := pow_pos (by omega) a
          exact Nat.mul_pos h1 hk1
        have hkd : p ∣ p ^ a * k := Dvd.dvd.mul_left hk _
        have hrw : p ^ (a + 1) * k = p * (p ^ a * k) := by ring
        rw [hrw, hd_dvd _ hk1' hkd, ih]
        ring
  -- the defect vanishes on multiples of p
  have hzero_dvd : ∀ k : ℕ, 1 ≤ k → p ∣ k → totientDefect g k = 0 := by
    intro k hk1 hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    obtain ⟨N, hN⟩ := hsmall (1 / (2 * (k : ℝ))) (by positivity)
    have hbig : N ≤ p ^ N * k := by
      have h1 : N < 2 ^ N := Nat.lt_two_pow_self
      have h2 : (2 : ℕ) ^ N ≤ p ^ N := Nat.pow_le_pow_left hp2 N
      have h3 : p ^ N ≤ p ^ N * k := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hbound := hN _ hbig
    have hdef : ((totientDefect g (p ^ N * k) : ℤ) : ℝ)
        = (g (p ^ N * k) : ℝ) - (Nat.totient (p ^ N * k) : ℝ) := by
      simp [totientDefect]
    rw [← hdef, hpow k hk1 hk N] at hbound
    have hpN : (0 : ℝ) < (p : ℝ) ^ N := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
      positivity
    have hcastpow : (((p : ℤ) ^ N * totientDefect g k : ℤ) : ℝ)
        = (p : ℝ) ^ N * ((totientDefect g k : ℤ) : ℝ) := by push_cast; ring
    rw [hcastpow, abs_mul, abs_of_pos hpN] at hbound
    have hcastnat : ((p ^ N * k : ℕ) : ℝ) = (p : ℝ) ^ N * (k : ℝ) := by push_cast; ring
    rw [hcastnat] at hbound
    have hhalf : |((totientDefect g k : ℤ) : ℝ)| ≤ 1 / 2 := by
      have hb : (p : ℝ) ^ N * |((totientDefect g k : ℤ) : ℝ)|
          ≤ (p : ℝ) ^ N * (1 / 2) := by
        calc (p : ℝ) ^ N * |((totientDefect g k : ℤ) : ℝ)|
            ≤ 1 / (2 * (k : ℝ)) * ((p : ℝ) ^ N * (k : ℝ)) := hbound
          _ = (p : ℝ) ^ N * (1 / 2) := by field_simp
      exact le_of_mul_le_mul_left hb hpN
    have hlt : |totientDefect g k| < 1 := by
      have h : |((totientDefect g k : ℤ) : ℝ)| < 1 := by linarith
      exact_mod_cast h
    exact Int.abs_lt_one_iff.mp hlt
  -- transfer to every positive argument
  by_cases hdn : p ∣ n
  · exact totientDefect_eq_zero_iff.mp (hzero_dvd n hn hdn)
  · have hpn1 : 1 ≤ p * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have h1 : totientDefect g (p * n) = 0 := hzero_dvd _ hpn1 ⟨n, rfl⟩
    rw [hd_not_dvd n hn hdn] at h1
    have hp1 : ((p : ℤ) - 1) ≠ 0 := by
      have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp2
      omega
    have := (mul_eq_zero.mp h1).resolve_left hp1
    exact totientDefect_eq_zero_iff.mp this

/-! ## Desk D (r08 Lemma 3): the smooth-shift coordinate -/

/-- **Smooth shift.**  If `p^a ∣ N` then the `p`-adic valuation is frozen on the
whole window `0 < m < p^a`: `v_p(N + m) = v_p(m)`.

Taking `N_L = ∏_{p ∈ U} p^{a_p}` with `p^{a_p} > L` therefore freezes the
`U`-smooth part of every `φ(N_L + m)`, `1 ≤ m ≤ L`, at polynomial cost in `L`.
This is the new coordinate extracted from r08. -/
theorem smooth_shift_padicValNat
    {p a m N : ℕ} (hp : p.Prime) (hN : p ^ a ∣ N) (hm : 0 < m) (hlt : m < p ^ a) :
    padicValNat p (N + m) = padicValNat p m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := hm.ne'
  have hNm0 : N + m ≠ 0 := by omega
  have hpe_m : p ^ padicValNat p m ∣ m := pow_padicValNat_dvd
  have hea : padicValNat p m < a := by
    have h1 : p ^ padicValNat p m ≤ m := Nat.le_of_dvd hm hpe_m
    have h2 : p ^ padicValNat p m < p ^ a := lt_of_le_of_lt h1 hlt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp h2
  have hpe_N : p ^ padicValNat p m ∣ N :=
    dvd_trans (pow_dvd_pow p hea.le) hN
  have hge : padicValNat p m ≤ padicValNat p (N + m) :=
    (padicValNat_dvd_iff_le hNm0).mp (Dvd.dvd.add hpe_N hpe_m)
  have hle : padicValNat p (N + m) ≤ padicValNat p m := by
    by_contra hcon
    have hcon' : padicValNat p m + 1 ≤ padicValNat p (N + m) := by omega
    have hd : p ^ (padicValNat p m + 1) ∣ N + m :=
      (padicValNat_dvd_iff_le hNm0).mpr hcon'
    have hdN : p ^ (padicValNat p m + 1) ∣ N :=
      dvd_trans (pow_dvd_pow p hea) hN
    have hdm : p ^ (padicValNat p m + 1) ∣ m := (Nat.dvd_add_right hdN).mp hd
    have := (padicValNat_dvd_iff_le hm0).mp hdm
    omega
  omega

/-! ## Desk E, claim E2: the top prime band is rank one -/

/-- **Desk E, claim E2 — top-band layer cancellation is unique.**
In the top prime band of the Möbius–Mersenne cyclotomic lattice the layer
weight factorises as a rank-one product, so the cancellation equation
`Λ D = m W` pins a single index `m`: two distinct indices cannot both be
cancelled by the same correction.  Elementary integer form. -/
theorem topBand_prime_layer_cancellation_unique
    {D W Λ m₁ m₂ : ℤ} (hD : 0 < D) (hΛ : 0 < Λ) (hm : m₁ ≠ m₂) :
    ¬ (Λ * D = m₁ * W ∧ Λ * D = m₂ * W) := by
  rintro ⟨h₁, h₂⟩
  have hsub : (m₁ - m₂) * W = 0 := by linarith [h₁, h₂, sub_mul m₁ m₂ W]
  have hne : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr hm
  have hW : W = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd h hne
    · exact h
  rw [hW, mul_zero] at h₁
  nlinarith

end ErdosProblems.Erdos249
