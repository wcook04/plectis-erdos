import Erdos249257.TotientActualLcmShortKill
import Erdos249257.LcmConeFlatness

/-! Paper-form restatements of two long-paper environments:

* `prop:SK-01-inv` — the two explicit short-window certificates
  `C(H_16, H_16, 23)` and `C(H_64, H_64, 93)`, the short-window inequalities
  `23 < 32` and `93 < 128`, and the resulting `Ω_4, Ω_6 ∉ ℤ`;
* `prop:A9-inv` — rationality `S = a/(2^c v)` in lowest terms with `v` odd
  gives the explicit period `h = φ(v)`: `v ∣ 2^h - 1`,
  `2^N (2^h - 1) S ∈ ℤ` and `R_{N+h} - R_N ∈ ℤ` for every `N ≥ c`; together
  with the soundness direction, the converse for irrational `S`, and the
  pointwise depth supply.

Here `H(t) = periodLcm t`, `R_N = totientTail N`, `C(h,N,L) = certifiedKill h N L`
and `Ω_a = actualLcmTailOrbit a`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine

/-! ### `prop:SK-01-inv` — explicit finite examples -/

/-- `Ω_a` is the diagonal tail orbit `R_{2H(2^a)} - R_{H(2^a)}`. -/
theorem actualLcmTailOrbit_eq_tail_difference (a : ℕ) :
    actualLcmTailOrbit a =
      totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) :=
  rfl

/-- **Explicit finite examples.**  The pre-existing certificates
`C(H_16, H_16, 23)` and `C(H_64, H_64, 93)` hold, both satisfy the short-window
restriction (`23 < 32` and `93 < 128`), and they give `Ω_4 ∉ ℤ` and
`Ω_6 ∉ ℤ`. -/
theorem shortWindow_certificates_kill_omega_four_and_six :
    certifiedKill (periodLcm 16) (periodLcm 16) 23 ∧
      (23 : ℕ) < 32 ∧
      certifiedKill (periodLcm 64) (periodLcm 64) 93 ∧
      (93 : ℕ) < 128 ∧
      actualLcmTailOrbit 4 ∉ Set.range ((↑) : ℤ → ℝ) ∧
      actualLcmTailOrbit 6 ∉ Set.range ((↑) : ℤ → ℝ) :=
  ⟨certifiedKill_diagonal_t16, by norm_num,
    certifiedKill_diagonal_t64, by norm_num,
    actualLcmTailOrbit_four_and_six_notMem_int.1,
    actualLcmTailOrbit_four_and_six_notMem_int.2⟩

/-- The short-window restriction in its `L < 2·2^a` form at `a = 4, 6`. -/
theorem shortWindow_inequalities :
    (23 : ℕ) < 2 * 2 ^ 4 ∧ (93 : ℕ) < 2 * 2 ^ 6 := by
  constructor <;> norm_num

/-! ### `prop:A9-inv` — rationality gives an eventual tail period -/

/-- The paper's degenerate case `v = 1`: the period is `h = φ(1) = 1`. -/
theorem totient_one_eq_one : Nat.totient 1 = 1 := Nat.totient_one

/-- **Rationality gives an eventual tail period, with explicit witnesses.**
If `S = p` with `p.den = 2^c · v` and `v` odd (so `p = a/(2^c v)` in lowest
terms), then with `h = φ(v)`:

* `v ∣ 2^h - 1` (Euler);
* `2^N (2^h - 1) S ∈ ℤ` for every `N ≥ c`;
* `R_{N+h} - R_N ∈ ℤ` for every `N ≥ c`. -/
theorem rational_tail_period_explicit_witnesses
    (p : ℚ) (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (p : ℝ))
    (c v : ℕ) (hden : p.den = 2 ^ c * v) (hvodd : Odd v) :
    v ∣ 2 ^ Nat.totient v - 1 ∧
      (∀ N : ℕ, c ≤ N →
        ((2 : ℝ) ^ N * ((2 : ℝ) ^ Nat.totient v - 1)) *
            (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ∈
          Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ N : ℕ, c ≤ N →
        totientTail (N + Nat.totient v) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ)) := by
  have hcop : Nat.Coprime 2 v := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_
    rintro ⟨k, hk⟩
    have hv1 : v % 2 = 1 := Nat.odd_iff.mp hvodd
    omega
  have hmdvd : v ∣ 2 ^ Nat.totient v - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp
      (Nat.ModEq.pow_totient hcop).symm
  have hdenDvd : ∀ N : ℕ, c ≤ N →
      p.den ∣ 2 ^ N * (2 ^ Nat.totient v - 1) := by
    intro N hN
    rw [hden]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left _ hcop)
      (dvd_mul_of_dvd_left (pow_dvd_pow 2 hN) _)
      (dvd_mul_of_dvd_right hmdvd _)
  have hden0 : ((p.den : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.den_pos.ne'
  refine ⟨hmdvd, ?_, fun N hN =>
    tail_diff_int_of_den_dvd p hS (Nat.totient v) N (hdenDvd N hN)⟩
  intro N hN
  obtain ⟨k, hk⟩ := hdenDvd N hN
  refine ⟨(k : ℤ) * p.num, ?_⟩
  have hcastK : ((2 ^ N * (2 ^ Nat.totient v - 1) : ℕ) : ℝ)
      = (2 : ℝ) ^ N * ((2 : ℝ) ^ Nat.totient v - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
    push_cast
    ring
  rw [hS, ← hcastK, hk, Rat.cast_def]
  push_cast
  first
    | (field_simp; ring)
    | field_simp
    | ring

/-- **The existential form.**  If `S` is not irrational, some period `h ≥ 1`
makes every shifted tail difference an integer from some threshold on. -/
theorem eventual_tail_period_of_not_irrational
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) :=
  eventual_period_of_not_irrational hrat

/-- **Soundness.**  The quantified certificate condition rules out
rationality. -/
theorem irrational_of_certificate_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_certificate_supply hsupply

/-- **The converse, from the prefix-tail identity.**  If `S` is irrational then
every positive-shift tail difference is nonintegral. -/
theorem tail_diff_notMem_int_of_irrational
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    {h N : ℕ} (hh : 0 < h) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  have h1 := two_pow_mul_totient_series_eq (N + h)
  have h2 := two_pow_mul_totient_series_eq N
  have hkey : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (z : ℝ) + ((totientPrefix (N + h) : ℝ) - (totientPrefix N : ℝ)) := by
    linear_combination h1 - h2 - hz
  have h2h : (1 : ℝ) < (2 : ℝ) ^ h := one_lt_pow₀ (by norm_num) (by omega)
  have hMpos : (0 : ℝ) < (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) :=
    mul_pos (by positivity) (by linarith)
  have hMcast : ((2 ^ N * (2 ^ h - 1) : ℕ) : ℝ)
      = (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
    push_cast
    ring
  have hMne : ((2 ^ N * (2 ^ h - 1) : ℕ) : ℝ) ≠ 0 := by
    rw [hMcast]; exact hMpos.ne'
  refine hirr ⟨((z + (totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℚ) /
      ((2 ^ N * (2 ^ h - 1) : ℕ) : ℚ), ?_⟩
  have hcast :
      ((((z + (totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℚ) /
          ((2 ^ N * (2 ^ h - 1) : ℕ) : ℚ) : ℚ) : ℝ)
        = ((z + (totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℝ) /
          ((2 ^ N * (2 ^ h - 1) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, div_eq_iff hMne, hMcast]
  push_cast
  linear_combination -hkey

/-- **Pointwise completeness supplies a depth.**  For every `h, N` a
certificate exists at some depth exactly when the tail difference is
nonintegral. -/
theorem exists_certifiedKill_iff_tail_diff_nonintegral (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) :=
  exists_certifiedKill_iff_tail_diff_notMem_int h N

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_eq_tail_difference
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_certificates_kill_omega_four_and_six
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_inequalities
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_one_eq_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.rational_tail_period_explicit_witnesses
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.eventual_tail_period_of_not_irrational
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_certificate_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tail_diff_notMem_int_of_irrational
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_tail_diff_nonintegral
