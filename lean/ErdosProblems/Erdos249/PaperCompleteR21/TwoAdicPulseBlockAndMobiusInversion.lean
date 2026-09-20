import Erdos249257.TotientTwoAdicPulseBlock
import Erdos249257.TotientShiftedMobiusPulse

/-! Paper-form restatements of three long-paper environments about totient
increments at primes and the Möbius expansion of the tail:

* `prop:CP-05-inv` — for every `h > 0` and every `B` there is a prime `p > B`
  with `φ(p+4h) - φ(p) ≡ 2 (mod 4)`;
* `prop:TA-inv` — an arbitrarily long zero prefix followed by a two-adic
  pulse, the resulting `D(H, p-K, K) ≡ 2^(K-1) (mod 2^K)`, and the transfer
  `R_{p+H} - R_p ∈ ℤ` with `R_{p+H} - R_p ≡ 2^(K-1) (mod 2^K)` under an
  eventual integrality hypothesis;
* `prop:MP-01-inv` — the Möbius-inversion formula for the tail.

Here `R_N = totientTail N`, `D(h,N,L) = windowDiscrepancy h N L`,
`r_d(N) = forwardMultipleShift N d` and `q_d(N) = forwardMultipleQuotient N d`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.TotientShiftedMobiusPulse

/-! ### `prop:CP-05-inv` — a totient difference congruent to two modulo four -/

/-- **A totient difference congruent to two modulo four.**  For every positive
integer `h` and every `B ∈ ℕ` there is a prime `p > B` with
`φ(p + 4h) - φ(p) ≡ 2 (mod 4)`. -/
theorem exists_prime_totient_shift_four_mul_congr_two_mod_four
    (h B : ℕ) (hh : 0 < h) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] := by
  obtain ⟨p, hpB, hp, hcong⟩ :=
    exists_prime_deltaTotient_four_mul_mod_four_two h B hh
  exact ⟨p, hpB, hp, hcong⟩

/-! ### `prop:TA-inv` — a zero prefix followed by a two-adic pulse -/

/-- The displayed divisor data at a prime `p` gives the two-adic letter
pattern: the terminal totient increment is the half-turn `2^(K-1)` and the
preceding `K-1` increments vanish, all modulo `2^K`. -/
theorem pulse_delta_of_divisor_data {H K p : ℕ} (hK : 2 ≤ K) (hp : p.Prime)
    (hmod : p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K])
    (htop : 2 ^ K ∣ Nat.totient (p + H))
    (hlower : ∀ j : ℕ, 1 ≤ j → j < K →
      2 ^ K ∣ Nat.totient (p - j) ∧ 2 ^ K ∣ Nat.totient (p - j + H)) :
    deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K] := by
  constructor
  · have hpPred : p - 1 ≡ 2 ^ (K - 1) [MOD 2 ^ K] := by
      have hsub := hmod.sub hp.one_le (by simp : 1 ≤ 1 + 2 ^ (K - 1))
        (Nat.ModEq.refl 1)
      simpa using hsub
    have hpTotNat : Nat.totient p ≡ 2 ^ (K - 1) [MOD 2 ^ K] := by
      simpa [Nat.totient_prime hp] using hpPred
    have hpTotInt :
        (Nat.totient p : ℤ) ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
      simpa using Int.natCast_modEq_iff.mpr hpTotNat
    have htopInt : (Nat.totient (p + H) : ℤ) ≡ 0 [ZMOD (2 : ℤ) ^ K] := by
      apply Int.modEq_zero_iff_dvd.mpr
      exact_mod_cast htop
    have hneg : deltaTotient H p ≡ -(2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
      simpa [deltaTotient] using htopInt.sub hpTotInt
    exact hneg.trans (neg_twoPow_pred_modEq_self (by omega))
  · intro j hj1 hjK
    obtain ⟨hbot, htopj⟩ := hlower j hj1 hjK
    have hbotInt : (2 : ℤ) ^ K ∣ (Nat.totient (p - j) : ℤ) := by
      exact_mod_cast hbot
    have htopjInt : (2 : ℤ) ^ K ∣ (Nat.totient (p - j + H) : ℤ) := by
      exact_mod_cast htopj
    apply Int.modEq_zero_iff_dvd.mpr
    simpa [deltaTotient] using dvd_sub htopjInt hbotInt

/-- **An arbitrarily long zero prefix followed by a two-adic pulse.**  Let
`K ≥ 2` and `H > K`.  For every `B` there is a prime `p > max(B, H+K)` with
`p ≡ 1 + 2^(K-1) (mod 2^K)`, `2^K ∣ φ(p+H)`, and `2^K ∣ φ(p-j)`,
`2^K ∣ φ(p-j+H)` for every `1 ≤ j < K`.  For such a `p` the first `K-1`
totient differences in the window starting at `p-K` vanish modulo `2^K`
while the last is `2^(K-1)`, and consequently
`D(H, p-K, K) ≡ 2^(K-1) (mod 2^K)`. -/
theorem exists_prime_twoAdic_pulse_block (K H B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧
      2 ^ K ∣ Nat.totient (p + H) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        2 ^ K ∣ Nat.totient (p - j) ∧ 2 ^ K ∣ Nat.totient (p - j + H)) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  obtain ⟨p, hpB, hpHK, hp, hmod, htop, hlower⟩ :=
    exists_prime_totient_twoAdic_pulse_divisors H K B hK hHK
  obtain ⟨hterm, hzero⟩ := pulse_delta_of_divisor_data hK hp hmod htop hlower
  exact ⟨p, hpB, hpHK, hp, hmod, htop, hlower, hzero, hterm,
    windowDiscrepancy_modEq_half_of_twoAdic_pulse hK (by omega) hterm hzero⟩

/-- **The integral transfer.**  If `R_{N+H} - R_N ∈ ℤ` for every `N ≥ N₀`,
then for every `B` there is a prime `p > B` for which `R_{p+H} - R_p` is an
integer congruent to `2^(K-1)` modulo `2^K`. -/
theorem exists_prime_integral_tailDiff_half_pulse
    {H K N₀ : ℕ} (hK : 2 ≤ K) (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ))
    (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] :=
  eventual_integral_tailDiff_has_cofinal_twoAdic_half_pulse hK hHK hint B

/-! ### `prop:MP-01-inv` — a Möbius-inversion formula for the tail -/

/-- `r_d(N) = d - (N mod d)` and `q_d(N) = ⌊N/d⌋ + 1`, with
`1 ≤ r_d(N) ≤ d` and `d ∣ N + r_d(N)`. -/
theorem forwardMultiple_spec (N : ℕ) {d : ℕ} (hd : 0 < d) :
    forwardMultipleShift N d = d - N % d ∧
      forwardMultipleQuotient N d = N / d + 1 ∧
      1 ≤ forwardMultipleShift N d ∧
      forwardMultipleShift N d ≤ d ∧
      d ∣ N + forwardMultipleShift N d :=
  ⟨rfl, rfl, forwardMultipleShift_pos N hd, forwardMultipleShift_le N d,
    forwardMultipleShift_dvd N hd⟩

/-- `r_d(N)` is the distance to the *next strictly larger* multiple of `d`:
no smaller positive shift reaches a multiple of `d`. -/
theorem forwardMultipleShift_least (N : ℕ) {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hlt : m < forwardMultipleShift N d) : ¬ d ∣ N + m := by
  intro hdvd
  have h0 : (N + m) % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hNd : N % d < d := Nat.mod_lt N hd
  have hr : forwardMultipleShift N d = d - N % d := rfl
  rw [hr] at hlt
  have hmd : m % d = m := Nat.mod_eq_of_lt (by omega)
  have hsum : N % d + m < d := by omega
  rw [Nat.add_mod, hmd, Nat.mod_eq_of_lt hsum] at h0
  omega

/-- The multiples of `d` strictly after `N` have quotients `q_d(N) + ℓ` and
forward distances `r_d(N) + d·ℓ`, for `ℓ ≥ 0`. -/
theorem forwardMultiple_enumeration (N : ℕ) {d : ℕ} (hd : 0 < d) (l : ℕ) :
    N + (forwardMultipleShift N d + d * l) =
      d * (forwardMultipleQuotient N d + l) := by
  have h := add_forwardMultipleShift_eq N hd
  calc
    N + (forwardMultipleShift N d + d * l)
        = (N + forwardMultipleShift N d) + d * l := by ring
    _ = d * forwardMultipleQuotient N d + d * l := by rw [h]
    _ = d * (forwardMultipleQuotient N d + l) := by ring

/-- **A Möbius-inversion formula for the tail.**
`R_N = ∑_{d≥1} μ(d) 2^(d - r_d(N)) (q_d(N)/(2^d-1) + 1/(2^d-1)^2)`. -/
theorem totientTail_eq_tsum_mobius_inversion (N : ℕ) :
    totientTail N =
      ∑' d : ℕ+,
        (((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) *
            (2 : ℝ) ^ ((d : ℕ) - forwardMultipleShift N (d : ℕ))) *
          (((forwardMultipleQuotient N (d : ℕ) : ℕ) : ℝ) /
              ((2 : ℝ) ^ (d : ℕ) - 1) +
            1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  rw [totientTail_eq_tsum_shiftedMobiusPulse N]
  exact tsum_congr fun d => rfl

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_totient_shift_four_mul_congr_two_mod_four
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.pulse_delta_of_divisor_data
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_pulse_block
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_integral_tailDiff_half_pulse
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_spec
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.forwardMultipleShift_least
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_enumeration
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totientTail_eq_tsum_mobius_inversion
