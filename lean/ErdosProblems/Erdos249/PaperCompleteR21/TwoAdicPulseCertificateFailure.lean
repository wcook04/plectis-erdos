import Erdos249257.TotientTwoAdicPulseBlock

/-! The long #249 manuscript's failure of a specified two-adic congruence
construction (`prop:b4`).  The pulse construction does place the window
discrepancy at the half-turn `2^{K-1}` modulo `2^K`, but its defining
congruence forces the prime to exceed `2^{K-1}`, and the certificate's error
bound `N + h + L + 2` is then larger than the residue.  So the residue fails
the certificate inequalities at every depth `K`. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-- **The specified two-adic pulse construction never certifies** (`prop:b4`).

For every depth `K ≥ 2` and every shift `H > K` the construction supplies a
prime `p` beyond the pulse threshold with

* `p > H + K` and `p > 2^{K-1}` (the defining congruence
  `p ≡ 1 + 2^{K-1} (mod 2^K)` forces `p ≥ 1 + 2^{K-1}`);
* the length-`K` window discrepancy at `N = p - K`, `h = H`, `L = K` congruent
  to the half-turn `2^{K-1}` modulo `2^K`;

and yet the certificate inequalities fail there, because the error bound
`N + h + L + 2 = p + H + 2` already exceeds the residue `2^{K-1}`.  This is a
statement about this construction only; it proves nothing about other uses of
the Chinese Remainder Theorem or other prescribed totient patterns. -/
theorem twoAdic_pulse_construction_never_certifies
    (H K : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, p.Prime ∧ H + K < p ∧ 2 ^ (K - 1) < p ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ¬ certifiedKill H (p - K) K := by
  obtain ⟨p, hpB, hpHK, hp, hterminal, hzero⟩ :=
    exists_prime_deltaTotient_twoAdic_pulseBlock H K (2 ^ (K - 1)) hK hHK
  have hpK : K ≤ p := by omega
  have hword := windowDiscrepancy_modEq_half_of_twoAdic_pulse hK hpK hterminal hzero
  refine ⟨p, hp, hpHK, hpB, hword, ?_⟩
  rintro ⟨hleft, -⟩
  have hKpred : K - 1 + 1 = K := by omega
  have hpospred : (0 : ℤ) < 2 ^ (K - 1) := by positivity
  have hsplit : (2 : ℤ) ^ K = 2 * 2 ^ (K - 1) := by
    conv_lhs => rw [← hKpred]
    rw [pow_succ]
    ring
  have hlt : (2 : ℤ) ^ (K - 1) < 2 ^ K := by linarith
  have hres : windowDiscrepancy H (p - K) K % 2 ^ K = (2 : ℤ) ^ (K - 1) := by
    have h : windowDiscrepancy H (p - K) K % 2 ^ K = (2 : ℤ) ^ (K - 1) % 2 ^ K := hword
    rw [h, Int.emod_eq_of_lt hpospred.le hlt]
  rw [hres] at hleft
  have hcastsub : (((p - K : ℕ) : ℤ)) = (p : ℤ) - (K : ℤ) := Nat.cast_sub hpK
  have hpgt : (2 : ℤ) ^ (K - 1) < (p : ℤ) := by exact_mod_cast hpB
  have hH0 : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg H
  rw [hcastsub] at hleft
  linarith

/-- **The defining congruence and its consequence** (`prop:b4`, second
sentence): the prime supplied by the pulse construction satisfies
`p ≡ 1 + 2^{K-1} (mod 2^K)`, hence `p ≥ 1 + 2^{K-1}`. -/
theorem twoAdic_pulse_defining_congruence (H K B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧ 1 + 2 ^ (K - 1) ≤ p := by
  obtain ⟨p, hpB, hpHK, hp, hcong, -, -⟩ :=
    exists_prime_totient_twoAdic_pulse_divisors H K B hK hHK
  refine ⟨p, hpB, hpHK, hp, hcong, ?_⟩
  have h2 : 2 ≤ 2 ^ (K - 1) := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (K - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsplit : (2 : ℕ) ^ K = 2 * 2 ^ (K - 1) := by
    conv_lhs => rw [show K = (K - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hlt : 1 + 2 ^ (K - 1) < 2 ^ K := by omega
  have hmod : (1 + 2 ^ (K - 1)) % 2 ^ K = 1 + 2 ^ (K - 1) := Nat.mod_eq_of_lt hlt
  have hp' : p % 2 ^ K = 1 + 2 ^ (K - 1) := by
    have hthis : p % 2 ^ K = (1 + 2 ^ (K - 1)) % 2 ^ K := hcong
    rw [hthis, hmod]
  calc 1 + 2 ^ (K - 1) = p % 2 ^ K := hp'.symm
    _ ≤ p := Nat.mod_le p (2 ^ K)

/-- **The error bound exceeds the residue** (`prop:b4`, third sentence): at
`N = p - K`, `h = H`, `L = K` the certificate's error bound `N + h + L + 2`
equals `p + H + 2`, and `p > 2^{K-1}` makes it exceed the residue
`2^{K-1}`. -/
theorem twoAdic_pulse_error_bound (H K p : ℕ) (hKp : K ≤ p)
    (hp : 2 ^ (K - 1) < p) :
    (p - K) + H + K + 2 = p + H + 2 ∧ 2 ^ (K - 1) < p + H + 2 :=
  ⟨by omega, by omega⟩

#print axioms twoAdic_pulse_construction_never_certifies
#print axioms twoAdic_pulse_defining_congruence
#print axioms twoAdic_pulse_error_bound
end ErdosProblems.Erdos249.PaperCompleteR21
