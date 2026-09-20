import Erdos249257.TotientTwoAdicPulseBlock

/-! Paper-form restatements of two long-paper environments of Erdős #249:

* the unconditional two-adic pulse theorem: for every `K ≥ 2`, every `H > K`
  and every bound `B` there is a prime `p > B` whose length-`(K-1)` prefix of
  totient increments vanishes modulo `2^K` while the terminal letter is the
  half-modulus, so that `D(H, p-K, K) ≡ 2^{K-1} (mod 2^K)`; and the transfer
  of that residue to an actual tail-difference integer under eventual
  integrality;
* the sufficient accumulated-residue condition: a cofinal supply of triples
  with `D(h,N,L) ≡ 2^{L-1} (mod 2^L)` and `N+h+L+2 < 2^{L-1}` gives `S ∉ ℚ`.

Here `R_N = totientTail N`, `D(h,N,L) = windowDiscrepancy h N L` and
`C(h,N,L) = certifiedKill h N L`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-! ### A two-adic congruence that does not give a certificate -/

/-- **The two-adic half-modulus pulse.**  For every `K ≥ 2`, every `H > K` and
every bound `B` there is a prime `p > B` with a length-`(K-1)` zero prefix and
a terminal half-modulus, giving `D(H, p-K, K) ≡ 2^{K-1} (mod 2^K)`. -/
theorem exists_prime_twoAdic_half_pulse_window (H K B : ℕ) (hK : 2 ≤ K)
    (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  obtain ⟨p, hpB, hpHK, hp, hterminal, hzero⟩ :=
    exists_prime_deltaTotient_twoAdic_pulseBlock H K B hK hHK
  refine ⟨p, hpB, hp, hzero, hterminal, ?_⟩
  exact windowDiscrepancy_modEq_half_of_twoAdic_pulse hK (by omega) hterminal hzero

/-- **Transfer under eventual integrality.**  If every shift `R_{N+H} - R_N`
past `N₀` is an integer, the pulse produces cofinally many primes `p` with an
integer `z` equal to `R_{p+H} - R_p` and `z ≡ 2^{K-1} (mod 2^K)`. -/
theorem eventual_integral_tailDiff_twoAdic_half_pulse {H K N₀ : ℕ} (hK : 2 ≤ K)
    (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] :=
  eventual_integral_tailDiff_has_cofinal_twoAdic_half_pulse hK hHK hint

/-! ### A sufficient accumulated-residue condition -/

/-- The two displayed conditions imply the certificate `C(h,N,L)`. -/
theorem certifiedKill_of_halfModulus_residue {h N L : ℕ} (hL : 1 ≤ L)
    (hcong : windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L])
    (hsmall : ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    certifiedKill h N L := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  have hk : k + 1 - 1 = k := by omega
  rw [hk] at hcong hsmall
  have hpos : (0 : ℤ) < 2 ^ k := by positivity
  have hsplit : (2 : ℤ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
  have hlt : (2 : ℤ) ^ k < 2 ^ (k + 1) := by rw [hsplit]; linarith
  have hmod : (2 : ℤ) ^ k % 2 ^ (k + 1) = 2 ^ k := Int.emod_eq_of_lt hpos.le hlt
  have hcong' : windowDiscrepancy h N (k + 1) % 2 ^ (k + 1)
      = (2 : ℤ) ^ k % 2 ^ (k + 1) := hcong
  have hval : windowDiscrepancy h N (k + 1) % 2 ^ (k + 1) = 2 ^ k := by
    rw [hcong', hmod]
  unfold certifiedKill
  rw [hval]
  refine ⟨hsmall, ?_⟩
  rw [hsplit]
  linarith

/-- **A sufficient accumulated-residue condition.**  If for every `h ≥ 1` and
every `N₀` there are `N ≥ N₀` and `L ≥ 1` with `D(h,N,L) ≡ 2^{L-1} (mod 2^L)`
and `N+h+L+2 < 2^{L-1}`, then `S ∉ ℚ`. -/
theorem irrational_of_accumulated_halfModulus_supply
    (hsupply : ∀ h : ℕ, 1 ≤ h → ∀ N₀ : ℕ, ∃ N L : ℕ, N₀ ≤ N ∧ 1 ≤ L ∧
      windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L] ∧
      ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_certificate_supply ?_
  intro h hh N₀
  obtain ⟨N, L, hN, hL, hcong, hsmall⟩ := hsupply h hh N₀
  exact ⟨N, hN, L, certifiedKill_of_halfModulus_residue hL hcong hsmall⟩

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_half_pulse_window
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.eventual_integral_tailDiff_twoAdic_half_pulse
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_halfModulus_residue
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_accumulated_halfModulus_supply
