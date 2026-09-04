import ErdosProblems.Erdos249.PeriodMultipleEscape

namespace ErdosProblems.Erdos249.PeriodMultipleEscape

/-!
# Eventual affine boundary modes are impossible

The exact endpoint cocycle says that an affine tail for the signed endpoint
error would make the consecutive totient letters affine as well.  Two late
prime arguments and the doubled first prime give three non-collinear totient
points: `φ(p)=p-1`, `φ(q)=q-1`, but `φ(2p)=p-1`.  This eliminates the exact
affine part of the surviving linear-scale boundary mechanism.
-/

/-- A fixed-quotient pure-dyadic endpoint error is eventually affine in its
height. -/
def EventuallyAffinePureDyadicEndpointError (c : ℕ) (k : ℤ) : Prop :=
  ∃ A B : ℤ, ∃ H0 : ℕ, ∀ H, H0 ≤ H →
    pureDyadicEndpointError H c k = A * H + B

/-- The actual consecutive-totient word admits no eventually affine
fixed-quotient endpoint-error tail.

This consumes `pureDyadicEndpointError_succ`.  The three-ray obstruction is
arbitrarily late: choose primes `p < q`, then compare the recurrence letters
at `p`, `q`, and `2p`. -/
theorem not_eventuallyAffine_pureDyadicEndpointError (c : ℕ) (k : ℤ) :
    ¬ EventuallyAffinePureDyadicEndpointError c k := by
  rintro ⟨A, B, H0, hAffine⟩
  obtain ⟨p, hpLower, hpPrime⟩ :=
    Nat.exists_infinite_primes (max (c + H0 + 2) 3)
  obtain ⟨q, hqLower, hqPrime⟩ := Nat.exists_infinite_primes (2 * p + 1)
  let Hp : ℕ := p - (c + 1)
  let Hq : ℕ := q - (c + 1)
  let H2p : ℕ := 2 * p - (c + 1)
  have hpLarge : c + H0 + 2 ≤ p := le_trans (le_max_left _ _) hpLower
  have hpThree : 3 ≤ p := le_trans (le_max_right _ _) hpLower
  have hqLarge : 2 * p + 1 ≤ q := hqLower
  have hHp : H0 ≤ Hp := by simp only [Hp]; omega
  have hHq : H0 ≤ Hq := by simp only [Hq]; omega
  have hH2p : H0 ≤ H2p := by simp only [H2p]; omega
  have hIndexP : c + Hp + 1 = p := by simp only [Hp]; omega
  have hIndexQ : c + Hq + 1 = q := by simp only [Hq]; omega
  have hIndex2p : c + H2p + 1 = 2 * p := by simp only [H2p]; omega
  have hHpLtH2p : Hp < H2p := by simp only [Hp, H2p]; omega
  have digit_affine (H : ℕ) (hH : H0 ≤ H) :
      (Nat.totient (c + H + 1) : ℤ) =
        -A * (H : ℤ) + A - B + k := by
    have hrec := pureDyadicEndpointError_succ H c k
    rw [hAffine H hH, hAffine (H + 1) (by omega)] at hrec
    push_cast at hrec
    linarith
  have hpEq := digit_affine Hp hHp
  have hqEq := digit_affine Hq hHq
  have h2pEq := digit_affine H2p hH2p
  rw [hIndexP, Nat.totient_prime hpPrime] at hpEq
  rw [hIndexQ, Nat.totient_prime hqPrime] at hqEq
  have hpNeTwo : p ≠ 2 := by omega
  have hphi2p : Nat.totient (2 * p) = p - 1 := by
    rw [Nat.totient_two_mul_of_odd (hpPrime.odd_of_ne_two hpNeTwo),
      Nat.totient_prime hpPrime]
  rw [hIndex2p, hphi2p] at h2pEq
  have hAZero : A = 0 := by
    have hgap : (0 : ℤ) < (H2p : ℤ) - (Hp : ℤ) := by omega
    nlinarith
  rw [hAZero] at hpEq hqEq
  have hpq : p < q := by omega
  omega

end ErdosProblems.Erdos249.PeriodMultipleEscape
