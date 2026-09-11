import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
# Erdős #68: strict-successor arithmetic

Let `N = m Nprev + 1 - b`, with `b` confined to the full rounding interval
`[-1,m-1]`.  Divisibility of `N` by `m` is then equivalent to the single value
`b = 1`.  At a dilated index `k p`, divisibility by `p^k` separates further
into a finite choice of digit slots and one predecessor congruence.  The case
`k = 2` leaves two explicit branches.

These are local arithmetic equivalences.  They do not show that either branch
fails at infinitely many primes, which is the global input still needed by
the prime-endpoint approach to Erdős #68.
-/

namespace ErdosProblems.Erdos68

/-- Arithmetic core of the strict-successor recurrence.  If

`N = m * Nprev + 1 - b`

with the sharp digit bounds `-1 ≤ b ≤ m - 1` and `m ≥ 3`, then `m ∣ N`
holds exactly when `b = 1`.  The result is stated over `ℤ` because the
rounding digit can attain `-1` at the lower endpoint. -/
theorem dvd_strictSuccessor_iff_roundingDigit_eq_one
    {m N Nprev b : ℤ}
    (hm : 3 ≤ m)
    (hrec : N = m * Nprev + 1 - b)
    (hbLower : -1 ≤ b)
    (hbUpper : b ≤ m - 1) :
    m ∣ N ↔ b = 1 := by
  constructor
  · intro hdiv
    have hmul : m ∣ m * Nprev := dvd_mul_right m Nprev
    have hsmallDvd : m ∣ 1 - b := by
      have hsub : m ∣ N - m * Nprev := hdiv.sub hmul
      convert hsub using 1
      omega
    have hsmallAbs : |1 - b| < m := by
      rw [abs_lt]
      constructor <;> omega
    have hzero : 1 - b = 0 :=
      Int.eq_zero_of_abs_lt_dvd hsmallDvd hsmallAbs
    omega
  · rintro rfl
    rw [hrec]
    ring_nf
    exact dvd_mul_right m Nprev

/-- Exact two-stage criterion for a prime-power hit at a dilated
strict-successor index.  The first stage forces the rounding digit into one
of the `k` residue slots `1 + p r`; the second stage is the surviving
predecessor congruence modulo `p^(k-1)`. -/
theorem pow_dvd_dilation_strictSuccessor_iff
    {p N Nprev b : ℤ} {k : ℕ}
    (hp : 3 ≤ p)
    (hk : 1 ≤ k)
    (hrec : N = ((k : ℤ) * p) * Nprev + 1 - b)
    (hbLower : -1 ≤ b)
    (hbUpper : b ≤ (k : ℤ) * p - 1) :
    p ^ k ∣ N ↔
      ∃ r : ℤ,
        0 ≤ r ∧ r < (k : ℤ) ∧
          b = 1 + p * r ∧
            p ^ (k - 1) ∣ (k : ℤ) * Nprev - r := by
  have hp0 : p ≠ 0 := by omega
  have hpNonneg : 0 ≤ p := by omega
  have hkSplit : k = (k - 1) + 1 := by omega
  have hpowSplit : p ^ k = p * p ^ (k - 1) := by
    calc
      p ^ k = p ^ ((k - 1) + 1) :=
        congrArg (fun e : ℕ => p ^ e) hkSplit
      _ = p ^ (k - 1) * p := pow_succ p (k - 1)
      _ = p * p ^ (k - 1) := by ring
  constructor
  · intro hpow
    rcases hpow with ⟨t, ht⟩
    have hpDvd : p ∣ N := by
      refine ⟨p ^ (k - 1) * t, ?_⟩
      rw [ht, hpowSplit]
      ring
    have hbaseDvd : p ∣ ((k : ℤ) * p) * Nprev := by
      refine ⟨(k : ℤ) * Nprev, ?_⟩
      ring
    have hsmallDvd : p ∣ 1 - b := by
      have hsub := hpDvd.sub hbaseDvd
      convert hsub using 1
      rw [hrec]
      ring
    have hbSubDvd : p ∣ b - 1 := by
      rcases hsmallDvd with ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      calc
        b - 1 = -(1 - b) := by ring
        _ = -(p * c) := by rw [hc]
        _ = p * (-c) := by ring
    rcases hbSubDvd with ⟨r, hr⟩
    have hbr : b = 1 + p * r := by omega
    have hrNonneg : 0 ≤ r := by
      by_contra hr
      have hrLe : r ≤ -1 := by omega
      have hmulLe : p * r ≤ p * (-1) :=
        mul_le_mul_of_nonneg_left hrLe hpNonneg
      nlinarith
    have hrLt : r < (k : ℤ) := by
      by_contra hr
      have hkLe : (k : ℤ) ≤ r := by omega
      have hmulLe : p * (k : ℤ) ≤ p * r :=
        mul_le_mul_of_nonneg_left hkLe hpNonneg
      nlinarith
    refine ⟨r, hrNonneg, hrLt, hbr, ?_⟩
    refine ⟨t, ?_⟩
    apply mul_left_cancel₀ hp0
    calc
      p * ((k : ℤ) * Nprev - r) = N := by
        rw [hrec, hbr]
        ring
      _ = p ^ k * t := ht
      _ = p * (p ^ (k - 1) * t) := by rw [hpowSplit]; ring
  · rintro ⟨r, _hrNonneg, _hrLt, hbr, hsecond⟩
    rcases hsecond with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      N = ((k : ℤ) * p) * Nprev + 1 - b := hrec
      _ = p * ((k : ℤ) * Nprev - r) := by rw [hbr]; ring
      _ = p * (p ^ (k - 1) * t) := by rw [ht]
      _ = p ^ k * t := by rw [hpowSplit]; ring

/-- At dilation `k = 2`, a square hit has exactly two possible digit and
predecessor-residue branches. -/
theorem sq_dvd_double_strictSuccessor_iff
    {p N Nprev b : ℤ}
    (hp : 3 ≤ p)
    (hrec : N = (2 * p) * Nprev + 1 - b)
    (hbLower : -1 ≤ b)
    (hbUpper : b ≤ 2 * p - 1) :
    p ^ 2 ∣ N ↔
      (b = 1 ∧ p ∣ 2 * Nprev) ∨
        (b = 1 + p ∧ p ∣ 2 * Nprev - 1) := by
  rw [pow_dvd_dilation_strictSuccessor_iff hp (by omega)
    (by simpa using hrec) hbLower (by simpa using hbUpper)]
  constructor
  · rintro ⟨r, hr0, hr2, hbr, hsecond⟩
    have hr : r = 0 ∨ r = 1 := by omega
    rcases hr with rfl | rfl
    · left
      constructor
      · simpa using hbr
      · simpa using hsecond
    · right
      constructor
      · simpa [mul_one] using hbr
      · simpa using hsecond
  · rintro (⟨hb, hdiv⟩ | ⟨hb, hdiv⟩)
    · refine ⟨0, by omega, by omega, ?_, ?_⟩
      · simpa using hb
      · simpa using hdiv
    · refine ⟨1, by omega, by omega, ?_, ?_⟩
      · simpa [mul_one] using hb
      · simpa using hdiv

/-- For an odd prime, the factor `2` cancels in the first square-hit
branch, leaving the exact predecessor divisibility stated in the #68
prime-power reduction. -/
theorem sq_dvd_double_strictSuccessor_prime_iff
    {p : ℕ} (hp : p.Prime) (hpTwo : p ≠ 2)
    {N Nprev b : ℤ}
    (hrec : N = (2 * (p : ℤ)) * Nprev + 1 - b)
    (hbLower : -1 ≤ b)
    (hbUpper : b ≤ 2 * (p : ℤ) - 1) :
    (p : ℤ) ^ 2 ∣ N ↔
      (b = 1 ∧ (p : ℤ) ∣ Nprev) ∨
        (b = 1 + (p : ℤ) ∧
          (p : ℤ) ∣ 2 * Nprev - 1) := by
  have hp3Nat : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  have hp3 : (3 : ℤ) ≤ p := by
    exact_mod_cast hp3Nat
  rw [sq_dvd_double_strictSuccessor_iff hp3 hrec hbLower hbUpper]
  constructor
  · rintro (⟨hb, hdiv⟩ | hright)
    · left
      refine ⟨hb, ?_⟩
      rcases Int.Prime.dvd_mul' hp hdiv with hpTwoDvd | hpN
      · have hpTwoDvdNat : p ∣ 2 :=
          Int.natCast_dvd_natCast.mp (by simpa using hpTwoDvd)
        have hpLeTwo : p ≤ 2 :=
          Nat.le_of_dvd (by omega) hpTwoDvdNat
        exact (hpTwo (by omega)).elim
      · exact hpN
    · exact Or.inr hright
  · rintro (⟨hb, hpN⟩ | hright)
    · left
      exact ⟨hb, dvd_mul_of_dvd_right hpN 2⟩
    · exact Or.inr hright

#print axioms pow_dvd_dilation_strictSuccessor_iff
#print axioms sq_dvd_double_strictSuccessor_iff
#print axioms sq_dvd_double_strictSuccessor_prime_iff

end ErdosProblems.Erdos68
