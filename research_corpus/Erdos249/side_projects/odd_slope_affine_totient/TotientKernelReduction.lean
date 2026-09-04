import Mathlib.Data.Nat.Totient

/-!
# Reduction identities for the totient `k`-kernel, for every integer base

Toward the exact rank theorem `dim_Q V_{k,e} = k^e + 1` for every integer
`k ≥ 2` (paper proof in
`docs/formal_math/odd_slope_affine_totient_independence.md`).  This file
formalises the *spanning* half: the identities that collapse a section
`n ↦ φ(k^j n + r)` onto a canonical one.

* `totient_mul_eq_of_primes_dvd` — if every prime of `k` divides `m`, then
  `φ (k * m) = k * φ m`.  This is the engine.
* `totient_pow_mul_eq` — `φ (k^j * n) = k^(j-1) * φ (k * n)` for `j ≥ 1`,
  which is the zero-residue relation `F_{j,0} = k^(j-1) • F_{1,0}`.
* `totient_pow_mul_gcd_cross_eq` — a division-free composite-base reduction
  for `φ(k^t m)`, with the exact `gcd` correction exposed.
* `totient_pow_mul_affine_gcd_cross_eq` — the corresponding affine-section
  formula, whose coefficient depends only on the residue class `u`.

Nothing here concerns irrationality, and none of it bears on Erdős #249.
-/

namespace Erdos249257

/-- If every prime dividing `k` also divides `m`, then multiplying the argument
by `k` multiplies the totient by exactly `k`.

This is the composite-base generalisation of `Nat.totient_mul_of_prime_of_dvd`,
and it is what makes every kernel reduction below a *scalar* one. -/
theorem totient_mul_eq_of_primes_dvd :
    ∀ k : ℕ, 0 < k → ∀ m : ℕ,
      (∀ p : ℕ, p.Prime → p ∣ k → p ∣ m) →
      Nat.totient (k * m) = k * Nat.totient m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk m hsupp
    rcases Nat.lt_or_ge k 2 with h1 | h1
    · have hk1 : k = 1 := by omega
      subst hk1
      simp
    · obtain ⟨p, hp, k', rfl⟩ :
          ∃ p : ℕ, p.Prime ∧ ∃ k' : ℕ, k = p * k' := by
        obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
        obtain ⟨k', rfl⟩ := hpk
        exact ⟨p, hp, k', rfl⟩
      have hk'pos : 0 < k' := by
        rcases Nat.eq_zero_or_pos k' with h | h
        · simp [h] at hk
        · exact h
      have hlt : k' < p * k' := by
        have hstep : 2 * k' ≤ p * k' := Nat.mul_le_mul hp.two_le (le_refl k')
        exact lt_of_lt_of_le (by omega) hstep
      have hpm : p ∣ m := hsupp p hp ⟨k', rfl⟩
      have hsupp' : ∀ q : ℕ, q.Prime → q ∣ k' → q ∣ m := by
        intro q hq hqk'
        exact hsupp q hq (hqk'.mul_left p)
      have hIH : Nat.totient (k' * m) = k' * Nat.totient m :=
        ih k' hlt hk'pos m hsupp'
      have hassoc : p * k' * m = p * (k' * m) := by ring
      rw [hassoc, Nat.totient_mul_of_prime_of_dvd hp (hpm.mul_left k'), hIH]
      ring

/-- The zero-residue relation of the totient `k`-kernel: for `j ≥ 1`,
`φ (k^j * n) = k^(j-1) * φ (k * n)`.

In kernel notation this is `F_{j,0} = k^(j-1) • F_{1,0}`, so every zero-residue
section at any level collapses onto the single canonical channel `F_{1,0}`. -/
theorem totient_pow_mul_eq (k : ℕ) (hk : 0 < k) (n : ℕ) :
    ∀ j : ℕ, 1 ≤ j →
      Nat.totient (k ^ j * n) = k ^ (j - 1) * Nat.totient (k * n) := by
  intro j hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0; simp
    · have hstep :
          Nat.totient (k ^ (j + 1) * n) = k * Nat.totient (k ^ j * n) := by
        have hsupp : ∀ p : ℕ, p.Prime → p ∣ k → p ∣ k ^ j * n := by
          intro p _ hpk
          exact Dvd.dvd.mul_right (hpk.trans (dvd_pow_self k (by omega))) n
        have hassoc : k ^ (j + 1) * n = k * (k ^ j * n) := by ring
        rw [hassoc, totient_mul_eq_of_primes_dvd k hk (k ^ j * n) hsupp]
      rw [hstep, ih (by omega)]
      have : j + 1 - 1 = (j - 1) + 1 := by omega
      rw [this, pow_succ]
      ring

/-- Division-free composite-base reduction for a positive power of `k`.

The rational scalar usually written
`k^(t-1) * φ(k) * gcd(k,m) / φ(gcd(k,m))` is deliberately cross-multiplied:
this statement remains valid in `ℕ` without introducing an exact-division
side condition. -/
theorem totient_pow_mul_gcd_cross_eq
    (k : ℕ) (hk : 0 < k) (m t : ℕ) (ht : 1 ≤ t) :
    Nat.totient (Nat.gcd k m) * Nat.totient (k ^ t * m) =
      k ^ (t - 1) * Nat.totient k * Nat.gcd k m * Nat.totient m := by
  rw [totient_pow_mul_eq k hk m t ht]
  calc
    Nat.totient (Nat.gcd k m) *
          (k ^ (t - 1) * Nat.totient (k * m)) =
        k ^ (t - 1) *
          (Nat.totient (Nat.gcd k m) * Nat.totient (k * m)) := by ring
    _ = k ^ (t - 1) *
          (Nat.totient k * Nat.totient m * Nat.gcd k m) := by
      rw [Nat.totient_gcd_mul_totient_mul]
    _ = k ^ (t - 1) * Nat.totient k * Nat.gcd k m * Nat.totient m := by
      ring

/-- Adding a multiple of `k` does not change the gcd with `k`; written in the
exact affine-section shape used by the all-base totient kernel. -/
theorem gcd_pow_mul_add_eq_gcd
    (k h n u : ℕ) (hh : 1 ≤ h) :
    Nat.gcd k (k ^ h * n + u) = Nat.gcd k u := by
  obtain ⟨h', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  simpa [pow_succ, Nat.add_comm, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    using Nat.gcd_add_mul_right_right k u (k ^ h' * n)

/-- Exact affine-section specialization of `totient_pow_mul_gcd_cross_eq`.

For `m = k^h n + u` with `h ≥ 1`, the correction factor is controlled by
`gcd(k,u)` and is therefore constant along the entire section.  This is the
arithmetic layer needed before the finite-dimensional all-base kernel basis
argument; it does not assert the remaining linear independence theorem. -/
theorem totient_pow_mul_affine_gcd_cross_eq
    (k : ℕ) (hk : 0 < k) (h n u t : ℕ) (hh : 1 ≤ h) (ht : 1 ≤ t) :
    Nat.totient (Nat.gcd k u) *
        Nat.totient (k ^ t * (k ^ h * n + u)) =
      k ^ (t - 1) * Nat.totient k * Nat.gcd k u *
        Nat.totient (k ^ h * n + u) := by
  rw [← gcd_pow_mul_add_eq_gcd k h n u hh]
  exact totient_pow_mul_gcd_cross_eq k hk (k ^ h * n + u) t ht

/-- Coprime affine sections have an exact scalar reduction.

When the residue `u` is coprime to the base `k`, the gcd correction in
`totient_pow_mul_affine_gcd_cross_eq` is `1`.  This is the canonical
prime-to-base section interface for downstream finite-kernel arguments; it
does not assert the remaining all-base linear-independence theorem. -/
theorem totient_pow_mul_affine_coprime_eq
    (k : ℕ) (hk : 0 < k) (h n u t : ℕ) (hh : 1 ≤ h) (ht : 1 ≤ t)
    (hcoprime : Nat.Coprime k u) :
    Nat.totient (k ^ t * (k ^ h * n + u)) =
      k ^ (t - 1) * Nat.totient k * Nat.totient (k ^ h * n + u) := by
  have hcross :=
    totient_pow_mul_affine_gcd_cross_eq k hk h n u t hh ht
  have hgcd : Nat.gcd k u = 1 := hcoprime
  simpa [hgcd] using hcross

end Erdos249257
