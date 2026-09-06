import Erdos249257.LcmConeFlatness

/-!
# Erdős #249: the affine diagonal `(h, h-1)`, and a progression-cofinal normal form

`LcmConeFlatness` already reduces #249 to a one-parameter supply along the
*lcm diagonal* `(periodLcm t, periodLcm t)`
(`irrational_totient_series_iff_lcm_diagonal_certificate_supply`), and to a
two-parameter supply with a free basepoint
(`irrational_totient_series_iff_certificate_supply`).

This module deletes the basepoint search a different way.  Fix the basepoint to
the *deterministic* point `N = h - 1` immediately below the shift.  Then:

* `affineDiagonalKillSupply_iff_irrational` — a certificate on **every** ray at
  its own affine basepoint is exactly #249.  Neither the multiplier, nor a
  prime index, nor a cyclotomic factor, nor a threshold, nor a free basepoint
  survives in the statement.

* `progressionDiagonalKillSupply_iff_irrational` — the *same* conclusion
  follows from the strictly weaker demand of certificates at **cofinally many
  `h` in every arithmetic progression**.  This is the form that matters: a
  rational value supplies one eventual period `d`, and only multiples of `d`
  beyond the pre-period need to be killed, so a producer never has to handle
  every `h` — only cofinally many in each `dℕ`.

* `factorialDiagonalKillSupply_iff_irrational` — one single cofinal sequence
  `h = m!` suffices, since every period eventually divides a factorial.

The mechanism is the telescope `tail_diff_mem_int_of_dvd`: under an eventual
period `d`, integrality of one `d`-shift propagates to every multiple of `d`,
so a kill at `(h, h-1)` with `d ∣ h` and `h - 1` past the pre-period is already
a contradiction.

## Why fixed-depth residue constructions cannot supply these certificates

`certifiedKill_depth_floor` gives `2(N+h+L+2) < 2^L`, hence
`certifiedKill_basepoint_lt_two_pow`: **every** certificate has
`N < 2^(L-1)`.  A termwise Chinese-remainder construction that annihilates the
depth-`1` denominator letter needs a prime `a ≡ 1 [MOD 2^(L-1)]` dividing
`N + 1`, forcing `N + 1 ≥ a ≥ 2^(L-1) + 1`.  Those two are incompatible
(`no_certifiedKill_of_large_prime_annihilator`).  So exact residue engineering
at fixed depth realises any prescribed dyadic word, but always outside the
certificate cone; the missing input for #249 is quantitative — centrality
*before* the linear radius overtakes the exponential modulus — not residue
support.

## Claim ceiling

**Erdős #249 remains open.**  Nothing here supplies a certificate at any new
`(h, N)`.  What is settled is that the search space is smaller than it looked:
the basepoint is determined by the shift, and cofinality inside each
progression replaces universality over shifts.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

/-! ## Telescoping an eventual period along its own multiples -/

private theorem mem_range_int_add {x y : ℝ}
    (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) (hy : y ∈ Set.range ((↑) : ℤ → ℝ)) :
    x + y ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by push_cast; rw [ha, hb]⟩

/-- **Multiples of an eventual period stay integral.**  If every `d`-shift is
integral from `N₀` on, then so is every `k·d`-shift. -/
theorem tail_diff_mem_int_of_multiple {d N₀ : ℕ}
    (hint : ∀ N, N₀ ≤ N →
      totientTail (N + d) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∀ (k N : ℕ), N₀ ≤ N →
      totientTail (N + k * d) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  intro k
  induction k with
  | zero =>
      intro N _
      simp only [Nat.zero_mul, Nat.add_zero, sub_self]
      exact ⟨0, by norm_num⟩
  | succ k ih =>
      intro N hN
      have hstep : totientTail (N + k * d + d) - totientTail (N + k * d)
          ∈ Set.range ((↑) : ℤ → ℝ) := hint _ (le_trans hN (Nat.le_add_right _ _))
      have hidx : N + k * d + d = N + (k + 1) * d := by ring
      rw [hidx] at hstep
      have hsum := mem_range_int_add hstep (ih N hN)
      have heq : totientTail (N + (k + 1) * d) - totientTail (N + k * d)
            + (totientTail (N + k * d) - totientTail N)
          = totientTail (N + (k + 1) * d) - totientTail N := by ring
      rwa [heq] at hsum

/-- The divisibility form: `d ∣ h` transports integrality of the `d`-shift to
the `h`-shift. -/
theorem tail_diff_mem_int_of_dvd {d h N₀ : ℕ} (hdvd : d ∣ h)
    (hint : ∀ N, N₀ ≤ N →
      totientTail (N + d) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ))
    (N : ℕ) (hN : N₀ ≤ N) :
    totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨k, hk⟩ := hdvd
  have := tail_diff_mem_int_of_multiple hint k N hN
  rwa [show k * d = h from by rw [Nat.mul_comm]; exact hk.symm] at this

/-! ## The three diagonal supplies -/

/-- A certificate on **every** ray, at the deterministic basepoint `h - 1`. -/
def AffineDiagonalKillSupply : Prop :=
  ∀ h : ℕ, 0 < h → ∃ L, certifiedKill h (h - 1) L

/-- Certificates at **cofinally many `h` in every arithmetic progression**,
each at its own affine basepoint.  Strictly weaker than universality. -/
def ProgressionDiagonalKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ B : ℕ,
    ∃ h : ℕ, B < h ∧ d ∣ h ∧ ∃ L, certifiedKill h (h - 1) L

/-- Certificates along one cofinal factorial sequence. -/
def FactorialDiagonalKillSupply : Prop :=
  ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ∃ L, certifiedKill (Nat.factorial m) (Nat.factorial m - 1) L

/-! ## The reduction -/

/-- **The progression-cofinal affine diagonal proves #249.**  A rational value
supplies one eventual period `d` and a pre-period `N₀`; a certificate at any
multiple `h` of `d` past `N₀`, sitting at its own basepoint `h - 1`, already
contradicts it. -/
theorem irrational_of_progressionDiagonalKillSupply
    (hsupply : ProgressionDiagonalKillSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨d, hd, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  obtain ⟨h, hBh, hdvd, L, hcert⟩ := hsupply d hd N₀
  have hbase : N₀ ≤ h - 1 := by omega
  have hmem : totientTail (h - 1 + h) - totientTail (h - 1)
      ∈ Set.range ((↑) : ℤ → ℝ) := tail_diff_mem_int_of_dvd hdvd hint (h - 1) hbase
  exact tail_diff_notMem_int_of_certifiedKill hcert hmem

theorem progressionDiagonalKillSupply_of_affineDiagonal
    (hsupply : AffineDiagonalKillSupply) : ProgressionDiagonalKillSupply := by
  intro d hd B
  have hle : B + 1 ≤ d * (B + 1) := Nat.le_mul_of_pos_left (B + 1) hd
  have hpos : 0 < d * (B + 1) := Nat.mul_pos hd (Nat.succ_pos B)
  exact ⟨d * (B + 1), by omega, dvd_mul_right d (B + 1), hsupply _ hpos⟩

theorem progressionDiagonalKillSupply_of_factorialDiagonal
    (hsupply : FactorialDiagonalKillSupply) : ProgressionDiagonalKillSupply := by
  intro d hd B
  obtain ⟨m, hm, L, hcert⟩ := hsupply (max d B)
  refine ⟨Nat.factorial m, ?_, Nat.dvd_factorial hd (le_of_lt (lt_of_le_of_lt (le_max_left d B) hm)), L, hcert⟩
  have hle : m ≤ Nat.factorial m := Nat.self_le_factorial m
  have : B < m := lt_of_le_of_lt (le_max_right d B) hm
  omega

/-! ## Exact normal forms -/

/-- **The affine diagonal is an exact normal form for #249.**  The forward
direction is pointwise certificate completeness at the single point
`(h, h - 1)`; the reverse is the telescope. -/
theorem affineDiagonalKillSupply_iff_irrational :
    AffineDiagonalKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine ⟨fun hs => irrational_of_progressionDiagonalKillSupply
    (progressionDiagonalKillSupply_of_affineDiagonal hs), fun hirr h hh => ?_⟩
  exact (irrational_totient_series_iff_pointwise_certificates.mp hirr) h hh (h - 1)

/-- **The progression-cofinal diagonal is also an exact normal form.**  This is
the weakest of the three: a producer only has to hit cofinally many `h` in each
`dℕ`, never every `h`. -/
theorem progressionDiagonalKillSupply_iff_irrational :
    ProgressionDiagonalKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨irrational_of_progressionDiagonalKillSupply, fun hirr =>
    progressionDiagonalKillSupply_of_affineDiagonal
      (affineDiagonalKillSupply_iff_irrational.mpr hirr)⟩

/-- **One cofinal factorial sequence suffices.** -/
theorem factorialDiagonalKillSupply_iff_irrational :
    FactorialDiagonalKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine ⟨fun hs => irrational_of_progressionDiagonalKillSupply
    (progressionDiagonalKillSupply_of_factorialDiagonal hs), fun hirr B => ?_⟩
  refine ⟨B + 1, by omega, ?_⟩
  exact (irrational_totient_series_iff_pointwise_certificates.mp hirr)
    (Nat.factorial (B + 1)) (Nat.factorial_pos _) _

/-! ## The certificate cone excludes termwise residue engineering -/

/-- Every certificate forces its basepoint strictly below `2^(L-1)`. -/
theorem certifiedKill_basepoint_lt_two_pow {h N L : ℕ} (hcert : certifiedKill h N L) :
    (N : ℤ) < 2 ^ (L - 1) := by
  have hfloor := certifiedKill_depth_floor hcert
  have hL : 1 ≤ L := by
    by_contra hL
    have : L = 0 := by omega
    subst this
    norm_num at hfloor
    omega
  have hsplit : (2 : ℤ) ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit] at hfloor
  omega

/-- **The termwise-CRT no-go, in exact form.**  A construction that annihilates
the depth-`1` denominator letter supplies a divisor `a` of `N + 1` with
`2^(L-1) < a`.  No such basepoint can carry a certificate at depth `L`. -/
theorem no_certifiedKill_of_large_prime_annihilator {h N L a : ℕ}
    (hdvd : a ∣ N + 1) (hpos : 0 < N + 1) (hbig : 2 ^ (L - 1) < a) :
    ¬ certifiedKill h N L := by
  intro hcert
  have hbase := certifiedKill_basepoint_lt_two_pow hcert
  have hale : a ≤ N + 1 := Nat.le_of_dvd hpos hdvd
  have : (2 : ℤ) ^ (L - 1) < (N : ℤ) + 1 := by exact_mod_cast lt_of_lt_of_le hbig hale
  omega

end TotientTailPeriodKiller
end Erdos249257
