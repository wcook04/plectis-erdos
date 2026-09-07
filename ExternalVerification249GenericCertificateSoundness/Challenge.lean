/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge: generic certificate soundness and the tail-period law

Two statements about a coefficient sequence `c : ℕ → ℕ` with `c n ≤ n`, whose
binary value is `∑_{n ≥ 0} c (n+1) / 2 ^ (n+1)` and whose scaled tail at
height `N` is `T c N = ∑_{j ≥ 0} c (N + j + 1) / 2 ^ (j+1)`.

`generic_soundness` is the certificate half. A finite integer window of length
`L` comparing the block after `N + h` with the block after `N` determines a
discrepancy `window c h N L`. If that discrepancy sits in the central arc
modulo `2 ^ L`, at distance more than `N + h + L + 2` from both endpoints,
then `T c (N + h) - T c N` is not an integer.

`generic_tail_period` is the converse-side period law. If the binary value is
the rational `p / (2 ^ e * m)` with `m` positive and `m ∣ 2 ^ h - 1`, then for
every `N ≥ e` the shift `T c (N + h) - T c N` is an integer.

Neither statement supplies a certificate for any particular sequence. Applied
to `c = φ` they bound what a proof of irrationality for
`∑_{n ≥ 1} φ n / 2 ^ n` must produce, and Erdős Problem 249 remains open.
-/

namespace Erdos249257.ExternalVerification249GenericCertificateSoundness

/-- The binary value `∑_{n ≥ 0} c (n+1) / 2 ^ (n+1)`. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

/-- The scaled tail `T c N = ∑_{j ≥ 0} c (N + j + 1) / 2 ^ (j+1)`. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

/-- The length-`L` integer window comparing the blocks after `N + h` and `N`. -/
def window (c : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((c (N + h + 1 + j) : ℤ) - (c (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

/-- The certificate: the window discrepancy lies in the central arc modulo
`2 ^ L`, at distance more than `N + h + L + 2` from both endpoints. -/
def Kill (c : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N : ℤ) + h + L + 2 < window c h N L % 2 ^ L ∧
    window c h N L % 2 ^ L < 2 ^ L - ((N : ℤ) + h + L + 2)

/-- **Certificate soundness.** A kill certificate forces the tail shift off the
integers. -/
theorem generic_soundness (c : ℕ → ℕ) (hg : ∀ n, c n ≤ n)
    {h N L : ℕ} (hkill : Kill c h N L) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- **The rational tail-period law.** A rational value with denominator
`2 ^ e * m` and `m ∣ 2 ^ h - 1` freezes every tail shift of step `h` above
the preperiod `e` at an integer. -/
theorem generic_tail_period (c : ℕ → ℕ) (hg : ∀ n, c n ≤ n)
    (p : ℤ) (e m h N : ℕ) (hm : 0 < m) (heN : e ≤ N)
    (hdiv : m ∣ 2 ^ h - 1)
    (hseries : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * (m : ℝ))) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry

end Erdos249257.ExternalVerification249GenericCertificateSoundness
