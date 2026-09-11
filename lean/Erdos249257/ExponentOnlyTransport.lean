import Erdos249257.LcmConeFlatness
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Exponent-only transport for Erdős #249

This module isolates the support-stable side of an LCM prime-power jump.  If
`p ∣ H`, multiplying `H` by `p` cannot add a squarefree divisor channel: every
squarefree divisor of `p * H` already divides `H`.  Consequently the
four-vertex commutator is pure transport on the active Möbius support, unlike
the new-prime jump where a migrated `p`-saturated layer must be retained.

The residue kernel is also decomposed into its genuine affine state.  The
periodic residue coordinate alone is insufficient: dilation transports both a
linear slope and an intercept.  The first-order formula below records both
blocks and prevents the constant-block determinant from being mistaken for a
global non-cancellation theorem.

The final theorem is conditional on an explicitly named infinite supply.  No
such supply is asserted here, and this file does not claim Erdős #249.
-/

namespace Erdos249257.ExponentOnlyTransport

open scoped ArithmeticFunction.Moebius
open TotientTailPeriodKiller

/-! ## Squarefree support stability -/

/-- If `p` is already a divisor of `H`, multiplication by `p` adds no
squarefree divisor channels.  This is stronger than the prime-power-jump
specialization: the exponent and primality of `p` are not needed. -/
theorem squarefree_dvd_mul_iff_of_dvd
    {p H d : ℕ} (hpH : p ∣ H) (hsq : Squarefree d) :
    d ∣ p * H ↔ d ∣ H := by
  constructor
  · intro hdpH
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    rw [← Finset.lcm_eq_prod]
    · exact Finset.lcm_dvd fun q hq => by
        have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
        have hqd : q ∣ d := Nat.dvd_of_mem_primeFactors hq
        rcases hqprime.dvd_or_dvd (hqd.trans hdpH) with hqp | hqH
        · exact hqp.trans hpH
        · exact hqH
    · intro q hq r hr hqr
      exact (Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors hq)
        (Nat.prime_of_mem_primeFactors hr)).mpr hqr
  · exact fun hdH => hdH.mul_left p

/-- Prime-form API used by the exponent-only LCM jump. -/
theorem squarefree_dvd_prime_mul_iff_of_prime_dvd
    {p H d : ℕ} (_hp : p.Prime) (hpH : p ∣ H) (hsq : Squarefree d) :
    d ∣ p * H ↔ d ∣ H :=
  squarefree_dvd_mul_iff_of_dvd hpH hsq

/-- The nonzero Möbius support is unchanged across `H -> pH` once `p ∣ H`. -/
theorem mobius_ne_zero_dvd_mul_iff_of_dvd
    {p H d : ℕ} (hpH : p ∣ H)
    (hmu : ArithmeticFunction.moebius d ≠ 0) :
    d ∣ p * H ↔ d ∣ H :=
  squarefree_dvd_mul_iff_of_dvd hpH
    (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu)

/-! ## Pure transport and old-channel cancellation -/

/-- Least positive shift sending `N` to a multiple of `d`. -/
def transportResidueOffset (d N : ℕ) : ℕ := d - N % d

/-- Exact Möbius residue kernel, stated locally so this disjoint transport
owner can be validated independently of adjacent projection files. -/
noncomputable def transportResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - transportResidueOffset d N) *
      (((N + transportResidueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))

/-- Diagonal increment of the exact transport kernel. -/
noncomputable def transportResidueIncrement (d H : ℕ) : ℝ :=
  transportResidueKernel d (2 * H) - transportResidueKernel d H

/-- Channelwise first-order transport of the diagonal residue increment. -/
noncomputable def residueTransportDefect (d H p : ℕ) : ℝ :=
  transportResidueIncrement d (p * H) - p * transportResidueIncrement d H

/-- A divisor channel has the standard linear form. -/
theorem transportResidueIncrement_of_dvd
    {d H : ℕ} (hd : 0 < d) (hdvd : d ∣ H) :
    transportResidueIncrement d H =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (H : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  have h2dvd : d ∣ 2 * H := dvd_mul_of_dvd_right hdvd 2
  have hmod : H % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have h2mod : (2 * H) % d = 0 := Nat.mod_eq_zero_of_dvd h2dvd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpowNat : 1 < 2 ^ d := Nat.one_lt_two_pow hd.ne'
  have hpowR : (1 : ℝ) < (2 : ℝ) ^ d := by exact_mod_cast hpowNat
  have hM : (2 : ℝ) ^ d - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpowR)
  unfold transportResidueIncrement transportResidueKernel transportResidueOffset
  rw [hmod, h2mod]
  simp only [Nat.sub_zero, Nat.sub_self, pow_zero]
  push_cast
  field_simp [hdR, hM]
  ring

/-- Every old divisor channel is annihilated exactly by first-order transport. -/
theorem residueTransportDefect_eq_zero_of_dvd
    {d H p : ℕ} (hd : 0 < d) (hdH : d ∣ H) :
    residueTransportDefect d H p = 0 := by
  have hdpH : d ∣ p * H := hdH.mul_left p
  rw [residueTransportDefect,
    transportResidueIncrement_of_dvd hd hdpH,
    transportResidueIncrement_of_dvd hd hdH]
  push_cast
  ring

/-! ## The actual affine residue state -/

/-- Periodic coefficient of the linear-in-`N` part of the residue kernel. -/
noncomputable def residueSlope (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (N % d) /
      ((d : ℝ) * ((2 : ℝ) ^ d - 1))

/-- Periodic intercept of the residue kernel. -/
noncomputable def residueIntercept (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (N % d) *
      (((transportResidueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))

/-- The exact kernel is affine in the scale coordinate and periodic in the
residue coordinate.  This is the state omitted by a residue-permutation-only
transport matrix. -/
theorem transportResidueKernel_eq_affineState
    {d N : ℕ} (hd : 0 < d) :
    transportResidueKernel d N =
      (N : ℝ) * residueSlope d N + residueIntercept d N := by
  have hmodle : N % d ≤ d := (Nat.mod_lt N hd).le
  have hpow : d - (d - N % d) = N % d := Nat.sub_sub_self hmodle
  rw [transportResidueKernel, residueSlope, residueIntercept,
    transportResidueOffset, hpow]
  rw [Nat.cast_add, Nat.cast_sub hmodle]
  ring

/-- The slope state is periodic modulo the channel index. -/
theorem residueSlope_add_period {d N : ℕ} (_hd : 0 < d) :
    residueSlope d (N + d) = residueSlope d N := by
  simp [residueSlope]

/-- The intercept state is periodic modulo the channel index. -/
theorem residueIntercept_add_period {d N : ℕ} (_hd : 0 < d) :
    residueIntercept d (N + d) = residueIntercept d N := by
  simp [residueIntercept, transportResidueOffset]

/-- Linear block of the four-vertex `H -> 3H` transport. -/
noncomputable def threeTransportSlopePart (d H : ℕ) : ℝ :=
  3 * (H : ℝ) *
    (2 * residueSlope d (6 * H) - residueSlope d (3 * H) -
      2 * residueSlope d (2 * H) + residueSlope d H)

/-- Constant block of the four-vertex `H -> 3H` transport. -/
noncomputable def threeTransportInterceptPart (d H : ℕ) : ℝ :=
  residueIntercept d (6 * H) - residueIntercept d (3 * H) -
    3 * residueIntercept d (2 * H) + 3 * residueIntercept d H

/-- Exact first-order affine transfer.  Both blocks are present; invertibility
of a constant residue-permutation block alone cannot prove this expression is
nonzero or prevent cancellation between channel indices. -/
theorem residueTransportDefect_three_eq_affineState
    {d H : ℕ} (hd : 0 < d) :
    residueTransportDefect d H 3 =
      threeTransportSlopePart d H + threeTransportInterceptPart d H := by
  simp only [residueTransportDefect, transportResidueIncrement]
  rw [transportResidueKernel_eq_affineState (d := d) (N := 2 * (3 * H)) hd,
    transportResidueKernel_eq_affineState (d := d) (N := 3 * H) hd,
    transportResidueKernel_eq_affineState (d := d) (N := 2 * H) hd,
    transportResidueKernel_eq_affineState (d := d) (N := H) hd]
  unfold threeTransportSlopePart threeTransportInterceptPart
  push_cast
  ring

/-! ## The infinite endpoint socket -/

/-- The actual four-vertex transport on the totient tail. -/
noncomputable def threeTransportTailCommutator (H : ℕ) : ℝ :=
  (totientTail (6 * H) - totientTail (3 * H)) -
    3 * (totientTail (2 * H) - totientTail H)

/-- Exact unresolved supply on the fixed `3^a` LCM tower. -/
def ExponentOnlyThreeTransportSupply : Prop :=
  ∀ t₀ : ℕ, ∃ a : ℕ,
    2 ≤ a ∧ t₀ ≤ 3 ^ a - 1 ∧
      threeTransportTailCommutator (periodLcm (3 ^ a - 1)) ∉
        Set.range ((↑) : ℤ → ℝ)

/-- The fixed-three transport supply contradicts rational LCM-cone flatness
and therefore proves irrationality of the totient series. -/
theorem irrational_totient_series_of_exponentOnlyThreeTransportSupply
    (hsupply : ExponentOnlyThreeTransportSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨a, _ha, ht, hnonint⟩ := hsupply t₁
  obtain ⟨x, hx⟩ := hflat (3 ^ a - 1) ht 1 1 (by omega)
  obtain ⟨y, hy⟩ := hflat (3 ^ a - 1) ht 3 3 (by omega)
  apply hnonint
  refine ⟨y - 3 * x, ?_⟩
  rw [threeTransportTailCommutator]
  push_cast
  rw [show 1 * periodLcm (3 ^ a - 1) + 1 * periodLcm (3 ^ a - 1) =
      2 * periodLcm (3 ^ a - 1) by ring, one_mul] at hx
  rw [show 3 * periodLcm (3 ^ a - 1) + 3 * periodLcm (3 ^ a - 1) =
      2 * (3 * periodLcm (3 ^ a - 1)) by ring] at hy
  rw [show 6 * periodLcm (3 ^ a - 1) =
      2 * (3 * periodLcm (3 ^ a - 1)) by ring]
  linarith [hx, hy]

#print axioms squarefree_dvd_mul_iff_of_dvd
#print axioms transportResidueKernel_eq_affineState
#print axioms residueTransportDefect_three_eq_affineState
#print axioms irrational_totient_series_of_exponentOnlyThreeTransportSupply

end Erdos249257.ExponentOnlyTransport
