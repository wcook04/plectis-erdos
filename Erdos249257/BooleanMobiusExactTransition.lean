import Erdos249257.BooleanMobiusLocalRepair

/-!
# Exact endpoint transitions for Boolean--Möbius quotients

This module records the unconditional one-step arithmetic behind the finite
endpoint search.  For every Mersenne rank `d ≥ 2`, doubling the endpoint scale
either doubles its integral quotient or doubles it and adds one.  The extra
unit occurs exactly when `d` divides the new endpoint.

Summing this identity over a fixed finite Boolean support gives the exact
support transition.  The final lemmas rewrite the same statement as the
signed endpoint-defect recurrence

`H(M + 1) = 2 H(M) + 1 - S(M + 1)`.

These are reduction lemmas only.  In particular, they do not prove that the
defect is nonnegative and do not construct an exact Boolean support.
-/

namespace Erdos249257

open scoped BigOperators

/-! ## A single Mersenne quotient -/

/-- The integral Mersenne quotient has a binary endpoint transition.  The
new low bit is one precisely at endpoints divisible by the rank. -/
theorem localMersenneQuotient_endpoint_succ
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient (M + 1) d =
      2 * localMersenneQuotient M d + if d ∣ M + 1 then 1 else 0 := by
  let N := 2 ^ M
  let q := 2 ^ d - 1
  let Q := N / q
  let R := N % q
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  have hqTwo : 2 ≤ q := by
    have hfour : 4 ≤ 2 ^ d := by
      simpa using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) hd)
    dsimp [q]
    omega
  have hdecomp : N = Q * q + R := by
    dsimp [Q, R]
    simpa [Nat.mul_comm] using (Nat.div_add_mod N q).symm
  have hrem : R = 2 ^ (M % d) := by
    dsimp [N, q, R]
    exact two_pow_mod_mersenne hd
  have hpowSucc : 2 ^ (M + 1) = 2 * N := by
    simp [N, pow_succ, Nat.mul_comm]
  by_cases hdiv : d ∣ M + 1
  · have hmod : M % d = d - 1 := by
      simpa using
        (pred_mod_eq_pred_of_dvd
          (n := M + 1) (d := d) (by omega) hd hdiv)
    have hpowSplit : 2 ^ d = 2 ^ (d - 1) * 2 := by
      calc
        2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (d - 1) * 2 := by rw [pow_succ]
    have htwiceRem : 2 * R = q + 1 := by
      rw [hrem, hmod]
      dsimp [q]
      omega
    have hnext : 2 ^ (M + 1) = (2 * Q + 1) * q + 1 := by
      calc
        2 ^ (M + 1) = 2 * N := hpowSucc
        _ = 2 * (Q * q + R) := by rw [hdecomp]
        _ = (2 * Q + 1) * q + 1 := by
          rw [mul_add, htwiceRem]
          ring
    simp only [if_pos hdiv]
    change 2 ^ (M + 1) / q = 2 * Q + 1
    apply Nat.div_eq_of_lt_le
    · rw [hnext]
      exact Nat.le_add_right _ _
    · rw [hnext]
      calc
        (2 * Q + 1) * q + 1 < (2 * Q + 1) * q + q :=
          Nat.add_lt_add_left (by omega) _
        _ = (2 * Q + 1 + 1) * q := by ring
  · have hmodne : M % d ≠ d - 1 := by
      intro hmod
      apply hdiv
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, hmod,
        Nat.mod_eq_of_lt (by omega : 1 < d),
        Nat.sub_add_cancel (by omega : 1 ≤ d), Nat.mod_self]
    have hmodlt : M % d < d := Nat.mod_lt _ (by omega)
    have hmodSuccLe : M % d + 1 ≤ d - 1 := by omega
    have hpowsLe : 2 ^ (M % d + 1) ≤ 2 ^ (d - 1) :=
      Nat.pow_le_pow_right (by norm_num) hmodSuccLe
    have hpowSplit : 2 ^ d = 2 ^ (d - 1) * 2 := by
      calc
        2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (d - 1) * 2 := by rw [pow_succ]
    have hhalfTwo : 2 ≤ 2 ^ (d - 1) := by
      simpa using
        (Nat.pow_le_pow_right
          (by norm_num : 0 < 2) (by omega : 1 ≤ d - 1))
    have htwiceRemLt : 2 * R < q := by
      calc
        2 * R = 2 ^ (M % d + 1) := by
          rw [hrem, pow_succ']
        _ ≤ 2 ^ (d - 1) := hpowsLe
        _ < q := by
          dsimp [q]
          omega
    have hnext : 2 ^ (M + 1) = (2 * Q) * q + 2 * R := by
      calc
        2 ^ (M + 1) = 2 * N := hpowSucc
        _ = 2 * (Q * q + R) := by rw [hdecomp]
        _ = (2 * Q) * q + 2 * R := by ring
    simp only [if_neg hdiv, add_zero]
    change 2 ^ (M + 1) / q = 2 * Q
    apply Nat.div_eq_of_lt_le
    · rw [hnext]
      exact Nat.le_add_right _ _
    · rw [hnext]
      calc
        (2 * Q) * q + 2 * R < (2 * Q) * q + q :=
          Nat.add_lt_add_left htwiceRemLt _
        _ = (2 * Q + 1) * q := by ring

/-! ## Finite Boolean supports -/

/-- Summing the one-rank transition over a fixed finite Boolean support adds
exactly the number of selected ranks dividing the new endpoint. -/
theorem localPrefixQuotient_succ
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M +
        endpointDivisorContribution D (M + 1) := by
  classical
  unfold localPrefixQuotient endpointDivisorContribution
  calc
    ∑ d ∈ D, localMersenneQuotient (M + 1) d =
        ∑ d ∈ D,
          (2 * localMersenneQuotient M d +
            if d ∣ M + 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hdmem
      exact localMersenneQuotient_endpoint_succ (hD d hdmem)
    _ = 2 * (∑ d ∈ D, localMersenneQuotient M d) +
          (D.filter fun d ↦ d ∣ M + 1).card := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum]

/-- The integer target corresponding to the dyadic value immediately below
`1/2` at endpoint scale `2^M`. -/
def halfEndpointTarget (M : ℕ) : ℕ :=
  2 ^ (M - 1) - 1

theorem halfEndpointTarget_succ
    {M : ℕ} (hM : 1 ≤ M) :
    halfEndpointTarget (M + 1) = 2 * halfEndpointTarget M + 1 := by
  have hpow : 2 ^ M = 2 * 2 ^ (M - 1) := by
    calc
      2 ^ M = 2 ^ ((M - 1) + 1) := by congr 1 <;> omega
      _ = 2 * 2 ^ (M - 1) := by rw [pow_succ']
  have hone : 1 ≤ 2 ^ (M - 1) := Nat.one_le_pow _ _ (by norm_num)
  unfold halfEndpointTarget
  simp only [Nat.add_sub_cancel]
  omega

/-- With a support held fixed, an exact endpoint row propagates one step if
and only if exactly one selected rank divides the new endpoint. -/
theorem localPrefixQuotient_succ_eq_halfEndpointTarget_iff
    {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hexact : localPrefixQuotient D M = halfEndpointTarget M) :
    localPrefixQuotient D (M + 1) = halfEndpointTarget (M + 1) ↔
      endpointDivisorContribution D (M + 1) = 1 := by
  rw [localPrefixQuotient_succ hD, halfEndpointTarget_succ hM, hexact]
  omega

/-! ## Signed endpoint defect -/

/-- The signed finite-row defect from the integer immediately below one half.
Unlike `localBinarySuffix`, this definition never truncates subtraction. -/
def localEndpointDefect (D : Finset ℕ) (M : ℕ) : ℤ :=
  (halfEndpointTarget M : ℤ) - (localPrefixQuotient D M : ℤ)

/-- The exact `H = 2 A + 1 - S` transition, stated without a nonnegativity
assumption by working in the integers. -/
theorem localEndpointDefect_succ
    {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    localEndpointDefect D (M + 1) =
      2 * localEndpointDefect D M + 1 -
        (endpointDivisorContribution D (M + 1) : ℤ) := by
  unfold localEndpointDefect
  rw [localPrefixQuotient_succ hD, halfEndpointTarget_succ hM]
  push_cast
  ring

/-- When the previous quotient has not crossed its endpoint target, the
natural suffix is the signed defect, so `localRepairInteger` is literally the
next endpoint defect. -/
theorem localRepairInteger_eq_localEndpointDefect_succ
    {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hbelow : localPrefixQuotient D M ≤ halfEndpointTarget M) :
    localRepairInteger D 1 (M + 1) = localEndpointDefect D (M + 1) := by
  have hsuffix :
      localBinarySuffix D 1 M =
        halfEndpointTarget M - localPrefixQuotient D M := by
    unfold localBinarySuffix halfEndpointTarget
    omega
  have hsuffixCast :
      (localBinarySuffix D 1 M : ℤ) = localEndpointDefect D M := by
    unfold localEndpointDefect
    rw [hsuffix, Nat.cast_sub hbelow]
  calc
    localRepairInteger D 1 (M + 1) =
        2 * localEndpointDefect D M + 1 -
          (endpointDivisorContribution D (M + 1) : ℤ) := by
      unfold localRepairInteger
      rw [show M + 1 - 1 = M by omega, hsuffixCast]
    _ = localEndpointDefect D (M + 1) :=
      (localEndpointDefect_succ hM hD).symm

end Erdos249257
