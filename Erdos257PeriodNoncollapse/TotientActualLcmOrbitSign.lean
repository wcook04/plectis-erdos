import Erdos257PeriodNoncollapse.TotientActualLcmOrbitArithmetic
import Erdos257PeriodNoncollapse.TotientTailCarryPeriod

/-!
# Positive sign corridor for the actual LCM tail orbit

The short actual-LCM arithmetic word has strictly positive letters.  The
quantitative quarter-height bounds are strong enough to turn that finite
fact into an Archimedean statement about the true (infinite) tail orbit:
through almost the whole short LCM window, the translated difference

`R_(2H+J) - R_(H+J)`,  where `H = lcm(1, ..., 2^a)`,

is positive.  The proof keeps an `a+6`-letter positive prefix and absorbs the
entire uncontrolled future with the directed lower tail bound.

This is a sign theorem, not an irrationality theorem.  Its carry consumer
records the precise consequence for the existing survivor surface: whenever
the true orbit is integral, the true endpoint survivor is on the negative
side throughout this corridor.  Spurious survivors of either sign may still
exist, and no nonintegrality claim is made here.
-/

namespace Erdos257PeriodNoncollapse
namespace DiagonalFreshLossBridge
namespace PowerTwoOddWindowAffine

open Finset
open TotientTailPeriodKiller

/-- **Unconditional positive-sign corridor.**  At a power-of-two LCM height,
the true translated tail difference stays positive as long as an `a+6`-term
lookahead remains inside the short arithmetic window.

The first lookahead letter already contributes more than enough: its
quarter-height lower bound, amplified by `2^(a+5) = 32 * 2^a`, dominates four
copies of the LCM height.  All remaining lookahead letters are positive, and
the directed lower bound controls the untranslated infinite remainder. -/
theorem actualLcmTailDiff_shift_pos
    {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 <
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J) := by
  let t : ℕ := 2 ^ a
  let H : ℕ := periodLcm t
  let L : ℕ := a + 6
  let c : ℤ := deltaTotient H (H + J + 1)
  have htPos : 0 < t := by
    simp [t]
  have htTwo : 2 ≤ t := by
    dsimp [t]
    exact (show 2 ^ 1 ≤ 2 ^ a by
      exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have hHt : t ≤ H := by
    dsimp [H]
    exact le_periodLcm t
  have hJL : J + L < 2 * t := by
    simpa [L, t] using hshort
  have hLPos : 0 < L := by
    dsimp [L]
    omega
  have hoffsetPos (r : ℕ) : 0 < J + r + 1 := by omega
  have hoffsetShort (r : ℕ) (hr : r < L) :
      J + r + 1 < 2 * t := by
    omega
  have hdeltaPos (r : ℕ) (hr : r < L) :
      0 < deltaTotient H (H + J + 1 + r) := by
    have hpos := lcmRayArithmeticLetter_pos_of_lt_two_mul
      (a := a) (j := J + r + 1) ha (hoffsetPos r)
        (by simpa [t] using hoffsetShort r hr)
    rw [lcmRayArithmeticLetter_eq_deltaTotient] at hpos
    simpa [H, t, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpos
  have hcPos : 0 < c := by
    simpa [c] using hdeltaPos 0 hLPos
  have hHc : (H : ℤ) < 8 * (t : ℤ) * c := by
    have hbound := periodLcm_lt_eight_mul_t_mul_lcmRayArithmeticLetter
      (a := a) (j := J + 1) ha (by omega)
        (by simpa [t] using hoffsetShort 0 hLPos)
    rw [lcmRayArithmeticLetter_eq_deltaTotient] at hbound
    simpa [H, t, c, Nat.add_assoc] using hbound
  have hB4H : H + J + L + 2 < 4 * H := by
    omega
  have hpow : (2 : ℤ) ^ (L - 1) = 32 * (t : ℤ) := by
    dsimp [L, t]
    calc
      (2 : ℤ) ^ (a + 5) = 2 ^ a * 2 ^ 5 := by rw [pow_add]
      _ = 32 * (2 : ℤ) ^ a := by norm_num; ring
  have hfirstLarge :
      ((H + J + L + 2 : ℕ) : ℤ) < c * (2 : ℤ) ^ (L - 1) := by
    have hB4HZ : ((H + J + L + 2 : ℕ) : ℤ) < 4 * (H : ℤ) := by
      exact_mod_cast hB4H
    calc
      ((H + J + L + 2 : ℕ) : ℤ) < 4 * (H : ℤ) := hB4HZ
      _ < 4 * (8 * (t : ℤ) * c) :=
        mul_lt_mul_of_pos_left hHc (by norm_num)
      _ = c * (2 : ℤ) ^ (L - 1) := by rw [hpow]; ring
  have hfirstLe :
      c * (2 : ℤ) ^ (L - 1) ≤ windowDiscrepancy H (H + J) L := by
    let f : ℕ → ℤ := fun r ↦
      deltaTotient H (H + J + 1 + r) * 2 ^ (L - 1 - r)
    have hsingle : f 0 ≤ ∑ r ∈ Finset.range L, f r := by
      apply Finset.single_le_sum
      · intro r hr
        exact mul_nonneg (hdeltaPos r (Finset.mem_range.mp hr)).le
          (by positivity)
      · exact Finset.mem_range.mpr hLPos
    calc
      c * (2 : ℤ) ^ (L - 1) = f 0 := by simp [f, c]
      _ ≤ ∑ r ∈ Finset.range L, f r := hsingle
      _ = windowDiscrepancy H (H + J) L := by
        unfold windowDiscrepancy
        apply Finset.sum_congr rfl
        intro r _hr
        simp [f, deltaTotient, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
  have hwindowLarge :
      ((H + J + L + 2 : ℕ) : ℤ) < windowDiscrepancy H (H + J) L :=
    hfirstLarge.trans_le hfirstLe
  have hsplit :=
    tail_diff_eq_windowDiscrepancy_div_add_shifted H (H + J) L
  have htail := tail_diff_directed_bounds H (H + J + L)
  have hwindowLargeR :
      ((H + J + L + 2 : ℕ) : ℝ) <
        (windowDiscrepancy H (H + J) L : ℝ) := by
    exact_mod_cast hwindowLarge
  have htailLower :
      -((H + J + L + 2 : ℕ) : ℝ) <
        totientTail (H + J + L + H) - totientTail (H + J + L) := by
    convert htail.1 using 1 <;> push_cast <;> ring
  have hnum :
      0 < (windowDiscrepancy H (H + J) L : ℝ) +
        (totientTail (H + J + L + H) - totientTail (H + J + L)) := by
    linarith
  have hden : (0 : ℝ) < 2 ^ L := by positivity
  have hpos :
      0 < totientTail (H + J + H) - totientTail (H + J) := by
    rw [hsplit, ← add_div]
    exact div_pos hnum hden
  simpa [H, t, two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hpos

/-- The actual LCM orbit itself is the first point of the positive corridor. -/
theorem actualLcmTailOrbit_pos (a : ℕ) (ha : 8 ≤ a) :
    0 < actualLcmTailOrbit a := by
  have haPow : a < 2 ^ a := Nat.lt_two_pow_self
  have hSix : 6 ≤ 2 ^ a := by
    calc
      6 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hshort : 0 + (a + 6) < 2 * 2 ^ a := by omega
  simpa [actualLcmTailOrbit, actualLcmHeight, two_mul] using
    (actualLcmTailDiff_shift_pos (a := a) (J := 0) ha hshort)

/-- A true integral representative of the actual LCM tail orbit cannot be
nonpositive.  This is the direct sign consumer for the nonintegrality lane. -/
theorem actualLcmTailOrbit_integralRepresentative_pos
    {a : ℕ} (ha : 8 ≤ a) {z : ℤ}
    (hz : (z : ℝ) = actualLcmTailOrbit a) :
    0 < z := by
  have hpos : (0 : ℝ) < (z : ℝ) := by
    rw [hz]
    exact actualLcmTailOrbit_pos a ha
  exact_mod_cast hpos

/-- **Survivor-sign consumer.**  If a translated actual LCM orbit is
integral at the start of the positive corridor, then at every later endpoint
which still has an `a+6`-letter lookahead, the survivor supplied by the true
carry is strictly negative.  Thus the nonnegative true-survivor branch is
eliminated; this does not assert that the finite survivor set has no
nonnegative spurious elements. -/
theorem actualLcm_trueEndpointSurvivor_neg
    {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J)) :
    -carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) d K < 0 ∧
      endpointSurvivor (periodLcm (2 ^ a))
        (periodLcm (2 ^ a) + J) K
        (-carryOrbit (periodLcm (2 ^ a))
          (periodLcm (2 ^ a) + J) d K) := by
  let H : ℕ := periodLcm (2 ^ a)
  have hd' : (d : ℝ) = totientTail ((H + J) + H) - totientTail (H + J) := by
    simpa [H, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
  have htrack := carryOrbit_eq_tail_diff hd' K
  have hpos := actualLcmTailDiff_shift_pos (a := a) (J := J + K) ha (by
    simpa [Nat.add_assoc] using hshort)
  have horbitPosR :
      (0 : ℝ) <
        (carryOrbit H (H + J) d K : ℝ) := by
    rw [htrack]
    simpa [H, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpos
  have horbitPos : 0 < carryOrbit H (H + J) d K := by
    exact_mod_cast horbitPosR
  constructor
  · simpa [H] using (neg_neg_of_pos horbitPos)
  · simpa [H] using integral_tailDiff_has_endpointSurvivor hd' K

/-- **Exact obstruction to a sign-only modular kill.**  Once the dyadic
modulus is wider than the directed endpoint strip, integrality together with
the positive-sign corridor does not put the discrepancy residue in the
central arc.  It forces the opposite: the residue is exactly the top-edge
representative `2^K - carry_K`.

Consequently the upper inequality required by `directedCertifiedKill` fails
strictly.  Any contradiction after the sign theorem therefore needs an
independent arithmetic exclusion of this top boundary band; the carry reset
alone merely re-encodes the persistent negative survivor. -/
theorem actualLcm_integral_forces_topEdgeResidue
    {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J))
    (hroom :
      ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
        (2 : ℤ) ^ K) :
    let H := periodLcm (2 ^ a)
    let e := carryOrbit H (H + J) d K
    let P := (2 : ℤ) ^ K
    let B := ((2 * H + J + K + 2 : ℕ) : ℤ)
    windowDiscrepancy H (H + J) K % P = P - e ∧
      P - B < windowDiscrepancy H (H + J) K % P ∧
      windowDiscrepancy H (H + J) K % P < P := by
  let H : ℕ := periodLcm (2 ^ a)
  let e : ℤ := carryOrbit H (H + J) d K
  let P : ℤ := (2 : ℤ) ^ K
  let B : ℤ := ((2 * H + J + K + 2 : ℕ) : ℤ)
  have hd' : (d : ℝ) = totientTail ((H + J) + H) - totientTail (H + J) := by
    simpa [H, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
  have htrack := carryOrbit_eq_tail_diff hd' K
  have hpos := actualLcmTailDiff_shift_pos (a := a) (J := J + K) ha (by
    simpa [Nat.add_assoc] using hshort)
  have hePosR : (0 : ℝ) < (e : ℝ) := by
    dsimp [e]
    rw [htrack]
    simpa [H, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpos
  have hePos : 0 < e := by
    exact_mod_cast hePosR
  have htailUpper := (tail_diff_directed_bounds H (H + J + K)).2
  rw [← htrack] at htailUpper
  have heUpperR : (e : ℝ) < ((2 * H + J + K + 2 : ℕ) : ℝ) := by
    dsimp [e]
    convert htailUpper using 1 <;> push_cast <;> ring
  have heUpper : e < B := by
    dsimp [B]
    exact_mod_cast heUpperR
  have hBP : B < P := by
    simpa [H, B, P] using hroom
  have heP : e < P := heUpper.trans hBP
  have hmod :
      (-e) % P = windowDiscrepancy H (H + J) K % P := by
    have hsurvivor := integral_tailDiff_has_endpointSurvivor hd' K
    simpa [e, P] using hsurvivor.2
  have hnegEmod : (-e) % P = P - e := by
    rw [show -e = (P - e) + P * (-1) by ring,
      Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by omega)]
  have hres : windowDiscrepancy H (H + J) K % P = P - e := by
    rw [hnegEmod] at hmod
    exact hmod.symm
  change windowDiscrepancy H (H + J) K % P = P - e ∧
    P - B < windowDiscrepancy H (H + J) K % P ∧
      windowDiscrepancy H (H + J) K % P < P
  refine ⟨hres, ?_, ?_⟩
  · rw [hres]
    omega
  · rw [hres]
    omega

#print axioms actualLcmTailDiff_shift_pos
#print axioms actualLcmTailOrbit_pos
#print axioms actualLcmTailOrbit_integralRepresentative_pos
#print axioms actualLcm_trueEndpointSurvivor_neg
#print axioms actualLcm_integral_forces_topEdgeResidue

end PowerTwoOddWindowAffine
end DiagonalFreshLossBridge
end Erdos257PeriodNoncollapse
