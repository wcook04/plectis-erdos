/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1041 collinear straight-chord package

This Mathlib-only statement isolates the geometric consumer of the collinear
root argument.  A quantitative collinear critical family for a complex
polynomial `p` at diameter `D` and level `M` records, for each index, one
critical point and two distinct roots of `p`, together with three numerical
fields: the two roots are at distance at most `D`, the product of the critical
value moduli is at most `M ^ Fintype.card ι`, and the modulus of `p` on the
straight segment joining the two roots is dominated by the modulus of `p` at the
paired critical point.

The three theorems below select one index from that data.  At the
Chebyshev-refined level `(D / 2) ^ n / 2 ^ (n - 2)` with `0 < D < 2` and
`n ≥ 2`, the selected chord joins two distinct roots of `p`, lies strictly
inside the open unit lemniscate, and has length below two.  The unrestricted
form keeps the level and the diameter bound.  The single-certificate consumer
does the same selection-free step for one prescribed pair of endpoints.

The critical-family fields are hypotheses.  No theorem here constructs such a
family from a polynomial, so the package does not solve Erdős Problem 1041.
-/

namespace Erdos249257.ExternalVerification1041CollinearChord

open Set
open Polynomial

/-- The affine segment from `a` to `b`, parametrised by the real unit interval. -/
def realSegment (a b : ℂ) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) * a + (t : ℂ) * b

/-- The certificate emitted by the collinear-root argument for one pair of
endpoints: one interior critical value dominates the modulus on the segment,
that critical value has modulus below one, and the endpoints are closer than
two. -/
structure CollinearPeakCertificate (f : ℂ → ℂ) (a b c : ℂ) : Prop where
  endpoint_distance_lt_two : dist a b < 2
  critical_value_lt_one : ‖f c‖ < 1
  segment_control : ∀ t ∈ Icc (0 : ℝ) 1, ‖f (realSegment a b t)‖ ≤ ‖f c‖

/-- Quantitative finite critical-gap data.  For a degree-`n` collinear
polynomial of root diameter `D`, the intended instantiation uses
`M = (D / 2) ^ n / 2 ^ (n - 2)` and `ι = Fin (n - 1)`. -/
structure CollinearScaleCriticalFamily
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) (D M : ℝ) where
  critical : ι → ℂ
  leftRoot : ι → ℂ
  rightRoot : ι → ℂ
  left_isRoot : ∀ i, p.eval (leftRoot i) = 0
  right_isRoot : ∀ i, p.eval (rightRoot i) = 0
  roots_ne : ∀ i, leftRoot i ≠ rightRoot i
  endpoint_distance_le : ∀ i, dist (leftRoot i) (rightRoot i) ≤ D
  critical_product_le : ∏ i, ‖p.eval (critical i)‖ ≤ M ^ Fintype.card ι
  segment_control : ∀ i t, t ∈ Icc (0 : ℝ) 1 →
    ‖p.eval (realSegment (leftRoot i) (rightRoot i) t)‖ ≤
      ‖p.eval (critical i)‖

/-- Strict Erdős-1041 collinear chord.  For `0 < D < 2` and `n ≥ 2` the level
`(D / 2) ^ n / 2 ^ (n - 2)` is strictly below one, so the selected chord joins
two distinct roots of `p` inside the open unit lemniscate and has length below
two. -/
theorem CollinearScaleCriticalFamily.exists_erdos1041_chord
    {n : ℕ} (hn : 2 ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) {D : ℝ} (hD : 0 < D) (hD2 : D < 2)
    (h : CollinearScaleCriticalFamily p D
      ((D / 2) ^ n / (2 : ℝ) ^ (n - 2))) :
    ∃ i : ι,
      p.eval (h.leftRoot i) = 0 ∧
      p.eval (h.rightRoot i) = 0 ∧
      h.leftRoot i ≠ h.rightRoot i ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
          ‖p.eval (realSegment (h.leftRoot i) (h.rightRoot i) t)‖ < 1) ∧
        dist (h.leftRoot i) (h.rightRoot i) < 2 := by
  sorry

/-- Quantitative diameter/level chord.  The selected chord preserves the exact
level `(D / 2) ^ n / 2 ^ (n - 2)` and the diameter budget `D`. -/
theorem CollinearScaleCriticalFamily.exists_diameter_chord
    {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℂ[X]) {D : ℝ} (hD : 0 < D)
    (h : CollinearScaleCriticalFamily p D
      ((D / 2) ^ n / (2 : ℝ) ^ (n - 2))) :
    ∃ i : ι,
      p.eval (h.leftRoot i) = 0 ∧
      p.eval (h.rightRoot i) = 0 ∧
      h.leftRoot i ≠ h.rightRoot i ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
          ‖p.eval (realSegment (h.leftRoot i) (h.rightRoot i) t)‖ ≤
            (D / 2) ^ n / (2 : ℝ) ^ (n - 2)) ∧
        dist (h.leftRoot i) (h.rightRoot i) ≤ D := by
  sorry

/-- Polynomial-facing single-certificate consumer: a collinear peak certificate
for `p` at `a, b, c` puts the whole segment from `a` to `b` strictly inside the
open unit lemniscate and keeps the endpoints closer than two. -/
theorem polynomial_straightSegment_solution_of_collinearPeak
    (p : ℂ[X]) {a b c : ℂ}
    (h : CollinearPeakCertificate p.eval a b c) :
    (∀ t ∈ Icc (0 : ℝ) 1, ‖p.eval (realSegment a b t)‖ < 1) ∧
      dist a b < 2 := by
  sorry

end Erdos249257.ExternalVerification1041CollinearChord
