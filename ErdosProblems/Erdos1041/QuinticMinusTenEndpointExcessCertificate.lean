import Mathlib

/-!
# Erdős 1041: algebra for the endpoints of the `μ = -10` phase arc

The analytic input is the support--oscillation lemma and the exact rational
interval/Sturm certificate replayed by the companion Python checker. This
module checks the signed endpoint level curve, terminal elimination,
transverse factorization, and final rational fan-in.
-/

namespace ErdosProblems.Erdos1041

private def endpointA (q t : ℝ) : ℝ :=
  q * (t ^ 5 - 10 * t ^ 3 + 5 * t) + 5 * t ^ 4 - 10 * t ^ 2 + 1

private def endpointB (q t : ℝ) : ℝ :=
  5 * q * t ^ 4 - 30 * q * t ^ 2 + 5 * q + 20 * t ^ 3 - 20 * t

private def endpointC (q t : ℝ) : ℝ :=
  10 * q * t ^ 3 - 30 * q * t + 30 * t ^ 2 - 10

private def endpointQ (q t b : ℝ) : ℝ :=
  endpointA q t * b ^ 2 + endpointB q t * b + endpointC q t

private def endpointD (q k t : ℝ) : ℝ :=
  k ^ 4 * q + k ^ 3 * q * t + 5 * k ^ 3
    + k ^ 2 * q * t ^ 2 - 10 * k ^ 2 * q + 5 * k ^ 2 * t
    + k * q * t ^ 3 - 10 * k * q * t + 5 * k * t ^ 2 - 10 * k
    + q * t ^ 4 - 10 * q * t ^ 2 + 5 * q + 5 * t ^ 3 - 10 * t

private def endpointS (q k t w : ℝ) : ℝ :=
  -endpointD q k t * w ^ 2 + endpointB q t * w + endpointC q t * (k - t)

/-- After `x=b(t+i)`, the endpoint ray condition `Im F+q Re F=0` is
quadratic in the radial variable `b`. -/
theorem quintic_minusTen_endpoint_level_curve_radial (q t b : ℝ) :
    q * (b ^ 2 * t ^ 5 - 10 * b ^ 2 * t ^ 3 + 5 * b ^ 2 * t
          + 5 * b * t ^ 4 - 30 * b * t ^ 2 + 5 * b
          + 10 * t ^ 3 - 30 * t)
      + (5 * b ^ 2 * t ^ 4 - 10 * b ^ 2 * t ^ 2 + b ^ 2
          + 20 * b * t ^ 3 - 20 * b * t + 30 * t ^ 2 - 10) =
        endpointQ q t b := by
  simp [endpointQ, endpointA, endpointB, endpointC]
  ring

/-- The chamber endpoint equation `8q²=1` and terminal direction equation
`A_q(k)=0` eliminate to the even degree-ten polynomial used by the exact
Sturm isolation. -/
theorem quintic_minusTen_endpoint_terminal_polynomial
    (q k : ℝ)
    (hq : 8 * q ^ 2 = 1)
    (hk : q * (k ^ 5 - 10 * k ^ 3 + 5 * k)
            + 5 * k ^ 4 - 10 * k ^ 2 + 1 = 0) :
    -k ^ 10 + 220 * k ^ 8 - 910 * k ^ 6 + 980 * k ^ 4
        - 185 * k ^ 2 + 8 = 0 := by
  calc
    -k ^ 10 + 220 * k ^ 8 - 910 * k ^ 6 + 980 * k ^ 4
          - 185 * k ^ 2 + 8 =
        (8 * q ^ 2 - 1) * (k ^ 5 - 10 * k ^ 3 + 5 * k) ^ 2
          - 8 *
            (q * (k ^ 5 - 10 * k ^ 3 + 5 * k)
              - (5 * k ^ 4 - 10 * k ^ 2 + 1)) *
            (q * (k ^ 5 - 10 * k ^ 3 + 5 * k)
              + (5 * k ^ 4 - 10 * k ^ 2 + 1)) := by ring
    _ = 0 := by
      have hq' : 8 * q ^ 2 - 1 = 0 := by linarith
      have hk' : q * (k ^ 5 - 10 * k ^ 3 + 5 * k)
            + (5 * k ^ 4 - 10 * k ^ 2 + 1) = 0 := by
        calc
          q * (k ^ 5 - 10 * k ^ 3 + 5 * k)
                + (5 * k ^ 4 - 10 * k ^ 2 + 1) =
              q * (k ^ 5 - 10 * k ^ 3 + 5 * k)
                + 5 * k ^ 4 - 10 * k ^ 2 + 1 := by ring
          _ = 0 := hk
      rw [hq', hk']
      ring

/-- The polynomial `D` is the divided difference of the terminal leading
coefficient. -/
theorem quintic_minusTen_endpoint_divided_difference (q k t : ℝ) :
    endpointA q t - endpointA q k = (t - k) * endpointD q k t := by
  simp [endpointA, endpointD]
  ring

/-- With `w=b(k-t)`, the apparently singular infinite tail becomes the
polynomial curve `S=0`. -/
theorem quintic_minusTen_endpoint_transverse_factor
    (q k t b : ℝ) (hk : endpointA q k = 0) :
    endpointS q k t (b * (k - t)) = (k - t) * endpointQ q t b := by
  simp [endpointS, endpointD, endpointQ, endpointA, endpointB, endpointC] at hk ⊢
  linear_combination b ^ 2 * (t - k) * hk

/-- Exact rational arithmetic at the endpoint support--oscillation fan-in. -/
theorem quintic_minusTen_endpoint_excess_rational_fanin :
    ((7 : ℚ) / 20 - 1 / 4)
          + (9 / 10) * (11 / 40 - 2 / 5) = -1 / 80 ∧
      (-1 : ℚ) / 80 < 0 := by
  norm_num

end ErdosProblems.Erdos1041
