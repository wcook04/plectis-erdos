# Erdős 1041: the phase-direction Sturm bound — `25 E_phiphi = E + K`, the total-variation crux, and endpoint domination on every allowed arc

Date: 2026-08-30.  Origin: wave-2 opus phase-convexity agent (identity
derived and 511-point verified, zero violations), main-loop review of
the proof chain.  Checker: `scripts/check_erdos1041_phi_convexity_sturm.py`.
Consumes `QuinticChamberWallReduction.md` (the `mu`-direction theorem
and its §4 locally uniform tail bounds, which supply the one imported
step here) and the `mu = -10` certificates.  Notation as there:
`F = F_mu`, arms `x_pm(s)` of `F(x) = e^{-i phi} s`, pair excess
`mathcal E(mu, phi)`.

## 1. The theorem

Let `Phi := (F/F')' = 1 - F F''/F'^2` and `omega := F/F'`.

> **Theorem (phase Sturm bound).**  For every fixed `mu != -10` and
> every `phi` in the (open) allowed arc:
>
> ```text
> (I)   25 (d^2/d phi^2) mathcal E = mathcal E + K,
>       K = sum_a int_{Gamma_a} (25|Phi|^2 - 1) |dx|;
> (II)  5 sigma_a + e_a >= 0 per arm, where
>       sigma_a = int_{Gamma_a} (|Phi| - 1/5) |dx|;
> (III) hence  (d^2/d phi^2) mathcal E + mathcal E / 25 >= 0
>       on every allowed arc, unconditionally;
> (IV)  since every allowed arc has length <= pi < 5 pi (the comparison
>       length for the constant 1/25), the Sturm comparison gives, on
>       an arc [phi_lo, phi_hi] of length D,
>
>       mathcal E(phi) <= [ sin((phi_hi - phi)/5) mathcal E(phi_lo)
>                         + sin((phi - phi_lo)/5) mathcal E(phi_hi) ]
>                         / sin(D/5),
>
>       whose weights sum to cos((a-b)/2)/cos((a+b)/2) >= 1
>       (a, b the two scaled offsets).  Consequently, whenever both
>       endpoint values are <= 0, mathcal E <= max of the endpoint
>       values on the WHOLE arc.
> ```

Proof ingredients (checker-replayed):

- **Closed forms.**  `5 Phi = 1 + N_3 / C_mu^2` with
  `N_3 = -30 mu x^3 - 30(mu-10) x^2 + 80(mu+10) x + 6(mu+10)^2` — the
  `x^2`-pole cancels, so `Phi`'s only poles are the FOREIGN critical
  points, the same objects that cut the chamber; `Phi(0) = 1/2`;
  `Phi - 1/5 = -6mu/(25 x^3) + O(x^-4)`.  And
  `5 F/F' = (1+x) + R`, `R = (3 mu x - 2(mu+10))/C_mu`, `R(0) = -1`,
  `R -> 0` at infinity.
- **(II), the crux, is elementary**: `d omega/ds = Phi x'`, so
  `5 int |Phi| |dx| = 5 TV(omega) >= 5 |omega(S)| -> |1 + x(S)| + o(1)`
  by the second closed form, while `int |dx| = L(S)`; subtract.
- **(I)** is the second phase-derivative of the arm system computed
  through `d_phi x = -i (e^{-i phi} s)/F'(x)`, with the exchange of
  `d^2/d phi^2` and `lim_S` supplied by the locally uniform tail bounds
  of `QuinticChamberWallReduction.md` §4 (the analogous bound for the
  `|Phi|^2` integrand was verified symbolically by the origin agent).
  This is the ONE imported analytic step.
- **(III)**: `25|Phi|^2 - 1 = (5|Phi|-1)^2 + 2(5|Phi|-1)`, so
  `K = 25 sum_a I_a + 10 sum_a sigma_a` with `I_a >= 0`, and (II) gives
  `10 sum sigma_a >= -2 mathcal E`.  Note the integrand `25|Phi|^2 - 1`
  is NOT pointwise nonnegative (measured negative somewhere on 621 of
  680 arcs) — only the integrated budget is signed; and the comparison
  constant `1/25` beats every arc length by a factor 15, which is the
  slack that makes (IV) unconditional.

Verification battery (origin agent): the identity (I) matches 5-point
finite differences at 65 `(mu, phi)` points to relative `1.3e-5`, with
the residual PROVEN to be the `O(S^{-3/5})` quadrature truncation
(`1.4e-5 -> 2.1e-9` as `S: 1e9 -> 1e15`); (II) and (IV) hold at all
511 sweep points (min crux slack `+7.3e-4`, min Sturm slack `+1.1e-6`);
instrument anchor `mathcal E(50+30 sqrt3, -pi/2) = -0.1694610448` vs
corpus `-0.1694610452`.

## 2. Consequences

1. **(EX-W) ⟹ (EX-U), with no `mu = -10` excision in the phase
   direction.**  Together with `QuinticChamberWallReduction.md`'s
   `mu`-direction theorem, the whole (EX-U) obligation is now EXACTLY
   the wall inequality: if `mathcal E <= 0` at every arc-endpoint
   (wall) point, then `mathcal E <= 0` on every arc interior, hence on
   the chamber.
2. **A second, independent closure of the `mu = -10` arc.**  The landed
   endpoint certificates (`mathcal E(-10, +-phi_0) < -1/80`) plus (IV)
   give `mathcal E(-10, phi) < -1/80` on the WHOLE arc — structurally
   independent of, and 1.25x sharper than, the same-day interval
   certificate `QuinticMinusTenFullArcExcessCertificate.md`
   (`< -1/100` over 64 phase anchors).  (EX-10) is therefore closed
   twice over, conditional only on the §1 interchange applying at the
   `-10` limit — which the origin agent verified numerically to `8e-10`
   (Richardson in `mu` against the direct triple-hub pair at 5 phases),
   with the certificate route needing no such step.
3. The interchange data also corrects one figure in
   `QuinticChamberWallReduction.md` §7: the chamber-side real-approach
   limit at `phi = 0` is `-0.06876` (two independent computations), not
   the `-0.0694` quoted from the quick main-loop probe.

## 3. Claim boundary

(I)–(IV) are ordinary proved mathematics modulo the single imported
exchange step named above; the checker replays the closed forms
symbolically and the crux/Sturm inequalities numerically.  Nothing here
proves (EX-W) itself, the real-scale transfer, degree five, or the
parent.  The `-10` consequence inherits the interchange caveat as
stated; the interval certificate route is unconditional.
