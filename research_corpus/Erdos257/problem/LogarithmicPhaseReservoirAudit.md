# A logarithmic phase/reservoir potential

Status: exact deductions and exact finite computations, 2026-08-20.  The
candidate inequality below is not proved at all depths, and the perturbed
target from `FirstFailureGreedyBridge.md` shows that it is not sufficient by
itself to prove nonnegativity of the endpoint energy.

## 1. The two quantities which the seam couples

Retain the actual greedy orbit for `1/21`.  Immediately before the decision
at a skipped rank `m`, put

\[
 Y_m=2^m r_{m-1},\qquad
 \beta_m=\frac{2^m}{2^m-1},\qquad
 \Delta_m=\beta_m-Y_m>0.
 \tag{1}
\]

Thus `Delta_m/2^m` is the exact amount by which the rank-`m` coin is
unaffordable.  Let

\[
 F_N=P_N+4-2Q_N
\]

be the endpoint-compensated reservoir from
`DelayedDoublingBorrowCocycleAudit.md`.

If the greedy block beginning at `m` is `0 1^k`, the seam theorem in
`FirstFailureGreedyBridge.md` gives

\[
 2^m\sum_{j=1}^k\frac1{2^{m+j}-1}\leq Y_m<\beta_m.
 \tag{2}
\]

Consequently

\[
 0<\Delta_m\leq
 2^m\left(\frac1{2^m-1}
   -\sum_{j=1}^k\frac1{2^{m+j}-1}\right).
 \tag{3}
\]

Using `1/(2^n-1)>2^-n` in the sum and
`2^m/(2^m-1)<1+2^(1-m)` gives the elementary bound

\[
 \Delta_m<2^{-k}+2^{1-m}.
 \tag{4}
\]

For `k<=m-1`, this is less than `2^(1-k)`.  A long selected suffix therefore
requires exponentially fine alignment with the skipped-coin boundary.  On
the other hand, replacing `1 0^k` by `0 1^k` loses exactly `k+1` units of
`F` at horizon `m+k`.  This makes

\[
 \mathcal L_m=F_{m-1}+\log_2\Delta_m
 \tag{5}
\]

the literal joint coordinate suggested by the repeated wall: `F` measures
discrete binary capacity, while `Delta` retains the complete rational
endpoint/divisor phase.

## 2. Exact finite audit

Directed dyadic interval arithmetic through rank `20000` certifies, at every
skipped rank in that range,

\[
 \boxed{\Delta_m\geq2^{-F_{m-1}-2}.}
 \tag{6}
\]

The exponent `2` cannot be replaced by `1` in this finite range.  The sharp
row is `m=56`, where

\[
 F_{55}=4,qquad
 \Delta_{56}\approx0.03072271026758,qquad
 -\log_2\Delta_{56}\approx5.0245506978.
\]

The greedy block there is `0 1^5`.  Thus the sharp row is simultaneously a
deep suffix seam and a small-reservoir row; this is not a comparison of two
unrelated statistics.  The computation is finite and does not establish
(6) for arbitrary `m`.

## 3. Why the logarithmic bound does not close the proof

The same-cylinder target

\[
 x^-=\frac1{21}-\frac1{3\,2^{63}}
\]

is a decisive adversarial test.  Its support agrees with the `1/21` support
through rank `60`, where `F_60=5`.  At rank `61` it skips and then selects
twice.  Exact rational arithmetic gives

\[
 \Delta^-_{61}\approx0.0664600618959,qquad
 -\log_2\Delta^-_{61}\approx3.91137.
\]

It therefore satisfies a much stronger inequality than (6), yet its energy
states at ranks `60,61,62,63` are `5,3,0,-1`.  The logarithmic phase bound
alone cannot exclude a first failure.

The sufficient statement must also retain the energy of the protective
counterfactual.  If a common prefix is followed either by `1 0^k` or by
`0 1^k`, write `F_alt` for the endpoint energy of the first word.  The second
word has energy `F_alt-(k+1)`.  Hence the exact target-specific exclusion
still needed is

\[
 F_{\rm alt}<k+1
 \quad\Longrightarrow\quad
 Y_m\text{ does not lie in the seam interval (2)}.
 \tag{7}
\]

For `x^-` at `m=61,k=2`, the protective word is the actual `1/21` block
`100`, with `F_alt=2<3`; the perturbed phase nevertheless enters the seam.
The exact `1/21` phase lies above the rank-`61` take threshold.  Thus (7),
not a generic lower bound on `Delta`, is the surviving mathematical law.

The value of (5) is diagnostic: it unifies suffix depth and divisor phase and
identifies the sharp finite alignment.  Its failure to imply (7) prevents it
from being promoted as a solution.

## 4. Reproduction

`scripts/logarithmic_phase_reservoir_audit.py` certifies (6) by maintaining
directed dyadic bounds for the real greedy residual.  At a skip, the upper
residual bound gives a rigorous lower bound for `Delta`; all logarithmic
comparisons are then cross-multiplied as integers.  A separate exact
`Fraction` calculation reproduces the rank-`56` row and the `x^-` block.
