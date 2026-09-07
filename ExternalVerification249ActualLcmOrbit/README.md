# Erdős #249: exact actual-LCM orbit frontier

Let

\[
H_a=\operatorname{lcm}(1,\ldots,2^a),\qquad
R_a=\operatorname{totientTail}(2H_a)-\operatorname{totientTail}(H_a).
\]

This package proves two exact facts.  First, `R_a` is an integer translate of

\[
2^{H_a}(2^{H_a}-1)
  \sum_{n\ge1}\frac{\varphi(n)}{2^n}.
\]

Second, the binary totient series is irrational if and only if `R_a` is
non-integral for cofinally many exponents `a`.

## Mathematical position

This is a principal exact reformulation, not another quantitative sufficient
condition.  It is distinct from the canonical-Mersenne residue formulation
and the full-depth period-multiple formulation because it uses the actual LCM
diagonal and asks only non-integrality of its real tail orbit.  All three are
equivalent coordinates for the same open target; none proves its own missing
cofinal condition.

The stronger actual-LCM separation supply requires a fixed `1/32` margin plus
an approximation error.  It implies this non-integrality condition but is not
equivalent to it and is intentionally not substituted for the sharp frontier
here.

`Challenge.lean` imports only Mathlib and gives literal definitions.
`Solution.lean` transports the exact source identity and equivalence from
`TotientActualLcmOrbitSeparation.lean` and
`TotientActualLcmOrbitNonintegrality.lean`.  The negative configuration adds
an extra `True` hypothesis to the equivalence and must be rejected.

The positive configuration permits exactly `propext`, `Quot.sound`, and
`Classical.choice`, and enables NanoDa.  Supported Comparator replay, public
pinning, deliberate-negative rejection, and Palomar review remain separate
mechanical steps.
