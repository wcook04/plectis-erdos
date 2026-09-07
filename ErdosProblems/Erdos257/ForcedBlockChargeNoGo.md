# Forced-block charge: exact forms and the tautological boundary

This note audits the proposed final-skip inequality for the denominator-(21)
forced block.  It records an exact new dictionary and the precise point at
which the desired lower bound becomes equivalent to the conclusion itself.

## 1. Four exact forms of (J_L)

Let (D_L=A\cap[2,L]), and write

\[
 J_L=\sum_{L<n\le2L}2^{2L-n}\,\operatorname{supportCoeff}(D_L,n).
\]

For (q_D(M)=\sum_{d\in D} \lfloor2^M/(2^d-1)\rfloor), expanding the finite
geometric quotients gives

\[
 J_L=q_{D_L}(2L)-2^Lq_{D_L}(L).                         \tag{1}
\]

Equivalently, with the exact fractional mass

\[
 \rho_D(M)=\sum_{d\in D}\frac{2^{M\bmod d}}{2^d-1},
\]

the quotient-plus-fraction identity yields

\[
 J_L=2^L\rho_{D_L}(L)-\rho_{D_L}(2L).                  \tag{2}
\]

The divisor-incidence form is

\[
 J_L=\sum_{d\in D_L}
 \sum_{\lfloor L/d\rfloor<k\le\lfloor2L/d\rfloor}2^{2L-kd}. \tag{3}
\]

Finally, using the exact bridge in `ActualPrefixForcedBlockCharge.md`,

\[
 J_L=2^L(Q_L-1)+B_L+1-Q_{2L}.                          \tag{4}
\]

Equations (1)--(4) are identities, not estimates.  In particular, (2) is the
precise fraction-mass/tail form: (J_L) is the dyadic amplification of the
old-prefix fractional mass minus the later fractional mass.

## 2. The proposed lower bound is exactly the boundary conclusion

The desired inequality

\[
 J_L>2^L(Q_L-1)+B_L                                  \tag{5}
\]

is, by (4), exactly (Q_{2L}<1).  Since (Q_{2L}) is a natural number, (5)
is equivalent to (Q_{2L}=0), which is precisely the exclusion of a final
skip.  Thus no proof of (5) can be obtained from (1)--(3) alone: any such
proof would already be the missing global theorem in a different coordinate.

The final-skip hypothesis gives the opposite inequality (J_L\le
2^L(Q_L-1)+B_L), because it forces (Q_{2L}\ge1).  This is not a weakness in
the charge calculation; it is the exact boundary dichotomy.

## 3. Adversarial complementarity test

Complementarity is genuinely necessary for any one-sided estimate.  Take the
non-greedy Boolean prefix (D_L=\varnothing) at (L=10).  Then (J_L=0),
(Q_L=\lfloor2^{10}/21\rfloor=48), and
(B_L=780).  Hence

\[
 0\not>2^{10}(48-1)+780.
\]

Here (Q_{2L}>1), exactly as (4) predicts.  Any proposed proof that omits the
actual greedy residual inequalities is therefore false even for a finite
Boolean prefix.

For the actual greedy word, the exact audit through (L=384) found no final
skip: the sole nonnegative forced defect is (L=6), where
(Q_6=1), (B_6=3), (J_6=4), and (Q_{12}=0).  This is finite evidence that
(5) often holds on actual skips, but it is not a proof of a uniform exchange
inequality.

## 4. Surviving research statement

The only genuinely one-sided target is now clear: prove, from the greedy
complementarity condition at a skipped (L), that the old-prefix fractional
mass satisfies

\[
 2^L\rho_{D_L}(L)-\rho_{D_L}(2L)
 >2^L(Q_L-1)+B_L.
\]

By (4), this is exactly the zero-forced-defect theorem.  A local period, a
fractional-mass bound without the skipped-rank inequalities, or a generic
least-action assertion cannot supply it.  The missing ingredient must be a
genuinely global exchange principle that uses the actual residual at the
skipped rank and controls the amplified old-prefix mass.
