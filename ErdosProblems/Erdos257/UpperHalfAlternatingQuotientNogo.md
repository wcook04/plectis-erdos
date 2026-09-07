# Alternating quotient and divisor-pulse limits in the upper-half cell

## Result

Let $M_n=2^n-1$.  In the notation of
`Fixed465BackwardPowerDescent.md`, put $q=m-p$ and

\[
 \kappa=\left\lfloor\frac{M_p-1}{2^q+1}\right\rfloor .
\]

This note gives the exact alternating binary expansion of $\kappa$.  In the
first upper-half cell, $m/2<p<2m/3$, it also rewrites the fatal inequality as

\[
 2^hM_q-1<\frac{465P}{R}<2^hM_q,
 \qquad h=p-q=2p-m.                                  \tag{1}
\]

Thus multiplication of the actual pre-selection residual $r=R/(465P)$ by
$M_q$ gives

\[
 2^{-h}<M_qr<2^{-h}(1+r).                            \tag{2}
\]

The quotient-remainder expansion of $M_q/M_d$ splits the left side of (2)
into an integer pulse and a fractional residue for every earlier selected rank
$d$.  Selected ranks dividing $q$ contribute only to the integer pulse.
Consequently (2) does not force positive selected-divisor mass at ranks
dividing $q$.

This is not only a formal limitation.  The ordinary greedy orbit from
$81/465$ has a reachable first-cell unsafe skip with no selected divisor of
$q$ before the last selection.  Its two Euclidean representatives are not
earlier orbit numerators.  The example disproves any source-independent orbit
closure or divisor-mass conclusion obtained solely from the first-cell
Mersenne identity.  It does not disprove a further statement specific to the
source $1/465$.

## 1. The quotient in every upper-half cell

Write

\[
 p=aq+s,
 \qquad a=\left\lfloor\frac pq\right\rfloor,
 \qquad 0\leq s<q,
\]

and define the alternating binary integer

\[
 Q_{p,q}=\sum_{j=1}^{a}(-1)^{j-1}2^{p-jq}.           \tag{3}
\]

Telescoping gives

\[
 (2^q+1)Q_{p,q}=2^p+(-1)^{a-1}2^s.                 \tag{4}
\]

Since $M_p-1=2^p-2$, Euclidean division in (4) yields

\[
 \boxed{
 \kappa=
 \begin{cases}
 Q_{p,q},&a\text{ is even and }s>0,\\
 Q_{p,q}-1,&a\text{ is odd, or }s=0.
 \end{cases}}                                      \tag{5}
\]

The corresponding remainder modulo $2^q+1$ is

\[
 \boxed{
 \rho=
 \begin{cases}
 2^s-2,&a\text{ is even and }s>0,\\
 2^q,&a\text{ is even and }s=0,\\
 2^q-2^s-1,&a\text{ is odd}.
 \end{cases}}                                      \tag{6}
\]

Each displayed value satisfies $0\leq\rho<2^q+1$, so (5) is the floor,
not an asymptotic expansion.

In the first cell $q<p<2q$, one has $a=1$ and $s=p-q=h$.  Equations
(5) and (6) reduce to

\[
 \kappa=M_h,
 \qquad
 M_p-\kappa=2^hM_q.                                 \tag{7}
\]

If $E=M_pR-465P$, the forced cell
$\kappa<E/R<\kappa+1$ is therefore equivalent to (1).  The two positive
representatives are

\[
 J=2^hM_qR-465P,
 \qquad
 C=465P-(2^hM_q-1)R,
 \qquad 0<J,C<R.                                    \tag{8}
\]

Dividing the inequalities $0<J<R$ by $465P$ proves (2).  Equivalently,
$2^hM_qr-1$ is positive and smaller than $r$.  This is an exact
renormalisation in the integer-coefficient lattice; (8) alone does not place
either representative on the coefficient-one prefix orbit.

## 2. Exact divisor-pulse split

Let $F$ be the selected support before $p$.  More generally, for a source
$u/v$, write

\[
 r=\frac uv-\sum_{d\in F}\frac1{M_d}.
\]

For each $d\in F$, put $q=b_dd+t_d$ with $0\leq t_d<d$.  Direct
division of $2^q-1$ by $2^d-1$ gives

\[
 \boxed{
 \frac{M_q}{M_d}
 =2^{t_d}\sum_{j=0}^{b_d-1}2^{jd}
  +\frac{M_{t_d}}{M_d}.}                            \tag{9}
\]

The sum is empty if $b_d=0$.  Define

\[
 I_q(F)=\sum_{d\in F}2^{t_d}\sum_{j=0}^{b_d-1}2^{jd},
 \qquad
 \Phi_q(F)=\sum_{d\in F}\frac{M_{t_d}}{M_d}.       \tag{10}
\]

Multiplication of the actual residual now has the exact form

\[
 \boxed{M_qr=\frac{uM_q}{v}-I_q(F)-\Phi_q(F).}       \tag{11}
\]

When $d\mid q$, $t_d=0$, so the term indexed by $d$ contributes an
integer to $I_q(F)$ and zero to $\Phi_q(F)$.  The first-cell fatal
condition (2) constrains the value in (11), but its fractional phase is
insensitive to the amount contributed by selected divisors of $q$.  No
positive lower bound for that divisor mass follows from (2).

## 3. A reachable failure of the proposed closure

Run ordinary greedy subtraction from

\[
 r_0=\frac{81}{465}=\frac{27}{155}.
\]

Ranks $1$ and $2$ are skipped, and rank $p=3$ is selected.  The
post-selection residual is

\[
 r_3=\frac{81}{465}-\frac17
     =\frac{102}{465\cdot7}
     =\frac{34}{1085}.                              \tag{12}
\]

Rank $4$ is skipped.  At $m=5$,

\[
 \frac1{2^5}<\frac{34}{1085}<\frac1{M_5},           \tag{13}
\]

so rank $5$ is dyadically unsafe.  Here

\[
 q=2,\qquad h=1,\qquad \kappa=1,\qquad P=1,\qquad
 R=81,\qquad E=102.
\]

The representatives in (8) are

\[
 J=21,qquad C=60.                                  \tag{14}
\]

The only earlier prefix numerator is $81$; neither $21$ nor $60$ is
on the earlier orbit.  Moreover $F=\varnothing$ before the selection at
$p=3$.  In particular, the selected-divisor mass at ranks dividing $q=2$
is zero, while (2) holds:

\[
 \frac12< M_2\frac{81}{465}
          =\frac{81}{155}
 <\frac12\left(1+\frac{81}{465}\right).             \tag{15}
\]

This reachable orbit proves that the alternating quotient, the
dyadic--Mersenne factorisation (7), and the pulse identity (11) do not by
themselves give orbit closure.

## 4. What remains special about $1/465$

For the source $1/465$, every prefix numerator satisfies

\[
 R\equiv P\pmod{465}.                               \tag{16}
\]

Suppose an earlier prefix has product $Q$, numerator $U$, and
$P=QD$.  Its numerator rescaled to denominator $465P$ is $UD$, and
$UD\equiv P\pmod{465}$.  Hence (8) gives two necessary conditions for
same-denominator re-entry:

\[
 \boxed{
 J=UD\Longrightarrow 465\mid(c-1)P,
 \qquad
 C=UD\Longrightarrow 465\mid cP,}
 \quad c=2^hM_q.                                    \tag{17}
\]

These congruences can exclude isolated early cells.  They do not settle the
late $1/465$ orbit.  The actual greedy support contains ranks $14$, $24$,
and $25$; their Mersenne factors make $465=3\cdot5\cdot31$ divide $P$
from rank $25$ onward.  Both conditions in (17) are then automatic.

The exact unresolved statement is therefore source-specific reachability
beyond the quotient and divisor-pulse identities.  A proof must use more of
the selected-support history than the residue class of $P$ or the terms
with indices dividing $q$.

## 5. Finite audit

The companion program checks (3)--(6) for all $1\leq q<p\leq160$, verifies
(9) on a finite grid, and performs the greedy calculation (12)--(15) with
exact rational arithmetic.  These checks support only the stated finite
audit; the identities above follow from the displayed algebra.

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/upper_half_alternating_quotient_nogo.py
```
