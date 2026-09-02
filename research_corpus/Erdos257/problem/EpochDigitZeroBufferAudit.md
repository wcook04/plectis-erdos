# Epoch digits do not exclude the zero-buffer seam

Write
\[
 w_n=\frac1{2^n-1},\qquad M(2,H)=\frac1{3(2^H-1)}.
\]
The exact two-packet obstruction
\[
 P(15,2)+P(15,1)=6M(2,15)=2w_{15}
\]
suggests retaining parity and then successively higher binary digits of an
anchored coefficient.  This note determines exactly what those digits see.
They detect the obstruction only when their depth grows with the recoding
height.  No fixed amount of (2)-adic coefficient data can exclude it.

## 1. The zero-buffer seam at a common height

Fix (r\geq 2), and let (H) be divisible by both (r) and (r-1).  Put
\[
 S_r(H)=\frac{2^H-1}{2^r-1},\qquad
 A_r(H)=3S_r(H).
\]
Thus (A_r(H)M(2,H)=w_r).  A coefficient (C) lies in the fatal
zero-buffer interval
\[
 2w_r\leq C M(2,H)<w_{r-1}                         \tag{1}
\]
if and only if
\[
 2A_r(H)\leq C<A_{r-1}(H).                         \tag{2}
\]
The number of integer coefficients in this half-open interval is exactly
\[
 \begin{aligned}
 T_{H,r}
 &=A_{r-1}(H)-2A_r(H)\\
 &=\frac{3(2^H-1)}{(2^{r-1}-1)(2^r-1)}.            \tag{3}
 \end{aligned}
\]
The last identity is the coefficient form of
\[
 w_{r-1}-2w_r=M(r-1,r).
\]
Thus the zero-buffer seam is not a single exceptional equality after LCM
lifting.  It is a full interval whose width grows exponentially like
(2^{H-2r}).

## 2. Every fixed (2)-adic residue occurs in the seam

The endpoints in (2) and the width in (3) are multiples of three.  Divide
the interval by three.  It contains
\[
 Q_{H,r}=\frac{2^H-1}{(2^{r-1}-1)(2^r-1)}          \tag{4}
\]
consecutive integers.  Since multiplication by three permutes the residue
classes modulo (2^k), if (Q_{H,r}\geq2^k), then the coefficients in
(2) that are divisible by three already realize every residue class modulo
(2^k).

For fixed (r) and (k), condition (Q_{H,r}\geq2^k) holds for all
sufficiently large multiples of (operatorname{lcm}(r,r-1)).  It remains
true if (H) is additionally required to be divisible by 15, as in the
rooted anchor-two genealogy.  Therefore:

> For every fixed number (k) of low coefficient bits, every possible
> (k)-bit state occurs inside a height-15-compatible zero-buffer seam.

This rules out parity, a bounded (2)-adic valuation, or any invariant
depending on a fixed coefficient suffix as the missing global exclusion.
The statement is stronger than exhibiting unrelated counterexamples: the
counterexamples remain in the anchor-two cone, have coefficient divisible
by three, and may be placed at common heights divisible by 15.

## 3. The root already contains the fatal suffix

The first exact root residual is
\[
 M(2,3)-w_5=1510M(2,15),
\]
where
\[
 1510=2^1+2^2+2^5+2^6+2^7+2^8+2^{10}.
\]
The isolated zero-buffer pair has coefficient
\[
 6=2^1+2^2.
\]
Consequently
\[
 1510\equiv6\pmod {32}.                            \tag{5}
\]
After lifting both coefficients from height 15 to any multiple (H) of
15, the lift factor is
\[
 \frac{2^H-1}{2^{15}-1}
 =1+2^{15}+\cdots+2^{H-15}\equiv1\pmod {2^{15}}.
\]
Hence the root residual and the lifted bad pair continue to have identical
five-bit suffixes.  The complete coefficient is safe only because of its
higher occupied blocks.  Any successful ownership rule must prove that
processing those blocks cannot strand the suffix (110_2); the suffix
itself provides no protection.

## 4. Exact digit transport is a borrow cocycle

The low digits do carry one exact law.  Consider a primitive packet
\[
 P(b,j)=2^jM(2,b)
\]
with front (r=2+b-j), and refine both (b) and (r) to a common height
(H).  Its incoming coefficient is
\[
 I=2^j\frac{2^H-1}{2^b-1}.
\]
After emitting (w_r), its residual coefficient is
\[
 B=I-3\frac{2^H-1}{2^r-1}.
\]
For every (k\leq\min(b,r)), both geometric lift factors are congruent to
one modulo (2^k).  Hence
\[
 \boxed{B\equiv2^j-3\pmod {2^k}.}                 \tag{6}
\]
More generally, while all emitted ranks are at least (k), each release
subtracts exactly three from the (k)-digit epoch state.

This is the literal binary borrow behind the residual clouds.  A single
occupied digit (2^j) is replaced, in the low window, by (2^j-3); for a
window below (j), the result is (-3), a string of ones ending in (01).
Thus the substitution that is strongly contractive in anchored load is
simultaneously expansive in suffix occupancy.  The two phenomena are not
independent.

Equation (6) is useful bookkeeping, but Section 2 shows why it cannot itself
be the exclusion law.  The fatal interval realizes every fixed residue.
Once an emitted rank falls below the observed window, its coefficient is no
longer congruent to three; the full geometric word
(3(1+2^r+2^{2r}+\cdots)) enters.  Retaining those words for all previous
ranks is precisely the moving support/phase state, rather than a bounded
epoch digit.

## 5. The seam is a corridor between two pulse clocks

There is a more rigid description of the moving high window.  For
(r\geq4), the two endpoints in (2) are
\[
 \begin{aligned}
 L_{H,r}&=6S_r(H)
   =6\sum_{q=0}^{H/r-1}2^{qr},\\
 U_{H,r}&=3S_{r-1}(H)
   =3\sum_{q=0}^{H/(r-1)-1}2^{q(r-1)}.             \tag{7}
 \end{aligned}
\]
There are no carries within either displayed sum.  In binary, the lower
clock is the block (110_2) repeated every (r) places, while the upper
clock is (11_2) repeated every (r-1) places.  Their difference is the
product-denominator width (3).

Put (J=H-r).  Direct comparison gives
\[
 6\,2^J<L_{H,r}<U_{H,r}<7\,2^J.                   \tag{8}
\]
The final inequality follows from
\[
 7\,2^J(2^{r-1}-1)-3(2^H-1)
 =2^H\left(\frac12-\frac7{2^r}\right)+3>0.
\]
Therefore every coefficient in the fatal corridor has leading
radix-(2^J) digit exactly six: its first visible block is (110_2).
In fact the common prefix is longer.  Put
\[
 s=H-2r+4.
\]
Then
\[
 \left\lfloor\frac{L_{H,r}}{2^s}\right\rfloor
 =\left\lfloor\frac{U_{H,r}-1}{2^s}\right\rfloor
 =3\,2^{r-3}.                                     \tag{9}
\]
Thus every dangerous coefficient starts with the (r-1)-bit word
\[
 \boxed{11\,0^{r-3}}.                              \tag{10}
\]
The proof is just the endpoint bounds after removing the common leading
(6\,2^{H-r}): the lower remainder is below (2^s), and so is the upper
remainder minus one.  The next endpoint pulses occur one position apart, so
this is the maximal common prefix.

Stripping that block gives an exact renormalisation:
\[
 C=6\,2^{H-r}+C_1
\]
lies in ([L_{H,r},U_{H,r})) if and only if
\[
 6S_r(H-r)\leq C_1<3S_{r-1}(H-r+1).               \tag{11}
\]
The lower clock retreats by (r) positions, while the upper clock retreats
by (r-1).  Their relative phase therefore slips by one position at every
renormalisation.  This is an exact version of the observed interaction
between an almost-full binary suffix and LCM/divisor pulses: a dangerous
state is a coefficient word trapped between two adjacent-period pulse
trains.

Equation (11) is not yet an exclusion theorem.  It identifies the smallest
non-scalar candidate state: the ancestry rewrite must transport where its
coefficient word sits in this slipping two-clock corridor.  Scalar load sees
only the leading (110_2); a fixed (2)-adic suffix sees only the opposite
end; neither records survival through the successive recuts in (9).

The descent does not terminate in an empty corridor.  The lower endpoint is
an exact impostor at every depth:
\[
 L_{H,r}-6\,2^{H-r}=L_{H-r,r}.                     \tag{12}
\]
Iterating (12) reaches (L_{r,r}=6).  For (r=15), this is not an
artificial anchored coefficient.  At every common height (H) divisible by
15,
\[
 L_{H,15}=6\frac{2^H-1}{2^{15}-1}
\]
is exactly the LCM lift of the actual first-wave root subcohort
(P(15,2)+P(15,1)).  Thus the corridor strip has a genuine root-ancestry
lineage all the way to the terminal word (110_2).

What the impostor lacks is completeness: the other five first-wave root
packets are still physically present.  At rank 15 an exact exhaustive audit
of all Boolean subsets of ranks (2,\ldots,14) finds no complete root tail
in the corridor, even though the isolated ancestry subcohort lies on its
lower boundary.  This finite fact is not a proof for all ranks.  It isolates
the remaining target-specific statement sharply:

> other root ancestry cannot be discharged in a Boolean prefix while
> stranding the periodic lower-clock subcohort inside the zero-buffer
> corridor.

The bare corridor arithmetic cannot prove that statement, because (12)
supplies exact ancestry-compatible counterstates at arbitrary LCM depth.

Nor does the almost-all-ones borrow suffix by itself provide hereditary
solvency.  The smallest clean counterexample is
\[
 Y=(2^5-3)M(2,15)=\frac{29}{98301}.
\]
This is exactly the suffix shape forced by (6), at the threshold
(5=15-2\cdot7+4) where its highest suffix bit reaches the rank-7 tax
scale.  Nevertheless the allowed Boolean atom (w_{12}), which uses neither
protected rank 7 nor 8, gives
\[
 0<Y-w_{12}=\frac{974}{19168695}
 <M(6,7)=\frac1{8001}.                             \tag{13}
\]
Thus a dense borrow suffix may initially cover the external tax and then
discharge almost all of that value at an unrelated rank.  The first-wave
solvency theorem for the coefficient 1504 is genuinely a whole-cohort
achievement statement; it cannot be inherited from the congruence
(2^j-3) alone.

## 6. The information is at the opposite end of the word

For fixed (r), the coefficients in (2) have size on the order of
(2^{H-r}), whereas the interval width in (3) has size on the order of
(2^{H-2r}).  Membership in the seam therefore constrains about (r) of
the most significant coefficient bits while leaving an arbitrarily long
low-bit suffix free as (H\to\infty).

The exact state that detects aggregate return is the moving quotient
\[
 q_{H,r}(C)=\left\lfloor\frac{C}{A_r(H)}\right\rfloor
\]
together with comparison of the remainder against
(T_{H,r}).  In the dangerous case (q_{H,r}(C)=2) and
\[
 0\leq C-2A_r(H)<T_{H,r}.                          \tag{14}
\]
This state is lossless, but it is an Archimedean moving-front state, not a
bounded (2)-adic invariant.  Equation (6) is precisely the coefficient
version of the fatal gap; calling it a new reduction would be circular.

The useful conclusion is narrower.  Higher epoch digits can be relevant
only if ownership transports a window whose depth grows with the current
LCM height and keeps it coupled to the unprocessed higher blocks.  A fixed
parity or finite-(2)-adic decoration cannot repair the transactional
release rule.

## 7. Reproduction

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/epoch_digit_zero_buffer_audit.py
```

The script verifies the exact interval formula, the root suffix identity,
and exhaustive residue coverage for representative common heights.  The
coverage theorem itself is the elementary consecutive-interval argument in
Section 2; the sweep is only a regression receipt.
