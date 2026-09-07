# All-ones anchor-two packets: parity split and the (H=11) hole

Put
\[
 w_n=\frac1{2^n-1},\qquad M(2,H)=\frac1{3(2^H-1)},
\]
and consider
\[
 X_{H,k}=(2^k-1)M(2,H),\qquad 1\leq k\leq H.
\]
The all-ones coefficient has a clean parity decomposition, but that
decomposition does not give a closed Boolean carry grammar.  The first
structurally interesting even block,
\(X_{11,10}=341w_{11}), falls into an exact finite hole after the forced
atoms (w_3,w_6).  Hence it has no Boolean Mersenne representation at all.

## 1. Exact parity and order-three decompositions

Since (2^k-1) is divisible by three exactly when (k) is even,
\[
 X_{H,k}=
 \begin{cases}
 \displaystyle \frac{2^k-1}{3},w_H,&k\text{ even},\\[2mm]
 \displaystyle \frac{2^k-2}{3},w_H+M(2,H),&k\text{ odd}.
 \end{cases}                                      \tag{1}
\]
The multiplicities themselves have alternating binary support:
\[
 \frac{2^{2m}-1}{3}=\sum_{i=0}^{m-1}2^{2i},
 \qquad
 \frac{2^{2m+1}-2}{3}=\sum_{i=0}^{m-1}2^{2i+1}.   \tag{2}
\]
Thus even (k) gives power blocks at even exponents.  Odd (k) gives
power blocks at odd exponents plus one exact (M(2,H)) bank.

There is a second clock: (7\mid2^k-1) exactly when (3\mid k), because
the order of two modulo seven is three.  Hence the natural coefficient
classes are indexed modulo six.  This is useful bookkeeping, but neither
clock is a carry invariant.

For example, the odd bank can be spent immediately.  At ((H,k)=(4,3)),
\[
 \begin{aligned}
 X_{4,3}
 &=2w_4+M(2,4)\\
 &=w_3+M(2,4)-M(3,4)\\
 &=w_3+12M(6,4).                                  \tag{3}
 \end{aligned}
\]
The last line is positive because lifting the first coordinates to six
gives (M(2,4)=21M(6,4)) and (M(3,4)=9M(6,4)).
Thus an odd coefficient permits a labelled bank to be retained, but parity
does not force that bank to remain hereditary under a legal positive recut.

## 2. The diagonal family

Set (H=k+1).  Then
\[
 X_{H,H-1}
 =\frac{2^{H-1}-1}{3(2^H-1)}
 =\frac16-\frac{w_H}{6}.                           \tag{4}
\]
For every (H\geq5), the first Boolean decisions are forced:

* (w_3) is selected;
* (w_4,w_5) are skipped;
* (w_6) is selected.

Indeed (X_{H,H-1}\geq w_3) for (H\geq3).  After subtracting (w_3),
the residual is below (w_5), and it is at least (w_6) exactly when
(w_H\leq1/21), which holds for (H\geq5).

After these decisions the residual is
\[
 R_H=\frac1{126}-\frac{w_H}{6}.                   \tag{5}
\]
Two adjacent thresholds isolate a single height:
\[
 \begin{aligned}
 R_H>\frac2{255}quad&\Longleftrightarrow\quad H\geq11,\\
 R_H<w_7=\frac1{127}quad&\Longleftrightarrow\quad H\leq11.
 \end{aligned}                                    \tag{6}
\]
The equivalences follow directly from
\[
 \frac1{126}-\frac2{255}=\frac1{10710},
 \qquad
 \frac1{126}-\frac1{127}=\frac1{16002},
\]
and the inequalities (w_H<1/1785) and (w_H>1/2667), respectively.
Among powers of two these thresholds meet only at (H=11).

## 3. A rigorous finite obstruction at (H=11,k=10)

At the exceptional height,
\[
 X_{11,10}=\frac{341}{2047}=341w_{11},
 \qquad
 341=1+4+4^2+4^3+4^4.                             \tag{7}
\]
After the forced atoms (w_3,w_6),
\[
 R_{11}=\frac{1013}{128961}.                       \tag{8}
\]
Exact comparison gives
\[
 R_{11}-\frac2{255}=\frac{131}{10961685}>0,
 \qquad
 w_7-R_{11}=\frac{310}{16378047}>0.               \tag{9}
\]
On the other hand,
\[
 \sum_{n\geq8}w_n<\frac2{255}.                    \tag{10}
\]
To prove (10), use
\((1-2^{-n})^{-1}<(1-2^{-8})^{-1}) for (n\geq8)
and sum the dyadic tail.

The Mersenne weights are strictly superincreasing:
\[
 w_n>\sum_{m>n}w_m.
\]
Indeed the same estimate used in (10) gives
\[
 \sum_{m>n}w_m<\frac2{2^{n+1}-1}<\frac1{2^n-1}=w_n.
\]
Therefore every Boolean representation is lexicographically forced.  At
rank seven, (9) says that (w_7) is too large, while (9)--(10) say that the
entire permitted tail is too small.  Consequently
\[
 \boxed{X_{11,10}\text{ is not a Boolean subsum of the }w_n.} \tag{11}
\]
This is not a failed greedy heuristic or a depth-limited computation.  It is
a finite interval obstruction.

The obstruction also kills a tempting batch rule: a coefficient supported
at the even exponents (0,2,4,6,8) need not admit a closed positive Boolean
carry grammar, even though every block separately has the standard cylinder
tax identity.

## 4. Boundary of the result

There are trivial infinite Boolean subfamilies:
\[
 X_{H,2}=w_H,
 \qquad
 X_{H,H}=w_2.
\]
The theorem above shows that the parity-(0) multiplicity class as a whole
is not Booleanizable.  Equation (3) shows that the parity-(1) bank is an
ownership choice, not an invariant.  No nontrivial infinite closed carry
grammar follows from the mod-six class alone.

## 5. Reproduction

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/all_ones_anchor_two_family.py
```

The script verifies (1)--(10), the finite forced-decision trace, and the
positive bank-consuming identity (3) with exact rational arithmetic.
