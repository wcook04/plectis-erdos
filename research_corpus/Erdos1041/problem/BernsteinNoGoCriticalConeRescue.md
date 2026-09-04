# Exact critical-cone rescue of the Bernstein quintic no-go

## 1. Scope

`BernsteinOriginSpokeCertificate.md` records an exact rational quintic for
which only one root is certified by the Bernstein-control test.  This note
tests that same polynomial against the independent critical-centred energy
row of `CriticalSpokePhaseMomentHybrid.md`.  The result is positive: the
Bernstein no-go is not a no-go for the combined selector.

This is an exact rescue of one adversarial row, not the universal
Bernstein-or-critical dichotomy.

## 2. The sharp quintic occupied cone

At a non-root critical point `c`, put

```text
mu = |P(c)|,
d_k = |a_k-c|,
p_i = d_i^(-2) / sum_k d_k^(-2),
S_i = (1-p_i)/p_i.
```

For the straight segment from `c` to `a_i`, the critical-spoke energy
majorant is

```text
|P(c+t(a_i-c))|/mu
 <= F_(5,S_i)(t)
 := (1-t)[1+t/2+(S_i/4)t^2]^2.                 (1)
```

If `S_i <= 3/2`, monotonicity in `S_i` and the exact factorization

```text
1-F_(5,3/2)(t)
 = t^3(9t^2+15t+40)/64 >= 0                  (2)
```

show that the whole segment lies in `{|P| <= mu}`.  The constant is sharp
for this row: the coefficient of `t^2` in `F_(5,S)(t)-1` is
`S/2-3/4`, so every `S>3/2` fails near `t=0`.  Equivalently,

```text
S_i <= 3/2  iff  p_i >= 2/5.                 (3)
```

Consequently, if the ordered reciprocal weights satisfy `p_2>=2/5`, both
nearest critical spokes are contained.

## 3. Exact rational witness and isolated critical point

Take `P(z)=prod_(j=1)^5 (z-a_j)` with the exact rational complex roots whose
decimal notation is

```text
a_1 =  0.9954764088478315  - 0.08383149424545093 i,
a_2 =  0.14881265879891825 + 0.9878541352756472  i,
a_3 = -0.6277869770917356  + 0.7771000652387186  i,
a_4 = -0.5684933442778939  - 0.8214720430493883  i,
a_5 =  0.26099542375571383 - 0.964304095593592   i.
```

The checker uses the rational centre

```text
c_0 = -0.21899631614693127 + 0.7322132764652212 i
```

and radius `rho=10^(-8)`.  Expanding `P'(c_0+w)=sum_(k=0)^4 A_k w^k`, exact
rational lower and upper square-root bounds prove on `|w|=rho` that

```text
|A_1| rho > |A_0| + sum_(k=2)^4 |A_k| rho^k. (4)
```

Rouche's theorem therefore gives exactly one critical point `c` in this
disc.  The same rational norm enclosures prove simultaneously that

```text
|P(c)| < 0.756771637475 < 1,                  (5)
```

that `a_3,a_2` are respectively the nearest and second-nearest roots
throughout the disc, and that for the second-nearest root

```text
S_2 < 1.423690707361 < 3/2.                  (6)
```

Since `p_1>=p_2`, (2) also certifies the nearest row.  Thus both straight
spokes from `c` to `a_3,a_2` lie in `{|P|<1}` except at their root endpoints,
where `P=0` anyway.  The sharp geometric-mean-scale two-nearest budget `(F)`
from `BarycentricEnvelope.md` gives

```text
|a_3-c|+|a_2-c| <= 2 |P(c)|^(1/5) < 2.       (7)
```

Their concatenation is therefore a target-valid connector for this exact
quintic.

## 4. A canonical zero-Bernstein-safe witness is also rescued

There is a stronger exact stress test.  Put `r=99999/100000` and take roots

```text
r,
r(-20+99i)/101,  r(-20-99i)/101,
r(-28+195i)/197, r(-28-195i)/197.             (8)
```

All five direction factors have modulus one, so every root has modulus `r`.
Exact Bernstein arithmetic finds a failed control at indices

```text
(j_1,j_2,j_3,j_4,j_5)=(3,1,1,1,1);            (9)
```

each corresponding value of `|B_j(a_i)|^2-1` is a strictly positive rational
number.  Thus this quintic has **zero** Bernstein-certified origin spokes.

Nevertheless the rational disc of radius `10^(-8)` about

```text
-0.17007015573494415 + 0.98440121712080436 i
```

contains exactly one critical point by the same Rouche argument.  Exact norm
enclosures give

```text
|P(c)| < 0.004772041898,
S_2(c) < 1.014981981961 < 3/2.                 (10)
```

The nearest roots are exactly the two upper-half-plane roots in (8).  Hence
the sharp energy row contains both critical spokes, and the geometric-mean
budget again gives a connector of length `<2`.  The conjugate critical point
gives the reflected certificate.

This zero-safe witness is substantially stronger evidence for
complementarity than the one-safe witness of section 3, while remaining an
exact individual rescue rather than a global selector theorem.

## 5. Pure-cone implication is false; full `J2` remains

The tempting global implication

```text
if fewer than two roots satisfy every Bernstein control |B_j(a)|<=1,
then some critical point c with |P(c)|<1 has ordered reciprocal weight
p_2(c)>=2/5                                   (BC5)
```

is **false**.  Source-current adversarial sweeps among rows with fewer than two
Bernstein-safe roots find `min_c S_2` as large as approximately `1.7241` in a
circle stream and `3.67125` in a near-regular angular stream, both beyond the
sharp pure-energy ceiling `3/2`.  These floating searches are falsifier
evidence, not an exact no-go theorem, but `(BC5)` must not be used as a proof
producer.

The live global producer is instead Bernstein-or-full-sharp-`J2`: if fewer
than two roots satisfy all Bernstein controls, find a critical point whose
two nearest rows obey the separately optimized phase-moment barrier (12)--(14)
of `CriticalSpokePhaseMomentHybrid.md`.  The already-proved finite
near-Fekete connector consumes the singular shell where a direct critical-row
selector may degenerate.  This full dichotomy remains unproved.

Thus the exact rational no-go proves genuine complementarity and shows that
one strong explicit Bernstein obstruction is consumed by the simplest sharp
critical cone.  It does not support a universal pure-cone implication.

## 6. Replay

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_bernstein_nogo_critical_cone_rescue.py
```

The replay is symbolic/rational apart from printed decimal summaries.  All
complex norms are enclosed by integer square-root bounds before comparison.
