# Minimal-degree no-go for fixed-nearest-pair CE--GM

## Exact theorem

There is a monic quartic `g`, all of whose roots lie in the open unit disc,
such that its unique least-critical-value point has a unique pair of nearest
roots, but those two roots lie in different components of
`{|g|<=Gcrit(g)}`.  Consequently no path of any shape joins that prescribed
pair at the geometric-mean critical level.  In particular, fixed-pair CE--GM
is false.

Degree four is minimal: the quadratic case is immediate, while
`CubicCriticalHub.md` proves that the two nearest normalized cubic roots have
safe spokes from the least critical point at level `mu<=Gcrit`.

This is stronger and cleaner than merely exhibiting a failed stationary hub:
it refutes the entire fixed-pair minimax problem and leaves only joint
pair-and-hub selection alive.

## Quartic and critical values

Before unit-disc rescaling, put

```text
F(z)=z^4-(1321/5000+33i/125)z^2
        -(33/12500+1183i/12500)z-16/25-9i/50.               (1)
```

Its derivative factors exactly as

```text
F'(z)=4(z-c1)(z-c2)(z-c*),
c1=11/25+i/5,   c2=-7/20-i/10,   c*=-9/100-i/10.            (2)
```

Writing `Vj=|F(cj)|^2`,

```text
V1 = 1108755728681/2441406250000,
V2 = 7315188509201/16000000000000,
V* = 4459277974823361/10000000000000000.                    (3)
```

Both `V1-V*` and `V2-V*` are strictly positive, so `c*` is the unique least
critical point.  With `T=27/40`, exact rational inequalities give

```text
V* < V1 < T^2 < V2,
T^6-V1 V2 V* > 0.                                           (4)
```

Thus `Gcrit(F)<T<|F(c2)|`.

## Exact root isolation and selector

Rouché estimates on the four radius-`1/1000` discs centred at

```text
qL=-122/125-53i/500,       qB=-1/200-213i/250,
qR=493/500+163i/1000,      qT=-3/500+159i/200               (5)
```

have respective positive margins

```text
73095707/200000000000,       145462253/62500000000,
707606309/500000000000,      718138961/500000000000.         (6)
```

The discs are disjoint, hence contain exactly one root each and exhaust the
quartic.  The exact distance intervals from `c*` are

```text
root B < .758,   root L < .888,   root T > .897,   root R > 1.106.  (7)
```

So the prescribed nearest pair is uniquely `(B,L)`.

## A strict lemniscate barrier

Let

```text
m=-11/10-i/4,              r0=3/4.                          (8)
```

The whole L root disc is inside `D(m,r0)` and the other three are outside its
closure.  On the boundary, use

```text
z(t)=m+(3/4)(1+it)/(1-it).
```

Exact expansion gives

```text
(1+t^2)^4 (|F(z(t))|^2-T^2)=P(t)/10^11,                    (9)
```

where

```text
P(t)=10874172360773t^8-10022578403256t^7
    +11403058106654t^6-4349728276488t^5
    +2240976658314t^4-335445488208t^3
    +129719679758t^2-24307214976t+1427842325.
```

For `t<=0`, the alternating coefficients make every term positive.  For
`t>=0`, transform by `s=t/(1+t)` and subdivide its degree-eight Bernstein form
at `1/8,1/4,1/2`.  The minimum controls on the four cells are

```text
14036359191955/458752,
69526329128125/524288,
3649093538125/2048,
77478869257/2,                                                (10)
```

all positive.  Hence `|F|>T` on the complete circle.  Every path from L to B
crosses this circle, so no such path lies in `{|F|<=Gcrit(F)}`.

The last critical level `|F(c2)|` is exactly the merge height for those two
components; the counterexample therefore also identifies the surviving
critical-contact obstruction rather than only separating the roots.

## Unit-disc form

Define the monic quartic

```text
g(z)=F(2z)/16
    =z^4-(1321/20000+33i/500)z^2
       -(33/100000+1183i/100000)z-1/25-9i/800.              (11)
```

The root discs show every root of `F` has modulus below `23/20`; therefore
every root of `g` has modulus below `23/40<1`.  All selector, component, and
level relations scale exactly.  This proves the stated no-go inside the open
unit disc.

## Correct surviving producer and consumer

For distinct roots `ai,aj`, define the maximum on the two hub arms and let

```text
Vfree(f)=min_{i != j} inf_{|h-ai|+|h-aj|<=2} Mij(h).
```

The surviving all-degree target is

```text
Vfree(f) <= Gcrit(f).                                       (FP-GM)
```

It chooses the pair jointly with the hub.  Since `Gcrit<=R^n` for roots in a
closed disc of radius `R`, minimum-enclosing-disc normalization turns FP-GM
into a two-arm path of length at most `2R` and level at most `R^n`.  For roots
in the open unit disc, `R<1`, so both inequalities become strict.  Thus FP-GM
still implies unrestricted Erdős #1041.

The compact exact checker reconstructs (1)--(11), including Rouché margins and
all Bernstein cells.  `CEGMQuarticFixedPairNoGo.lean` checks the Gaussian-
rational derivative and critical-value kernel, threshold ordering, the exact
circle polynomial, and its negative-half-line positivity.  Rouché, the
positive-half-line Bernstein consumer, Jordan separation, and merge topology
remain ordinary mathematics.

The unrestricted problem remains open.  The fixed-nearest-pair CE--GM lane is
retired; free-pair FP-GM is the correct consumer-facing frontier.
