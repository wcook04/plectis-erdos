# Erdős 1041: an exact mixed-mode boundary for Bernstein plus critical J2

## Status

This note gives an exact rational counterexample to the proposed quintic
certificate disjunction

```text
at least two Bernstein-safe origin spokes
or
some admissible critical point satisfies mu J_2 <= 1.                 (BCJ2)
```

Here `J_2` is the full pointwise phase/energy row of
`CriticalSpokeHybridLowModeDichotomy.md`, not its closed energy-only
relaxation.  The result is an ordinary exact proof with a rational-ball
checker.  It refutes only `(BCJ2)`: it is not a counterexample to Erdős 1041
and it does not say that the required curved connector is absent.

## 1. Exact witness

Take the five exact Gaussian-rational roots

```text
a0 =  0.9976274963 - 0.0688286176 i,
a1 =  0.2336442603 + 0.9723211196 i,
a2 = -0.8077935542 + 0.5894638019 i,
a3 = -0.8347956985 - 0.5505580276 i,
a4 =  0.3448410498 - 0.9386600292 i.                       (1)
```

Every displayed decimal is interpreted as a rational number.  Direct exact
squared-norm tests give `|a_i|<1`.  Put

```text
P(z)=product_i (z-a_i).                                    (2)
```

Both low coefficients are genuinely present and the second mode dominates:

```text
|[z]P|^2 > 1/500,             |[z^2]P|^2 > 4 |[z]P|^2.    (3)
```

The normalized Vandermonde lies in the finite near-gon band,

```text
0.9597 < product_(i<j)|a_i-a_j|^2 / 5^5 < 0.9599.          (4)
```

Thus (1) is a genuinely mixed first/second-mode point, not the regular
pentagon and not a pure one-mode degeneration.

## 2. Exactly one Bernstein-safe root

For a root `a`, write

```text
P(ta)=sum_(k=0)^5 q_k(a)t^k,
B_j(a)=sum_(k=0)^j q_k(a) binom(j,k)/binom(5,k).             (5)
```

The Bernstein convex-hull theorem certifies the origin spoke whenever all
six controls have modulus at most one.  Exact Gaussian-rational arithmetic
on (1) gives failing control indices

```text
root       a0   a1   a2   a3   a4
failure    B1   B1   --   B3   B1,                         (6)
```

and every control of `a2` has modulus strictly below one.  Hence precisely
one root is Bernstein-safe.

## 3. Every admissible critical point fails the full J2 row

Let `c` be a non-root critical point, `mu=|P(c)|`, and let `a_i` be its
second-nearest root.  With

```text
u_j=(a_i-c)/(a_j-c),
S_i=sum_(j!=i)|u_j|^2,
F_i(t)=(1-t)(1+(2t+S_i t^2)/4)^2,                           (7)
```

write

```text
P(c+t(a_i-c))/P(c)=sum_(k=0)^5 C_k t^k
```

and use the exact endpoint-absorbed phase row

```text
H_i(t)=1-t^5+sum_(k=2)^4 |C_k|t^k+|C_5+1|t^5,
J_i=max_(0<=t<=1) min(F_i(t),H_i(t)).                       (8)
```

The checker isolates the four zeros of `P'` in disjoint rational disks of
radius `10^(-10)`.  Rouché's theorem applies because the linear Taylor term
of `P'` dominates the other terms on each disk.  Since `P'` has degree four,
these disks exhaust its critical points.

Three disks satisfy `mu<1`.  Their nearest pairs and rational witness
parameters are

| critical-disk centre | nearest pair | `t` |
|---|---:|---:|
| `-0.08110254623302735637 + 0.45420358003252453847 i` | `(a1,a2)` | `3143/10000` |
| `-0.39725974112619382945 - 0.06141457026133894437 i` | `(a3,a2)` | `163/500` |
| ` 0.38081381182063186505 - 0.23575517147048456797 i` | `(a0,a4)` | `2281/10000` |

On the entire corresponding critical disk, rational triangle bounds prove

```text
mu F_2(t)-1 > 2*10^(-5),        mu H_2(t)-1 > 10^(-2).      (9)
```

Therefore `mu J_2>1` at all three admissible critical points.  On the fourth
critical disk the same exact bounds give `mu>1`, so it is not an admissible
hub.  This proves failure of `(BCJ2)`.

The phase lower bound in (9) contains no sampled maximum.  It bounds the
Taylor coefficients

```text
C_k=P^(k)(c)(a_i-c)^k/(k! P(c))                             (10)
```

and the terminal numerator `(a_i-c)^5+P(c)` separately on the rational disk,
then evaluates the lower envelope at the displayed rational `t`.  The small
energy margins in (9) are therefore exact, not floating-point grid evidence.

## 4. Consequence for the proof architecture

The exact global product budget for the first Bernstein column remains true,
as does the occupied-cone theorem and every individual sufficient spoke
criterion.  What fails is their proposed **selector**: the safe roots can be
misaligned across Bernstein columns while every admissible critical row sits
just above one.

The obstruction is already in the finite mixed first/second-mode band.  The
correct consumer is therefore the connector mechanism proved for the compact
mixed model in `QuinticMixedGlobalAtlas.md`, together with a finite-capacity
transfer across the band (4).  A proof cannot close this band merely by
asserting Bernstein-or-critical-`J2`; it must use a curved/truncated connector,
a stronger genuinely coupled selector, or a direct finite atlas on the
actual polynomial.

## Exact open boundary

This note proves no failure of contained paths, no failure of the mixed-model
connector, and no counterexample to the length-two theorem.  It also does not
prove the finite-capacity transfer from `QuinticMixedGlobalAtlas.md` at
Vandermonde level (4).  That transfer is the surviving degree-five task.
