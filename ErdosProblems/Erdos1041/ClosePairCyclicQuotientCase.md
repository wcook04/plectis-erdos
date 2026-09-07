# Erdős #1041 for arbitrary-degree cyclic quotients with a close pair

Status: analytic theorem proved, 2026-08-24; the exact factor budget and metric
fan-in are formalized in `ClosePairCyclicQuotientCase.lean`, with focused Lean
validation pending. This is an all-degree sufficient class, not a solution of
unrestricted Erdős #1041, and no literature-priority claim is made.

## The theorem

Let `m,q>=2`, let `h` be complex, and let

```text
P(w)=product_{k=1}^m (w-w_k),       f(z)=P((z-h)^q).
```

Assume every listed zero of `f` lies in the open unit disk. If two distinct
quotient roots, say `w_1,w_2`, have distance `d` satisfying

```text
2^(m-2) d^2 < 4,                                      (1)
```

then two distinct zeros of `f` are joined inside `{|f|<1}` by a rectifiable
path of length strictly below `2`.

The factor-by-factor threshold is not the endpoint of the argument.  Put

```text
Phi_m(y)=y(1+sqrt(1-y))^(m-2),       Y=d^2/4.
```

The radial-deficit refinement proved below gives the stronger all-degree
criterion

```text
max_{0<=y<=Y} Phi_m(y) <= 1.                         (1')
```

On `0<=Y<=4(m-1)/m^2`, `Phi_m` is increasing, so (1') reduces to the single
algebraic inequality `Phi_m(Y)<=1`.  If `Y_m` denotes the first positive root
of `Phi_m(Y)=1`, every pair with `d^2<=4Y_m` is therefore safe.  Equality is
allowed because the unselected-factor estimates below are strict (and for
`m=2`, open-disk roots cannot have `d=2`).  This
strictly improves (1) in each fixed degree while retaining an explicit
one-variable certificate.

For quotient degree five, the factor-by-factor form (1) is simply

```text
d < 1/sqrt(2).                                         (2)
```

Thus every translated cyclic lift of a quintic having such a close quotient
pair satisfies Erdős #1041, in every total degree `5q>=10`.

There is a strictly stronger quintic threshold.  The geometry of the unit
disk couples the selected pair to the other three factors, and gives the
improved sufficient condition

```text
d^2 <= 5/9,                                             (2')
```

or `d <= sqrt(5)/3=0.745355...`, rather than
`d<1/sqrt(2)=0.707106...`.

## Proof

As in the quadratic, cubic, and quartic quotient cases, a complete `q`-point
fibre over each `w_k` lies in the open unit disk. Averaging squared moduli over
that regular fibre gives

```text
|h|^2+|y_k|^2 < 1,       y_k^q=w_k,
```

and hence `|w_k|<1`.

Parameterize the quotient chord by

```text
w(t)=(1-t)w_1+t w_2,       0<=t<=1.
```

The two selected factors are exact:

```text
|w(t)-w_1| |w(t)-w_2| = t(1-t)d^2 <= d^2/4.           (3)
```

The open unit disk is convex, so `|w(t)|<1`. For each remaining quotient root,

```text
|w(t)-w_k| < |w(t)|+|w_k| < 2.                        (4)
```

Multiplying (3)--(4) and using (1) yields

```text
|P(w(t))| < (d^2/4) 2^(m-2) < 1.                     (5)
```

The strict inequality also holds at the endpoints because `P=0` there. Thus
the entire quotient chord lies in the strict unit lemniscate.

Now lift the chord continuously through `y -> y^q` (splitting at zero if the
chord crosses zero), and translate by `h`. The power-map chord-lift lemma from
`QuarticQuotientFiberCase.md` gives a lift joining a `q`-th root of `w_1` to a
`q`-th root of `w_2` with length at most

```text
|w_1|^(1/q)+|w_2|^(1/q) < 2.                          (6)
```

The endpoint zeros are distinct because `w_1!=w_2`, and (5) pulls back exactly
to `|f|<1`. This proves the theorem.

## The strengthened quintic chord estimate

For a quintic, put

```text
y=t(1-t)d^2.
```

The Hilbert-space convexity identity gives more than `|w(t)|<1`:

```text
|w(t)|^2
 = (1-t)|w_1|^2+t|w_2|^2-t(1-t)|w_1-w_2|^2
 < 1-y.                                                 (7)
```

Consequently each of the other three root factors is strictly below
`1+sqrt(1-y)`, and hence

```text
|P(w(t))| < y(1+sqrt(1-y))^3.                          (8)
```

The same argument with `m-2` remaining roots proves (1') in every degree.  To
locate its one-variable maximum, set `s=sqrt(1-y)`.  Then

```text
Phi_m(y)=(1-s)(1+s)^(m-1),
d/ds log Phi_m = ((m-2)-m s)/((1-s)(1+s)).
```

Thus `Phi_m` increases with `y` until
`y=1-((m-2)/m)^2=4(m-1)/m^2`, proving the endpoint reduction used above.
For `m=5` the first root is just beyond `5/36`, which is why the following
rational certificate nearly saturates the exact radial-deficit method.

For `0<=y<=5/36`, concavity of the square root and elementary polynomial
algebra give

```text
sqrt(1-y) <= 1-y/2,
y(1+sqrt(1-y))^3
  <= y(2-y/2)^3
   = 8y-6y^2+(3/2)y^3-(1/8)y^4
  <= 8y-6y^2+(3/2)y^3
  <= 31085/31104 < 1.                                 (9)
```

The cubic majorant in (9) is increasing on this interval because its
derivative is positive there.  Condition (2') implies
`y<=d^2/4<=5/36`, so (8)--(9) prove the stronger quintic statement.  This is
not a numerical fit: `5/9` is a deliberately rational, Lean-friendly
certificate.  The optimal squared-distance threshold obtainable from (8) is
`4Y=0.5585151265...`, where `Y` is the unique root in `(0,1)` of
`Y^4+Y^3+Y^2+7Y-1=0`; no global optimality claim is made here.

## What changes, and what does not

The result promotes the close-pair branch of the quartic proof to arbitrary
quotient degree. The usable threshold is exponential in `m`, so this does not
settle the separated-root regime. In quotient degree five, the corpus contains
an exact configuration with no safe root chord and at most one safe radial arm
through the minimum-enclosing-disc centre; it blocks the naive quartic
chord-or-two-radii dichotomy, but it does not contradict this theorem or
Erdős #1041.

The next hard boundary is therefore precise: treat quotient configurations in
which every pair has distance at least the applicable close-pair threshold,
using a polynomial-adapted
hub, curved path, or component mechanism rather than another fixed-origin
selector.  This residual is nonempty already for `m=5`: the exact adaptive-MEC
witness in `AdaptiveMecDichotomyLab.md` has every root chord unsafe, so the
strengthened theorem just proved forces every one of its ten pair distances to
satisfy `d^2>5/9`.  That is a consequence of the exact chord failures, not a
new floating-point measurement.
