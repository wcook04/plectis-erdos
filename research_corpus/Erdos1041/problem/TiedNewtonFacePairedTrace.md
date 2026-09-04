# The disk-forced paired mode breaks every tied-face critical trace

## Status

This is an all-degree analytic theorem strengthening
`TiedNewtonFaceCriticalTrace.md`.  The leading low Newton face has total
critical-value trace zero.  If that leading trace gives no strictly negative
critical value, the **first complementary high mode forced by the disk
constraint has strictly negative trace**.  Thus every low tied face has a
lexicographically negative critical saddle; equality of the leading model
cannot persist through the first paired correction.

The finite trace identity and lexicographic selector are Lean checked in
`TiedNewtonFacePairedTrace.lean`.  This closes strict saddle selection, not the
remaining metric scattering-length inequality, so Erdős #1041 remains open.

## 1. The second Newton moment identity

Let

```text
Q(z)=sum_(m in M) A_m z^m-z^n,       1<=m<n/2,
```

and let `c_1,...,c_(n-1)` be the critical points with multiplicity.  The
previous theorem used the missing coefficient block in `Q'/(-n)` to prove

```text
S_k:=sum_i c_i^k=0                   (1<=k<=max M).        (1)
```

Newton's identities one step farther give, for every active `m`,

```text
S_(n-m) = m(n-m) A_m/n.                                  (2)
```

Indeed, put `N=n-1`.  The coefficient of `z^(m-1)` in the monic derivative is
`a_(m-1)=-mA_m/n`.  In Newton's identity at `k=n-m`, its direct contribution is

```text
(n-m)a_(m-1).
```

The only possible cross term from another active degree `ell` has
`j=n-ell` and is

```text
a_(ell-1) S_(ell-m).
```

It is absent for `ell<m` and zero by (1) for `ell>m`.  Thus

```text
S_(n-m)+(n-m)(-mA_m/n)=0,
```

which is (2).  This identity is coefficient-general; the checker replays the
exact recurrence on Gaussian-rational rows in every degree `5,...,40`.

## 2. The paired trace is a negative square

For a tangent perturbation of roots inside the disk, Fourier pairing gives

```text
E_(n-m) = -conj(E_m) + higher radial order.               (3)
```

Consequently the complementary correction associated with `A_m` is

```text
R_m(z)=-conj(A_m) z^(n-m).                                (4)
```

Summing (4) over the critical multiset and using (2),

```text
sum_i R_m(c_i)
 = -conj(A_m) S_(n-m)
 = -m(n-m)|A_m|^2/n < 0.                                 (5)
```

The right side is real and strictly negative whenever `A_m!=0`.  This is the
new invariant: the disk constraint does not merely add an uncontrolled next
term.  Its total effect on the critical values is a negative norm square.

## 3. Why the maximal tied mode acts first

Along a rational Newton face, write the common balance scale as `z=u^q zeta`.
The low mode `m` and `-z^n` have common leading weight.  Its complementary
mode `n-m` arrives later by the positive integer gap

```text
                         q(n-2m).                         (6)
```

This gap decreases strictly with `m`.  Therefore, if `M=max M`, the first
paired correction is exactly

```text
-conj(A_M) zeta^(n-M),
```

and (5) for `m=M` cannot be cancelled by any other paired mode at that order.

Let `L_i=Re Q(c_i)` and `K_i=Re R_M(c_i)`.  The two trace identities say

```text
sum_i L_i=0,                       sum_i K_i<0.            (7)
```

Hence some critical point is lexicographically negative:

```text
L_i<0,        or        L_i=0 and K_i<0.                  (8)
```

If a leading value is already negative, take it.  Otherwise every `L_i` is
nonnegative, so their zero sum forces all of them to vanish; the negative
second sum then supplies `K_i<0`.  Lean checks precisely this finite selector.

For simple critical points, the first variation of the critical value is just
`R_M(c_i)`: displacement of the critical point contributes
`Q'(c_i) delta c_i=0`.  Equivalently, without choosing branches, the total
critical-value trace of the perturbed polynomial has the negative first
coefficient (5).  Thus for every sufficiently small positive face parameter,
some actual critical value has negative real part.  Multiple critical points
are handled at the multiset trace level; no labelling of their split branches
is needed.

Combining this with the harmonic maximum-principle argument of the preceding
note gives a strict two-ended merger below level zero after the first paired
term.  The formerly dangerous all-zero leading trace is therefore not a true
containment obstruction.

## 4. The quintic adversary identifies the formula exactly

An outer differential-evolution search over both compact coefficient faces of

```text
Re(Az+Bz^2-z^5),          max(|A|,|B|)=1,
```

maximized the best critical-hub two-arm certificate.  On the `|B|=1` face it
converged to

```text
|A|^3=27/320,
arg A=8pi/5,
arg B=7pi/10,
```

the conjugate of the corpus's independently derived sharp equality chart.
This was not a new numerical constant.  It was a diagnostic that the trace
was binding at exactly the known model equality.

Rotate by `z=exp(-i pi/10)x`.  The model becomes

```text
Q(z)=i P(x),             P(x)=x^5+x^2-u x,
u^3=27/320.                                                (9)
```

One critical point is

```text
x=(2u/3)(1-i sqrt(5)),
x^3=(-7+i sqrt(5))/20.                                  (10)
```

Exact substitution gives

```text
P'(x)=0,                P(x)=-8u^2/5 in R,               (11)
```

so the leading harmonic critical value is exactly zero.  The paired cubic
correction is `Re(x^3)=-7/20`, strictly negative.  The deterministic checker
verifies (10)--(11) symbolically.  This recovers the earlier quintic tie-break
as one instance of the all-degree negative-square trace rather than an isolated
trigonometric accident.

The sextic adversary similarly returns the pure second-mode face, where the
leading hub path has zero metric defect.  That is an equality mechanism, not a
counterexample; the corpus already closes the pure-mode face by a different
connector.  These controls are why the computation supports the invariant
without being promoted to proof.

## 5. What is now left

The all-degree tied-face pipeline has advanced twice:

1. the leading critical trace forces a safe two-ended component;
2. the first disk-forced paired mode makes some critical merger strictly
   negative even when every leading critical value lies on level zero.

The remaining model-level obligation is genuinely metric.  One must prove, or
find an exact counterexample to, a two-ended connector with nonpositive
renormalized defect

```text
                         L(R)-2R<=0.                      (12)
```

The critical-hub two-straight-arm version survived the bounded normalized
search in degrees `5,...,9`, with equality only at already recognized strata,
but it is not proved.  Once (12) is available, the negative paired trace gives
the strict containment needed for finite transfer through equality charts.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_tied_newton_face_paired_trace.py --json
```
