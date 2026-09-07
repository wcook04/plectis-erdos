# Erdős 1041: phase-exact Bernstein spoke certificate and its sharp no-go

## Status

This note proves an exact finite phase-sensitive certificate for an
origin-to-root spoke.  It identifies the controls as polarized root products
and gives product laws for the first and penultimate controls.  It also
gives an exact rational quintic for which only one root passes the certificate,
so the certificate is not silently promoted to a universal two-root selector.

The positive statements and the no-go are ordinary exact theorems with a
rational symbolic checker.  The no-go is a failure of this sufficient
certificate, not a counterexample to Erdős 1041.

## 1. Power coefficients to Bernstein controls

Let

```text
P(z)=sum_(k=0)^n p_k z^k,          p_n=1,
```

have all roots in the open unit disk, and fix a root `a`.  Along its origin
spoke put

```text
Q_a(t)=P(t a)=sum_(k=0)^n q_k(a)t^k,
q_k(a)=p_k a^k.                                             (1)
```

Its degree-`n` Bernstein controls are

```text
B_j(a)=sum_(k=0)^j q_k(a) binom(j,k)/binom(n,k),
0<=j<=n.                                                     (2)
```

The power-to-Bernstein identity is

```text
Q_a(t)=sum_(j=0)^n B_j(a) binom(n,j)t^j(1-t)^(n-j).          (3)
```

The basis weights in (3) are nonnegative and sum to one.

> **Theorem C (Bernstein root-spoke certificate).**  If
>
> ```text
> |B_j(a)|<=1                  for every 0<=j<=n,             (4)
> ```
>
> then the whole spoke `[0,a]` lies in `{|P|<1}`.

Indeed, (3) and convexity give `|Q_a(t)|<=1`.  In fact the inequality is
strict for `0<t<1`: every Bernstein weight is then positive and
`B_n(a)=Q_a(1)=P(a)=0`.  At `t=0`, `B_0=p_0=P(0)` has modulus below one by
Vieta; at `t=1`, the value is zero.  If two root occurrences pass (4), joining
them through the origin has length below two and proves Erdős 1041.

Unlike an absolute coefficient norm, (2) retains every complex cancellation.

## 2. Root polarization formula

Write `P(z)=product_(ell=1)^n(z-a_ell)` and select `a=a_i`.  Each spoke factor
has endpoint controls

```text
t a_i-a_ell=(-a_ell)(1-t)+(a_i-a_ell)t.                    (5)
```

Multiplying degree-one Bernstein forms gives the exact polarization

```text
B_j(a_i)
 =1/binom(n,j) sum_(|S|=j)
    product_(ell in S)(a_i-a_ell)
    product_(ell notin S)(-a_ell).                         (6)
```

Every summand with `i in S` vanishes.  Formula (6) is the phase information
lost by all `l1` coefficient collars.

At `j=n-1`, only `S={1,...,n}\{i}` survives, so

```text
B_(n-1)(a_i)=-a_i P'(a_i)/n.                              (7)
```

Consequently

```text
product_i |B_(n-1)(a_i)|
 =|p_0| |Disc(P)|/n^n
 <=|p_0|<1,                                                (8)
```

where the last inequality is the sharp Fekete--Vandermonde bound for points
in the closed unit disk.  Thus at least one root always has its penultimate
Bernstein control strictly inside the unit disk.  This is a genuine exact
product/averaging principle, but it controls only one of the `n+1` rows needed
in (4).

### The first-column product law

There is a second all-degree product budget at the opposite end.  For roots
in the **closed** unit disk,

```text
product_i |B_1(a_i)| <=1.                                  (9)
```

The proof uses a separate-subharmonic reduction and is short.  The product

```text
H(a_1,...,a_n)=product_i B_1(a_i)
```

is a holomorphic polynomial in every root variable, so its maximum on the
closed polydisc occurs on the distinguished torus `|a_i|=1`.  On that torus
write `m=(1/n)sum_i a_i`.  Self-inversivity gives

```text
B_1(a_i)=p_0 a_i conjugate(a_i-m),
|B_1(a_i)|=|a_i-m|.                                       (10)
```

Consequently, by AM--GM and the centroid variance identity,

```text
product_i |B_1(a_i)|
 <=[(1/n)sum_i |a_i-m|^2]^(n/2)
 =(1-|m|^2)^(n/2)<=1.                                    (11)
```

Thus every polynomial has at least one root whose first control is safe, just
as (8) supplies at least one root whose penultimate control is safe.  The two
roots need not coincide, and neither product law controls the interior
columns `2<=j<=n-2`; this is exactly the surviving matching problem.

## 3. Exact rational quintic no-go

The simultaneous two-root Bernstein selector is false.  Take the following
five exact rational complex numbers (the displayed finite decimals are the
numbers themselves, not rounded notation):

```text
a_1= 0.9954764088478315 -0.08383149424545093 i,
a_2= 0.14881265879891825+0.9878541352756472  i,
a_3=-0.6277869770917356 +0.7771000652387186  i,
a_4=-0.5684933442778939 -0.8214720430493883  i,
a_5= 0.26099542375571383-0.964304095593592   i.            (12)
```

Exact integer comparison gives `|a_i|^2<1` for every `i`.  Let
`P=product_i(z-a_i)` and form (2) in rational complex arithmetic.  The largest
control moduli are

| root | largest control | modulus |
|---:|---:|---:|
| 1 | `j=3` | `1.0022159118...` |
| 2 | `j=1` | `1.0103931500...` |
| 3 | `j=2` | `1.0517616591...` |
| 4 | `j=2` | `1.0140874939...` |
| 5 | `j=0` | `0.9950099900...` |

For roots `1` through `4`, the checker proves `|B_j|^2-1>0` by exact rational
numerator signs.  For root `5`, it proves `|B_j|^2-1<0` for all six controls.
Hence **exactly one** root passes (4).

This witness is deliberately attached to the positive theorem.  It proves
that neither endpoint-column product law nor numerical prevalence can supply
the missing second root.  It does not say that the four failing spokes escape;
failure of a convex-hull certificate is only non-support.

## 4. Computed scope and exact boundary

Deterministic degree-five sweeps show why the theorem is still useful: random
disk configurations usually have at least three certified roots, and generic
near-pentagons usually have at least two.  Pure angular perturbations produce
the thin exceptional set represented by (9).  These frequency statements are
calibration only.

The exact remaining problem for this route is a simultaneous phase allocation:
control all `B_j(a_i)` at two roots, or combine a failing Bernstein row with
the critical one-row/curved connector.  Formulas (8) and (9) solve the two
endpoint columns.  The interior-column resultant bounds suggested by the same
torus reduction, and a matching argument that keeps all controls on the same
two roots, remain open.
