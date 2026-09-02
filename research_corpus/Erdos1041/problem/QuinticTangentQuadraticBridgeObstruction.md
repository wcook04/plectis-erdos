# Erdős 1041: the tangent inverse-ray pair exactly obstructs the two-sheet quadratic bridge

Date: 2026-08-30. Checker:
`scripts/check_erdos1041_quintic_tangent_quadratic_bridge_obstruction.py`.

## 1. Result

At the exceptional tangent representative

```text
b1=(3/4)5^(-1/3) exp(i pi/5),       b2=exp(9 i pi/10),
```

take the canonical rightward inverse-ray pair born at the small trace-maximal
hub.  Its true pair excess is negative, by the existing exact certificate
`QuinticTangentCurvedExcessCertificate.md`, but its proposed two-sheet
quadratic majorant has the opposite sign:

```text
E_L1 < 0,                     Q_pair > 29/1000 > 0,       (Q0)

Q_pair = (1/2) integral_0^infinity
         (|q_+(rho)|^2+|q_-(rho)|^2-2) d rho.
```

Here `q_+-` are derivatives of the two inverse branches with respect to the
monic radial parameter.  Numerically, only as a diagnostic,
`Q_pair=0.31205...` while `E_L1=-0.0363...`.  Thus the elementary inequality
that bounds `L1` pair excess above by quadratic pair energy can be strict in
the wrong direction even on the exact canonical trace-max pair: the available
negative `L1` currency is invisible to this quadratic consumer.

This is a no-go for that proof route, not a counterexample to the Erdős 1041
metric target.  It does not obstruct a moved-block average, an entropy-weighted
allocation, or a direct `L1` argument.

## 2. Exact chart and energy identity

Reuse the real tangent normal form

```text
G(V)=V^5+40V^2-60V,             h=sqrt(3)-1,
G(V)=G(h)+i s,                  rho=s^(1/5).
```

Write either selected arm as `V=h+A(1+i t)`.  With `q=t^2`, the exact level
polynomial is

```text
P(A,q)=A^3(5q^2-10q+1)+5hA^2(q^2-6q+1)
       +20(1-h)A(1-3q)+60h(1-q)=0.                    (Q1)
```

The checker replays the source certificate that the right graph (`A>0`) and
left graph (`A<0`) are the unique selected arms and that their physical graph
slopes satisfy `0<p_R<1` and `7/8<p_L<7/5`.  If `x=|A|`,

```text
p=t-A P_A/P_t,
S=Im(G(V)-G(h)),
rho_x=S_x/(5 rho^4),

(|dV/d rho|^2-1)d rho
  = ((1+p^2)/rho_x-rho_x) dx.                         (Q2)
```

For numerical stability the replay does not expand `S` naively.  It uses the
critical-point factorization

```text
S=A^2 t B,
B=A^3(q^2-10q+5)+20hA^2(1-q)
  +20(1-h)A(3-q)+120h,                                (Q3)
```

and differentiates (Q3) along `P=0`.  This preserves the exact quadratic
vanishing at the hub.

## 3. Rational integration and the infinite tail

On `1/100 <= x <= 20`, exact parametric interval Newton tubes isolate the
selected root of (Q1) in every cell.  A centered cubic Taylor evaluation in
`A` remains sharp at the left-arm turning point.  Rational fifth-root boxes,
direct interval evaluation of (Q2), and directed rational lower summation
give, after paying the omitted hub interval by the elementary bound
`|dV/d rho|^2-1 >= -1`,

```text
right compact lower > -0.456094166837,
left  compact lower >  1.966042601517.                 (Q4)
```

For the tail put `R=x-1`.  Since `|G(h)|<23`,

```text
e(R)=56/R^3+72/R^4+23/R^5,
|dV/d rho| >= 1-e(R).
```

The replayed slope bounds give `|V_x|<7/4`, hence the tail debt of either arm
is at most

```text
(7/2)/(1-e(19)) * (28/19^2+24/19^3+23/(4*19^4))
 = 1874369/6545312 < 29/100.                           (Q5)
```

Combining (Q4)--(Q5), including the factor `1/2`, produces the exact computed
normal-form lower bound

```text
Q_G > 3833966005559069387/8181640000000000000
    > 1/10.                                            (Q6)
```

The original representative is the positive similarity
`lambda=40^(-1/3)`.  Quadratic excess scales by `lambda`, just as `L1`
excess does.  Finally

```text
40(29/100)^3 < 1,
```

so `lambda>29/100`; (Q6) implies (Q0).  Every comparison above is exact
rational arithmetic.  Floating point only proposes root tubes and reports
decimal diagnostics; the interval-Newton inclusions and all sign gates are
rechecked exactly.

## 4. Boundary

This certificate proves one precise obstruction:

```text
canonical tangent pair:     true L1 excess < 0 < quadratic pair energy.
```

It does not say that all trace-max pairs have positive quadratic energy, and
it does not refute the moved-block quadratic-budget equivalence.  It rules out
closing the canonical-pair problem by demanding nonpositive quadratic energy
for the very pair whose `L1` length is already good.
