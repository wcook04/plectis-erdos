# Erdős 1041: exact negative curved inverse-ray excess on the quintic tangent stratum

Date: 2026-08-30.  Checker:
`scripts/check_erdos1041_quintic_tangent_curved_excess.py`.  Lean algebra:
`QuinticTangentCurvedExcessCertificate.lean`.

## 1. Result

The isolated real-`mu` tangent point of the universal trace-max chamber is

```text
(mu,phi) = (50+30sqrt(3), -pi/2).
```

For this point, the two curved inverse branches of the rightward value ray
born at the selected hub have strictly negative pair excess.  In the real
normal form used below the exact estimate is

```text
E_pair <= -19517458527181 / 5000000000000000 < 0.       (T0)
```

Positive similarity scaling therefore proves
`mathcal E(50+30sqrt(3),-pi/2)<0` in the notation of
`QuinticTraceMaxUniversalChamber.md`.

This closes the curved-ray metric obligation on the singular tangent gauge
orbit.  It is stronger than the previously landed straight skip-pair rescue
at the same shape: the actual canonical inverse-ray pair is now certified.
It does not prove the universal inequality away from this isolated point.

## 2. Real tangent normal form and the exact level curve

After a domain rotation, a range rotation, and a positive similarity, the
tangent orbit is represented by

```text
G(V) = V^5 + 40V^2 - 60V,
h    = sqrt(3)-1,
G'(V)=5(V-h)(V+1+sqrt(3))(V^2-2V+6).
```

The rightward value ray in the original gauge becomes the upward ray

```text
G(V)=G(h)+is,  s>=0.                                    (T1)
```

Write either branch as

```text
V=h+A(1+it),  A real.
```

Direct expansion factors its real level equation as `A^2 P(A,t^2)=0`,
where, putting `q=t^2`,

```text
P(A,q) = A^3(5q^2-10q+1)
       + 5hA^2(q^2-6q+1)
       + 20(1-h)A(1-3q)
       + 60h(1-q).                                      (T2)
```

The branch with `A>0` has exactly one root `q_R(A)` in `(1/10,1)`.
Indeed `P(A,1/10)>0`, `P(A,1)<0`, and

```text
P_q/10 = -(1-q)A^3 -(3-q)hA^2 -6(1-h)A -6h < 0.
```

For `A=-B<0`, the branch has exactly one root `q_L(B)` in `(9/10,2)`.
The two endpoint polynomials `P(-B,9/10)` and `P(-B,2)` have respectively
positive and negative sign for every `B>0`: Sturm over
`Q(sqrt(3))` gives zero positive roots for both, and their signs at zero are
opposite.  Since `P` is quadratic in `q`, the sign change also proves that
the selected root is simple and unique.  Thus both branches are global
real-analytic graphs.

Locally `t -> 1` and (T1) has `s>0` on both sides.  The selected graphs meet
no other zero of `G'`; along a regular component of `Re G=G(h)`, `Im G` has
no stationary point.  Hence these two graphs are exactly the two upward
inverse-ray arms, not merely components of the undirected real level set.

At infinity their slopes tend to the two positive roots

```text
k_R^2 = 1-2sqrt(5)/5,       k_R=0.3249196962...,
k_L^2 = 1+2sqrt(5)/5,       k_L=1.3763819205....         (T3)
```

The terminal directions are therefore

```text
u_R=exp(i pi/10),          u_L=exp(-7i pi/10).
```

## 3. Exact tangent-angle and oscillation certificate

On a graph (T2), implicit differentiation gives the physical tangent slope

```text
p = d(At)/dA = t - A P_A/P_t.                           (T4)
```

For a proposed slope `p_0`, a crossing must satisfy

```text
P=0,       R_p0 := (t-p_0)P_t-A P_A=0.                 (T5)
```

Eliminate `t`, then eliminate `h` with `h^2+2h-2=0`.  Exact resultant
isolation gives the following candidate counts on the relevant half-axis:

```text
branch       p_0          resultant candidates    selected crossings
right         0                    2                       0
right         1                    5                       0
left         7/8                   2                       0
left         7/5                   2                       0.
```

At every candidate interval, rational interval evaluation first traps the
unique selected root of (T2), then proves `R_p0` has fixed nonzero sign.
The endpoint limits and one rational test point consequently give

```text
0 < p_R < 1,                 7/8 < p_L < 7/5.           (T6)
```

The half-angle formula

```text
tan(|atan a-atan b|/2)
  = |a-b|/(sqrt((1+a^2)(1+b^2))+1+ab)
```

then gives the rational enclosures

```text
tan(alpha_R/2) < 2401/10000,
tan(alpha_L/2) < 57/500.                                (T7)
```

It remains to price the transverse reversals.  In terminal coordinates set

```text
Y_R(A)= Im(conj(u_R)(V-h)) =  A(t-k_R)/sqrt(1+k_R^2),
Y_L(A)= Im(conj(u_L)(V-h)) = -A(t-k_L)/sqrt(1+k_L^2).
```

Their finite stationary points are exactly the selected solutions of (T5)
with `p_0=k_R,k_L`.  Eliminating also
`5k^4-10k^2+1=0` gives a degree-60 rational resultant.  Sturm isolates ten
positive and two negative candidate `A`-values.  Rational interval guards
exclude every candidate except

```text
A_R in (1.700532023...,1.700532032...),
A_L in (-3.870849878...,-3.870849869...).               (T8)
```

Exact opposite signs of `R_k` across small rational neighbourhoods prove
that both survivors are actual crossings.  Thus each selected arm has one
finite transverse extremum.

For completeness, if `r=k^2` and

```text
e = -5h(r^2-6r+1)/(10r-10),
```

then the expansion `q=r+e/A+O(A^-2)` gives the exact terminal offsets

```text
Y_R(oo)= e_R/(2k_R sqrt(1+k_R^2)) =  0.2262161402...,
Y_L(oo)=-e_L/(2k_L sqrt(1+k_L^2)) = -0.5922415440....   (T9)
```

Evaluating (T8) with rational intervals and subtracting (T9) proves

```text
Osc_R < 277/1000,              Osc_L < 63/2000.         (T10)
```

Here `Osc` is exactly the smaller of the positive and negative transverse
variations in the support--oscillation lemma: the right arm rises once above
its positive terminal offset and returns, while the left arm falls once
below its negative offset and returns.

## 4. Negative fan-in

The support--oscillation lemma of `TraceMaxEntropyAngularBudget.md` says

```text
e_u(gamma)
 <= tan(alpha/2)(|Im(conj(u)h)|+2 Osc)-Re(conj(u)h).
```

For the two terminal directions this becomes

```text
E_pair <= K_R(h sin 18deg+2 Osc_R)-h cos 18deg
        + K_L(h sin 54deg+2 Osc_L)+h sin 36deg,          (T11)
```

with `K_R=2401/10000`, `K_L=57/500`.  Finally use the outward rational
enclosures

```text
73205/100000 < h < 732051/1000000,
sin 18deg < 309018/10^6,       cos 18deg > 951056/10^6,
sin 54deg < 809018/10^6,       sin 36deg < 587786/10^6.
```

Substitution of (T10) into (T11) is exact rational arithmetic and yields

```text
E_pair
 <= -19517458527181 / 5000000000000000
 < 0,
```

which is (T0).

## Claim boundary

This is an ordinary proof of the curved rightward inverse-ray excess at the
single tangent gauge orbit.  The checker recomputes the level-set and gap
identities, all resultants and Sturm isolations, every branch-selection sign,
the algebraic-number interval guards, the two oscillation bounds, and the
final rational fan-in.  Lean checks the new critical-gap collapse and final
rational margin.  The rest of the compact universal chamber `(EX-U)`, the
real-scale transfer, degree five, and unrestricted Erdős 1041 remain open.

