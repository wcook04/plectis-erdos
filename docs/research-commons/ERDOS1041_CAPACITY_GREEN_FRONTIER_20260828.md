# Erdős 1041 capacity and Green-polarization frontier — 2026-08-28

This is a public, source-current research frontier, not a proof of unrestricted
Erdős 1041.  The target remains open.

## Exact advances

For a proper `k`-root component at level `t`, let `m=n-k`, let `B` be its
degree-`m` exterior Blaschke product, and put

```text
p=|B(0)|=cap(closure U)^n/t.
```

The complete antipodal boundary fibre has the exact saturation law

```text
Delta=(1-p)/(1+p)-m/n=sum_j h_j/[n(n-h_j)],
sum_j h_j <= n^2 Delta/(1+n Delta/m) <= n^2 Delta,
```

where `h_j=n-|B'(zeta_j)|`.  Following the closest excluded root also gives
the attachment-compatible ceiling

```text
b_next/t <= M_n(p^(1/m)) <= p^(-(n-1)/m).
```

At fixed product, the conjectured sharp symmetric merge envelope is now proved
for two exterior zeros.  For three exterior zeros it is proved on two global
slices: arbitrary angles with equal radii, and arbitrary radii at regular
`120`-degree angles.  The regular triangle is a strict local maximum in every
nonzero product-preserving radial direction.

The equal-weight three-ray product shortcut is false.  The exact rational
witness `r_1=r_2=1/1600`, `r_3=1/25`, angles `0,0,pi`, `x=8` exceeds the regular
product by a factor greater than `1.1673`; the minimum-ray envelope survives.

## Intrinsic coupled inequality

Write `a_j=r_j exp(i theta_j)`, `p=r_1r_2r_3`, and `q=1/x`.  Every radial
factor is a pseudohyperbolic distance, hence exactly

```text
F_j(x)/x^n=|B(q exp(i theta_j))|.
```

The regular triangle equals

```text
T_p(q)=(q^3-p)/(1-pq^3).
```

The coupled pointwise conjecture is therefore

```text
min_j |B(q exp(i theta_j))| <= T_p(q),  max_j r_j<=q<1. (GP3)
```

Fixed-seed global searches support the radius-weighted certificate

```text
sum_j r_j log|B(q exp(i theta_j))|
 <= (sum_j r_j)log T_p(q).                              (WGP3)
```

The difference in `WGP3` vanishes at `q=1`.  Its derivative reduces to the
explicit rational inequality

```text
sum_(j,k) r_j H(q,r_k,cos(theta_j-theta_k))
 >= (sum_j r_j)[3q^2/(q^3-p)+3pq^2/(1-pq^3)],          (DGP3)

H(q,r,c)=(1-r^2)[q(1+r^2)-rc(1+q^2)]
 /[(q^2-2qrc+r^2)(1-2qrc+q^2r^2)].
```

`DGP3`, `WGP3`, and `GP3` are unproved.  Even `GP3` still needs a
selector/interval lemma to produce one fixed ray whose optimized barrier is
below the regular barrier.

The angular half of `DGP3` is exact.  The kernel decomposes as

```text
H(q,r,c)=(q-rc)/(q^2+r^2-2qrc)
         -(qr^2-rc)/(1+q^2r^2-2qrc),
```

and direct differentiation gives

```text
d^2H/dc^2=4qr^2[(q^2-r^2)/(q^2+r^2-2qrc)^3
                +(1-q^2r^2)/(1+q^2r^2-2qrc)^3] > 0.
```

Hence every pair kernel is strictly convex in the pair cosine and lies above
its tangent at `c=-1/2`.  Exact minimization of the resulting weighted
three-cosine energy reduces `DGP3` to a piecewise rational inequality in only
`(r_1,r_2,r_3,q)`.  A global falsifier search minimizes that radial residual
at equal radii to numerical precision; the rational inequality is still open.

## Prior-art firewall

Dubinin proved that a rotationally symmetric finite Blaschke product maximizes
the least critical-value modulus when `C(0)=0` and `|C'(0)|` is fixed: V. N.
Dubinin, *An upper bound for the least critical values of finite Blaschke
products*, Sbornik: Mathematics 213:6 (2022), 744–751,
DOI `10.1070/SM9679`.  That theorem does not directly apply here: the merge
function is the meromorphic inner quotient `z^n/B(z)`, not an analytic finite
Blaschke product with nonzero derivative at the origin.

## Replay and provenance

```sh
python3 experiments/erdos1041_three_exterior_green_polarization.py
```

Projected from private source commits:

```text
947af3a15fee7710a7335856bc2b9739b94f7aca  capacity bridge
a317ab7ca8c4be2750ab2411003002760cac5146  exact m=2 envelope
f5fe5280083dcbb84d213da20c3ba35d77de3584  m=3 angular envelope
804a430ecb3186d20c1e7e03ea3fffe9456abc07  m=3 local radial theorem
6d6c99bbde62f666db449ae47cd6b5e8aa3d74cf  regular-angle radial theorem
a397aa8c0effc9a51389cdb4e9c37ce5cd93e4d7  product-shortcut no-go
f944dbd3e9128bcc7757b32fbf3994da83676c3b  Green-polarization reduction
```
