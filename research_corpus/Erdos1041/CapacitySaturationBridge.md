# Erdős 1041: capacity saturation and an exact multi-exterior merge ceiling

## Status

This note assimilates the returned capacity-saturation research pass against the
source-current corpus on 2026-08-28. It proves two new corpus consequences and
retains one stronger conjecture as computation only:

1. composing the sharpened `mu<=1/64` lattice with the exterior-fibre capacity
   theorem removes the proper `k0=9` cell in every degree `10<=n<=459`;
2. every proper component has an explicit capacity-controlled upper bound for
   its next merger, obtained by following the closest excluded root in the
   exterior coordinate while all other Blaschke factors contract;
3. deterministic finite-Blaschke searches support, but do not prove, a much
   sharper symmetric-envelope merge ceiling.

The returned fibre-saturation inequality is also proved below. The unrestricted
parent theorem remains open: the exact radial ceiling loses all spectator
factors and is too weak in the large-degree fixed-arity shell, while the sharper
symmetric envelope has not been proved.

## 1. Source-current correction to the returned degree bands

Let `C` be the component used by the LC2 arity-capacity certificate, let `k<n`
be its root count, and put

```text
kappa = cap(closure C)/t^(1/n),       p = kappa^n.
```

The exterior-fibre theorem gives

```text
p < k/(2n-k).                                             (1)
```

If the metric certificate closes whenever `kappa<=q`, then (1) makes it
automatic whenever

```text
k/(2n-k) < q^n.                                          (2)
```

For rational `q=a/b`, this is the exact integer inequality

```text
k b^n < (2n-k) a^n.                                      (3)
```

The returned pass correctly found three bands from the older lattice. The
source-current fourth row is stronger: at `mu<=1/64`, `k=9`, the cutoff is now
`q=99/100`, not `18/19` or `39/40`.

> **Theorem 1 (source-current band composition).** For a proper minimizing
> component, the only nonempty automatic bands obtained by composing every row
> of the current four lattices with (1) are
>
> ```text
> mu<=1/2,  k=16, q=39/40:   22<=n<=93;
> mu<=1/4,  k=11, q=49/50:   13<=n<=167;
> mu<=1/8,  k=9,  q=18/19:   15<=n<=35;
> mu<=1/64, k=9,  q=99/100:  10<=n<=459.
> ```
>
> Hence a counterexample with `mu<=1/64` and `10<=n<=459` cannot have a
> proper minimizing `k0=9` component. In that range the remaining proper-cell
> residual has `k0<=8`.

*Proof.* Apply (3) to each source-current rational cutoff. Exact integer
arithmetic gives the four intervals. For fixed `k,q`,

```text
F(x)=x log q + log(2x-k)-log k
```

is strictly concave, so its positive integer set is one interval; the endpoint
and adjacent-failure checks therefore certify the complete bands. The checker
also exhausts every listed row through degree `5000`; no other row is nonempty.
The strict theorem is (2), while the finite exhaustion is only a guard against
table transcription error. ∎

The qualifier *proper* matters. If `k=n`, (1) is unavailable; this theorem does
not delete the degree-nine whole-component cell.

## 2. The returned fibre-saturation inequality

Retain the notation of `ExteriorBlaschkeFibreCapacityGap.md`. Thus `B` is the
degree-`m=n-k` exterior finite Blaschke product,

```text
p=|B(0)|=cap(closure U)^n/t,
```

and on the antipodal fibre `B(zeta_j)=-B(0)/|B(0)|` put

```text
x_j=|B'(zeta_j)|,       h_j=n-x_j>0.
```

The exact fibre identity is

```text
sum_j 1/x_j = (1-p)/(1+p).
```

Put

```text
Delta=(1-p)/(1+p)-m/n.
```

> **Theorem 2 (complete-fibre saturation).** One has
>
> ```text
> Delta = sum_j h_j/[n(n-h_j)],                          (4)
> sum_j h_j <= n^2 Delta/(1+n Delta/m) <= n^2 Delta.     (5)
> ```
>
> In particular every point of the complete antipodal fibre has speed deficit
> at most the first quantity on the right of (5).

*Proof.* Equation (4) is the termwise identity

```text
1/x_j-1/n = h_j/[n(n-h_j)].
```

For (5), harmonic mean is at most arithmetic mean:

```text
sum_j x_j >= m^2/(sum_j 1/x_j)
              = mn/(1+n Delta/m).
```

Subtract from `mn`. Positivity gives the individual bound. ∎

With `p0=(n-m)/(n+m)`, direct subtraction also gives

```text
Delta = 2(p0-p)/[(1+p)(1+p0)].                           (6)
```

This is an exact and useful conversion, but its normalization must not be
blurred: failure of a `kappa<=q` certificate says only `p=kappa^n>q^n`.
For fixed `q<1` and large `n`, `q^n/p0` tends to zero. Therefore high normalized
capacity `kappa` does **not** uniformly imply near-saturation `p/p0≈1`. The
returned architecture needs a separate Green-crowding/near-regular branch
outside the finite saturation band.

## 3. Exact multi-exterior capacity-to-merge theorem

Let `U` be a proper regular component of `{|f|<t}` containing `k` roots of a
monic degree-`n` polynomial, and put `m=n-k`. Normalize the exterior Riemann map
so `U` corresponds to the closed unit disk. With

```text
B(eta)=product_j (eta-a_j)/(1-conj(a_j)eta),
```

the analytic completion used by the component-capacity formula is

```text
W(eta):=f(Phi^(-1)(eta)) = unit*t*eta^n/B(eta).          (7)
```

The excluded roots are `xi_j=1/conj(a_j)`. Write

```text
p=product_j |a_j|=cap(closure U)^n/t,
r=max_j |a_j|,
```

and choose `a_*` with modulus `r`. The corresponding excluded root is the
closest one in the exterior radial coordinate.

For `0<r<(n-1)/(n+1)`, define

```text
M_n(r) = max_(1<=x<=1/r) x^n (1-rx)/(x-r).               (8)
```

The maximum is explicit. Its interior maximizer `R>1` is the larger root of

```text
R^2 - [((n-1)+(n+1)r^2)/(nr)]R + 1 = 0,                 (9)
```

and

```text
M_n(r)=R^n(1-rR)/(R-r).                                  (10)
```

> **Theorem 3 (radial spectator-drop merge ceiling).** The component `U` joins
> at least one excluded root inside the closed level
>
> ```text
> {|f| <= t M_n(r)}.
> ```
>
> Consequently, since `r>=p^(1/m)` and `M_n` is decreasing,
>
> ```text
> b_next/t <= M_n(p^(1/m)) <= p^(-(n-1)/m),              (11)
> ```
>
> where `b_next` is the first level at which the component acquires an
> excluded root.

*Proof.* Rotate so `a_*=r>0` and follow the exterior radial segment
`eta=x`, `1<=x<=1/r`. For every spectator zero `a`,

```text
|x-a|^2-|1-conj(a)x|^2=(x^2-1)(1-|a|^2)>=0.             (12)
```

Thus every spectator factor of `1/B` has modulus at most one. The selected
factor equals `(1-rx)/(x-r)`, so (7) gives

```text
|W(x)|/t <= x^n(1-rx)/(x-r).                             (13)
```

The segment starts on `partial U` and ends at the excluded root `1/r`, so its
preimage is an actual attachment-compatible curve. Equation (13) proves the
first assertion. Boundary speed gives `(1+r)/(1-r)<n`, hence
`r<(n-1)/(n+1)` and the profile has the interior maximum (9)-(10).

For fixed `x`, logarithmic differentiation of the last factor in (8) has sign

```text
(1-x^2)/[(1-rx)(x-r)] <= 0,
```

so `M_n` decreases with `r`; geometric mean gives `r>=p^(1/m)`. Finally set
`y=rx`. The last inequality in (11) reduces to

```text
y^n(1-y) <= y-r^2,
```

which follows from `y^n<=y` and `y>=r`. ∎

This is the requested multi-exterior *existence* bridge. It is exact and keeps
the same component and an actual excluded root throughout. Quantitatively it is
not yet the parent closure: discarding all spectator factors changes the useful
large-`m` scale into the much worse exponent `(n-1)/m` in (11).

## 4. Exact symmetric model and the sharper live conjecture

The returned paper solved `m=1`. The same algebra closes every symmetric
degree-`m` exterior model. Let

```text
B_s(z)=(z^m-s)/(1-s z^m),       0<s<(n-m)/(n+m),
W_s(z)=t z^n/B_s(z).
```

Put `y=z^m`. Exterior critical points satisfy

```text
y^2 - [((n+m)s^2+(n-m))/(ns)]y + 1 = 0.                 (14)
```

If `y>1` is the larger root, the first symmetric critical level is

```text
b_sym/t = y^(n/m)(1-sy)/(y-s).                           (15)
```

At `s0=(n-m)/(n+m)`, equation (14) has a double root at `y=1`. Writing
`y=e^v` gives the exact parametrization

```text
s(v)=[n cosh(v)-sqrt(m^2+n^2 sinh(v)^2)]/(n+m).          (16)
```

If `s=(1-epsilon)s0`, expansion of (15)-(16) yields

```text
log(b_sym/t)
 = (sqrt(2)/3) (n^2-m^2)/(sqrt(n)m^(3/2)) epsilon^(3/2)
   + O(epsilon^(5/2)).                                   (17)
```

Thus the returned `3/2` cusp is not peculiar to one exterior root; it is the
universal symmetric finite-Blaschke cusp.

The computation suggests the substantially stronger statement

```text
b_next/t <= b_sym(n,m,p)/t                               (18)
```

at fixed `p=|B(0)|`: the regular equal-radius exterior configuration appears
to maximize the first merge height. Across deterministic perturbed tests at
`(n,m)=(8,2),(10,3),(12,4)`, every accepted boundary-speed configuration lay
below the symmetric value; the largest observed ratio was `0.999681`.

Equation (18) is **conjectural**. The experiment is a falsifier search, not a
proof. A proof would retain the spectator factors lost in Theorem 3 and would
put the large-degree fixed-arity shell on the correct scale. The natural
analytic formulation is a circular-symmetrization or mountain-pass theorem for

```text
log|W(z)/t| = n log|z| - log|B(z)|
```

on the exterior disk with fixed `|B(0)|`.

## 5. Parent-proof effect and surviving obstruction

The assimilation changes the live frontier in four precise ways.

1. The returned old degree bands are superseded by Theorem 1; the deep proper
   top cell now disappears through degree `459`.
2. Theorem 2 turns capacity saturation into complete-fibre speed saturation,
   but only when `p/p0` is actually close to one.
3. Theorem 3 supplies the first rigorous multi-exterior capacity-to-next-merge
   conversion with an attachment-compatible curve.
4. The exact symmetric model identifies the likely sharp envelope and preserves
   the `3/2` cusp for every `m`, but (18) is the first unsupported implication.

The most valuable next attack is therefore to prove or refute (18), not to add
another scalar capacity cutoff. If (18) holds, the capacity-defect branch and
merge branch can be co-optimized along the actual arity cascade. If it fails,
the counterexample will identify which angular statistic beyond `p` must be
retained.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_capacity_saturation_bridge.py
```

The checker labels exact arithmetic separately from floating evidence.
