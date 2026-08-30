# Erdős #1041: the hidden sextic null direction continues exactly

Status, 2026-08-25: complete analytic one-parameter theorem, exact symbolic
replay, and Lean formalization of the load-bearing convex interpolation and
ray bound. This enlarges the degree-six homogeneous atlas. It does **not**
prove the full sextic mixed model, a finite actual-polynomial neighbourhood,
or unrestricted Erdős #1041.

## 1. What the constrained adversary found

At the canonical sextic point

```text
H_0(z)=Re(-z^2-z^6)
```

there are four square-contact adjacent connectors. Their contact points are
the four vertices

```text
z=a(±1±i),       a=r_0(3-sqrt(3))/2,
r_0^4=(7+4sqrt(3))/27.
```

For a tangent coefficient perturbation

```text
delta H=Re((a_1+i b_1)z-i theta z^2+i c z^3),
```

the four contact gradients have one common null direction:

```text
a_1=theta=0,             b_1=-2a^2 c.                   (1)
```

An adversarial search forced away from the already-closed `c=0` slice and
converged to (1) after undoing sixth-root rotation. Numerically, its ratio
`|A|/c=0.57665...` is `2a^2` to the search accuracy. This is why the earlier
optimizer appeared to approach zero without finding a new phase orbit.

The first-order null direction is not merely infinitesimal. It continues as
an exact algebraic branch.

## 2. Exact branch

Put

```text
s=sqrt(3),             t_0=s-1,
q_0=(7+4s)/27,
beta_*=(106+25s)/1221.
```

For `0<=beta<=beta_*`, choose `r,u,c>0` by

```text
r^4=q_0(1+(3/2)beta t_0),
c=beta/r,
u=3 beta r(2-s).                                         (2)
```

Consider

```text
H_beta(z)=Re(-i u z-z^2+i c z^3-z^6).                    (3)
```

Use the adjacent sixth-root directions `omega^2,omega^3`, where
`omega=exp(pi i/3)`, with common truncation radius `r`. The real ray
`omega^3=-1` is automatically strict. The other ray and the joining chord
are nonpositive. Their total length is `2-r<2`.

At `beta=0`, (2) is the canonical four-contact point. Differentiating (2) at
zero gives `u/c=3r_0^2(2-s)=2a^2`, exactly the null relation (1).

## 3. Why the whole chord is nonpositive

Parameterize the chord and divide its value by the positive factor `r^2/2`.
The resulting polynomial is affine in `beta`:

```text
F_beta(t)=F_0(t)+beta F_1(t),             0<=t<=1.        (4)
```

The radius equation in (2) makes `t=t_0` a double zero for every beta. The
canonical endpoint `F_0` is the square-times-positive certificate proved in
`SexticCanonicalMixedSlice`. At the other endpoint one obtains exactly

```text
F_{beta_*}(t)
 = (239+137s)/407 (t-1)(t-t_0)^2 P(t),                   (5)
```

where

```text
P(t)=-t^3+(4-2s)t^2+(-13/2+10s)t+69/2-17s.
```

The Bernstein coefficients of `P` on `[0,1]` are

```text
69/2-17s,
97/3-41s/3,
63/2-11s,
31-9s.
```

All are positive already from `sqrt(3)<2`. Thus (5) is nonpositive: its only
potentially negative factor is `t-1`, while every other displayed factor is
nonnegative. Finally

```text
F_beta=(1-beta/beta_*)F_0+(beta/beta_*)F_{beta_*},        (6)
```

a convex combination of nonpositive polynomials. This proves the entire
chord at once, with no interval subdivision.

## 4. The terminal ray contact

On the non-real selected ray write `x=r y`, `y>=1`. After division by `r^2/2`
the value is

```text
G_beta(y)=3s beta(2-s)y+y^2-2q(beta)y^6.                 (7)
```

Since `y<=y^2<=y^6`, it is bounded by

```text
y^2[3s beta(2-s)+1-2q(beta)].                            (8)
```

The bracket factors exactly as

```text
(-86/9+17s/3)(beta-beta_*).                              (9)
```

The first factor is positive and `beta<=beta_*`, so the ray is nonpositive.
At `beta=beta_*`, equality first appears at `y=1`; this explains the new
factor `t-1` in (5). Numerically,

```text
beta_*=0.1222778625...,
r_*=0.8746050559...,
c_*=0.1398092336...,
u_*=0.0859673480....
```

## 5. What this closes and what it changes

This is a second exact sextic **zero-contact connector family**, not another
reformulation. It classifies the unique first-order direction invisible at the
four canonical contacts and continues one prescribed zero-contact connector
until that connector acquires an additional ray-endpoint zero.

It is important not to call this an equality edge of the optimized connector
objective. A post-theorem all-pair search found that for every sampled
`beta>0` another adjacent pair, `(0,5)` (and its half-turn), already has a
strictly negative optimized margin; at `beta=beta_*` the sampled margin is
about `-0.00597`. Thus (5) identifies an equality of the constructed
certificate, not a proved obstruction to uniform strict negativity.

The next task is sharper and more favourable: certify that companion strict
connector analytically along the null branch, then use its quantitative slack
in a neighbourhood. The rest of the compact sextic coefficient boundary and
the actual-polynomial remainder transfer remain open.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_sextic_null_branch.py
./repo-python source-provenance://private-authoring-project/scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems/Erdos1041/SexticNullBranch.lean
```
