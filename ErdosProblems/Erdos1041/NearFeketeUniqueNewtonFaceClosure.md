# Erdős #1041: every monotone unique Newton face closes along its analytic arc

Status: ordinary analytic theorem, exact valuation replay, and Lean-checked
integer/absorption kernel, 2026-08-25. This closes every tangent analytic
approach whose first nonzero polynomial degree is also the unique outer Newton
face. It does **not** close tied faces, face switches caused by a lower-degree
mode, the bulk away from the Fekete stratum, or unrestricted Erdős #1041.

## 1. Statement

Fix `n>=5`, `omega=exp(2 pi i/n)`, and a real-analytic arc of root
configurations

```text
a_j(eps)=omega^j(1+e_j(eps)),       |a_j(eps)|<1,       eps -> 0+.
```

Put `E_k(eps)=sum_j e_j(eps) omega^(-jk)`.  Discard coefficients which vanish
identically, and write

```text
E_k(eps)=eps^(q_k)(A_k+o(1)),        A_k != 0, q_k in N.
```

The balance radius of mode `k` is `eps^(q_k/(n-k))`.  Suppose:

1. `E_k` vanishes identically for `k<m`, `m<n/2`, and mode `m` uniquely
   minimizes `q_k/(n-k)` among the nonzero tangent modes after complementary
   high modes have been paired with their low modes;
2. the radial deficit `Delta=-Re E_0` and the anchored nonlinear error are
   higher order at this balance scale (the tangent case).

> **Monotone unique-Newton-face closure theorem.** Along this analytic arc, for all
> sufficiently small positive `eps`, two roots are joined inside `{|f|<1}` by
> a path of length `<2`. Hence Erdős #1041 holds eventually on the arc.

This includes arbitrary tangent order: `E_1`, then `E_2`, and so on may vanish
identically, and `E_m` may itself vanish to any finite order in `eps`. The
hypothesis is not “the first coefficient is bounded away from zero”; it is that
the first nonzero polynomial degree is also the one-vertex outer Newton face.

## 2. Why a unique face has a literal power gap

Let `q=q_m` and `d=n-m`. Reparameterize

```text
eps=u^d,             z=u^q zeta.                            (1)
```

The active term and the baseline have the common `u`-weight

```text
eps^q z^m  ~ u^(dq+qm)=u^(nq),       z^n=u^(nq) zeta^n.    (2)
```

Mode `k` has weight

```text
w_k=d q_k+q k.                                             (3)
```

Uniqueness of the Newton slope is exactly

```text
q(n-k)<q_k(n-m),
```

and therefore

```text
w_k-nq=q_k(n-m)-q(n-k)>=1.                                (4)
```

Thus every competitor is not merely `o(1)` by an unnamed compactness
argument: it factors exactly as

```text
u^w_k=u^(nq) u^gap_k,            gap_k>=1.                 (5)
```

`NearFeketeUniqueNewtonFaceClosure.lean` proves (4), (5), and the final strict
margin absorption. The checker audits the cross multiplication and exact power
ratios through degree 80 and rejects deliberately tied controls.

## 3. The limiting selector

Divide the origin-anchored logarithmic expansion by `u^(nq)`. On every compact
`zeta`-set, (5), the tangent pairing identity, and the anchored
`O(eta^2|z|)` estimate give

```text
u^(-nq) log|f(u^q zeta)|
  = Re(A_m zeta^m-zeta^n)+o(1).                            (6)
```

The restriction `m<=n/2` is precisely what makes the anchored quadratic term
higher order. A dominant high mode cannot create a new tangent face: its
complementary low mode has the same valuation to leading order and the larger
outer balance radius. The only self-paired case is `m=n/2`, already covered by
the exact Nyquist factorization.

Because `m<n/2` and `n>=5`, the phase orbit contains two distinct directions
strictly inside the negative half-plane. Indeed, put `d=gcd(n,m)` and `Q=n/d`.
The `Q` phase values each occur `d` times. If `Q>=5`, every open semicircle
contains at least two of them. If `Q=3` or `4`, it contains at least one and
`m<n/2`, `n>=5` force `d>=2`, so that value occurs on at least two root rays.
The case `Q=2` is exactly the excluded self-paired index `m=n/2`. Thus
`FormACutFirstNonzeroMode` may be sharpened here to choose two distinct
`n`-th-root directions
with

```text
Re(A_m omega^(mj))<0.
```

On either selected ray the model is

```text
t^m Re(A_m omega^(mj))-t^n <= -t^n<0       (t>0).          (7)
```

The crucial extra point is `k>m` for every competitor. Near the hub the strict
negative `m`-term dominates all higher `zeta`-powers; outward, the strict
`-t^n` term dominates. Formula (5) absorbs the competitors in the compact
middle range. This is exactly why a merely unique *outer* face, with a dormant
lower-degree mode, is not claimed.

## 4. Matching the three radial ranges

The transfer is the same two-cutoff argument as the transverse theorem, with
the integer gap replacing its fixed `|h'(0)|>=eta` cone.

* **Inner hub.** The exact negative constant `log|f(0)|` supplies a small safe
  disk. Outside it, every competitor has degree `k>m`, so the strictly negative
  active `m`-term controls until the fixed Newton annulus begins.
* **Newton annulus.** On `c<=|zeta|<=C`, (6) is uniform along the fixed arc;
  half of the model margin in (7) survives.
* **Outer matching region.** For `C u^q<=|z|<=R/2`, the degree-`n` term
  dominates because every lower mode has either the active balance already
  passed or a positive weight gap. The two selected actual root directions
  converge to their regular radial directions.
* **Root collar.** On every fixed radial annulus away from zero, the regular
  comparison is `|t^n-R^n|<=1-t^n<1`, with a uniform positive margin at its
  inner radius. Coefficient and root-direction continuity therefore carries
  the two straight arms all the way to their actual roots, where `f=0`.

The two straight root rays meet at the origin through the safe inner disk.
Their total length is the sum of the two root moduli, hence strictly below `2`.
This proves the theorem.

## 5. What this changes

The transition problem is no longer “infinitely many vanishing first modes.”
Every analytic tangent arc whose first polynomial mode is its one-vertex outer
Newton face is closed, regardless of how high its vanishing order is. The
surviving near-Fekete obstruction consists of the exact resonant set

```text
q_j/(n-j)=q_k/(n-k)     for at least two low modes j!=k.   (8)
```

plus face switches in which a lower polynomial degree is not the outer winner.
The ties are real: `q_j=c(n-j)` makes any chosen collection of modes share a
face. They cannot be dismissed by genericity. In degree five the existing
global mixed atlas already closes the tied/face-switching model; in degree six
the remaining compact mixed band is the first unclosed instance.

## 6. Claim boundary and exact handoff

Proved here: eventual Erdős #1041 along every tangent real-analytic near-Fekete
arc whose first nonzero polynomial degree `m<n/2` is also the unique outer
Newton face, including arbitrary coefficient-valuation order. Lean proves the
exact valuation separation and strict absorption kernel; the finite-dimensional
analytic matching is an ordinary proof, as in `NearFeketeTransverseClosure`.

Not proved: tied faces (8), face-switching Newton polygons, the self-paired
Nyquist boundary, a uniform neighbourhood containing those strata, the
away-from-Fekete regime, or unrestricted Erdős #1041.

The next owner should attack the first **tied** face, not “small first mode” in
general: normalize all active coefficients on one rational Newton face, prove a
finite connector theorem for that compact model, and use the positive integer
gaps (5) to transfer it to the actual polynomial.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_near_fekete_unique_newton_face.py
```
