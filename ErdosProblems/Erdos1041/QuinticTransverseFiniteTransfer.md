# Erdős #1041: the full finite near-Fekete theorem in degree five

Status: complete analytic and computer-assisted finite-polynomial theorem,
with exact outward-integer atlas replay and a focused Lean inequality kernel,
2026-08-25. This closes an explicit neighbourhood of the regular pentagon for
actual monic quintics. It does not prove unrestricted Erdős #1041 or any
higher-degree near-Fekete neighbourhood.

## 1. Statement

Let `omega=exp(2 pi i/5)` and

```text
a_k=omega^k(1+e_k),             eta=max_k |e_k|,
f(z)=product_k(z-a_k),           |a_k|<1.                 (1)
```

Use the standard rotational gauge in which

```text
E_0=sum_k e_k=-Delta is real,    Delta>=0,                (2)
```

and put `E_m=sum_k e_k omega^(-km)` and

```text
rho=max(|E_1|^(1/4),|E_2|^(1/3)).                         (3)
```

> **Theorem A (transverse finite transfer).** If
>
> ```text
> 0<rho<=10^(-20),                 Delta<=4rho^3,          (4)
> ```
>
> then two roots of `f` are joined by a polygonal path of length `<2`
> contained in `{|f|<1}`.

Together with `QuinticFinitePerturbationTransfer`, which proves the same
conclusion when `4rho^3<=Delta<=1/4096`, this gives:

> **Corollary B (complete quintic near-Fekete neighbourhood).** Every
> configuration (1)--(3) with
>
> ```text
> rho<=10^(-20),                   Delta<=1/4096           (5)
> ```
>
> has Form A-cut, hence satisfies Erdős #1041.

The case `rho=0<Delta` belongs to the radial branch. The case
`rho=Delta=0` would force every `e_k=0` by radial energy, hence put all roots
on the unit circle and is excluded by (1). In particular the simple
root-coordinate condition

```text
eta<=2*10^(-81)                                             (6)
```

implies (5), because `|E_m|<=5eta` and `Delta<=5eta`. Thus
Corollary B is a genuine open neighbourhood theorem, not an asymptotic
subsequence statement.

## 2. The coefficient and perturbation budgets

Write

```text
A=E_1/rho^4,                 B=E_2/rho^3.                 (7)
```

Then `max(|A|,|B|)=1`. Pairing and Fourier inversion give

```text
|E_3+conj(E_2)|<=2Delta,     |E_4+conj(E_1)|<=2Delta,
eta<=Delta+(2/5)(|E_1|+|E_2|)<=(24/5)rho^3.               (8)
```

At `z=rho zeta`, the finite Fourier polynomial divided by `rho^5` is

```text
Re(A zeta+B zeta^2-zeta^5)
 -rho Re(conj(B)zeta^3)-rho^3 Re(conj(A)zeta^4)
 + pairing defects.                                         (9)
```

On `|zeta|<=10`, (8), the angular bound
`|a_k/|a_k|-omega^k|<=3eta`, and the explicit logarithmic estimate of
`FormACutQuantitativeExpansion` give the deliberately coarse bound

```text
|finite expression - mixed model - paired cubic|
   <=10^6 rho                                                   (10)
```

away from the equality chart. Here is the complete accounting behind the
round constant: the paired cubic costs at most `10^3 rho`; its radial defect
costs at most `8*10^3 rho`; the fourth mode costs at most
`10^4 rho^3+8*10^4 rho^2`; angular displacement costs less than
`8*10^6 rho^3`; the `M=4` logarithmic budget contributes less than
`116rho+5*10^6rho^3+10^10rho^5`. For `rho<=10^(-20)` their sum is below the
right side of (10). The negative constant `E_0=-Delta` has only been discarded.

The exact atlas replay is strengthened here from strict sign to the common
rational margin

```text
mixed-model chord, ray endpoint, and ray-drop slack >=10^(-8). (11)
```

All 3,834 strict boxes pass (11) with outward integer scale `10^24`. Since
`10^6rho<=10^(-14)`, (10) is absorbed with six decimal orders to spare.

## 3. Why the equality chart is now uniform

Only the 81 boxes in the equality ball can have zero mixed-model margin. Put

```text
delta=(|A-A_*|^2+tau^2)^(1/2)<=17/2500.                  (12)
```

The old tetrahedron and its exact chord calculation give

```text
model contact <=-(59/1000)delta+8delta^2.                 (13)
```

The new `QuinticEqualityCubicExtension` says that, after adding the paired
cubic, one of the four contacts instead has first variation at most

```text
-12rho y^3 < -rho/4.                                     (14)
```

The last inequality is exact interval arithmetic at scale `10^24`; in fact
`12y^3=3/10` in this chart.

There is one subtlety: the defects in the tangent-pairing identities must not
be estimated by `Delta<=4rho^3` at equality, because that would be only
`O(rho)`. Split instead:

```text
Delta>=10eta^2:  log|f(0)|<=-Delta+(5/2)eta^2
                 absorbs every pairing defect;

Delta<10eta^2:   Delta<230.4rho^6, so the normalized
                 third-mode defect is O(rho^4).           (15)
```

After this split, the origin-anchored nonlinear error is `O(rho^2)`, not
`O(rho)`. Including the change from `B` to the equality value, all non-model
terms on the selected equality connector obey

```text
remainder <=10^6(rho delta+rho^2).                        (16)
```

Now divide the corner without a transition gap:

```text
delta>=10^9rho:
  (13)+(paired and finite error)
  <=[-59/1000+8(17/2500)+1/1000]delta<0;

delta<10^9rho:
  (14)+(13's quadratic part)+(16)
  <-rho/4+8*10^18rho^2+10^15rho^2+10^6rho^2<0.           (17)
```

The final inequality uses `rho<=10^(-20)`. This is the quantitative stability
arrow that was previously missing: the cubic barycentre handles the tangent
core, while the old tetrahedron handles its complement.

## 4. Completing the actual root arms

The atlas controls each selected arm from its truncation radius through
`t=10rho`. For the intermediate interval `10rho<=t<=1/2`, absolute Fourier
bounds already give

```text
Q_4(t a_j/|a_j|)<=-(998/1000)t^5.                         (18)
```

The three terms of the explicit `B_4(t,eta)` remainder use less than
`t^5/50`: the baseline logarithm costs at most `t^5/62`, and the Fourier tail
and quadratic logarithmic term are smaller by (4), (8). Hence `log|f|<0` on
this interval.

For `t>=1/2`, the factorwise telescoping estimate from the radial transfer is

```text
|f(t a_j/|a_j|)|<=1-t^5+95eta<1,                          (19)
```

because `95eta<1/32<=t^5`. Thus both selected arms reach their actual roots.
The certified connector joins their truncation points, and
`TruncatedSpokeReduction` gives total length `<2`.

## 5. Verification and claim boundary

The checker regenerates the complete atlas, replays every accepted box with
outward integers, requires the stronger margin (11), and checks every rational
absorption in (17)--(19). Lean proves the higher-mode sparse-ray implication,
the two equality absorptions, the intermediate-ray budget, and the exact
assembly of the radial/transverse dichotomy.

Closed here: the full finite near-Fekete neighbourhood for actual monic
quintics. Still open: configurations outside this neighbourhood and the
corresponding finite mode-envelope transfer in degrees at least six. Therefore
unrestricted Erdős #1041 remains open.
