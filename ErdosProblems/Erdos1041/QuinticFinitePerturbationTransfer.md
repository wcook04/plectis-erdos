# Erdős #1041: finite transfer of the radial-dominant quintic cone

Status: complete analytic finite-polynomial theorem for the radial-dominant
near-Fekete branch, with deterministic actual-polynomial replay and a focused
Lean inequality kernel, 2026-08-25. This proves Form A-cut for this branch of
actual monic quintics. The transverse atlas branch and unrestricted Erdős
#1041 remain open.

## 1. Statement

Let `omega=exp(2 pi i/5)` and

```text
a_k=omega^k(1+e_k),              eta=max_k |e_k|,
f(z)=product_k(z-a_k),            |a_k|<=1.               (1)
```

Rotate once so that

```text
E_0=sum_k e_k=-Delta is real,     Delta>0,                (2)
```

and put `E_m=sum_k e_k omega^(-km)` and
`rho=max(|E_1|^(1/4),|E_2|^(1/3))`. Assume

```text
Delta<=1/4096,                    4rho^3<=Delta.           (3)
```

Then every root ray is contained from radius `Delta/10` outward:

```text
|f(t a_j/|a_j|)|<1,       Delta/10<=t<=|a_j|.             (4)
```

The whole disk `|z|<=Delta/10` is also contained in `{|f|<1}`. Hence any two
distinct roots, their two truncated arms, and the joining chord give Form
A-cut. By `TruncatedSpokeReduction`, the desired path has length `<2`.

This is an actual-polynomial theorem, not a leading-order statement.

## 2. Cone consequences

The disk constraint gives the exact pair bounds

```text
|E_3+conj(E_2)|<=2Delta,       |E_4+conj(E_1)|<=2Delta.   (5)
```

`QuinticRadialDominantCone` therefore gives

```text
sum_(m=1)^4 |E_m|<=5Delta.                                (6)
```

Fourier inversion, including `E_0=-Delta`, gives the crucial finite estimate

```text
eta<=(Delta+sum_(m=1)^4|E_m|)/5<=6Delta/5.               (7)
```

In particular `eta<1/3`, every root modulus exceeds `1-eta>1/2`, and the near
and far arm intervals below overlap.

## 3. The near half of every arm

Put `u_j=a_j/|a_j|`, `z=t u_j`, `0<=t<=1/2`, and

```text
N(z)=sum_(m=1)^4 E_m z^m-Delta z^5,
P(z)=N(z)/(1-z^5).                                       (8)
```

The exact anchored expansion from `FormACutQuantitativeExpansion` is

```text
log|f(z)|=log|f(0)|+log|1-z^5|+Re P(z)+R(z).              (9)
```

Every error in (9) has an explicit budget:

```text
log|f(0)| <= -Delta+(5/2)eta^2,                           (10)
log|1-z^5| <= -t^5+4eta^2,                               (11)
|P(z)-N(z)| <= Delta/10,                                  (12)
|R(z)| <= 20eta^2.                                        (13)
```

For (10), use `log(1+x)<=x` on
`|1+e_k|^2=1+2Re(e_k)+|e_k|^2`. For (11),
`|u_j-omega^j|<=2eta/(1-eta)<=3eta`, whence
`|u_j^5-1|<=15eta`; the exact identity

```text
|1-xv|^2=(1-x)^2+x|1-v|^2,       x=t^5, |v|=1,           (14)
```

then leaves less than `4eta^2`. For (12),

```text
|N|<=5Delta t+Delta t^5<=81Delta/32,
|z|^5/(1-|z|^5)<=1/31,
81/992<1/10.                                               (15)
```

Finally (13) is the anchored logarithmic remainder with
`alpha=eta/(1-t)<=2eta<1/2`.

The extra term `-Delta Re(z^5)` inside `N` is nonpositive because
`Re(u_j^5)>0`. The radial-cone Young inequality therefore supplies the core
bound `-Delta/2`. Combining (7) and (10)--(13),

```text
log|f(tu_j)|
 <= -Delta/2+Delta/10+(53/2)eta^2
 <  -3Delta/8.                                            (16)
```

This proves (4) for `t<=1/2` with a quantified strict margin.

## 4. The far half needs no logarithmic expansion

For `|z|<=1`, telescoping the five factors gives

```text
|f(z)-(z^5-1)|<=5 eta 2^4=80eta.                          (17)
```

On the actual root direction, `|u_j^5-1|<=15eta`; hence

```text
|f(tu_j)|<=1-t^5+95eta.                                  (18)
```

When `t>=1/2`, (3) and (7) give

```text
95eta<=57/2048<1/32<=t^5.                                (19)
```

Thus (18) is strictly below one on the entire far half, including every root
endpoint. No compactness or unnamed neighbourhood is used.

## 5. The connector disk

For `u=|z|<=Delta/10`, use (9) without selecting a phase. The estimates

```text
log|f(0)|<=-Delta+(5/2)eta^2,
log|1-z^5|<=u^5<=u,
|P(z)|<=(20/3)Delta u,
|R(z)|<=20eta^2 u                                         (20)
```

and (7) give

```text
log|f(z)| < -3Delta/4.                                   (21)
```

The chord between any two points `(Delta/10)u_i` lies in this convex disk.
Together with §§3--4, this proves the theorem.

## 6. Verification and next handoff

The checker generates 1,000 actual inward quintic perturbations across twelve
orders of magnitude, verifies (3), and evaluates all five complete root arms
and ten truncation chords on a dense adversarial mesh. This is regression
evidence; the proof is (5)--(21). Lean checks the two absorption inequalities,
the far-half rational margin, the fifth-power lower bound, and the Fourier
inversion budget.

Closed here: the exact radial-dominant near-Fekete branch for degree five.
Still open: transfer the transverse global atlas, especially its unique
zero-margin equality orbit, through the paired cubic correction; then overlap
the resulting degree-five neighbourhood with the non-near-Fekete regime.
Erdős #1041 remains open.
