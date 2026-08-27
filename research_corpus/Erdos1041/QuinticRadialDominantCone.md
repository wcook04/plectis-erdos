# Erdős #1041: the radial-dominant quintic Fourier cone

Status: complete analytic model theorem with exact symbolic replay and a
focused Lean kernel, 2026-08-25. This closes the radial-dominant branch of the
degree-five finite Fourier model. It does not yet transfer the whole staple to
the exact perturbed polynomial, and it does not prove unrestricted Erdős
#1041.

## 1. The theorem

Put

```text
G(z)=-Delta+Re(E_1 z+E_2 z^2+E_3 z^3+E_4 z^4-z^5),       (1)
rho=max(|E_1|^(1/4),|E_2|^(1/3)).                         (2)
```

Assume

```text
0<Delta<=1/4096,                    4 rho^3<=Delta,
|E_3+conj(E_2)|<=2 Delta,           |E_4+conj(E_1)|<=2 Delta.  (3)
```

Then every fifth-root ray `t omega^j`, `0<=t<=1`, satisfies

```text
G(t omega^j)<=-Delta/2.                                  (4)
```

Moreover the whole disk `|z|<=Delta/10` satisfies

```text
G(z)<=-2 Delta/5.                                        (5)
```

Consequently all five truncated arms from `(Delta/10)omega^j` to
`omega^j` are strictly safe, and the chord joining **any** two truncation
points is strictly safe. The radial-dominant model does not merely have a
selector: it has the complete five-spoke staple fan.

## 2. The coefficient cone collapses to one scalar budget

Since `rho<=1`, (2)--(3) give

```text
|E_1|<=rho^4<=rho^3<=Delta/4,
|E_2|<=rho^3<=Delta/4,
|E_3|<=|E_2|+2Delta,
|E_4|<=|E_1|+2Delta.
```

Therefore

```text
|E_1|+|E_2|+|E_3|+|E_4|<=5Delta.                         (6)
```

This is the useful geometry of the inward radial cone: once its mean deficit
dominates the two low Newton scales, every remaining Fourier direction costs
at most five copies of the same deficit.

## 3. The exact ray inequality

Let `s=Delta^(1/4)`, so `s<=1/8`. For `s,t>=0`, the identity

```text
t^5-5s^4 t+4s^5
  =(t-s)^2(t^3+2s t^2+3s^2 t+4s^3)>=0                  (7)
```

is weighted Young's inequality with its equality point exposed. On a fifth
root ray, (6) and `t^m<=t` for `0<=t<=1` give

```text
G(t omega^j)
 <= -Delta+5Delta t-t^5
 <= -Delta+4Delta s
 <= -Delta/2.                                            (8)
```

There is no phase selection and no compactness argument in (8).

## 4. The inner disk

For `u=|z|<=Delta/10`, (6) gives

```text
G(z)<=-Delta+5Delta u+u^5
     <=-Delta+Delta/2+Delta/10
     = -2Delta/5.                                        (9)
```

The second inequality uses `Delta<=1` and `u^5<=u`. A chord between two points
of the disk stays in the disk, proving (5) and the staple assertion.

## 5. Why this is the correct complement to the global atlas

The global mixed atlas treats the transverse branch `Delta<=K rho^3`. The
present theorem treats `4rho^3<=Delta`; choosing `K=4` makes the two model
branches meet without a gap.

Fourier inversion adds another quantitative gain. Including `E_0=-Delta`,
(6) implies

```text
eta=max_k|e_k| <= (Delta+sum_(m=1)^4 |E_m|)/5
                 <= 6Delta/5.                            (10)
```

Thus the nonlinear logarithmic error is quadratic in `Delta`, while (4)--(5)
have a linear `Delta` margin. The remaining finite-polynomial transfer is not
a new mode-selection problem. Its precise obligation is to use the existing
origin/unanchored expansion on the near part of each arm and the regular
factor compactness on the far part, with the `Delta/2` margin absorbing all
coordinate and logarithmic errors.

## 6. Verification and claim boundary

`QuinticRadialDominantCone.lean` checks the factorized Young inequality, the
five-delta coefficient budget, the reduction of four powers to one linear
ray budget, and both explicit margins. The deterministic checker verifies the
factorization exactly over the rationals and stress-tests 400,000 admissible
coefficient/ray/disk samples.

Closed here: the entire radial-dominant degree-five Fourier cone, with explicit
overlap constant `4` and strict margins. Still open: the exact finite transfer,
then the corresponding all-degree mode-envelope theorem. Erdős #1041 remains
open.
