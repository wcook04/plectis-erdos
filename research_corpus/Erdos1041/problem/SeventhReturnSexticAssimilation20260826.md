# Erdős 1041: seventh-return sextic assimilation

## Outcome

The seventh Type-B return contains two valid connector mechanisms, but its
claimed low-sextic residual uses a theorem for the paired tangent model on a
different, unpaired reciprocal model.  This note preserves the valid content,
strengthens both quantitative branches, and records the exact model-separation
counterexample.

Unrestricted Erdős 1041 is **not** proved.  The result is a smaller exact
sextic producer and a corrected compact residual.

## 1. The models must remain distinct

Let `omega=exp(pi i/3)` and define

```text
L_(A,B,C)(z) = Re(Az+Bz^2+iCz^3-z^6),

P_(A,B,C)(z) = Re(Az+Bz^2+iCz^3-conj(B)z^4-conj(A)z^5-z^6).
```

`L` is the low reciprocal sextic.  `P` is the paired tangent/correction
sextic.  `SexticFirstModeThreeQuarterOverlap.md` concerns `P`, because its ray
identity contains both paired differences `t-t^5` and `t^2-t^4`.

### Proposition A (exact model-separation witness)

At the favourable scalar ray data

```text
A=3/4,  B=1,  C=0,  a=-3/8,  b=1,  t=1/2,
```

the low and paired ray values are respectively

```text
a t+b t^2-t^6 = 3/64 > 0,

a(t-t^5)+b(t^2-t^4)-t^6 = -1/256 < 0.             (S1)
```

Therefore the paired first-mode theorem does not remove the region
`|A|>=3/4` from the low model.  This exactly rejects the return's stated splice,
not either source theorem.

## 2. Strengthened all-amplitude large-Nyquist carrier

Fix `0<=alpha<=1`, assume `|A|<=alpha`, `|B|=1`, and put

```text
T_alpha  = (alpha+sqrt(3))/3,
mu_alpha = 1-T_alpha = (3-alpha-sqrt(3))/3,
K_alpha  = alpha+8.
```

Because `sqrt(3)<2` and `alpha<=1`, `mu_alpha>0`.

### Theorem B (parameterized low-sextic carrier)

If

```text
|C| >= 4(alpha+8)/(3sqrt(3)),                         (S2)
```

then some adjacent sixth-root pair has a complete unit chord and both outward
tails in `{L<=-mu_alpha}`.

### Proof

For `v_k=Re(A omega^k+B omega^(2k))`, fix either parity of adjacent pairs.
If no pair had both endpoints at most `T_alpha`, selecting one bad endpoint
from each of its three disjoint pairs would give a set `k_1,k_2,k_3` with

```text
sum_r v_(k_r) > 3T_alpha = alpha+sqrt(3).             (S3)
```

The eight selections have squared root-of-unity sum passports exactly

```text
(|sum omega^k|^2, |sum omega^(2k)|^2) in {(0,0),(1,3)}.
```

Hence the same sum is at most `|A|+sqrt(3)|B|`, contradicting `(S3)`.
Choose the parity for which the cubic term is nonpositive, as in the return.
Both endpoint values are then at most `T_alpha-1=-mu_alpha`.

On the chord, remove the cubic and call the remaining function `h`.  Since the
chord has unit speed and lies in the unit disk,

```text
|h'| <= |A|+2|B|+6 <= alpha+8=K_alpha.
```

If `d=min(u,1-u)`, the nearer endpoint gives

```text
h(u) <= -mu_alpha+K_alpha d.
```

The favourable cubic is

```text
-|C| (3sqrt(3)/2)u(1-u)
 <= -|C|(3sqrt(3)/4)d
 <= -K_alpha d
```

by `(S2)`.  Thus the whole chord is at most `-mu_alpha`.

On either selected root ray the cubic vanishes and

```text
L(t omega^j)=a t+b t^2-t^6,       t>=1.
```

Its derivative is at most

```text
alpha+2t-6t^5 <= alpha-4t^5 < 0.
```

It therefore decreases from its endpoint value, completing the proof.

### Corollaries

For the entire normalized B-dominant low face, take `alpha=1`:

```text
|A|<=1, |B|=1, |C|>=4sqrt(3)
  => margin (2-sqrt(3))/3.                             (S4)
```

For `alpha=3/4`, the exact threshold is `35/(3sqrt(3))`, strictly below `7`,
and the margin is `3/4-sqrt(3)/3`, strictly above `1/6`.  The return's rational
statement `|C|>=7`, margin `1/6`, follows but is not sharp even within its own
argument.  A convenient rational strengthening is `|C|>=27/4` with the same
`1/6` margin, using `sqrt(3)>=140/81`.

## 3. Strengthened paired two-chart cover

The return's B-dominant paired chart is correct and already follows from
`SexticChordCoveringCriterion.md`:

```text
max(|A|,|B|)=1, |A|<=|B|
  => an adjacent unit chord with margin 1/256.
```

The return also correctly proves that every sixth-root outward tail satisfies

```text
P_(A,B,C)(t xi) <= -t^6/64,       t>=1,                 (S5)
```

because after division by `t^6`, with `s=1/t`, the excess is bounded by

```text
(s-s^5)+(s^2-s^4)-1 <= 47/64+1/4-1=-1/64.
```

In the A-dominant chart, normalization gives `|A|=1`.  The first-mode theorem
requires

```text
0<u<=1/16,       8|C|u^2<=1,       8u^5<=1.
```

Instead of the return's much smaller `u=1/[16(1+|C|)]`, one may take the
maximal simple piecewise scale

```text
u_*(C) = 1/16                         if |C|<=32,
       = 1/sqrt(8|C|)                 if |C|>=32.        (S6)
```

It gives strict chord margin `u_*(C)/48`.  In particular `u=1/64` is valid
through `|C|<=512`, improving the return's cutoff `470` without changing its
margin `1/3072`.

Thus every non-null normalized paired sextic correction is indeed covered,
with stronger A-chart radii than the return states.

## 4. Corrected residual and parent-problem boundary

The all-amplitude Theorem B, not the paired first-mode theorem, removes the
unbounded cubic direction from the normalized low face.  A clean remaining
low-sextic slab is therefore contained in

```text
|B|=1,       |A|<=1,       |C|<4sqrt(3),                (S7)
```

after subtracting all existing strict cells and the already closed `A=0`
phase-circle/cubic-lift plane.  Its closure is compact.  Proving a finite exact
connector cover of `(S7)` would close this sextic low face, but it would still
leave the all-degree primitive odd tied-face grammar and the source-current
nonlinear transfer obligations.

The quantitative reciprocal error implication in the return is valid in its
abstract form: a model margin `mu` survives whenever the certified uniform
error is at most `mu/2`.  It does not supply the absent scalar
discriminant-defect-to-atlas-radius modulus, and no such modulus is claimed
here.

## 5. Claim dispositions

| Returned unit | Disposition |
|---|---|
| paired B-dominant chord margin `1/256` | landed from existing Lean-checked source |
| paired outward tails `-t^6/64` | strengthened-and-landed with exact replay |
| paired A-dominant variable radius | strengthened from `(1+|C|)^-1` to `(S6)` |
| fixed `u=1/64` through `|C|<=470` | strengthened to `|C|<=512` |
| low large-Nyquist theorem at `|A|<=3/4, |C|>=7` | composed into stronger parameterized Theorem B |
| use of paired first-mode theorem on low `L` | rejected exactly by `(S1)` |
| bounded residual `(57)` in the return | superseded by corrected compact slab `(S7)` |
| reciprocal strict-margin transfer | landed as a conditional scalar consumer |
| scalar discriminant-defect conversion | blocked external; no verified producer |
| all-degree odd tied-face grammar | blocked external; remains a parent-level producer |

The exact checker replays the finite selector passports, all displayed rational
constants, the model-separation witness, and the strengthened radius cutoff.
The Lean companion checks the load-bearing scalar cancellations.  Neither is a
formalization of the full complex-analytic selection proof.
