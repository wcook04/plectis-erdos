# Erdős 1041: exact two-hub compression on a simple saddle wall

Date: 2026-08-30. Status: ordinary exact wall-stratum reduction. Companion:
`AdmissibleCriticalArcProductPshReduction.md`. Deterministic exact replay:
`scripts/check_erdos1041_saddle_wall_pair_compression.py`.

This note does **not** prove the admissible critical-arc product or Erdős
1041. It replaces the first simple saddle-wall obligation left by the
cellwise plurisubharmonic reduction with one scalar three-arm estimate.

## 1. The simple wall normal form

Let `c` and `d` be simple critical points with nonzero critical values on the
same descending value ray,

```text
w_c = f(c) = t f(d) = t w_d,       0 < t < 1,
```

and suppose the lift from `d` meets `c`, with no further critical point on the
open value segments involved. Let the two descending arms from `c` have
lengths `A,B>0`. Let `S>0` be the saddle-connection length from `d` to `c`,
and let `C>0` be the other descending arm from `d`. Put

```text
X = S+C,                 T = A+B+X.
```

At the wall the lower hub gives the root-to-root arc of length

```text
L_c = A+B.
```

The upper lift can continue through either outgoing branch of `c`, giving two
contained root-to-root arcs

```text
L_d^A = X+A,             L_d^B = X+B.
```

All three arcs lie below the appropriate critical level: the lower one below
`|w_c|`, and both upper choices below `|w_d|`. This is the standard arm
decomposition on a simple Newton saddle wall recorded in
`SeparatrixAggregateReduction.md`.

## 2. Exact pair compression

> **Theorem (short-side wall compression).** In the setup above,
>
> ```text
> L_c min(L_d^A,L_d^B) <= T^2/2.                         (SW1)
> ```
>
> More precisely,
>
> ```text
> T^2/2 - L_c min(L_d^A,L_d^B)
>   = [X^2+(A+B)|A-B|]/2.                               (SW2)
> ```
>
> The two one-sided continuations also obey
>
> ```text
> L_c sqrt(L_d^A L_d^B) <= T^2/2.                       (SW3)
> ```

### Proof

Assume `A<=B`; the other case is symmetric. Then the shorter upper
continuation is `X+A`, and direct expansion gives

```text
(A+B+X)^2/2 - (A+B)(X+A)
  = [X^2+(A+B)(B-A)]/2,
```

which proves `(SW1)` and `(SW2)`. For the two-sided statement,

```text
(X+(A+B)/2)^2-(X+A)(X+B)=(A-B)^2/4,
```

so `sqrt((X+A)(X+B))<=X+(A+B)/2`. Multiplying by `A+B` and using

```text
T^2/2-(A+B)(X+(A+B)/2)=X^2/2
```

proves `(SW3)`. `[]`

The short-side inequality is strict for a genuine two-saddle wall because
`S>0`, hence `X>0`. Equality in the abstract nonnegative-length model occurs
only at `X=0` and `A=B`.

## 3. Normalized admissible-product consumer

Write

```text
beta  = |w_c|,
gamma = |w_d|,
q_c   = L_c/(2 beta^(1/n)),
q_d   = min(L_d^A,L_d^B)/(2 gamma^(1/n)).
```

Then `(SW1)` gives the exact normalized estimate

```text
q_c q_d <= T^2 / [8 (beta gamma)^(1/n)].                 (SW4)
```

Consequently the single scalar certificate

```text
T <= 2 sqrt(2) (beta gamma)^(1/(2n))                     (SWC)
```

closes the product of the two wall factors. If all other admissible factors
already have product at most one, `(SWC)` closes the complete admissible
product on that wall. More generally, `(SW4)` is the exact factor to insert
into an open merger block: it consumes the branch switch without choosing a
one-sided continuation in advance.

The total-length certificate `(SWC)` is sufficient but **not universal**.
`SymmetricTwoLevelWallFamily.md` gives the actual quartic saddle wall

```text
f(z)=(z^2-a^2)(z^2+b^2),       a>b>0,
```

for which `A=B=b`, `X=a`.  At `b/a=9/10`, `(SWC)` fails by the exact
fourth-power gap `5836/625`, while the true normalized lower/upper product
has square `3249/3620<1`.  Thus discarding the `X^2` slack in `(SW2)` loses
the theorem even on a highly structured polynomial wall.

Retaining the exact slack gives the correct shape-sensitive certificate

```text
T^2-X^2-(A+B)|A-B| <= 8 (beta gamma)^(1/n).             (SWC*)
```

By `(SW2)`, `(SWC*)` is exactly equivalent to `q_c q_d<=1`; unlike `(SWC)`,
it is not an additional strengthening of the wall block.

This is stronger than treating the two hubs independently. The lower arm
imbalance `|A-B|` and the genuine connection remainder `X` both become
explicit nonnegative slack in `(SW2)`.

## 4. What computation says on the first terminal family

The degree-five unit-circle probe attached to the psh reduction was expanded
to 200 deterministic rows. It found individual normalized merge factors as
large as `7.196625065273`, so no nodewise wall/graft bound is viable. Yet all
complete rooted subtree products and all hybrid Bergman-majorized subtree
products stayed below one; the largest hybrid value was
`0.979480920246`. Every one of the 55 positive graft debts was paid by
measured descendant slack. Eight rows had an uncertified virtual-cut cherry,
the largest measured factor being `0.916272979437`.

A separate 400-row unit-circle quintic search refuted the even stronger
factorwise direct claim `L(c)<=2|f(c)|^(1/5)`: 23 rows crossed one, with
maximum `1.080356937850`. Its full admissible product was only
`0.035847279817`. Thus the exact wall compression has the right allocation
shape: local overspend is real, and compensation must remain attached to the
three-arm subtree. These figures are floating-point falsifier evidence, not
part of the proof of `(SW1)`--`(SW4)`.

## 5. Claim boundary and next exact target

Proved here: the simple-wall arm decomposition consumer `(SW1)`--`(SW4)`, the
sufficient scalar threshold `(SWC)`, and the exact shape-sensitive equivalent
`(SWC*)`. Imported: the Newton inverse-ray arm decomposition and the target
sufficiency of the admissible product.

Now refuted: universal `(SWC)` for polynomial walls. Not proved: `(SWC*)` on
general polynomial walls; control of longer saddle spines; the product of the
remaining admissible factors; either one-sided cell limit away from the wall;
the admissibility/root-boundary/collision strata; degree five; or unrestricted
Erdős 1041.

The sharpened wall target is now shape-sensitive: prove `(SWC*)` while
retaining the stem and arm-imbalance slack, or close the complete rooted merger
block directly. `PartialClusterPreimagePerimeterIdentity.md` remains the
closest geometric consumer because it controls a stem forest plus a lifted
boundary perimeter, but any transfer that collapses those data to `T` alone
is now known to lose too much.
