# Erdős 1041: exact cubic scaling at three-exterior speed saturation

## Theorem

Fix `n>3`, put

```text
p_0=(n-3)/(n+3),
L_n(p,q)=-n log q+log(q^3-p)-log(1-pq^3),              (1)
```

and let `R_n(p)=exp(max_q L_n(p,q))` be the regular three-exterior
comparator.  As `p` increases to `p_0`, write

```text
delta=p_0-p,             q=1-sqrt(delta) X.            (2)
```

Then, uniformly for `X` in every fixed compact subset of `[0,infinity)`,

```text
L_n(p_0-delta,1-sqrt(delta)X)/delta^(3/2)
  --> G_n(X),

G_n(X)=A_n X-(C_n/6)X^3,                              (3)
A_n=(n+3)^2/6,
C_n=n(n-3)(n+3)/2.                                    (4)
```

The cubic has a unique positive maximizer

```text
X_n=sqrt(2A_n/C_n)
   =sqrt(2(n+3)/(3n(n-3))),                            (5)
```

and maximum

```text
K_n=G_n(X_n)=(2/3)A_n X_n
   =(n+3)^2 X_n/9.                                    (6)
```

Consequently the regular interior optimizer `q_n(p)` satisfies

```text
(1-q_n(p))/sqrt(p_0-p) --> X_n,                        (7)
log R_n(p)/(p_0-p)^(3/2) --> K_n.                      (8)
```

In the two active degrees this is

```text
n=5: X_5=4/sqrt(30),       K_5=256/(9sqrt(30)),
n=6: X_6=1/sqrt(3),        K_6=3sqrt(3).               (9)
```

## Proof

Direct differentiation of (1) at the saturation corner gives

```text
L_q(p_0,1)=L_qq(p_0,1)=0,
L_qqq(p_0,1)=C_n,
partial_p L_q(p_0,1)=A_n,                              (10)
L_qqqq(p_0,1)=-3n(n-3)(n+3).                          (11)
```

Taylor's theorem on a fixed compact `X`-interval, with
`p-p_0=-delta` and `q-1=-sqrt(delta)X`, gives

```text
L_n=A_n delta^(3/2)X-(C_n/6)delta^(3/2)X^3+O(delta^2), (12)
```

uniformly there.  This is (3).

For `p<p_0`, the regular profile has its unique maximum at an interior
stationary point and that point tends to one as `p` tends to `p_0`.  Dividing
the stationary equation `L_q=0` by `delta` after (2) gives

```text
0=-A_n+(C_n/2)X^2+O(sqrt(delta)).                      (13)
```

The positive solution therefore converges to (5).  Substitution in (3)
proves (8); at `C_n X_n^2=2A_n`, the cubic value is `(2/3)A_nX_n`, proving
(6).  The simplifications in (9) are exact.

## Frontier consequence

The saturation endpoint is cubic, not quadratically nondegenerate.  Its ray
displacement is of order `sqrt(p_0-p)` and its comparator excess is of order
`(p_0-p)^(3/2)`.  The quantitative Clark theorem
`ThreeExteriorQuantitativeSaturationStability.md` puts every admissible zero
configuration within `O(sqrt(p_0-p))` of the regular endpoint triangle.
Therefore the terminal selector problem has one exact compact blow-up:

```text
zero displacement / sqrt(delta),
(1-q)/sqrt(delta),
optimized log-barrier / delta^(3/2).                   (14)
```

A terminal proof must compare the limiting attached-ray cubic on the bounded
transverse set supplied by Clark stability with `K_n`.  Ordinary pointwise
continuity cannot do this because the transverse and ray variables live on
the same `sqrt(delta)` scale.  This theorem identifies that compact limiting
inequality; it does not prove the inequality, exclude finite nonregular KKT
contacts, prove the all-capacity selector, or prove unrestricted Erdős 1041.

## Replay

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_regular_saturation_cubic.py
```

The checker verifies (10)--(13), the exact cubic, its optimizer, and both
degree specializations symbolically.

```text
tao_pipeline_receipt:
  input_stage: quantitative saturation stability plus degenerating finite regular selector
  output_stage: exact endpoint blow-up reduction
  artifact: ThreeExteriorRegularSaturationCubicScaling.md plus symbolic checker
  human_understanding_delta: the missing endpoint collar is a compact cubic problem on sqrt-deficit scaled ray and zero displacements; the comparator margin is delta^(3/2)
  verification_state: ordinary Taylor/optimizer proof with exact symbolic replay
  publication_or_review_state: source-level research reduction, not independently reviewed
  canonicalization_state: saturation compactification in the finite three-exterior adaptive-selector family
  unresolved_downstream_bottleneck: prove the limiting attached-ray cubic selector on the Clark-bounded transverse set
  next_stage_owner: terminal three-exterior saturation selector lane
```
