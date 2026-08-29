# Erdős 1041 satellite: the three-point free-point mean inequality (FP3)

Date: 2026-08-29.  Origin: operator-supplied Type B mathematics (this
session's solve thread), proof re-derived and verified in the main loop.
Checker: `scripts/check_erdos1041_free_point_fp3.py`.

Context.  FRONTIER open gap #1 records Conjecture (S)
(`Sigma_k |f(c_k)|^{1/n} <= (n-1) R`, proved for `n = 2, 3` in
`SeparatrixAggregateReduction.md`) and its free-point form: for
`c_1, ..., c_m` in the closed unit disk,

```text
(1/m) Sigma_j ( prod_k |1 - conj(c_j) c_k| )^{1/m}  <=  1.      (FP_m)
```

The two-point case `FP_2` is the free-point ingredient of the landed
`n = 3` proof.  This note proves `FP_3`.

## Theorem (FP3)

For every `c_1, c_2, c_3` in the closed unit disk,

```text
Sigma_{j=1}^{3} ( prod_{k=1}^{3} |1 - conj(c_j) c_k| )^{1/3}  <=  3,
```

with equality if and only if `c_1 = c_2 = c_3 = 0`.

## Proof

Write `x_i = 1 - |c_i|^2 >= 0` and `d_{ij} = |1 - conj(c_i) c_j|`
(symmetric: `1 - conj(c_i) c_j` and `1 - conj(c_j) c_i` are complex
conjugates).  The `j`-th product contains its own diagonal factor
`|1 - |c_j|^2| = x_j`, so

```text
A_1 = x_1 d_{12} d_{13},   A_2 = x_2 d_{12} d_{23},   A_3 = x_3 d_{13} d_{23}.
```

Step 1 (Hölder).  Apply the three-column generalized Hölder inequality to
the columns `(x_1, x_2, x_3)`, `(d_{12}, d_{23}, d_{13})`,
`(d_{13}, d_{12}, d_{23})` — the row products are exactly `A_1, A_2, A_3` —
to get, with `S = Sigma_j A_j^{1/3}`:

```text
S <= (x_1 + x_2 + x_3)^{1/3} (d_{12} + d_{13} + d_{23})^{2/3},
```

hence `S^3 <= (Sigma x)(Sigma d)^2`.

Step 2 (Cauchy–Schwarz).  `(Sigma d)^2 <= 3 (d_{12}^2 + d_{13}^2 +
d_{23}^2)`.

Step 3 (exact identity).  With `Q = Sigma |c_i|^2`,
`E_2 = Sigma_{i<j} |c_i|^2 |c_j|^2`, `s = c_1 + c_2 + c_3`, and
`d_{ij}^2 = 1 - 2 Re(conj(c_i) c_j) + |c_i|^2 |c_j|^2`:

```text
d_{12}^2 + d_{13}^2 + d_{23}^2 = 3 + Q - |s|^2 + E_2,
(3 - Q)(3 + Q - |s|^2 + E_2) = 9 - Delta,
Delta := (Q^2 - 3 E_2) + Q E_2 + (3 - Q)|s|^2.
```

Step 4 (nonnegativity).  `Q^2 - 3 E_2 = (1/2) Sigma_{i<j} (|c_i|^2 -
|c_j|^2)^2 >= 0`; `Q E_2 >= 0`; `(3 - Q)|s|^2 >= 0` since `Q <= 3`.  So
`Delta >= 0` and

```text
S^3 <= 3 (3 - Q)(3 + Q - |s|^2 + E_2) = 3 (9 - Delta) <= 27.
```

Equality.  `S = 3` forces `Delta = 0`: the first term gives equal moduli
`|c_1| = |c_2| = |c_3| = r`; then `Q E_2 = (3 r^2)(3 r^4) = 0` forces
`r = 0`.  (All checks verified numerically in the checker: the identity to
`1e-10`, the Hölder chain, and a 20,000-sample adversarial sweep with
sampled sup `2.99375 < 3`.)  QED

## Claim boundary

`FP_3` is an ordinary proved theorem about three points of the disk.  It is
the `m = 3` case of the free-point form of Conjecture (S).  NO claim is made
here that `FP_3` implies (S) at `n = 4`: the reduction "(S) at degree
`m + 1` follows from `FP_m`" is recorded in the corpus only as the proof
route USED at `n = 2, 3` (psh/torus reduction + the self-inversive torus
identity + `FP_2`), and its general-`n` form has not been checked as a
landed theorem; composing them is the natural next step and should be done
against the original session records of
`SeparatrixAggregateReduction.md`.  (S) itself, even if so obtained, does
not imply the parent theorem.  PRIORITY CAVEAT: no literature search; the
inequality is classical-flavoured; claim "new to this directory" only.
