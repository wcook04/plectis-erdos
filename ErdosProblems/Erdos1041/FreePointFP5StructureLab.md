# Erdős 1041: the FP_5 structure lab — no violation, the perturbed-star extremal family, an exact ray law, and a PROVED all-degree rowwise certificate (ROWCERT+) that leaves only a crude outer case

Date: 2026-08-30.  Origin: wave-1 opus free-point agent (2e6 random
multistarts + 9 structured DE charts + 3,720 corner-seeded ascents,
50–60 dps verification of every leader; instrument validated by
reproducing the corpus's PM_6 counterexample value 7.251556), plus
main-loop verification of the certificate proof chain.  Checker:
`scripts/check_erdos1041_fp5_structure_lab.py`.  Consumes
`FreePointMeanInequalityFP3.md`, `FreePointZeroInsertionFP4Matching.md`,
`FreePointTorusPshReduction.md`, FRONTIER §4.1.  Sections 2–3 are
PROVED mathematics (checker-replayed ingredients); the rest is measured
structure.

Objects: `c_1..c_m` in the closed unit disk, `d_jk = |1 - conj(c_j)
c_k|`, row means `h_j = (1/m) sum_k log d_jk`, rows `e^{h_j}`,
`S_m = sum_j e^{h_j}`, `G_m = S_m/m`; FP_m asserts `G_m <= 1` with
equality only at `c = 0`.  Write `rho_j = |c_j|`,
`L_j = -log(1 - rho_j^2)`, `E = -sum_j h_j`.

## 1. Verdict and the extremal family (measured)

- NO violation: every search converges to `c = 0`; `sup G_5 = 1`; zero
  configs above `1 + 1e-12` (50-dps polish of the top-14).  Same at
  `m = 6, 7, 8`.
- The sphere profile `g(R) = max{G_5 : max_j rho_j = R}` is strictly
  decreasing: `1 - g(R) = 1.05e-6, 1.34e-4, 2.53e-3, 2.18e-2, 1.41e-1`
  at `R = 0.3, 0.5, 0.7, 0.9, 0.9999`; `1 - g ~ R^{10}` for small `R`.
- The maximiser is NOT the 5-star: it is a mirror-symmetric `1+2+2`
  modulus-GRADED, angle-SPREAD star `c = R(1, a e^{+-iA}, b e^{+-iB})`
  — at `R = 0.9`: moduli `(1, .728, .728, .677, .677)`, angles
  `+-0.4281 pi, +-0.8101 pi`; it beats the exact star by `0.0603` in
  `G` there (checker F8).  The same family is the maximiser for every
  `m <= 8` tested and for the root-free PM_5 functional.  The margin
  `1 - g_m(0.9)` SHRINKS with `m`: `2.18e-2, 1.28e-2, 7.9e-3, 5.1e-3`
  at `m = 5..8` (all-`m` uniformity must beat a vanishing margin).

## 2. Exact ray law and Hessian (proved; checker F1–F2)

With `u` a unit direction and power sums `q_r(u) = sum_j u_j^r`:

```text
G_m(t u) - 1 = -(1/m^2) sum_{r >= 1} t^{2r} |q_r(u)|^2 / r + O(t^{4 r_0}),
```

`r_0` the first `r` with `q_r != 0`.  In particular the Hessian of
`G_m` at `0` has the exact `t^2` coefficient `-|sum_j u_j|^2/m^2`:
eigenvalues `-2/m` (twice) and `0` (`2m - 2` times), i.e. signature
`(0, 2, 2m-2)` with kernel the balanced hyperplane `sum u_j = 0`.
Newton's identities force `r_0 <= m`, attained only by the exact
`m`-star, whose whole ray is exactly

```text
G_m(R omega^j) = (1 - u^m)^{1/m},   u = R^2               (checker F1).
```

Second-order flatness is maximal exactly on balanced configurations —
the reason naive Hessian arguments cannot close FP_m, and the reason
the extremal family lives in the balanced cone.

## 3. THEOREM (ROWCERT+, all degrees): a proved modulus-only certificate

Define `Phi` by `e^h = 1 + h + Phi(h) h^2` (`Phi(h) = (e^h - 1 - h)/h^2`,
increasing on `R`), and the modulus-only row ceiling

```text
H_j = (1/m) [ log(1 - rho_j^2) + sum_{k != j} log(1 + rho_j rho_k) ].
```

> **Theorem.**  If `(1/m) sum_j Phi(H_j) L_j <= 1` then `S_m <= m`,
> i.e. FP_m holds at `c`.

Proof.  (i) Identity: `S_m = m - E + sum_j Psi(h_j)` with
`Psi(h) = e^h - 1 - h = Phi(h) h^2 >= 0`.  (ii) Row ceiling:
`d_jj = 1 - rho_j^2` exactly and `d_jk <= 1 + rho_j rho_k` (triangle
inequality), so `h_j <= H_j`; since `Phi` is increasing,
`Psi(h_j) <= Phi(H_j) h_j^2`.  (iii) Fourier Cauchy–Schwarz: from
`log d_jk = -sum_r Re((conj(c_j) c_k)^r)/r`,

```text
h_j = -(1/m) sum_r Re(conj(c_j)^r p_r)/r,   p_r = sum_k c_k^r,
E   =  (1/m) sum_r |p_r|^2 / r,
```

and Cauchy–Schwarz with weights `1/r` gives
`h_j^2 <= (1/m^2)(sum_r rho_j^{2r}/r)(sum_r |p_r|^2/r) = (E/m) L_j`.
(iv) Chain: `sum_j Psi(h_j) <= (E/m) sum_j Phi(H_j) L_j <= E`, hence
`S_m <= m - E + E = m`.  ∎

This is the per-point sharpening of the FP_4 note's §3.1 envelope: only
the ONE-SIDED bound `h_j <= H_j` is needed, so the two-sided `M_j` of
the old rowwise route is replaced by the sharp `H_j`.  Quantitatively
(checker F5):

- uniform central radius (all-equal moduli threshold): `rho_* =`
  `0.943806 (m=3), 0.931680 (m=4), 0.924452 (m=5), 0.919669 (m=6),`
  `0.903233 (m=20)`, decreasing to the `m -> infty` limit
  `rho_infty = 0.896360263099` — the root of
  `(s - log(1+s)) log(1/(1-s)) = log^2(1+s)`, `s = rho^2 =`
  `0.803461721264`.  The old two-sided ROWCERT gives `0.845773` at
  every `m`: the certificate radius improves by `+0.05` UNIFORMLY IN
  `m`, and sampled coverage rises `73.3% -> 95.9%`.
- Residual weakness is quantified exactly: on the set where ROWCERT+
  fails, `sup G_m = (1 - rho_c^{2m})^{1/m}` at the `m`-star at its
  critical radius — for `m = 5`: `G = 0.885401` (checker F6).  **The
  remaining FP_5 burden is an OUTER bound with `0.115` of headroom**,
  against configurations of near-equal moduli `rho >~ 0.92`.  After the
  one-sided fix, essentially all remaining slack is step (iii)
  (`99.99%` of sampled configs satisfy the (ii)+(iii) composite within
  `1.07x`), and the natural Young-split repair of (iii) provably
  recovers ROWCERT+ exactly (no gain).

## 4. Dead routes at m = 5 (measured; do not rebuild)

- K4-analogue Hölder factorizations: the near-1-factorization scheme
  reaches `6.155` against target `5` (exact obstruction on the 5-star:
  bound `5 + (5/4)u^2 + O(u^3)` vs truth `5 - u^5`; all columns equal
  there, so NO weighting can help); the aligned/cyclic dedicated-x
  scheme reaches `5.0302` (obstruction: square-plus-origin at
  `R = 0.686`); free column exponents by convex min–max still fail
  (`1.0053`).  The obstruction is ONE family (perturbed stars), not an
  incompatible pair.  Degradation across `m`: `0.08%` excess (m=4)
  `-> 0.6%` (cyclic, m=5) `-> 23%` (matching-shaped, m=5).
- Row weights `w_j = x_j^alpha` fail for EVERY `alpha > 0` (sup
  `~1.020`, `alpha`-independent); FP_m sits exactly at the `alpha = 0`
  endpoint of the validity window.  `w = 1/M_j` fails (`1.0202`).
- The Lorentzian rank-2 structure yields the exact identity
  `S_m = (prod_k y_k)^{1/m} sum_j y_j Gamma_j` (`y_j = sqrt(1-rho_j^2)`,
  `Gamma_j = (prod_k cosh(delta_jk/2))^{1/m}`), but its AM–GM
  strengthening is FALSE at every `m` (fails already at `R = 0.2`).

## 5. Zero-insertion law (exact) and the odd-m matching remark

With `B_j` the row products of the `(m-1)`-point configuration:

```text
S_m(c_1..c_{m-1}, 0) = 1 + sum_j B_j^{(m-1)/m}          (checker F7),
```

so padding by zeros RAISES `G` on every sampled config (Jensen penalty
`>= 0`), with transferred deficit
`1 - G_m(c,0) >= ((m-1)/m)^2 (1 - G_{m-1})` asymptotically — an
induction handle whose loss decays only like `1/M^2`.  Star ladder:
`G_5` on a `k`-star plus zeros is `[(5-k) + k(1 - u^k)^{1/5}]/5`.
Remark (from the corpus's insertion theorem, new consequence): for ODD
`m`, any matching-shaped superunit graph has an isolated vertex, so the
FP_4 note's insertion theorem covers the whole matching stratum at
`m = 5` outright.

## 6. Consequences for the (S) lane

1. Prove the crude outer bound (near-equal moduli, `rho >= ~0.9`,
   target `G <= 0.99` say, headroom to `0.885`) and FP_5 — hence
   `(S)_6 by the landed bridge — CLOSES.  This is now the sharpest
   open free-point obligation, and it is a bounded, low-dimensional,
   large-margin problem.
2. The `m`-uniform frontier: the extremal family stabilises (same
   `1+2+2`-type graded star for all tested `m`) while the sphere margin
   at fixed `R` shrinks with `m` — any all-`m` proof must use the
   balanced-cone flatness structure of §2, not fixed-`R` margins.
3. PM_5 (the root-free strengthening) SURVIVES measured (`max sum_j A_j
   < 5` at every `R`, same extremal family) even though PM_6 is
   refuted; it remains the cleanest root-free target.

## Claim boundary

§2 and the §3 Theorem are proved (ordinary mathematics; the checker
replays every ingredient inequality and threshold numerically and the
star-ray law symbolically).  §§1, 4, 5's measured rows are adversarial
computation at the stated instrument strength; "no violation found" is
evidence, not proof, of FP_5.  Instrument caveat carried forward:
UNCONSTRAINED differential evolution demonstrably misses narrow
boundary basins — it failed to rediscover the KNOWN PM_6 counterexample
`(5/7, -1, -1, -1, -1, -1)`, which only corner-seeded ascent recovers
(`7.251555778`, matching the corpus to 7 digits) — so the FP_5 verdict
rests on the sphere-constrained profiles plus 3,720 structured seeds,
and any future "adversarially clean" claim from plain DE alone should
be treated as under-tested.  The critical radii are numerically
located thresholds of proved certificates (their defining equations are
exact).  Nothing here proves FP_5 itself, (S)_6, or anything about the
parent problem; the free-point lane remains auxiliary to Erdős 1041
((S) does not imply the parent).
