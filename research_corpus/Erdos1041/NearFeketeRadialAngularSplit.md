# Erdős 1041: the near-Fekete radial/angular split — stability, radial slice, and the origin-connector refutation

Date: 2026-08-29.  Origin: adversarial creation session (main loop +
falsifier subagent), all proofs re-verified in the main loop before landing;
the refutation witness replayed independently in exact rational arithmetic.
Checker: `scripts/check_erdos1041_near_fekete_radial_angular_split.py`.

Notation: `f` monic degree `n`, roots `a_k = rho_k u_k`, `|u_k| = 1`,
`rho_k in (0,1]`; `zeta = e^{2 pi i/n}`; `D = |disc f|/n^n`; power sums
`q_m = Sigma_k u_k^m` (for on-circle results) or `q_1 = Sigma_k a_k`.

## Theorem 1 (near Fekete, length is free)

The path `[a_i, 0] u [0, a_j]` has length `rho_i + rho_j <= 2`, strict when a
root is interior.  Consequently the near-Fekete obligation is PURE
CONTAINMENT: find `i != j` with `|f| <= 1` on both radial segments — or, after
the refutation below, on both segments of a perturbed hub.  Every metric
estimate in the near-Fekete lane is redundant.  (Trivial; load-bearing.)

## Theorem 2 (quantitative Fekete–Hadamard stability; explicit constants)

Let `a_1..a_n` lie in the closed unit disk and `D >= 1 - eta` with
`eta <= 1/(80 n^2)`.  Then

1. `1 - rho_i^2 <= n eta/(n-1)` for every `i`;
2. `|a_i - a_j| >= (2 - 2 sqrt(eta) - n eta)/(n-1)` for `i != j`;
3. there are a unimodular `omega` and a bijection `sigma` with
   `|a_i - omega^{1/n} zeta^{sigma(i)}| <= 7 sqrt(eta)` for every `i`.

Proof.  With `V` the Vandermonde matrix (`V_{im} = a_i^m`, `0 <= m < n`),
`G = V V^*`, `s_i = G_{ii} = Sigma_{m<n} rho_i^{2m} <= n`, and
`H = diag(s)^{-1/2} G diag(s)^{-1/2}` (PSD, unit diagonal):
`D = det H * prod_i (s_i/n)`, and both factors lie in `[1-eta, 1]` (Hadamard
for PSD gives `det H <= 1`; each `s_i/n <= 1`).  (1): `n - s_i =
Sigma_{m<n}(1 - rho_i^{2m}) >= (n-1)(1 - rho_i^2)` since `1 - x^m >= 1 - x` on
`[0,1]`, and `s_i/n >= 1 - eta`.  Fischer's inequality on the `{i,j}` block of
`H` gives `det H <= 1 - |H_{ij}|^2`, so `|H_{ij}|^2 <= eta` and
`|G_{ij}| <= n sqrt(eta)`.  (2): with `t = a_i conj(a_j)`,
`G_{ij} = Sigma_{m<n} t^m` and `|1 - t^m| <= m|1 - t|` give
`n sqrt(eta) >= n - |1-t| n(n-1)/2`, i.e. `|1-t| >= 2(1-sqrt(eta))/(n-1)`;
then `1 - t = (1 - rho_j^2) + conj(a_j)(a_j - a_i)` and `rho_j <= 1` give (2).
(3): `(1-t) G_{ij} = 1 - t^n` gives `|1 - a_i^n conj(a_j^n)| <= 2n sqrt(eta)`;
with `A_i = a_i^n`, `kappa = n^2 eta/(n-1)`, (1) gives `|A_i|^2 >= 1 - kappa`;
setting `omega = A_1/|A_1|` and unwinding (`|e^{ix}-1| >= 2|x|/pi`) yields the
angular bound and hence (3); bijectivity follows since `sigma(i) = sigma(j)`
would force `|a_i - a_j| <= 14 sqrt(eta)`, contradicting (2) under
`eta <= 1/(80 n^2)`.  QED

This is the object `HardRegimeIsNearFekete.md` names as missing ("a stability
estimate for the Fekete maximiser ... No such estimate is claimed, cited, or
known to this file").  Rate `sqrt(eta)` is correct (angular perturbations
enter `eta` quadratically); the constant `7` is measured ~30x conservative,
and the per-entry Fischer step loses a factor `n` recoverable from the trace
bound.  PRIORITY CAVEAT: classical-flavoured linear algebra; no literature
check run; claim "new to this directory" only.

## Theorem 3 (radial monotonicity) and Corollary 3a (radial reduction)

With `g(z) = prod_k (z - u_k)` (equimodular companion): if
`2 s Re(u_i conj(u_k)) <= 1 + rho_k` for all `k`, then
`|f(s u_i)| <= |g(s u_i)|` for `s in [0, rho_i]`.
Proof: `|s u_i - rho_k u_k|^2 - |s u_i - u_k|^2
= (1 - rho_k)(2 s Re(u_i conj(u_k)) - (1 + rho_k)) <= 0`; multiply.  QED

Corollary 3a: for `D >= 1 - eta`, `eta <= 1/(10 n^4)`, the hypothesis holds
for all `i, k` (via Theorem 2), so near-Fekete containment reduces to the
equimodular problem: RADIAL DEFICITS ONLY HELP; the entire near-Fekete
difficulty is angular.

## Theorem 4 (radial slice; unconditional for n <= 6)

Let `a_k = rho_k omega zeta^k` (EXACT gon directions, arbitrary radii
`rho_k in (0,1]`).  If `rho_k >= 2 cos(2 pi/n) - 1` for all `k` — vacuous for
`n = 3,4,5,6` — then for every `i` and `s in [0, rho_i]`:
`|f(s omega zeta^i)| <= 1 - s^n`.  Hence every pair of roots is joined by the
two-radii path of length `rho_i + rho_j <= 2` inside `{|f| <= 1}`, strictly
for interior roots.  Proof: Theorem 3 with `g = z^n - omega^n`,
`|g(s omega zeta^i)| = 1 - s^n`; the hypothesis reduces to
`2 cos(2 pi/n) <= 1 + rho_min`.  QED

New unconditional closed class for the parent (exact gon directions, any
radii, `n <= 6`; radial band `1 - rho <= 2(1 - cos(2 pi/n))` for all `n`) —
far wider than the quintic radial branch's `Delta <= 1/4096`.  Verified
`n = 3..14`, zero violations.

## Theorem 5 (exact spoke expansion and averaging identity; on-circle)

For `|u_k| = 1`, `s in [0,1)`:

```
log|f(s u_i)|            = - Sigma_{m>=1} (s^m/m) Re( q_m conj(u_i)^m ),
Sigma_i log|f(s u_i)|    = - Sigma_{m>=1} (s^m/m) |q_m|^2   <= 0.
```

At every level SOME spoke is contained; the good index moves with `s` — the
exact obstruction shape.  (Proof: expand `log|1 - s conj(u_k) u_i|`; sum.)

## Theorem 6 (first-mode obstruction / centroid half-plane law)

On-circle: if `Re(q_1 conj(u_i)) < 0` then `sup_s |f(s u_i)| > 1`.  So the
number of contained origin spokes is at most the number of roots in the
closed half-plane with inner normal `q_1`.  (Proof: first-order term of
Theorem 5.)  Predicts and matches the corpus's stored degree-6/9 spoke-failure
witnesses (3/6 and 4/9 contained origin spokes at `D = 0.999992`, `0.999947` —
where NO critical hub carries two contained spokes, so the origin hub strictly
beats every critical hub there).

## Theorem 7 + exact witness (REFUTATION: no origin-hub eta-neighbourhood)

For `n = 3` and every `n >= 5` there is NO `eta > 0` such that
`D >= 1 - eta` forces two contained origin spokes.

- `n = 3` (proved): `u = (1, zeta e^{-i delta}, zeta^2 e^{i delta})` has
  `q_1 = 1 - cos delta + sqrt(3) sin delta > 0` while two roots lie strictly
  on the wrong side; Theorem 6 kills both their spokes; `1 - D = 2 delta^2 +
  O(delta^4)`; shrink into the open disk preserving the escapes.
- `n = 5` (exact rational certificate, replayed independently in Fraction
  arithmetic in the main loop): `lambda = 999999/1000000`,
  `a_k = lambda u_k` with

  ```
  u_0 = 1,  u_1 = (1053 + 3196 i)/3365,  u_2 = (-5928 + 4255 i)/7297,
  u_3 = conj(u_2),  u_4 = conj(u_1)      (Pythagorean unimodulars)
  ```

  a real monic rational quintic, roots in the OPEN disk, `1 - D = 3.19991e-4`;
  exact rational signs: `|f|^2 - 1 = +2.2225e-4` at `s = 303/2000` on spokes
  1 and 4, `+6.3569e-5` at `s = 77/1000` on spokes 2 and 3 — FOUR of five
  spokes escape; at most one contained.  Persistence as `eta -> 0` measured at
  80 dps over seven decades with the model-predicted law `~ 0.2 s^{n/(n-2)}`
  (computational, not proved).  `n = 4` is the unique measured-safe degree
  (single Fourier mode + even vertex count), unproved.

Mechanism: containment of a spoke requires the whole vector of the first
`floor((n-1)/2)` Fourier modes of the angular perturbation to point the right
way; each mode halves the contained set, so generic contained count
`~ n/2^{floor((n-1)/2)} -> 0`.  Selection is unavoidable: no selection-free
envelope exists (crude modulus bounds on non-resonant modes cannot close near
`s = 0`).

## The repaired keystone and its finite residual

Every violating witness found is rescued by a PERTURBED hub: some `c != 0`
with `|a_i - c| + |a_j - c| <= 2` and `|f| < 1` on both segments; the
rescuing hub sits at `|c| ~ 0.35-0.4 rho`, `rho = max_m |q_m/n|^{1/(n-m)}`
(measured).  Restated keystone:

> (R1) exists `eta_n > 0`: `D >= 1 - eta_n` implies existence of `c` and
> `i != j` with `|a_i - c| + |a_j - c| <= 2` and `|f| <= 1` on
> `[a_i, c] u [c, a_j]`.

Discharged already: the metric side (Theorem 1 plus the ellipse expansion:
the length constraint reads `Re(c conj(a_i + a_j)) >= |c|^2 + O(|c|^3)`,
and near-gon adjacent pairs supply `a_i + a_j` in every direction spaced
`2 pi/n`, so a pair aligned with any prescribed `c`-half-plane always exists);
the radial direction (Theorem 3a); the `D`-to-geometry transfer (Theorem 2);
the `c = 0` case (refuted above, so hub selection is forced).  Remaining: the
containment selector (R1) itself — the general-`n` analogue of the quintic
atlas step S7-S8, whose model dimension grows linearly in `n`.

## Quintic-skeleton diagnosis (for the general-n atlas)

Of the proved quintic neighbourhood (`QuinticTransverseFiniteTransfer.md`
Corollary B): steps S1-S3, S5-form, S6c, S9, S10 are degree-independent or
mechanical; S6a (radial branch) and S10 (truncated-spoke metric) are now
SUPERSEDED by Theorems 3/4 and 1 respectively; the irreducible core is S7-S8
(compact transverse model + finite selector; real dimension
`2 floor((n-1)/2) - 1`, box count exponential).  The refutation above shows
the selector is forced, not an artifact of the quintic write-up.  A clean
general step available for reuse: `Sigma_m |E_m| t^m <= t^n/(K-1)` for
`t >= K rho` (the intermediate-ray bound), since `|E_m| <= rho^{n-m}`.

## Claim boundary

Theorems 1-7: ordinary proved mathematics (main-loop verified).  The `n = 5`
refutation: exact rational certificate (independent Fraction replay).
Persistence laws, `n = 6..12` violations, hub-rescue margins, `kappa_n ~ 0.4`:
computational (80 dps).  `n = 4` origin-route safety: measured only.  Nothing
here proves or refutes the parent theorem; the refutation concerns one
connector inside the near-Fekete shell, and every witness remains
parent-satisfiable via a perturbed hub.
