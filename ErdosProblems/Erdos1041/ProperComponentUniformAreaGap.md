# Erdős 1041: the uniform proper-component area gap — FRONTIER gap #5 is a theorem

Date: 2026-08-29.  Origin: main-loop proof (the delegated agent for this
target died on an infrastructure limit before starting; the skeleton had
been pre-verified in the main loop and is completed here).  Checker:
`scripts/check_erdos1041_proper_component_area_gap.py`.

Consumes (landed): the exterior factorization and the STRICT fibre-coupled
capacity bound of `ExteriorBlaschkeFibreCapacityGap.md`
(`cap(closure U)^n / t = prod_j |xi_j|^{-1} < k/(2n-k)` for every proper
regular component), its normalized exterior map from
`ProperComponentCapacityGap.md`, and Grönwall's area identity (the terminal
form is in `Degree5AssemblyAndSharpenedCuts.md`; the general exterior form
is classical and restated below).

## Theorem (uniform area gap)

For every `n >= 2` and `1 <= k < n` there is a constant

```text
A_{n,k}  <  (k/(2n-k))^{2/n}
```

such that EVERY monic degree-`n` polynomial `P`, every regular value
`t > 0`, and every component `U` of `{|P| < t}` containing exactly `k`
roots (with multiplicity) satisfy

```text
Area(U)  <=  pi A_{n,k} t^{2/n}.
```

Corollary (FRONTIER gap #5).  At `n = 5`, `k = 2`:

```text
A_{5,2}* := sup_U Area(U) / (pi t^{2/5})  <  (1/4)^{2/5} = 0.5743490...
```

— the strict two-root component area inequality named as the
highest-leverage missing ingredient in `Degree5AssemblyAndSharpenedCuts.md`
and FRONTIER §4.5.  Consequently the `k = 2` merge threshold
`Theta_{5,2} = tanh((1/4)^{-2/5})^{1} = 0.9404` of the dichotomy/cluster
chain (`ConnectedClusterBergman.md` (2), which consumes the AREA, not just
the capacity) improves strictly to `tanh(1/A_{5,2}*) > 0.9404`; the
numeric size of the improvement awaits an explicit constant (captured
follow-up).  FOLLOW-UP LANDED (2026-08-30):
`ProperComponentExplicitAreaConstant.md` proves
`A_{5,2}* <= 4^{-2/5}(1 - 6.76e-8)` (exact-rational certificate), so
`Theta_{5,2} >= 0.940354223795` — explicit, `+1.362e-8` over the old
threshold.

## Proof

Fix `n, k`; write `m = n - k` and `p* = k/(2n-k) < 1`.

Setup.  For a proper regular component `U`, let
`psi(zeta) = C zeta + c_0 + sum_{l>=1} c_l zeta^{-l}` be the exterior
Riemann map of `closure(U)` on `{|zeta| > 1}`, `C = cap(closure U)`.
Grönwall's identity for the capacity-normalized map
`Psi(zeta) = (psi(zeta) - c_0)/C = zeta + sum b_l zeta^{-l}` is

```text
Area(U) = pi C^2 (1 - sum_{l>=1} l |b_l|^2),
```

so with `p := C^n/t` and `E(U) := sum_l l |b_l|^2` (the Grönwall deficit),

```text
Area(U)/(pi t^{2/n}) = p^{2/n} (1 - E(U)).                     (*)
```

The landed strict bound gives `p < p*`.  The exterior factorization: with
`F = (P o psi)/t` (boundary modulus 1, zeros at the `m` exterior-root
preimages `xi_j`, `|xi_j| > 1`, pole of order `n` at infinity),

```text
g(z) := z^n F(1/z)
```

extends to a finite Blaschke product of degree `m` on the disk with
interior zeros `1/xi_j` and `g(0) = C^n/t = p > 0` (the exterior
leading-coefficient identity; after the standard unimodular normalization
`g(0)` is the positive real `p`).  Equivalently

```text
Q(Psi(zeta)) = zeta^n g(1/zeta)   on |zeta| > 1,               (**)
Q(z) := P(c_0 + C z)/t   (degree n, leading coefficient p).
```

Suppose the theorem fails: there are `P_nu, t_nu, U_nu` with
`Area_nu/(pi t_nu^{2/n}) -> p*^{2/n}`.  By `(*)` and `p_nu < p*`, BOTH
`p_nu -> p*` and `E_nu -> 0`.

Step 1 (`Psi_nu -> id`).  For `|zeta| >= R > 1`, Cauchy–Schwarz gives

```text
|Psi_nu(zeta) - zeta|^2 <= (sum_l l |b_l|^2)(sum_l |zeta|^{-2l}/l)
                        <= E_nu log(1/(1 - R^{-2})),
```

so `Psi_nu -> id` locally uniformly on `{|zeta| > 1}`.

Step 2 (coefficient compactness of `Q_nu`).  Fix the `n + 1` nodes
`zeta_s = 2 e^{2 pi i s/(n+1)}`.  By `(**)`,
`|Q_nu(Psi_nu(zeta_s))| = 2^n |g_nu(1/zeta_s)| <= 2^n`.  The interpolation
nodes `Psi_nu(zeta_s) -> zeta_s` are distinct in the limit, so the
Vandermonde matrices are invertible with uniformly bounded inverses for
large `nu`; hence the coefficient vectors of `Q_nu` are bounded, and along
a subsequence `Q_nu -> Q` coefficientwise, with `deg Q = n` and leading
coefficient `lim p_nu = p* > 0`.

Step 3 (Blaschke limit).  Write
`g_nu = omega_nu prod_{j=1}^{m} (z - a_{j,nu})/(1 - conj(a_{j,nu}) z)`
with `|a_{j,nu}| < 1`, `|omega_nu| = 1`.  Pass to a subsequence with
`omega_nu -> omega` and `a_{j,nu} -> a_j in closure(D)`.  A factor whose
zero reaches the boundary point `a` (`|a| = 1`) converges locally
uniformly on compact subsets of `C \ {a}` to the unimodular CONSTANT `-a`
(because `1 - conj(a) z = -conj(a)(z - a)` exactly when `|a| = 1`).  Hence
`g_nu -> g` locally uniformly on `D`, where `g` is a unimodular constant
times a finite Blaschke product with the surviving interior zeros.  Since
`g_nu(0) = p_nu` (positive real), `g(0) = p* in (0, 1)`; so `g` is not a
unimodular constant, it has at least one interior zero `a_1`, and every
interior zero satisfies `|a_j| >= |g(0)| = p* > 0` — in particular
`a_1 != 0`, so `g` has a genuine finite pole at `1/conj(a_1)`
(`1 < |1/conj(a_1)| <= 1/p*`).

Step 4 (limit identity and contradiction).  Passing to the limit in
`(**)` (Step 1 + Step 2 on the left, Step 3 on the right — for
`|zeta| > 1` the argument `1/zeta` stays in a compact subset of `D` on
compacta):

```text
Q(zeta) = zeta^n g(1/zeta)   on |zeta| > 1,
```

i.e. `g(w) = w^n Q(1/w)` on `0 < |w| < 1`.  The right-hand side equals
`sum_{j=0}^{n} q_j w^{n-j}` — a POLYNOMIAL in `w` — and two rational
functions that agree on an open set are identical.  So `g` is a
polynomial, contradicting its finite pole at `1/conj(a_1)`.  QED

Remarks.  (i) The mechanism: capacity saturation (`p -> p*`) and area
saturation (`E -> 0`) cannot happen together, because area saturation
makes the exterior map affine, which turns the exterior Blaschke factor
into a polynomial inner function — forcing `|g(0)| in {0, 1}` — while
capacity saturation pins `|g(0)| = p* in (0, 1)`.  (ii) The proof is a
normal-families/compactness argument, so `A_{n,k}` is not explicit; the
explicit-constant route (quantify Step 1's effect on the Fourier tail of
`g` against the Schur-tail lemma below) is the captured follow-up.
(iii) Critical levels follow from regular ones by monotone approximation
within a component's lifetime, exactly as in the landed capacity note.

## Appendix: the Schur-tail lemma (for the explicit constant)

Lemma.  Let `g` be inner on the disk with `g(0) = p in [0, 1)` (after a
unimodular normalization).  Then for every integer `N >= 0`,

```text
sum_{l > N} |hat g_l|^2  >=  (1 - p^2) p^{2N}.
```

Proof.  The Schur transform `s = (g - p)/(1 - p g)` is inner with
`s(0) = 0`, so the powers `1, s, s^2, ...` are ORTHONORMAL in `H^2`
(`<s^q, s^r> = int s^{q-r} dm = s^{q-r}(0) = 0` for `q > r`, using
`|s| = 1` a.e.).  Inverting, `g = p + (1 - p^2) sum_{r>=1} (-p)^{r-1} s^r`
(convergent in `H^2`).  Since `s^r` vanishes to order `>= r` at `0`, the
projection `Pi_N` onto polynomials of degree `<= N` kills every `s^r` with
`r > N`; hence, `Pi_N` being a contraction and the `s^r` orthonormal,

```text
||Pi_N(g - p)||^2 <= (1 - p^2)^2 sum_{r=1}^{N} p^{2(r-1)}
                  = (1 - p^2)(1 - p^{2N}).
```

The constant `p` is the 0-th coefficient of `g`, orthogonal to `g - p`
(whose 0-th coefficient vanishes), so
`sum_{l <= N} |hat g_l|^2 = p^2 + ||Pi_N(g - p)||^2
<= 1 - (1 - p^2) p^{2N}`, and `||g||^2 = 1` gives the claim.  QED

At `n = 5, k = 2, m = 3`: any exterior Blaschke factor with
`p >= 1/8` keeps at least `(1 - p^2) p^{10} >= 5.7e-10` of its Hardy
energy above degree 5 — the quantitative seed for an explicit `A_{5,2}`.

## Claim boundary

The theorem and the Schur-tail lemma are ordinary proved mathematics
(main-loop; the compactness bookkeeping is spelled out step by step
above).  No explicit numerical value of `A_{n,k}` is claimed; the
measured `0.482` (overall) and `0.264` (decisive band) from the corpus
remain measurements.  The checker verifies: the corollary's inequality on
sampled two-root quintic components with margins; the Schur-tail bound on
random degree-3 Blaschke products; the boundary-escape factor limit; and
the Grönwall/Pólya chain `(*)` on samples.  Nothing here is a parent
claim; the consequence for the merge thresholds becomes numeric only with
an explicit constant.  PRIORITY CAVEAT: no literature search; the
statement shape (uniform non-circularity of proper polynomial lemniscate
components at fixed capacity ratio) may exist; claim "new to this
directory" only.
