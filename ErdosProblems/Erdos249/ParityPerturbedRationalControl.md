# Parity-perturbed rational controls for the binary totient series

Target: Erdős #249, irrationality of `S = Σ_{n≥1} φ(n)/2^n`. Status of the target: open. Nothing in this note decides it.

What this note proves is that the two structural routes the corpus names as untried, the carry-rank gap (route (c)) and shifted-correlation input through the first-harmonic pivot (route (a)), cannot by themselves decide #249, because they cannot distinguish `φ` from an explicit coefficient sequence whose binary series is rational. The witness agrees with `φ` at every odd argument, differs from `φ` by at most two at even arguments, and has binary series exactly `5/4`. The paper's open problem `prob:carryrank` asked for precisely such a control ("a control recurrence with the same integrality and decay architecture and near-maximal dyadic rank"); the witness has the same odd totient kernel as `φ`, satisfies every hypothesis of the anti-compression theorem, and on the computed window its dyadic section rank is maximal.

Lean: `ErdosProblems/Erdos249/ParityPerturbedRationalControl.lean`. Probe: `formal_math/probes/erdos249_parity_perturbed_rational_control.py`, receipt `ErdosProblems/Erdos249/parity_perturbed_rational_control_probe_receipt.json` (copy of the probe's own output under `state/formal_math/probes/`).

## 1. Statements

Throughout, `c : ℕ → ℕ` is a coefficient sequence, its binary series is `Σ_{n≥1} c(n)/2^n`, and a *tempered integral carry* for `c` with multiplier `v ≥ 1` is an integer sequence `u` with `u(N+1) = 2u(N) − v c(N+1)` and `u(N)/2^N → 0`. For `c(n) ≤ n` the binary series is rational if and only if such a carry exists (`binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`).

**Theorem 1 (even-argument control; Lean).** There is `c : ℕ → ℕ` with

1. `c(n) ≤ n` for every `n`;
2. `c(n) = φ(n)` for every odd `n`;
3. `−2 ≤ c(n) − φ(n) ≤ 1` for every `n`;
4. `Σ_{n≥1} c(n)/2^n = 5/4`.

Explicitly, `ξ := 5/4 − S`, `x_0 := ξ`, `d_m := ⌊4x_{m−1} + 2/3⌋`, `x_m := 4x_{m−1} − d_m`, and `c(2m) := φ(2m) + d_m`, `c(2m−1) := φ(2m−1)`. The first certified digits are `d = 0, −2, 1, −2, 0, −2, 1, −1, 0, −1, 1, −1, −1, −2, 0, 1, −2, 0, −2, 1, …`, so `c(1..30) = 1, 1, 2, 0, 4, 3, 6, 2, 6, 4, 10, 2, 12, 7, 8, 7, 16, 6, 18, 7, 12, 11, 22, 7, 20, 11, 18, 10, 28, 8` against `φ(1..30) = 1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8, 16, 6, 18, 8, 12, 10, 22, 8, 20, 12, 18, 12, 28, 8`.

Lean declarations (namespace `ErdosProblems.Erdos249.ParityPerturbedRationalControl`): `control`, `control_le`, `control_odd`, `abs_control_sub_totient_le`, `control_sub_totient_bounds`, `control_series : binaryCoeffSeries control = 5/4`, `not_irrational_control`, and the package `parity_perturbed_rational_control`.

**Theorem 1′ (variants; probe, same proof).** With digit set `{−1,0,1,2}` and target `3/2` the same construction gives `−1 ≤ c − φ ≤ 2` on even arguments, `c = φ` on odd arguments, `Σ c(n)/2^n = 3/2`. With the perturbation placed on odd arguments instead (`c(2m) = φ(2m)`, `c(2m−1) = φ(2m−1) + d_m`, digit set `{−2,−1,0,1}` on `(1−S)/2`), `Σ c(n)/2^n = 1`. Every rational `ρ` with `ρ − S` in the representable interval works, so the set of rational values reachable by a bounded one-parity perturbation of `φ` contains a full interval of rationals.

**Theorem 2 (carry-rank transfer for odd-agreeing coefficients; Lean).** Let `c(n) = φ(n)` for every odd `n`, and let `u` be a tempered integral carry for `c` with multiplier `v ≥ 1`. Then for every `e`, the `ℚ`-span of the carry sections `n ↦ u(2^j n + r)`, `1 ≤ j ≤ e`, `0 ≤ r < 2^j`, has dimension at least `2^e − 1`.

Lean: `oddAgree_carryKernel_diff`, `canonicalCarryDifferenceFamily_eq_smul_totient_of_oddAgree`, `finrank_canonicalCarryKernel_ge_of_oddAgree`. The proof is the existing totient proof (`finrank_canonicalCarryKernel_ge_of_linearIndependent`) with its single totient input, the odd canonical channels, kept and nothing else assumed about `c`.

**Corollary 3 (the anti-compression architecture has a rational twin; Lean).** For the `c` of Theorem 1 there exist `v ≥ 1` and a tempered integral carry `u` for `c` whose finite-level carry sections have rank at least `2^e − 1` for every `e`, while `Σ c(n)/2^n = 5/4`.

Lean: `control_temperedOrbit_carryRank_unbounded`. Compare `not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`, whose conclusion is the same statement for `φ` under the hypothesis that `S` is rational. The conclusion is therefore consistent with rationality; no argument from the conclusion alone can reach a contradiction.

**Theorem 4 (density-zero support; authored, probe-checked).** Let `F := {1,2,3} ∪ {n ≥ 4 : 2^{⌊log₂log₂ n⌋} | n}`. Then `F` has natural density zero, and there is `c : ℕ → ℕ` with `c(n) ≤ n`, `c(n) = φ(n)` for every `n ∉ F`, and `Σ_{n≥1} c(n)/2^n = 3/2`.

**Corollary 5 (correlation-invariant inputs are inert).** Let `c` be as in Theorem 1 and put `F(n) = φ(n)/n`, `F_c(n) = c(n)/n`. For every `h ≥ 0` and `x ≥ 1`,

```
| Σ_{h<n≤x} c(n)c(n−h) − Σ_{h<n≤x} φ(n)φ(n−h) |  ≤  2x² + 6x,
| Σ_{h<n≤x} F_c(n)F_c(n−h) − Σ_{h<n≤x} F(n)F(n−h) |  ≤  4 log x + 8,
```

the second uniformly in `0 ≤ h ≤ x/2`. Consequently `c` satisfies the shifted-correlation asymptotic of Balasubramanian, Giri and Srivastav (Theorem 2.2 with `α = β = 1`, error `O(log² x)`, uniform in `|h| ≤ x/2`) with the same main term `C(h)` and the same error class, and satisfies the unnormalised form with error `O(x² log² x)` after partial summation. Any argument for #249 whose only arithmetic input about `φ` is such an asymptotic applies verbatim to `c` and would prove `5/4` irrational. The same holds for any fixed finite family of `k`-point correlations `Σ_{n≤x} Π_i g(n+h_i)` with error term `≫ x^k`, since a bounded perturbation moves them by `O(x^k)` against a main term of order `x^{k+1}`.

## 2. Proofs

### Centred base-four digits

Fix the digit set `D = {−2,−1,0,1}`, a complete residue system modulo `4`, and the half-open interval `J = [−2/3, 1/3)`. For real `x` put `δ(x) = ⌊4x + 2/3⌋` and `T(x) = 4x − δ(x)`. Writing `y = 4x + 2/3`, `T(x) = {y} − 2/3 ∈ [−2/3, 1/3)`, so `T` maps all of `ℝ` into `J` (`step_mem`), and for `x ∈ J` one has `−4/3 ≤ 4x + 2/3 < 2`, so `δ(x) ∈ D` (`digit_bounds`). With `x_0 = x`, `x_m = T(x_{m−1})`, `d_m = δ(x_{m−1})`, the identity `x_{m−1}/4^{m−1} = d_m/4^m + x_m/4^m` telescopes to

```
x = Σ_{m=1}^{M} d_m/4^m + x_M/4^M        (expansion)
```

and `|x_M| ≤ 2/3` gives `x = Σ_{m≥1} d_m/4^m` (`hasSum_digits`). Summability is by comparison with `(1/4)^m`.

### Bounds on `S`

`S ≥ φ(1)/2 + φ(2)/4 + φ(3)/8 + φ(4)/16 = 9/8` (`S_ge`). Since `φ(n) ≤ n − 1` for `n ≥ 2`, `S ≤ 1/2 + Σ_{n≥1} n/2^{n+1} = 1/2 + 1 = 3/2` (`S_le`, using `Σ n r^n = r/(1−r)²`). Numerically `S = 1.36763080198502235…`.

### Theorem 1

Put `ξ = 5/4 − S`. From `9/8 ≤ S ≤ 3/2`, `−1/4 ≤ ξ ≤ 1/8`, so `ξ ∈ J` and the digits `d_m ∈ D` sum to `ξ`. Also `ξ ≥ −5/12`, so `d_1 = ⌊4ξ + 2/3⌋ ≥ −1`. Define `c(2m) = φ(2m) + d_m` and `c(n) = φ(n)` for odd `n` (and `c(0) = 0`).

Bounds. For odd `n`, `c(n) = φ(n) ≤ n`. For `n = 2`, `c(2) = 1 + d_1 ∈ {0, 1, 2}`. For even `n ≥ 4`, `φ(n)` is even and positive, hence `≥ 2`, so `c(n) ≥ φ(n) − 2 ≥ 0`; and `c(n) ≤ φ(n) + 1 ≤ n` because `φ(n) ≤ n − 1`. Item 3 is immediate from `d_m ∈ D`.

Series. `Σ_{n≥1} c(n)/2^n = S + Σ_{m≥1} d_m/2^{2m} = S + Σ_{m≥1} d_m/4^m = S + ξ = 5/4`. In Lean the reindexing is `tsum_even_add_odd` applied to `n ↦ δ(n+1)/2^{n+1}`, whose even-indexed part vanishes and whose odd-indexed part is `m ↦ d_{m+1}/4^{m+1}`.

The variants of Theorem 1′ change only the digit set and the target: with `D' = {−1,0,1,2}`, `J' = [−1/3, 2/3)`, `δ'(x) = ⌊4x + 1/3⌋`, the same argument applies to `3/2 − S ∈ J'` (here `c(2m) ≤ φ(2m) + 2 ≤ m + 2 ≤ 2m` uses `φ(2m) ≤ m`, and `c(2) ≤ 2` needs `3/2 − S < 5/12`, that is `S > 13/12`). For the odd-argument variant, `Σ_{m≥1} d_m/2^{2m−1} = 2 Σ_m d_m/4^m`, so one expands `(1 − S)/2 ∈ J` with `D`; then `c(1) = 1 + d_1 ∈ {0,1}` because `d_1 ∈ {−1, 0}` there, and for odd `n ≥ 3`, `0 ≤ φ(n) − 2 ≤ c(n) ≤ φ(n) + 1 ≤ n`.

### Theorem 2

Let `u` be a tempered carry for `c` with multiplier `v`. For every `N ≥ 1`, `2u(N−1) − u(N) = v c(N)` (`carryDerivative_eq_scaledCoeff_of_recurrence`). At `N = 2^{j+1} n + (2r+1)`, an odd integer, `c(N) = φ(N)`, so

```
v φ(2^{j+1} n + 2r + 1) = 2 u(2^{j+1} n + 2r) − u(2^{j+1} n + 2r + 1).
```

Hence each odd canonical totient channel `n ↦ φ(2^{j+1}n + 2r + 1)`, `0 ≤ j < e`, `0 ≤ r < 2^j`, is `1/v` times a difference of two carry sections through level `e`. The odd canonical channels are linearly independent over `ℚ` (`linearIndependent_canonicalTotientKernelFamily`, restricted by `linearIndependent_totientOddKernelFamily`), and there are `2^e − 1` of them (`card_totientOddIndex`). So the span of the carry sections contains a `(2^e − 1)`-dimensional subspace.

### Corollary 3

`c(n) ≤ n` and `Σ c(n)/2^n = 5/4 ∈ ℚ` give a tempered carry by `not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit`; Theorem 2 gives the rank bound at every level.

### Theorem 4

Write `F` for the support set, `M(n) = 2^{⌊log₂log₂ n⌋}` for `n ≥ 4`. For `n ∈ F`, `n ≥ 4`, with `2^{2^k} ≤ n < 2^{2^{k+1}}` and `M(n) = 2^k`: either `n + 2^k < 2^{2^{k+1}}`, in which case `n + 2^k ∈ F`; or `2^{2^{k+1}} ≤ n + 2^k`, in which case `2^{2^{k+1}} ∈ F` (it is divisible by `2^{k+1}`). Either way the next element of `F` is at most `n + g` with `g = 2^k ≤ log₂ n`. For `n ∈ {1,2,3}` the next element is `n + 1`.

Density: for `2^{2^K} ≤ x < 2^{2^{K+1}}`, `|F ∩ [1,x]| ≤ 2^{2^K} + x/2^K ≤ 2x/2^K` and `2^K > (log₂ x)/2`, so `|F ∩ [1,x]|/x ≤ 4/log₂ x → 0`.

Greedy construction. Define the forced future mass and the free future capacity

```
L_n = Σ_{m>n, m∉F} φ(m)/2^m,     U_n = L_n + Σ_{m>n, m∈F} m/2^m.
```

Both tend to `0`, and `U_n − L_n ≥ 2^{−n}` for every `n ∈ F`: the next element `m₁ ≤ n + g` of `F` contributes `m₁/2^{m₁} ≥ (n+g)/2^{n+g}` (the map `t ↦ t/2^t` is non-increasing on integers `t ≥ 1`), and `(n+g)/2^g ≥ (n+g)/n > 1` because `2^g ≤ n` (for `n ≤ 3`, `g = 1` and `(n+1)/2 ≥ 1`). Choose `ρ = 3/2`; then `L_0 ≤ S ≤ 3/2` and `U_0 ≥ 1/2 + 2/4 + 3/8 + 4/16 + φ(5)/32 + φ(7)/128 > 3/2`, so `ρ ∈ [L_0, U_0]`.

Process `n = 1, 2, …` maintaining a residual `R_n` with `R_0 = ρ` and the invariant `R_n ∈ [L_n, U_n]`. At `n ∉ F` set `c(n) = φ(n)`; then `R_n = R_{n−1} − φ(n)/2^n ∈ [L_n, U_n]` because `L_{n−1} = L_n + φ(n)/2^n` and `U_{n−1} = U_n + φ(n)/2^n`. At `n ∈ F`, `L_{n−1} = L_n` and `U_{n−1} = U_n + n/2^n`; if `R_{n−1} ≤ U_n` set `c(n) = 0`, otherwise `c(n) = ⌈2^n(R_{n−1} − U_n)⌉`. In the second case `1 ≤ c(n) ≤ n` since `2^n(R_{n−1} − U_n) ≤ 2^n · n/2^n = n`, and `R_n = R_{n−1} − c(n)/2^n` satisfies `R_n ≤ U_n` and `R_n > U_n − 2^{−n} ≥ L_n`. The invariant forces `R_n → 0`, so `Σ_{n≥1} c(n)/2^n = ρ`.

The probe replays this greedy construction exactly over `n ≤ 3000` (413 free positions, maximal gap 8, invariant and capacity condition checked at every step).

### Corollary 5

`c(n)c(n−h) − φ(n)φ(n−h) = δ(n)φ(n−h) + φ(n)δ(n−h) + δ(n)δ(n−h)` with `|δ| ≤ 2` gives a termwise bound `2(n−h) + 2n + 4 ≤ 4n + 4`, and `Σ_{n≤x}(4n+4) ≤ 2x² + 6x`. In normalised form the termwise bound is `2/n + 2/(n−h) + 4/(n(n−h))`, whose sum over `h < n ≤ x` is at most `4(log x + 1) + 4`. The BGS asymptotic for `F = (μ/d) ∗ 1` has main term `(x − H)C(h)` and error `O(log² x)`; adding a perturbation of size `O(log x)` keeps both. Partial summation with `Q(t) = t(t−h)` transports the statement to `φ` with error `O(x² log² x)`, and the perturbation contributes `O(x²)`.

## 3. Computation receipts

Probe: `./repo-python formal_math/probes/erdos249_parity_perturbed_rational_control.py`, exit 0.

* Exact enclosure `lo ≤ S ≤ hi` with `lo = Σ_{n≤4000} φ(n)/2^n` and `hi − lo = 4002/2^4000`; running the digit recursion on both endpoints in exact rational arithmetic certifies `d_1, …, d_1200` of Theorem 1 (all 1200 agree). Digit histogram over those 1200: `−2: 290, −1: 282, 0: 322, 1: 306`. Growth, sign and parity checks pass for `n ≤ 2400`. The exact prefix `Σ_{n≤2400} c(n)/2^n` differs from `5/4` by less than `2^{−2389}`.
* Variants: the `{−1,0,1,2}`/`3/2` construction and the odd-argument/`1` construction agree with their targets to below `2^{−1980}` on `n ≤ 2000` (800-digit floating arithmetic).
* Truncated section ranks (64 evaluation points, exact rational elimination), sections through level `e`, count `2^{e+1} − 1`:

| `e` | sections | rank `φ` (expected `2^e+1`) | rank Theorem 1 control | rank `3/2` control | rank odd-argument control | odd sections (expected `2^e−1`) |
|---|---|---|---|---|---|---|
| 1 | 3 | 3 | 3 | 3 | 3 | 1 |
| 2 | 7 | 5 | 7 | 7 | 6 | 3 |
| 3 | 15 | 9 | 15 | 15 | 12 | 7 |
| 4 | 31 | 17 | 31 | 31 | 24 | 15 |

  Full row rank of a truncated evaluation matrix is an exact certificate of linear independence of the corresponding sections, so the even-argument controls have dyadic section rank exactly `2^{e+1} − 1` through every level `e ≤ 4`, larger than the totient's `2^e + 1`. The paper's request for "near-maximal dyadic rank" is met with equality on this window.
* Shifted correlations at `x = 1900`: `(Σ cc − Σ φφ)/x = 389, 193, 195` for `h = 1, 2, 6`, against main terms `Σ φφ / x² = 204, 255, 266`; the perturbation is of the order of `x²`, two orders below the main term `x³`.

## 4. What this establishes and what it does not

Established (Lean, focused replay 2026-09-02, exit 0 after 3542 jobs, sorry-free, every printed declaration with axioms `propext`, `Classical.choice`, `Quot.sound`): Theorem 1, Theorem 2, Corollary 3. Established (authored, elementary, probe-checked): Theorem 1′, Theorem 4, Corollary 5.

Consequences for the route inventory of #249.

1. Route (c), "push the rank gap `2^e − 1` versus `2^e + 1` into a contradiction via an explicit dyadic-rank obstruction", is closed in its stated generality. The rank bound `≥ 2^e − 1` is derived from the odd totient channels only, and Corollary 3 exhibits a coefficient sequence with those very channels, the same growth bound, a tempered integral carry, and a rational series. An argument in this coordinate must use the even-argument values of `φ` to within less than an additive `2` (equivalently, `φ(2m)` modulo `4` and beyond, since a perturbation by `{−2,…,1}` is exactly a free choice of residue modulo `4`).
2. The paper's open problem `prob:carryrank` (Section "Structural and Diophantine routes") is answered in the form its own text requested: a control recurrence with the same integrality and decay architecture, the same odd kernel, and maximal dyadic rank on the computed window, exists and is rational. A positive answer for `φ` itself remains equivalent to #249.
3. Route (a), "run the BGS shifted correlation through the first-harmonic pivot", cannot obtain its arithmetic content from the correlation input. By Corollary 5 the control satisfies the same shifted-correlation asymptotics in the same error class; only the pivot step, which reads `φ(N+m) mod 2^m` for `m` up to about `log N`, can separate `φ` from `c`. This sharpens the corpus's existing `PivotAntiReconstruction` obstruction (variance and additive energy do not imply phase separation) to a statement about the whole class of correlation-type inputs.
4. Theorem 4 shows the same for any property of `φ` that is determined by its values on a set of density one of the specific shape `ℕ ∖ F`: irrationality, if true, is carried by the values on a set of density zero. It does not show this for an arbitrary density-one set chosen by the prover, since a sparse free set with gaps larger than `log₂ n` has no capacity to absorb the residual.

Not established: irrationality of `S`; any statement about `φ` on even arguments; any bound on `‖v 2^c S‖`; any change to the canonical frontier `FullMersenneCanonicalBasepointResidueGapSupply`. The construction is not multiplicative and is not a Lambert series with a periodic weight, so it says nothing about route (b), the Möbius-weighted Duverney–Tachiya Padé construction.

## 5. Remaining obstacle

The smallest object that now separates `φ` from every rational control of this type is the residue `φ(2m) mod 4` along the even arguments together with the exact odd values: the construction shows that the residue class of `φ(2m)` modulo `4` (a free digit in `{−2,…,1}`) can always be re-chosen to make the series rational while the odd values are held fixed, and symmetrically for the odd arguments. An irrationality proof must therefore consume the joint 2-adic structure of `φ` at consecutive arguments of both parities, which is exactly what the canonical residue-gap producer `FullMersenneCanonicalBasepointResidueGapSupply` asks for and what no correlation or rank input supplies.

## 6. Pipeline receipt

```text
tao_pipeline_receipt
input_stage: generation
output_stage: verification
artifact: ErdosProblems/Erdos249/ParityPerturbedRationalControl.lean, .md, formal_math/probes/erdos249_parity_perturbed_rational_control.py
human_understanding_delta: the carry-rank coordinate and correlation-type inputs are provably insensitive to rationality; the deciding information is the residue of φ modulo 4 at one parity given the other
verification_state: Theorem 1, Theorem 2, Corollary 3 Lean-checked (replay exit 0, 3542 jobs; axioms propext, Classical.choice, Quot.sound; receipt in research_packet.json rows parity_perturbed_rational_control and odd_agreeing_carry_rank_transfer); Theorem 4, Corollary 5 authored with probe replay
publication_or_review_state: private; not packaged; not submitted
canonicalization_state: subordinate to canonical_full_mersenne_residue_normal_form; retires route (c) as stated and the correlation-only reading of route (a)
unresolved_downstream_bottleneck: the residue-gap supply H itself; no producer is added
next_stage_owner: packet row parity_perturbed_rational_control; paper Section "Structural and Diophantine routes" should cite the control against prob:carryrank

paper_assimilation
paper: erdos-249-binary-totient-series.tex
section: Structural and Diophantine routes (prob:carryrank); Obstructions for fixed-coordinate methods
canonical_mechanism_family: closed_rows_and_affine_regimes (rational control models)
relation: answers the control request attached to prob:carryrank; strengthens the rational control models globalBalancedCoeff (value 4/9, bounded payload) and idCoeff (rank two) by a control with the full odd totient kernel
understanding_delta: the anti-compression theorem's conclusion is rationality-compatible; any proof must read φ(2m) mod 4
evidence_boundary: Lean for Theorems 1, 2, Corollary 3; authored for Theorem 4 and Corollary 5; finite exact receipts for the rank table
hard_step: none in the construction; the hard step of #249 is untouched and is named in Section 5
meaningful_failed_route: route (c) carry-rank contradiction; correlation-only route (a)
open_remainder: FullMersenneCanonicalBasepointResidueGapSupply
```
