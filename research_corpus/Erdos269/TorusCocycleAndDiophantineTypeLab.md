# Erdős 269: the source system is a cocycle over a 2-torus rotation

## Analytic consumer

The bounded-radix dichotomy leaves one branch: an exact integral state of the
normalized source tail `X_a`, obeying

`X_(a+1) = b_a X_a - d_a`,  `b_a ∈ {2,6,10,30}`,  `0 < X_a ≤ C_a`.

Every retired attempt on that branch treated `(b_a, d_a)` as an opaque source
word and looked for a functional on it: bounded-lookahead Lyapunov descent,
phase-conditioned polynomial coboundaries of total degree ≤ 2, finite-dimensional
faithful observers, uniform post-clear transition classifications. This lab
identifies what the source word actually *is*, and then tests the strongest
tool that identification makes available.

## The identification

A power of 3 lies in the dyadic shell `[2^a, 2^(a+1))` exactly when
`⌊j·log₂3⌋ = a`; likewise for 5 with `log₂5`. Hence

`b_a = 2 · 3^[a ∈ B(log₂3)] · 5^[a ∈ B(log₂5)]`,

where `B(θ)` is the Beatty set `{⌊jθ⌋}`. The two indicator sequences are
Sturmian with slopes `1/log₂3 = log₃2` and `1/log₂5 = log₅2`, so the radix word
is their superposition: **a coding of the orbit of a rotation on the 2-torus by
`(log₃2, log₅2)` under a product partition.**

Exact checks:

- 0 mismatches against the literal source engine for `a = 1 … 2600`.
- Over 300,000 letters the radix frequencies match the independent-rotation
  prediction to five decimals: `2 ↦ 0.21009` (pred. `0.21012`),
  `6 ↦ 0.35924` (`0.35920`), `10 ↦ 0.15898` (`0.15895`),
  `30 ↦ 0.27169` (`0.27173`).
- Factor complexity is **exactly `p(n) = (n+1)²`** for `n = 1 … 22`
  (4, 9, 16, …, 529). That is the two-dimensional analogue of Sturmian
  complexity `n+1`, and it is the signature of a rank-2 rotation coding rather
  than a rank-1 (Sturmian) one or a positive-entropy word.

This is a mechanism family the packet did not have: the source is quasi-periodic
of rank two, driven by ratios of logarithms of 2, 3 and 5.

## Predeclared probe on the new family

The strongest transcendence tool for quasi-periodic expansions is the
Adamczewski–Bugeaud criterion (Schmidt Subspace Theorem applied to *stammering*
expansions). It needs one input: prefixes that are `(1+ε)`-powers with `ε`
bounded away from zero along a subsequence.

For a single Sturmian word of slope `α`, a period-`q` repetition persists for
about `1/‖qα‖` letters, so convergent denominators give exponents bounded away
from 1. For the **product** of two Sturmian words the period must serve both
slopes at once, so the governing quantity is *simultaneous* approximation of
`(log₃2, log₅2)`.

Falsifier: a repetition exponent that stays at 1 as `q` grows closes the lane;
a growing exponent opens it.

## Exact result: the stammering lane is closed

Measured at the record simultaneous-approximation denominators up to
`q ≤ 150,000`, against the literal 400,000-letter word:

| period `q` | `max(‖q·log₃2‖, ‖q·log₅2‖)` | matched length | exponent |
|---|---|---|---|
| 65 | 0.01043398 | 82 | 2.2615 |
| 7061 | 0.00717656 | 63 | 1.0089 |
| 7126 | 0.00542395 | 82 | 1.0115 |
| 15810 | 0.00361686 | 135 | 1.0085 |
| 45807 | 0.00109567 | 337 | 1.0074 |

The matched length tracks `1/‖qα‖`, so it grows like `q^{1/2}` while the period
grows like `q`: the exponent decays to 1 like `1 + O(q^{-1/2})`.

The cap is structural rather than a search depth. Dirichlet in dimension two
supplies simultaneous approximation only at exponent `1/2`, while the criterion
needs exponent `1` for both slopes at the *same* denominator — a measure-zero
condition on the slope pair. The failure margin is a full power `q^{1/2}`, not a
constant, so extending the search does not recover the lane.

**Claim boundary.** This retires the route on measured evidence plus the
Dirichlet cap; it is not yet a theorem. Turning it into one needs an effective
lower bound `max(‖q·log₃2‖, ‖q·log₅2‖) ≫ q^{-1+δ}`. Current bounds for two
logarithms do not supply it: Laurent–Mignotte–Nesterenko gives
`|b₁log3 − b₂log5| > exp(−C (log B)²)`, which is weaker than any fixed power of
`B`, and the best known irrationality measure for `log3/log2` (Rhin, ≈ 5.117)
gives only `‖q·log₃2‖ ≫ q^{-4.117}`. **That gap is the precise external input
this lane would need**, and naming it is the useful output: the route should not
be re-attempted through repetition structure until such a bound exists.

## Corroboration: the value is Diophantine-generic

The normalized tail `X_1` was expanded to **13,109 airtight-certified** partial
quotients (certification by common prefix of the continued fractions of the two
endpoints of the interval `(F/B, (F+κ)/B]` that provably contains `X_1`, so no
approximation heuristic enters). The engine truncation `F/B` was independently
checked to equal the direct smooth-number sum exactly as rationals.

- Gauss–Kuzmin frequencies: `1 ↦ 0.4208` (pred. `0.4150`), `2 ↦ 0.1665`
  (`0.1699`), `3 ↦ 0.0917` (`0.0931`), `4 ↦ 0.0575` (`0.0589`).
- Lévy constant `1.18869` against the theoretical `π²/(12 ln 2) = 1.18657`
  — **0.18% relative**.
- Largest partial quotient 129,114; empirical irrationality exponent `≈ 2`.

No Liouville behaviour and no algebraic or self-similar continued-fraction
structure exists below denominators of 22,483 bits. Two consequences:

1. The delayed-conspiracy reading that motivated the retired Lyapunov,
   coboundary and observer attempts has no support at any reachable scale.
2. Since the continued fraction does not terminate within 13,109 certified
   terms, `X_1` is **not rational with denominator below `2^22482 ≈ 10^6768`**.

## Corroboration on a bounded small-denominator rectangle

Over **640,000** (denominator, start) pairs — every odd `q ≤ 120` coprime to 30
against every start `a ≤ 20,000` — the canonical residue escapes the analytic
cap **in every single case**, at depth at most 18, concentrated at depths 10–13.
Measured against the counting threshold `log₈(q·κ)`, the mean excess is `0.97`
and the single largest is `7.09` at `q = 113, a = 11569`, meaning `113·X_11569`
sits within `4·10⁻⁷` of an integer from below. For 640,000 draws of a generic
quantity the expected closest approach is about `1.6·10⁻⁶`, so even the extreme
case is ordinary inside this finite rectangle.

This census does **not** establish genericity, a no-accumulation theorem, or a
uniform escape horizon.  The later exact affine-cylinder certificate
`affine_cylinder_delay_101_counterexample` has a 181-digit denominator whose
canonical state remains trapped for 200 post-clear steps.  It therefore refutes
every uniform cap through 199 and supersedes the earlier inference that larger
lookahead cannot reveal longer delays.  Conversely, one depth-200 witness does
not prove unbounded delay or an arbitrary-depth family.  The correct frontier
is arithmetic admissibility of rational points in successively deeper
cylinders, not extrapolation from either finite experiment.

## The route ceiling

Excluding all denominators `q ≤ Q` at window depth `L` is exactly the statement

`min { q ≥ 1 : (q·A) mod B ≤ W } > Q`,  `A = (-F) mod B`,  `W = Q·κ/9`,

a first-hit-of-a-rotation-in-an-interval problem. Solving it by the
Stern–Brocot recursion in `O(log B)` instead of scanning `q` one at a time gives
an exact exclusion of every odd denominator up to `≈ 10^187` at depth 420
(soundness cross-checked against a direct 200,000-term scan at ten depths).

The certified bound fits `log₂Q = 0.4974 · log₂B - 5.29`: it is `Θ(√B_L)`, with
the fitted exponent within 0.5% of `1/2` over 420 depths. That is the exact
best-approximation barrier suggested by the measured range.  The finite fit
does not prove that every escape/Farey argument is globally capped at `√B_L`,
nor that residue bias can never accumulate.  Together with the depth-200
affine-cylinder witness, it instead isolates the missing all-scale input: an
anti-concentration or scale-dependent escape theorem, or an arbitrary-depth
admissibility theorem for rational points in the nested cylinders.

## The other open producer lands in the same place

`cofinal_projective_window_pair_incoherence` asks, for every `B` coprime to 30,
for arbitrarily late pairs of individually admissible windows violating the
Lean-checked shadow `d_a·H_b ≡ d_b·H_a (mod B)`. The packet carries single exact
witnesses at `B = 11` and `B = 7` and states that neither supplies the quantifier.

Enumerating every admissible endpoint — base clears the cap, residue does **not**
escape it, residue coprime to `B` — for all 133 denominators coprime to 30 in
`[7,500]` across starts `a ≤ 3000` (the `B = 11` witness is reproduced exactly:
carries 61 and 259, heights 5 and 2 mod 11, defect 4):

- **Every** denominator admits violating pairs. The violating fraction runs from
  `0.828` at `B = 7` to `0.988` at `B = 499`.
- Admissible endpoints occur at density about one per two starts and keep
  appearing at the very top of every range (latest admissible start 2992–3000 for
  every `B`); violating pairs exist with both starts above 2963 for every `B`.
- **Same-start pairs are always coherent** — `P = 1.0000` exactly, at every `B`.
  So the construction must pair *different* starts. That constraint was not
  recorded anywhere.
- For different starts the residual coherence is purely short-range. Pairing
  neighbours gives coherence `1.23×`, `2.06×`, `6.42×` uniform at `B = 7, 101,
  499`; pairing endpoints separated by half the list gives `1.18×`, `1.10×`,
  **`0.92×`** — equidistributed.

So this producer's construction is not scarce, it is abundant; what is missing is
a proof, and the proof needs exactly two inputs: admissible endpoints occur
cofinally, and the projective defect equidistributes mod `B` across
far-separated pairs.

**Both remaining routes therefore reduce to the same missing analytic input.**
The integral-tail branch needs anti-concentration for `(-qF_L) mod B_L`; the
projective branch needs equidistribution of the defect across far-separated
pairs. Neither needs a new functional, a deeper scan, or repetition structure.
That is the one lane left, and it is a statement about the torus-rotation
cocycle.

## The value itself has a torus-analytic form

The radix *word* is a torus coding. The **value** turns out to be too, and
explicitly. With `L = log₂ s`, `θ = log₂3`, `φ = log₂5`, the running height is
`H(s) = 2^⌊L⌋ 3^⌊L/θ⌋ 5^⌊L/φ⌋` while `s³ = 2^L 3^{L/θ} 5^{L/φ}`, so

`1/H(s) = 2^{L} · 3^{L/θ} · 5^{L/φ} / s³`   (braces = fractional part),

verified to a maximum relative error of `1.5×10⁻¹⁴` over 4,000 smooth `s`.
Summing over the smooth lattice `s = 2^i 3^j 5^k`,

`S = Σ_{i,j,k≥0} W(L) / (8^i 27^j 125^k)`,  `W = 2^{L}3^{L/θ}5^{L/φ}`,
`L = i + jθ + kφ`.

`W` is a bounded function of the 3-torus point `({L}, {L/θ}, {L/φ})`, and because
`2^x3^y5^z` factorises, **each Fourier mode makes the `(i,j,k)` sum a product of
three ordinary geometric series**. Writing `λ = m₁ + m₂/θ + m₃/φ`, the mode
contributes

`c(m₁)c′(m₂)c″(m₃) / [(1 − e(λ)/8)(1 − e(λθ)/27)(1 − e(λφ)/125)]`

with `c(m) = 1/(ln2 − 2πim)`, `c′(m) = 2/(ln3 − 2πim)`, `c″(m) = 4/(ln5 − 2πim)`.

### The correction is exactly 17/2

`W` jumps wherever a coordinate hits 0 and the Fourier series converges there to
the jump midpoint, and those points are exactly the three coordinate axes of the
lattice. The excess is `9 − 1 = 8` at the origin plus `((p−1)/2)·Σ_{n≥1}1/H(pⁿ)`
on each axis. Those axis terms sum to exactly `1/2`, by a telescope: at each
prime power the height multiplies by `p`, so

`(p−1)/H(pⁿ) = 1/H(pⁿ−1) − 1/H(pⁿ)`,

and summing over every prime power gives `Σ_p (p−1) Σ_n 1/H(pⁿ) = 1/H(1) = 1`.
Checked exactly in rationals: the truncated value is `1 − 1/H(last)`, so the
identity is exact and the total correction is `8 + 1/2 = 17/2`.

`S = lim_{M→∞} [triple Fourier partial sum over |mᵢ| ≤ M] − 17/2.`

Measured corrected partial sums against the directly computed value:

| M | corrected | error |
|---|---|---|
| 20 | 1.738960 | 7.04e-2 |
| 40 | 1.756220 | 5.31e-2 |
| 80 | 1.788381 | 2.09e-2 |
| 160 | 1.799452 | 9.87e-3 |
| 320 | 1.804929 | 4.39e-3 |

The error halves as `M` doubles — the `1/M` rate a jump-discontinuous Fourier
series gives, and the sign is monotone.

### Why this matters for the programme

Every route the packet has tried is combinatorial: carries, Lyapunov
functionals, coboundaries, observers, escape certificates. This is the first
representation of the value as an explicit analytic object, and it puts the
arithmetic exactly where the torus reading predicted: **each Fourier mode is
governed by `λ = m₁ + m₂log₃2 + m₃log₅2`, a linear form in logarithms of 2, 3
and 5.** The denominators `1 − e(λ)/8` etc. are bounded away from zero, so no
mode is singular; what controls the sum is how the phases `e(λ)`, `e(λθ)`,
`e(λφ)` distribute — the same Diophantine input the escape and projective
branches both reduced to, now visible directly in the value rather than only in
the digit word.

**Claim boundary.** This is an exact representation, not an irrationality
argument. The triple sum is only conditionally summable — `Σ|c c′ c″|` diverges
like `(log M)³` — so it converges as a symmetric limit and would need
regularisation before any Diophantine estimate could be extracted from it.

## What is open after this lab

The producer must supply anti-concentration for the residues from the
*rotation's* Diophantine properties — that is, effective simultaneous
approximation bounds for `(log₃2, log₅2)`, or an all-scale invariant of the
cocycle over the 2-torus rotation. It cannot come from repetition structure
(closed above), from a finite-degree source potential (retired), or from
deeper finite escape scans (ceiling above).

## Replay

The block source has two engines: the exact one settles every comparison with
literal powers and is the authority; the fast one rebuilds the same data from
Beatty lattice counts with an exact guard band, is checked equal to the exact
engine on `a ≤ 3000`, and reaches `a ≤ 40,000` in ten seconds where the exact
engine stalls. That is what makes the 15,000-deep expansion above affordable.

```sh
./repo-python source-provenance://private-authoring-project/probes/erdos269_fast_engine.py 3000
./repo-python source-provenance://private-authoring-project/probes/erdos269_projective_cofinality.py --max-denominator 500 --max-start 3000
./repo-python source-provenance://private-authoring-project/probes/erdos269_torus_fourier_representation.py --max-mode 320
./repo-python source-provenance://private-authoring-project/probes/erdos269_torus_coding.py --max-a 300000 --verify-a 2600
./repo-python source-provenance://private-authoring-project/probes/erdos269_escape_depth_law.py --max-start 20000 --max-q 120
./repo-python source-provenance://private-authoring-project/probes/erdos269_stammering.py --max-a 400000 --max-q 150000
./repo-python source-provenance://private-authoring-project/probes/erdos269_continued_fraction.py --start 1 --depth 15000
./repo-python source-provenance://private-authoring-project/probes/erdos269_denominator_exclusion.py --start 1 --max-depth 420
```
