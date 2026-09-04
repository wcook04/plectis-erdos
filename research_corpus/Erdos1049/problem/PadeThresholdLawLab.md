# Erdős 1049: the Padé method has an exact threshold, and 3/2 misses it by 38.6%

## Claim boundary

Erdős #1049 at base `3/2` remains **open**. What is established is a sharp
**negative** law: the scalar q-Apéry Padé family has a closed-form critical
exponent over rational bases, the instrument reproduces every base where the
answer is already known, and at `3/2` the deficit is a fixed positive proportion
of the height at every index. `GAP < 0` is the height-versus-decay balance, not a
complete irrationality proof — nonvanishing of the forms is a separate
obligation. The constant `3/π²` is a numerical identification to `1.8e−5`, not a
derivation.

## Source and attribution boundary

The surrounding q-Apéry and Padé architecture is grounded in the downloaded
primary sources Amdeberhan--Zeilberger, *q-Apéry Irrationality Proofs by q-WZ
Pairs*, `annexes/arxiv-math9804122-amdeberhan-zeilberger-q-apery/source.tex`,
Sections 1.3--1.7 (source TeX lines 72--115 and 196--207) and Theorem 2
(lines 305--316); Van Assche, *Little q-Legendre polynomials and irrationality
of certain Lambert series*,
`annexes/arxiv-math0101187-van-assche-little-q-legendre-lambert/source.tex`,
source TeX lines 306--378 and 497--524; and Fischler--Zudilin, *A refinement
of Nesterenko's linear independence criterion with applications to zeta
values*, `annexes/fischler-zudilin-2010-nesterenko-refinement/source.pdf`,
PDF pp. 740--742 and 747--748, Theorems A and 2.  Zudilin's generalized
`q`-logarithm Hankel setting is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`, Section
4, source TeX lines 278--380, for the Hankel determinant and backward-shift
order estimate.  These sources do **not** state the cross-base fitted `κ`, the
`3/π²` term-by-term decomposition, or a universal rational-base threshold.
Those measurements, the `3/2` gap, and the explicit calibration/limitation
boundary are authored in this repository; no scalar impossibility or
irrationality theorem is claimed.

## The seeds are q-generic, so the machine runs at any base

The source recurrence's seeds have closed forms:

```
L_0 = 0,   L_1 = −q(q+2)/(q−1),      R_0 = 1,   R_1 = −(q² + q − 1),
```

recovered from the Casoratian identity of `CasoratianBlockLawProof.md`
(`W_0 = L_1 R_0 − L_0 R_1 = −q(q+2)/(q−1)`, which is `−21/2` at `q = 3/2`).
With those seeds

> `L_j / R_j → Σ_{n≥1} 1/(qⁿ − 1)`

at **every** rational `q > 1` tested — matched to 57–295 decimal digits across
ten bases. That is what makes cross-base comparison legitimate: it is the same
construction, aimed at the same constant, at every base.

## The exponents

Write `q = a/b` in lowest terms and `(A_j, B_j)` for the primitive integer vector
proportional to `(L_j, R_j)`. Measured with a **three-point estimator**
`(f(j+h) − 2f(j) + f(j−h)) / 2h²`, which cancels the linear term exactly and
needs no fitting:

| quantity | exponent (per `j²`) | agreement |
|---|---|---|
| `log|R_j|` | `(3/2)·log(a/b)` | `1e−8` |
| `log den(R_j)` | `(3/2)·log 2` (at `b=2`) | `1e−14` |
| `log|ρ_j − ρ|` | `−3·log(a/b)` | `1e−7` |
| content removed | `0` (max content `59`, i.e. `O(1)`) | exact |
| `log|B_j|` | `κ · log a` | see below |

The decisive structural fact:

> **`κ` depends only on the numerator `a`, never on `b`.**
>
> `q = 3/2 → κ = 1.80446` and `q = 3 → κ = 1.80393`
> `q = 5/2 → κ = 1.80415` and `q = 5/3 → κ = 1.80324`

Over 40 three-point estimates across ten bases the mean is **`κ = 1.803946`**,
against

```
3/2 + 3/π²  =  1.8039635…      (agreement 1.8e−5, spread 1.8026 … 1.8047)
```

An earlier estimate of `1.78` came from a first-difference slope contaminated by
the block-law fluctuation in `log|B_j|`; the three-point estimator is the right
instrument and shows scatter without drift.

### The `3/π²` is the φ-weighted cyclotomic part — confirmed term by term

`3/π² = 1/(2ζ(2))` and `Σ_{i≤j} φ(i) ~ (3/π²) j²`, which suggests

> **`log|B_j| = log a · ( (3/2) j² + Σ_{i≤j} φ(i) ) + O(j)`.**

That is testable far more sharply than a single fitted constant, because it
predicts the **per-step increment**:

```
( log|B_j| − log|B_{j−1}| ) / log a  −  (3j − 3/2)   =   φ(j) + O(1).
```

`φ(j)` swings violently — `φ(59) = 58` against `φ(60) = 16` — so tracking it
term by term is a confirmation of the mechanism, not a restatement of the fit.
Measured at `q = 3/2` over `j = 40…66`:

| `j` | 48 | 53 | 59 | 60 | 61 | 66 |
|---|---:|---:|---:|---:|---:|---:|
| `φ(j)` | 16 | 52 | 58 | 16 | 60 | 20 |
| residual | 12.7 | 53.5 | 59.5 | 16.7 | 59.3 | 20.7 |

> **correlation `0.98922`, slope `0.9905`.**

The residual follows every swing of `φ`. So the second term is the φ-weighted
primitive (cyclotomic) part of the products `∏_i (aⁱ − bⁱ)`, sitting on a smooth
`(3/2) log a` — identified, not guessed. What remains unproved is the derivation
of that decomposition from the recurrence.

## The threshold

The linear form is `B_j·ρ − A_j`, so

```
log|B_j ρ − A_j|  ~  ( κ log a − 3 log(a/b) ) · j²,
```

and the construction produces forms tending to zero exactly when

> **`log b / log a  <  1 − κ/3  =  1/2 − 1/π²  =  0.3986788…`**
>
> equivalently **`a > b^{2.50828…}`**.

## Calibration — the instrument reproduces the known landscape

| `q` | `log b/log a` | GAP | observed | predicted | already known |
|---|---:|---:|---|---|---|
| `3/2` | 0.63093 | **+0.76600** | fails | fails | **open (#1049)** |
| `5/2` | 0.43068 | +0.15480 | fails | fails | fails |
| `7/2` | 0.35621 | −0.24787 | closes | closes | **Bundschuh–Väänänen** |
| `2` | 0 | −0.82998 | closes | closes | **Erdős 1948 / Borwein** |
| `3` | 0 | −1.31401 | closes | closes | Borwein |
| `5/3` | 0.68261 | +1.36973 | fails | fails | — |
| `14/3` | 0.41629 | +0.14147 | fails | fails | — |
| `16/3` | 0.39624 | **−0.01988** | closes | closes | — |
| `31/4` | 0.40370 | +0.05288 | fails | fails | — |
| `33/4` | 0.39648 | **−0.02321** | closes | closes | — |

The closed form `GAP = (3/π² − 3/2) log a + 3 log b` reproduces not just the
*sign* but the *value* at every base, to about `0.002`:

| `q` | 3/2 | 5/2 | 7/2 | 14/3 | 16/3 | 31/4 | 33/4 |
|---|---:|---:|---:|---:|---:|---:|---:|
| closed form | +0.76546 | +0.15450 | −0.24794 | +0.13943 | −0.02028 | +0.05171 | −0.02307 |
| measured | +0.76600 | +0.15480 | −0.24787 | +0.14147 | −0.01988 | +0.05288 | −0.02321 |

`b = 2` needs `a > 2^2.50828 = 5.69`, so `a ≥ 7`: **`7/2` is the first
half-integer base at which the method closes, and `5/2` and `3/2` are not** —
exactly the recorded landscape. The `b = 3` and `b = 4` pairs are razor thin
(`|GAP| < 0.024` on the closing side) and the sign is still called correctly;
those two pairs are what pin the constant, since a `κ` outside
`(1.7889, 1.8106)` would mis-call them.

An instrument that did not reproduce `2`, `3` and `7/2` would have no standing to
pronounce on `3/2`. It does.

## What this costs Erdős #1049

At `q = 3/2` the deficit has a closed form:

> `GAP(3/2) = 3 log 2 − (3/2 − 3/π²) log 3 = 0.765461` per `j²`,
> **38.6% of the height, at every index.**

Three consequences, all negative and all sharp:

- **Bounded-rank recombination cannot close it.** A fixed positive proportion of
  a quadratic quantity is not reachable by any finite-rank operation on the rows.
- **Content extraction cannot close it.** The content actually removed in passing
  from `(L_j, R_j)` to `(A_j, B_j)` is `O(1)` — the maximum observed over all ten
  bases and all indices is **59**. There is no hidden common factor to find here;
  the primitive rows are already primitive.
- **A single window prime cannot close it.** A window divisor is worth
  `log p = O(s)`, linear, against a `Θ(j²)` deficit. This is the quantitative
  reason the window-divisor route is usable only for the nonvanishing `1/q` step
  and never for height reduction.  Its source-supported selector is finite in
  the current evidence, and its lift to the q-Apéry denominator remains
  conditional; it is not an all-index height result.

So any route that closes `3/2` must supply arithmetic cancellation of **positive
density in `j²`**. That is a much more specific demand than "close the height
gap", and it rules out the three cheapest families outright.

## Relation to what the packet recorded

The packet states the gap through start-3 data ("at least 1874 coefficient bits
for the certified common ceiling") and warns against reading the natural
expanding prefix as evidence of asymptotic compression. This lab supplies the
asymptotic form of that warning: the prefix is not merely uncompressed at small
starts, its compression is `O(1)` forever, and the exact shortfall is
`0.765461 j²`.

## Replay

```sh
./repo-python formal_math/probes/erdos1049_pade_threshold_law.py
./repo-python formal_math/probes/erdos1049_pade_threshold_law.py --max-index 150 --json
```

Seven falsifiers: q-generic seeds hitting the Lambert value to ≥30 digits at
every base; `α = (3/2) log q`; `κ` independent of `b` on the pairs `(3/2, 3)` and
`(5/2, 5/3)`; `κ = 3/2 + 3/π²` within `5e−3`; the landscape reproduced at
`2, 3, 7/2, 5/2, 3/2`; the threshold predicting the sign of GAP at every base
including both boundary pairs; and the φ mechanism tracking term by term
(correlation ≥ 0.95, slope within 0.10 of 1) at every base. Exit `0` iff all
seven pass.
