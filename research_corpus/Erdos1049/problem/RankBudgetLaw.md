# Erdős 1049: rank-budget calibration in the assumed type-I model

## The law

For `q = a/b` in lowest terms, write `t = log b / log a`. Under the decay,
homogenisation, clearing, and nonvanishing hypotheses listed below, a rank-`r`
type-I Hermite–Padé system can close base `a/b` only if

> **`t < (r − 1 − κ)/r`**,  where `κ` is the per-degree cyclotomic clearing rate.

Three exponents, all per unit of degree `D`:

| term | source | per-degree |
|---|---|---|
| **decay** | the Padé count: `r(D+1)` unknowns push the inner sum to `O(x^{rD})`, so the remainder is `q^{−(r−1)D}` | gain `(r−1)·log(a/b)` |
| **homogenise** | clearing `P_i(a/b)` to integers costs `b^D` | cost `log b` |
| **clear** | the cyclotomic denominator of the coefficients costs `a^{κD}` | cost `κ·log a` |

Cost below gain gives `κ log a + log b < (r−1)(log a − log b)`, i.e. the law.

`κ` is **measured**, not assumed, at rank two on the fixed diagonal: the clearing is
`(3/π²)j² log a` against `D_j = (3/2)j²`, so `κ = 2/π² = 0.202642`.

## Internal calibration: it reproduces the known rank-two budget

At `r = 2`,

```
t < (1 − 2/π²)/2 = 1/2 − 1/π² = 0.398678816358…
```

which is the packet's recorded threshold law, **to every digit**. That is the whole
warrant. The law is not fitted to anything; it reproduces the one rank whose
threshold was already established, and it explains that threshold's two halves —
`1/2` is homogenisation, `1/π²` is `Σ_{r≤n}φ(r) ~ 3n²/π²`.

At `κ = 0` it gives `t < 1/2`, i.e. `a > b²`, which is independently the
homogenisation ceiling proved in
[`HomogenisationCeilingProof.md`](HomogenisationCeilingProof.md).

## What the calibrated budget admits

Rank required is `r > (1 + κ)/(1 − t)`:

| base | `t` | rank at observed `κ` | rank at `κ = 0` |
|---|---|---|---|
| `q` integer | 0 | 2 | 2 |
| `7/2` | 0.35621 | **2** ← published | 2 |
| `5/2` | 0.43068 | 3 | **2** ← content route |
| `11/3` | 0.45816 | 3 | 2 |
| `10/3` | 0.47712 | 3 | 2 |
| **`3/2`** | **0.63093** | **4** | **3** |
| `4/3` | 0.79248 | 6 | 5 |
| `5/4` | 0.86135 | 9 | 8 |

Thresholds: rank 2 `0.39868`, rank 3 `0.59912`, rank 4 `0.69934`, rank 5 `0.75947`.

**Among the displayed bases, `3/2` is the first whose numerical budget excludes
rank two even with zero clearing, and excludes rank three at the observed rank-two
clearing rate.** It misses the rank-three threshold by `0.03181` in `t` and clears
the rank-four threshold by `0.06841`. These are admission-budget statements, not a
construction or an irrationality proof.

## Two calibrated routes within this model

**(A) Rank 3 with a better clearing.** Rank three clears this numerical budget iff
its per-degree clearing rate satisfies `(2 − κ₃)/3 > 0.63093`, i.e.

> **`κ₃ < 0.10721`** — at most **53%** of the rank-two rate.

The packet's recorded negative result — *"rectangular two-function Hermite–Padé
optimisation does not improve the classical threshold"* — is consistent with this
rather than contradicting it: that shape does not realise the generic count. Producer
`nonrectangular_multiple_q_jacobi_systems` explicitly notes the no-go "covers only
that explicit rectangular shape; it does not cover nonrectangular multi-indices,
varying evaluation diagonals, mixed type-I/type-II systems, congruence-constrained
selection, or minors chosen for arithmetic rather than symmetry." The number that
lane must beat is now explicit: **0.10721**.

**And a generic solve will not do it.** Building the type-I system for
`(1, ζ_q(1), ζ_q(2))` directly — solve `p_0 + p_1f_1 + p_2f_2 = O(x^{3D+2})` over `Q`
with `deg p_i ≤ D`, then take the primitive integer form — gives

| D | 3 | 4 | 5 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|---|
| `κ₃` | 1.388 | 1.193 | 1.319 | 1.338 | 1.205 | 1.438 | 1.541 |

against a budget of `0.10721`: **over by a factor of 11 at best, and rising.** The
reason is structural — a generic solve makes the coefficients Hankel minors, whose
height grows like `e^{D log D}`, so `κ₃ ~ log D → ∞`. (`D = 2` is a degenerate index
whose primitive coefficients are all `±1`; one index is not a family.)

For scale: the rank-two q-Apéry construction achieves `κ = 2/π² = 0.20264` precisely
by having **q-factorial (cyclotomic) denominators instead of generic minors** — and
even that is **twice** the rank-three budget. So the multiple q-Jacobi family would
have to be about twice as arithmetically efficient as q-Apéry. That is the shape of
the task, and it is a demanding one.

### Direct finite measurement of the actual PVA diagonal

The source's linear-independence construction is not a generic type-I solve. It uses
the genuinely nonrectangular type-II diagonal `m=n−1`, evaluates at `z=p^(2n−1)`,
and combines the common denominator with both explicit second-kind numerators and
the finite Lambert prefixes. The exact probe
[`measure_pva_multiple_q_jacobi.py`](scripts/measure_pva_multiple_q_jacobi.py)
reconstructs those displayed formulas over `p=3/2`, then primitive-normalises the
three rational channels.

The finite scan `n=2,…,10` gives exact primitive content `1` in every row. Its
height-rate proxy `log(H_n)/(n log 3)` is:

| `n` | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| proxy | 5.9791 | 14.3215 | 22.7694 | 32.7322 | 40.8786 | 50.0378 | 60.3251 | 68.0767 | 77.0722 |

Every measured row has rapidly growing raw primitive height and shows no post-hoc
content gain. This is a direct finite arithmetic warning against treating the
published PVA family as an immediate rank-three escape. The displayed proxy is not
an estimate of `κ₃`: no degree normalization or decomposition into homogenisation
and cyclotomic-clearing costs has been proved for this family. It is not an all-index
asymptotic theorem and does not close Erdős #1049; the remaining live alternatives
include an all-index structured arithmetic construction or a different
rank/congruence design.

**(B) Rank 4 at the observed rank-two clearing rate**, which clears the numerical
budget with a 10% margin and needs no content gain in this ledger. This does not
construct a rank-four family or establish its integrality, nonvanishing, or
remainder estimates.

### Where Zudilin's Hankel route sits — read carefully

It is tempting to call the Hankel route "rank four" because its decay is cubic. That
identification is **wrong**, and the distinction matters. Its decay is cubic in the
rank parameter `N`,

```
ord_q V_N* = N(N−1)(2N−1)/6 ~ N³/3     (HankelQOrderComputationalLab.md, exact for N ≤ 7)
```

but its *cost* is cubic in `N` too — `ZudilinResidualBorderChargeLab.md` records the
extractable content as at most `2N³ − N` against a requirement it writes as
`(39/41)(4N³ − 3N²)`. Both sides are cubic, so this is a **fixed-ratio** comparison
like a fixed rank, not a growing-rank escape. The packet's inequality
`41(2N³ − N) < 39(4N³ − 3N²)` is exactly the statement that the ratio is on the wrong
side — short by a factor of about two asymptotically.

So the honest placement is: the Hankel route is not blocked by the rank budget, and
this law does not rescue it. Its blocker is the cost side, and its recorded residual —
"must create higher-valuation-layer cancellation of cubic density, a genuinely global
norm or resultant gain beyond the first block, or a different integral model" — is
already the right statement of it. What this law adds is only the frame: the quantity
to improve is a cost-to-gain ratio, and the target is ratio `< 1`.

## What this is, and is not

This is a **budget**: a necessary condition and a room analysis under the stated
exponent model. It says which parameter choices pass or fail that model's numerical
admission test. It does not supply polynomials, exclude different decay models or
higher-rank constructions, or touch the real obstruction at high rank, which is
proving the constructed form is **nonzero** — the same obstruction that makes
Ball–Rivoal-type results hard. A rank with room is a lane worth entering, not a
theorem.

Two honest caveats:

- `κ` is measured only at rank two. Carrying it to `r > 2` is a model, which is why
  the rigorous `κ = 0` ceiling `t < (r−1)/r` is reported alongside every figure. The
  zero-clearing column is the universal optimistic ceiling; the observed rank-two
  `κ` column is a calibration scenario, and no lower bracket for the true rank-`r`
  threshold is asserted.
- The decay exponent `(r−1)D` is the generic Padé count. A specific family can fail
  to achieve it — that is exactly what the rectangular two-function no-go records.

## Source and attribution boundary

The displayed rank-budget inequality is a repository-authored consequence of four
explicit asymptotic hypotheses: Padé decay, rational-evaluation homogenisation,
coefficient clearing, and nonzero integral forms. No cited paper states this exact
three-term ledger, the local `κ₃ < 0.10721` value, or a rank-three family at base
`3/2`.

The standard effective-height framework is grounded in the downloaded primary PDF
of Stéphane Fischler and Wadim Zudilin, *A refinement of Nesterenko's linear
independence criterion with applications to zeta values*,
`annexes/fischler-zudilin-2010-nesterenko-refinement/source.pdf`: printed pp.
739–740, Theorems A–B compare small-form decay with coefficient growth, and printed
p. 742, Theorem 2 introduces the common-divisor improvement. Those results support
the bookkeeping vocabulary, not this local threshold or an auxiliary construction.

The concrete q-Padé denominator/decay model is checked against the downloaded
primary PDF of Walter Van Assche, *Little q-Legendre polynomials and irrationality
of certain Lambert series*,
`annexes/arxiv-math0101187-van-assche-little-q-legendre-lambert/source.pdf`:
printed pp. 1–2 give the q-Padé context, p. 7 equations (26)–(30) give the
cyclotomic denominator and totient-rate calculation, and p. 8 equations (32)–(33)
display the cleared forms and residual before the nonvanishing/decay conclusion.
The source uses integer exponential bases; it does not establish the local
rank-three rational-base claim.

The `7/2` entry is kept separate from the open `3/2` design target. The downloaded
primary PDF of Peter Bundschuh and Keijo Väänänen, *Arithmetical investigations of
a certain infinite product*,
`annexes/numdam-cm-1994-91-bundschuh-vaananen-infinite-product/source.pdf`, gives
the standing height hypotheses on printed pp. 175–176, Theorem 2 on p. 177, the
quantitative consequence on pp. 177–178, and the proof on pp. 189–193. The local
Lean surface `formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalBaseLambert.lean`
checks only the displayed numerical entrance inequality for `7/2`; it does not
reprove those external hypotheses, certify this rank law, or transfer the result
to `3/2`.

Finally, the downloaded Amdeberhan–Zeilberger q-Apéry source,
`annexes/arxiv-math9804122-amdeberhan-zeilberger-q-apery/source.tex`, lines 31–50,
72–95, 97–119, and 196–207, is the primary source for the integer-base q-WZ
construction and its recurrence/integrality context. Its integer-base theorem is
not a rational-base `3/2` family. The rank-budget equation, the finite degree scan,
the `3/2` constants, and all conclusions about the missing rank-three construction
are therefore repository-authored and remain conditional; they do not prove
irrationality of Erdős #1049.

## Consequence for the portfolio

Combined with [`HomogenisationCeilingProof.md`](HomogenisationCeilingProof.md), which
shows the rank-two content lane is capped at `a > b²` and that its content is
measurably zero (`gcd = 1`), the picture for `3/2` is now complete at the budget
level:

- rank 2 fails the model even with zero clearing;
- rank 3 passes only with `κ₃ < 0.10721`;
- rank 4 passes at the observed rank-two rate, with a 10% budget margin.

So effort should leave the rank-two content producers entirely. The lane this law
newly quantifies is `nonrectangular_multiple_q_jacobi_systems`: rank three has the
room (clearing-free ceiling `2/3 = 0.66667 > 0.63093`) and the whole question is
whether a nonrectangular multi-index can hold its clearing rate below `0.10721`. The
Hankel lane is unaffected by this law — see the reading above — and keeps its own
recorded cost-side residual. Erdős #1049 at base `3/2` remains open.

## Replay

```sh
./repo-python formal_math/probes/erdos1049_rank_budget_law.py
```

Five falsifiers: rank two equals the recorded threshold to 1e-15; rank two at zero
clearing equals `a > b²` on ten bases; the three published cases come out at rank
two; `3/2` has least calibrated rank 4 at the observed rate / rank 3 clearing-free;
and the rank-three clearing
target is a positive number strictly below the rank-two rate. Exit `0` iff all five
pass. Receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1049_rank_budget_law_receipt.json`.
