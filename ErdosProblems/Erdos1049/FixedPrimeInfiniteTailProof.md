# Erdős 1049: a conditional fixed-prime last-loss route — `5` divides every `B_j` from index 50 on if the all-level transfer holds

## What this changes

The packet's priority-1 producer `three_halves_pade_height_gap` recorded step 1 as
a **cofinal moving-prime law** whose remaining input was

> Boyd's heuristic for `J_p` made effective, not more block computation.

That is an open problem about *every* prime. It is not needed for the conditional
route below. Step 1 asks for a divisor across the window
`[s, s + 3s² + 5s + 3]` for cofinally many starts `s`. A **single fixed prime**
would supply it once the displayed all-level transfer is proved:

> **Conditional Theorem C.** If the all-level monodromy/continuity premise
> `(M)/(C5)` below holds for the q-Apéry specialization, then `5 | B_j` for
> every `j ≥ 50`. Hence for every start `s ≥ 50` the window gcd is divisible by
> `5`; this would make the window-divisor part of step 1 cofinal, with no
> first-appearance prime, no factoring of `3^s − 2^s`, and no input from Boyd.

Conditionally, the law is exact: `v_5(B_j) = 1 − v_5(H_{⌊j/2⌋})`, so the 5-part
of the window gcd at start `s` is `5^{1+⌊log_5(s/2)⌋}` and grows. The current
evidence certifies this only at the finite levels and indices recorded below.

## Source and attribution boundary

The q-Apéry recurrence and its integer-base boundary are grounded in the
downloaded primary source Tewodros Amdeberhan and Doron Zeilberger, *q-Apéry
Irrationality Proofs by q-WZ pairs*, Advances in Applied Mathematics 20 (1998),
275--283, `annexes/arxiv-math9804122-amdeberhan-zeilberger/source.tex`,
arXiv:math/9804122: source lines 31--50 define `h_q(1)`, lines 72--95 give
the q-WZ sequences, lines 97--119 give the recurrence coefficients, and lines
196--207 state the source's decay lemma and integer-base theorem.  The
downloaded primary PDF `annexes/boyd-1994-p-adic-harmonic-partial-sums/source.pdf`
(Boyd, *A p-adic Study of the Partial Sums of the Harmonic Series*,
Experimental Mathematics 3 (1994), 287--302) supports the Wolstenholme,
`J_p`, and Eswarathasan--Levine provenance on printed pp. 287--288 and the
recursive harmonic-zero generation on printed pp. 290--293.  The downloaded
primary PDF `annexes/sanna-2016-p-adic-harmonic-valuation/source.pdf` supports
the `J_5`/finiteness context and the valuation equivalence on PDF p. 1,
including Lemma 1.2; the downloaded primary arXiv PDF
`annexes/arxiv-2503-15714-harmonic-conjectures/source.pdf` provides the current
finite-range harmonic definitions and limitations on PDF pp. 1--3.  These
sources do not state the q-Apéry weighted transfer `(M)/(C5)`, the conditional
fixed-prime tail, or the exact `B_j` witnesses.  Those reductions, finite
replay, and conditional claim boundary are authored in this repository; no
unconditional cofinal tail or irrationality theorem is claimed.

## Why the recorded refutation does not apply

The packet says, correctly, that `p−1 ∈ J_p` for every `p ≥ 5` by Wolstenholme, but
its earlier discussion treated that fact as if it refuted every later fixed-prime
tail. That conclusion conflates two tails:

Wolstenholme kills the tail that starts at
the **first appearance** index `j = d = ord_p(3/2)`: the block `K = p−1` is always
lost, so `p | B_j` fails somewhere above `d`. It says nothing about the tail that
starts past the **last** loss block. If `J_p^{(ε)}` is finite there is such a tail,
and its threshold is `d·(max J_p^{(ε)} + 1)` — a finite arithmetic threshold.
For the q-Apéry denominator transfer, however, the implication from this finite
harmonic set to an all-index tail still depends on the all-level `(M)/(C5)` premise;
it is not an unconditional theorem in the current packet.

At `p = 5` the finiteness is a ten-element check.

## Lemma 1 (descent) — two lines, unconditional

Split `H_n` by divisibility:

```
H_n  =  (1/p)·H_{⌊n/p⌋}  +  Σ_{j ≤ n, p ∤ j} 1/j .
```

The second sum is `p`-integral. So if `v_p(H_n) ≥ 1` and `n ≥ p`, then
`(1/p)H_{⌊n/p⌋} = H_n − (p-integral)` has `v_p ≥ 0`, i.e. **`v_p(H_{⌊n/p⌋}) ≥ 1`**. ∎

Consequently `J_p ∪ {0}` is a **tree** under `n ↦ ⌊n/p⌋`, and the children of `n`
lie in `[pn, pn+p−1]`. An empty level proves the set is exactly what was found —
this is the standard Eswarathasan–Levine descent, restated here because it is the
only thing the whole argument needs from the harmonic side.

## Theorem A — `J_5 = {4, 20, 24}`, finite

| level | candidates | hits |
|---|---|---|
| 1 | `[1,4]` | `{4}` (`H_4 = 25/12`, `v_5 = 2`) |
| 2 | `[20,24]` | `{20, 24}` |
| 3 | `[100,104] ∪ [120,124]` | **none** |

Level 3 is empty, so by Lemma 1 the tree stops: `J_5 = {4,20,24}`. ∎
The same computation gives `J_3 = {2,7,22}` and `J_13 = {12,156,168}` — also finite,
also by an empty level. (`J_7` and `J_11` do not terminate in this range; they are
not needed.)

Note `{p−1, p²−p, p²−1} = {4,20,24}` for `p = 5`: at this prime the
Eswarathasan–Levine guaranteed elements are the *whole* set.

## Lemma 2 (monodromy at 5) — finite certification of the R-line

With `P_N := ord_{5^N}(3/2) = 2·5^{N−1}`:

The all-level statement needed by the transfer is

> **(M)** `R_{j+P_N} ≡ −R_j (mod 5^N)` for every `j ≥ 0` and every `N ≥ 1`.

The statement is certified only at `N = 1, 2, 3` (periods 2, 10, 50) over every
available index, with zero violations. The determinant half is a theorem: the
one-period transfer has
determinant `W_{j+P}/W_j`, and the Casoratian closed form (C) of
`CasoratianBlockLawProof.md` gives

```
W_j = −q^{j+1}(q^{j+1}+2)/(q^{j+1}−1),      q^{P_N} ≡ 1 (mod 5^N),
```

so that determinant is `≡ 1`. The content of (M) is that the transfer is `−1` on
the `R`-line; at the checked levels this is a one-period seed check. No argument
for that seed check at every `N` is supplied here.

**The second solution deliberately fails (M).** `L_{j+P}` is *not* `≡ −L_j` — the
first violation is at `j = 40`, `N = 2`. That failure is the resonant logarithmic
term of the `q`-difference equation, and it is exactly what produces the harmonic
number. A repair that made `L` anti-periodic too would destroy the mechanism.

## Lemma 3 (conditional 5-adic continuity) replaces the false hypothesis (H)

Write the block increment. From (C), at `j = 2m−1` and with `λ = q² = 9/4`,
`π = λ−1 = 5/4`, `u_m = (λ^m−1)/(mπ)`:

```
W_{2m−1} = −λ^m(λ^m+2)/(λ^m−1),        ρ_{2m} − ρ_{2m−1} = −(4/(5m))·g_m ,
g_m := λ^m(λ^m+2) / (u_m · R_{2m−1}R_{2m}) .
```

`λ^m` and `u_m` are 5-adically analytic in `m` (`v_5(π) = 1`, and
`v_5(π^{r−1}/r) ≥ 1` for every `r ≥ 2`), so both depend on `m` only mod `5^{N−1}`
when read mod `5^N`. **Assuming (M) at the relevant level**,
`m ↦ m + 5^{N−1}` shifts `j` by `P_N` and flips the sign of **both**
`R_{2m−1}` and `R_{2m}`, so the product is unchanged. Thus the all-level
continuity conclusion used here is conditional:

> **(C5)** `g_m mod 5^N` depends only on `m mod 5^{N−1}`.

Equivalently, **under the all-level premise**, there is a 5-adic unit `g_*` with
`v_5(g_{5^a t} − g_*) ≥ a+1` for every `a ≥ 0` and every `t` coprime to 5.
Measured at the checked levels: `g_* ≡ 2 (5)`, `≡ 17 (25)`, `≡ 17 (125)` — one
coherent finite-level pattern, and the periods of `g_m mod 5^N` come out exactly
`1, 5, 25`. This pattern does not prove the all-level premise.

### (H) as previously stated is false

`CasoratianBlockLawProof.md` derived the harmonic criterion from

> **(H)** `c_K ≡ c (mod p^ε)` for a fixed `p`-adic unit `c`, independent of `K`.

At `p = 5` that is **false**: `g_m mod 25 ∈ {2, 7, 17}`, three values. The
conclusion was right and the hypothesis was too strong. (C5) is the correct one,
and it is what the telescoped sum actually needs. Falsifier `F7` pins this so the
correction cannot be silently reverted.

## Conditional Theorem B — the exact harmonic law at 5

Assume (C5) at all levels and group `m ≤ K` by `a = v_5(m)`. Because
`5^a t ≡ 0 (mod 5^a)`, (C5) gives
`g_{5^a t} ≡ g_* (mod 5^{a+1})`, so

```
Σ_{m≤K} g_m/m  −  g_*·H_K
   =  Σ_a 5^{−a} Σ_{5∤t ≤ K/5^a} (g_{5^a t} − g_*)/t   ∈  5·Z_5 ,
```

using the exact decomposition `H_K = Σ_a 5^{−a} Σ_{5∤t ≤ ⌊K/5^a⌋} 1/t`. Each term
of the error carries `5^{−a}·5^{a+1} = 5`. Therefore, whenever `v_5(H_K) < 1`,

> `v_5(ρ_j) = v_5(H_{⌊j/2⌋}) − 1`,  and since `p | B_j ⟺ v_5(ρ_j) < 0`,
> **`5 | B_j ⟺ ⌊j/2⌋ ∉ J_5`.**

`ε = v_5(3² − 2²) = v_5(5) = 1`, so `J_5^{(ε)} = J_5`, and the conditional
threshold is `d·(max J_5 + 1) = 2·25 = 50`. This gives Conditional Theorem C. ∎

## Exact verification

`--max-index 300`, exact rational rows, primitive vector formed directly:

| quantity | value |
|---|---|
| `{ j ∈ [2, 301] : 5 ∤ B_j }` | exactly `{8, 9, 40, 41, 48, 49}` — the three blocks `J_5` predicts, nothing else |
| `v_5(B_j) = 1 − v_5(H_{⌊j/2⌋})` | holds at all 294 indices off those blocks |
| `v_5(R_j)` | `0` at every index — the standing unit hypothesis of the block theorem is true at 5 |
| monodromy (M) | `N = 1,2,3` over `300 / 292 / 252` indices, **zero** violations |
| (C5) | `a = 0,1,2` over `120 / 24 / 5` values of `t`; residues `[2]`, `[17]`, `[17]`; coherent |
| tail | `5 ∣ B_j` for every `j ∈ [50, 301]`; `v_5(B_j) ∈ {1,2,3,4}` there |
| descent lemma L1 | no violation among 19 996 actual valuations |

## Conditional family beyond 5

For every prime with a terminating `J_p^{(ε)}` tree, the same all-level transfer
would give its own fixed infinite tail. The table records finite arithmetic data and
the resulting conditional thresholds:

| p | d = ord_p(3/2) | ε | `J_p^{(ε)}` | tail |
|---|---|---|---|---|
| 5 | 2 | 1 | `{4, 20, 24}` | `j ≥ 50` |
| 13 | 4 | 1 | `{12, 156, 168}` | `j ≥ 676` |
| 17 | 16 | 1 | `{16, 272, 288}` | `j ≥ 4624` |
| 23 | 11 | 2 | `{22}` | `j ≥ 253` |
| 41 | 40 | 1 | `{40, 1640, 1680}` | `j ≥ 67 240` |
| 67 | 33 | 1 | `{66, 4422, 4488}` | `j ≥ 148 137` |
| 73 | 36 | 1 | `{72, 5256, 5328}` | `j ≥ 191 844` |

Read the `ε = 1` rows: every one of them is **exactly** `{p−1, p²−p, p²−1}`. Those
three are the elements Eswarathasan–Levine *guarantee*; the terminating tree proves
there is nothing else. So at these primes the descent is not merely finite, it is
the guaranteed set and no more — which is why the threshold is exactly `d·p²`.

`p = 23` is the cleanest illustration of Correction 1 of the Casoratian file: there
`ε = 2` because `23² ‖ 3¹¹ − 2¹¹`, so the criterion `v_p(H_K) ≥ ε` admits only the
Wolstenholme index (`v_23(H_22) = 2`) and the set collapses to a single block —
giving a threshold of 253, second lowest in the table despite `p` being fifth.

Conditionally, each additional prime contributes `≈ ε_p log p` to the window gcd
once `s` passes its threshold. Since `{p−1, p²−p, p²−1} ⊆ J_p` forces the
threshold above `d·p²`, the primes available at start `s` satisfy
`p ≲ √(s/d)`, so `log(window gcd)` grows like `√s` — unbounded, but far below the
height deficit. This would close the window-divisor substep, not the problem.

## Claim boundary

Conditionally, this closes the **window-divisor part** of step 1 of
`three_halves_pade_height_gap` if `(M)/(C5)` holds at all levels, and removes
"effective Boyd" from that conditional route. The finite checks do not close step 1
unconditionally. This bounds no coefficient height and supplies no analytic decay.
The measured deficit `log|B_jρ_∞ − A_j| ≈ +0.76 j²` is untouched, and Erdős #1049
at base `3/2` remains open.

Two things this does **not** settle:

- **the first-power condition.** The 1/q-gap consumer wants a prime to the *first*
  power in a two-row determinant. `v_5(B_j) = 1` exactly when `v_5(H_{⌊j/2⌋}) = 0`,
  which in the tested range occurs only for `⌊j/2⌋ ∈ [100,104] ∪ [120,124]`.
  Whether that recurs cofinally is open, and it is a question about `H_K`
  valuations, not about the recurrence.
- **(M) at every level.** The determinant half is proved; the `−1` on the `R`-line
  is a per-level finite check, certified for `N ≤ 3`.

## Replay

```sh
./repo-python formal_math/probes/erdos1049_fixed_prime_infinite_tail.py --max-index 300
```

Eight finite-level falsifiers: the descent lemma against 20 000 actual valuations;
termination of the `J_5` tree; monodromy at three levels; (C5) with cross-level
coherence of `g_*`; the loss set exactly equal to the predicted blocks; the
valuation law off those blocks; the **negative control** that old hypothesis (H) is
false; and the finite tail itself. Exit `0` iff all eight finite checks pass; it does
not certify all-level monodromy or an unconditional q-Apéry tail. Receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1049_fixed_prime_infinite_tail_receipt.json`.
