# Erdős 1049: the block structure is a telescoping Casoratian, and the law needs two corrections

## Claim boundary

The **block structure** — that the loss set is a union of whole intervals
`[dK, dK+d−1]` — is **proved here**, unconditionally, from an exact closed-form
Casoratian, under the single standing hypothesis that `R_j` is a `p`-adic unit.
The **harmonic criterion** that selects which blocks are lost is a conditional
transfer, not an unconditional consequence of the Casoratian.  The first form
below assumes the explicit congruence hypothesis (H), which the probe tests on
78 generic primes to index 420; (H) is false at `p = 5`, where the weaker
continuity premise (C5) below is the relevant conditional replacement.

Two claims in `HarmonicZeroBlockLawLab.md` are **corrected**, both with exact
witnesses. Erdős #1049 at base `3/2` remains open, and nothing here bounds a
coefficient height or supplies analytic decay.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction, including the
cleared source framework and analytic `q`-order machinery that motivates this
route, is due to Wadim Zudilin, *On the irrationality of generalized
q-logarithm*, Research in Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained locally at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the base-`3/2` recurrence, the closed Casoratian (C), the
telescoping quotient identity (T), the conditional harmonic transfer, or the
two corrected finite witnesses recorded here.  Those recurrence reductions,
exact rational checks, conditionality boundary, and corrections are authored
in this repository.

## The identity everything comes from

`L_j`, `R_j` are the two solutions of the source recurrence
`y_2 u_{j+1} + y_1 u_j + y_0 u_{j−1} = 0`, with `a = q^{j−1}`, `q = 3/2`,

```
y_0 = q(a−1)(qa+2),        y_2 = (qa−1)(a+2).
```

For any three-term recurrence the Casoratian `W_j = L_{j+1}R_j − L_jR_{j+1}`
satisfies `W_j = (y_0/y_2)·W_{j−1}`. Here

```
y_0/y_2  =  (3/2) · (3^m − 2^m)(3^{m+1} + 2^{m+2})
                  / (3^{m+1} − 2^{m+1})(3^m + 2^{m+1}),
```

and **both** fractions telescope. With `W_0 = −21/2` from the seeds,

> **(C)**  `W_j  =  − 3^{j+1} (3^{j+1} + 2^{j+2}) / ( 2^{j+1} (3^{j+1} − 2^{j+1}) ).`

Checked against exact rationals for `j ≤ 46`, no discrepancy. This is the whole
engine: the recurrence is a dynamical system, but its Casoratian is a *product*,
and a product can be read off.

## What (C) proves

Write `ρ_j = L_j / R_j`. Dividing (C) by `R_jR_{j+1}`,

> **(T)**  `ρ_{j+1} − ρ_j  =  W_j / (R_j R_{j+1})`,

so `ρ_j` is an explicit **telescoping sum**, not the output of a recurrence.
Since `(A_j, B_j)` is the primitive integer vector proportional to `(L_j, R_j)`,

```
p | B_j   ⟺   v_p(L_j) < v_p(R_j)   ⟺   v_p(ρ_j) < 0.
```

For `p ≥ 5`, (C) gives `v_p(W_j) = v_p(3^{j+1} + 2^{j+2}) − v_p(3^{j+1} − 2^{j+1})`,
and `v_p(3^{j+1} − 2^{j+1}) > 0` **exactly when `d | j+1`**, `d = ord_p(3/2)`.

**Theorem (block structure).** Assume `R_j` is a `p`-adic unit at every index.
Then every increment in (T) is `p`-integral except at `j = dK − 1`. Consequently,
if `v_p(ρ_j) < 0` at any `j` in `[dK, dK+d−1]`, then `v_p(ρ_j)` is *constant* on
that whole interval.

That is the block structure, and it is now a theorem. The boundaries are the
poles of a telescoping product; they are not an emergent feature of block
dynamics, and no computation is needed to locate them.

## Where the harmonic numbers come from

Sum the polar increments. At `j = dK − 1`, with `π = q^d − 1`, `ε = v_p(π) = v_p(3^d − 2^d)`,

```
3^{dK} − 2^{dK} = 2^{dK}((1+π)^K − 1) = 2^{dK} · K · π · u_K,
u_K = 1 + Σ_{r≥2} (1/r)·binom(K−1, r−1)·π^{r−1} ≡ 1  (mod p^ε)   for p ≥ 5,
```

so the increment at `j = dK − 1` is `−(1/(πK))·c_K` with

```
c_K = 3^{dK}(3^{dK} + 2^{dK+1}) / ( 2^{2dK} · u_K · R_{dK−1} R_{dK} ).
```

Every `K`-dependence in `c_K` is through `q^{dK} = (1+π)^K ≡ 1 (mod p^ε)`,
through `u_K ≡ 1`, and through `R_{dK−1}, R_{dK}` mod `p^ε`. The recurrence
coefficients depend on `j` only through `a = q^{j−1}`, which is `d`-periodic mod
`p^ε`; hence:

> **(H)**  `c_K ≡ c (mod p^ε)` for a fixed `p`-adic unit `c`, independent of `K`.

Under (H), and on the unit/generic class where the preceding valuation
calculation applies, the polar part of `ρ_j` is
`−(c/π)·Σ_{K≤⌊j/d⌋} 1/K`, i.e.

> `ρ_j  =  ρ_{j_0}  −  (c/π)·H_{⌊j/d⌋}  +  (p-integral)`,

giving the following **conditional** law on the generic class,

```
v_p(ρ_j) = v_p(H_{⌊j/d⌋}) − ε      when v_p(H_{⌊j/d⌋}) <  ε,
v_p(ρ_j) ≥ 0                        when v_p(H_{⌊j/d⌋}) ≥  ε,
```

and therefore

> **`p | B_j  ⟺  v_p(H_{⌊j/d⌋}) < ε`.**

The harmonic-number shape is *derived conditionally* here — it is the `Σ1/K` of
a telescoped product once (H), or the corrected (C5) premise at `p = 5`, controls
the unit weights — where the earlier lab obtained it from a leading-order
expansion of `Σ_{m≤n} 1/(1−q^m)` and recorded the result as measured.  Neither
the finite probe nor this derivation proves the required all-level premise.

## Correction 1 — the criterion is `ε`, not `J_p`

The recorded law used `J_p = { K : p | numerator(H_K) }`, i.e. `v_p(H_K) ≥ 1`.
The derivation gives `v_p(H_K) ≥ ε`. These coincide exactly when `ε = 1` and
part company when `p² | 3^d − 2^d`.

`p = 23` is a live case in range: `d = 11`, `3^11 − 2^11 = 175099 = 23²·331`, so
`ε = 2`. Wolstenholme gives `v_23(H_22) = 2`, which is `≥ ε` — the block is lost
— but a `K` with `v_p(H_K) = 1` would sit in `J_p` while **not** losing its block.

This correction is **conservative** for the window-divisor certificate: raising
the bar from `≥1` to `≥ε` can only make loss blocks rarer, hence window divisors
more abundant, so the certified starts stay certified.

## Correction 2 — the blocks are not wholly lost

The block-structure theorem assumed `R_j` is a `p`-adic unit. `R_j mod p` is
`d`-periodic, and **44 of the 122 primes below 700 have `R_j ≡ 0` on a nonempty
set of residues mod `d`** (always to first order, at fixed residues — e.g.
`p = 11`: `j ≡ 1 (mod 10)`; `p = 137`: `j ≡ 7, 43, 105, 118 (mod 136)`). At such
an index inside a loss block, (T) picks up an extra pole and `p | B_j` after all.

**Exact witness.** `H_3 = 11/6`, so `3 ∈ J_11` and `[30, 39]` is recorded as a
whole loss block. But `11 | B_31`. Verified in exact rational arithmetic, with
the primitive vector formed directly — no `p`-adic code in the path.

So the law as stated — "`p | B_j` for every `j ≥ d` **except** on the whole
blocks `[dK, dK+d−1]` with `K ∈ J_p`" — is **false**. The corrected statement is

> `p | B_j` for every `j ≥ d` except on `{ j ∈ [dK, dK+d−1] : v_p(H_K) ≥ ε }`
> **minus** the `R`-zero indices, a proper subset of the residues mod `d`.

This correction is also **conservative**: it makes more `B_j` divisible.

## Why the downstream certificate survives

The window-divisor criterion needs, for a *non*-divisor, at least one index in
each loss block where `p ∤ B_j`. The `R`-zero set is a union of residue classes
mod `d` and is a **proper** subset — `p` cannot divide every `R_j`, or the
primitive vector would not be primitive — so no loss block is ever covered
entirely. That is falsifier 6 in the probe, and it passes on all 122 primes.

Both corrections therefore leave `252 of 259 certified starts` intact; they move
the certificate from "measured law" to "proved structure plus a conservative
gap".

## Correction 3 (2026-08-24) — (H) is false at `p = 5`, and (C5) is what the sum needs

Hypothesis **(H)** above — `c_K ≡ c (mod p^ε)` for a fixed `p`-adic unit `c`
independent of `K` — is **false at `p = 5`**. In the normalisation

```
ρ_{2m} − ρ_{2m−1} = −(4/(5m))·g_m ,    g_m = λ^m(λ^m+2)/(u_m R_{2m−1}R_{2m}),
λ = q² = 9/4,   π = λ−1 = 5/4,   u_m = (λ^m−1)/(mπ),
```

`g_m mod 5` is the single value `2`, but **`g_m mod 25 ∈ {2, 7, 17}`** — three
values. So (H) already fails at the second digit, at the very prime the probe
certifies on.

The conclusion survives because the telescoped sum does not need a constant. It
needs 5-adic *continuity*:

> **(C5)** `g_m mod p^N` depends only on `m mod p^{N−1}`; equivalently there is a
> unit `g_*` with `v_p(g_{p^a t} − g_*) ≥ a+1` for every `a ≥ 0` and `p ∤ t`.

(C5) is strictly weaker than (H), and the finite checks support it (`g_*` measured
coherently as `2 (5)`, `17 (25)`, `17 (125)`; the periods of `g_m mod 5^N` are
exactly `1, 5, 25`).  It is exactly sufficient if established at every level:
grouping `m ≤ K` by `a = v_p(m)` and using
`H_K = Σ_a p^{−a} Σ_{p∤t ≤ ⌊K/p^a⌋} 1/t`,

```
Σ_{m≤K} g_m/m  −  g_*·H_K  =  Σ_a p^{−a} Σ_{p∤t} (g_{p^a t} − g_*)/t  ∈  p·Z_p ,
```

since each term carries `p^{−a}·p^{a+1}`. That is the same conclusion (H) was
introduced to reach.

(C5) in turn follows from a **monodromy lemma** if that lemma holds at every
level.  The lemma is currently certified only at `N = 1,2,3`, with zero
violations:

> **(M)** `R_{j+P_N} ≡ −R_j (mod 5^N)`, `P_N = ord_{5^N}(3/2) = 2·5^{N−1}`.

Its determinant half is a corollary of (C) itself (`q^{P_N} ≡ 1`, so the one-period
transfer has determinant `≡ 1`); the content is the `−1` on the `R`-line. The
second solution `L` deliberately violates (M) — first at `j = 40`, `N = 2` — and
that violation is the resonant logarithmic term producing the harmonic number.

**Conditional consequence, and it is not small.** If the all-level transfer is
established, then the criterion `v_p(H_K) ≥ ε` and a finite `J_p^{(ε)}` imply
`p | B_j` for **every** `j` past the last loss block. At `p = 5`,
`ε = v_5(3²−2²) = 1` and `J_5 = {4,20,24}` is finite by the descent tree, so
the conditional conclusion is `5 | B_j` for all `j ≥ 50`; the finite replay does
not make that an unconditional theorem.  Full statement, proof chain and prime family:
[`FixedPrimeInfiniteTailProof.md`](FixedPrimeInfiniteTailProof.md).

## Also proved: an exact series for the target constant

`ρ_j → Σ_{n≥1} 2^n/(3^n − 2^n)`, the Erdős #1049 constant at base `3/2`
— checked to **123 decimal digits**. With (C) and (T) that is an exact identity:

```
Σ_{n≥1} 2^n/(3^n−2^n)
   =  L_{j₀}/R_{j₀}  −  Σ_{i ≥ j₀}  3^{i+1}(3^{i+1}+2^{i+2})
                                    ─────────────────────────────────
                                    2^{i+1}(3^{i+1}−2^{i+1}) R_i R_{i+1}
```

and the remainder of the `j`-th approximation is the tail of that series, in
closed form:

```
R_j·ρ_∞ − L_j  =  −R_j · Σ_{i ≥ j} W_i/(R_i R_{i+1})   ≈  W_j / R_{j+1}.
```

Since `|W_j| ≈ (3/2)^{j+1}` is only *linear* in the exponent while `log|R_j|` is
quadratic, the rational forms decay superbly; the entire difficulty is the
content cleared when passing to `(A_j, B_j)`. Measured on the raw prefix:
`log|B_j| ≈ 1.96 j²` and `log|B_jρ_∞ − A_j| ≈ +0.76 j²`. The deficit is
**quadratic in `j`**, so no bounded-rank recombination and no single window
prime — worth `log p = O(s)` — can close it. This is a quantitative restatement
of the packet's standing warning not to read the natural expanding prefix as
evidence of asymptotic compression, and it is why the window divisor is used for
the nonvanishing `1/q` step rather than for height reduction.

## Replay

```sh
./repo-python formal_math/probes/erdos1049_casoratian_block_law.py
./repo-python formal_math/probes/erdos1049_casoratian_block_law.py \
    --max-index 420 --max-prime 700 --exact-index 46 --json
```

Six falsifiers: the closed form (C) against exact rationals; the limit against
the target constant; the divisibility law and the strict valuation law on the
generic class; a regression pinning `(p, j) = (11, 31)` as exceptional so the
anomaly cannot be silently absorbed; and the load-bearing check that no loss
block is ever wholly covered. Exit `0` iff all six pass. Receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1049_casoratian_block_law_receipt.json`.
