# Erdős 1049: the q-Apéry loss-block harmonic mechanism and its boundaries

## Superseded in two places — see `CasoratianBlockLawProof.md`

1. The **block structure** is no longer measured: it is proved from a
   closed-form telescoping Casoratian
   `W_j = −3^{j+1}(3^{j+1}+2^{j+2}) / (2^{j+1}(3^{j+1}−2^{j+1}))`, whose only
   `p`-adic poles sit at `j ≡ −1 (mod d)`. The harmonic-number shape is
   *derived conditionally* from the same identity once the weighted transfer
   is controlled; it is not an unconditional consequence of the leading-order
   expansion.
2. The law **as stated below is false**. Two corrections, both conservative for
   the certificate: the criterion is `v_p(H_K) ≥ ε` (not `K ∈ J_p`; they differ
   once `p² | 3^d − 2^d`, live at `p = 23`), and the blocks are **not wholly
   lost** — `11 | B_31` although `3 ∈ J_11` puts `[30,39]` in the loss set, by
   exact rational arithmetic. The exceptional indices are the `d`-periodic zero
   set of `R_j mod p`, present for 44 of the 122 primes below 700.

The rest of this lab stands as the record of how the law was found.

## Claim boundary

The block law below is an **exact empirical identification**, checked in both
directions against an independent p-adic run of the source recurrence. It is not
proved here. Wolstenholme's theorem, the Eswarathasan–Levine triple, and the
reflection symmetry are classical or proved; the identification that connects
them to `B_j` is measured. Erdős #1049 at base `3/2` remains open, and nothing
here bounds a coefficient height or supplies analytic decay.

## Source and attribution boundary

The ambient generalized-`q`-logarithm Padé/Hankel construction behind the
`B_j` recurrence is due to Wadim Zudilin, *On the irrationality of generalized
q-logarithm*, Research in Number Theory 2 (2016), Article 15, DOI
[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).  The
downloaded primary source is retained at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`; Section 4,
source TeX lines 278--380, defines the Hankel determinants, proves the
backward-shift order lemma, and derives the determinant estimate.  It does
**not** state the base-`3/2` loss-block identification or its transfer to
`B_j`.

The external harmonic input is grounded in the downloaded primary PDFs
`annexes/boyd-1994-p-adic-harmonic-partial-sums/source.pdf` (Boyd, *A p-adic
Study of the Partial Sums of the Harmonic Series*, Experimental Mathematics 3
(1994), 287--302; printed pp. 287--288, Introduction, for Wolstenholme,
`J_p`, and the Eswarathasan--Levine provenance; printed pp. 290--293, Section
3, for the recursive `J_p` generation) and
`annexes/sanna-2016-p-adic-harmonic-valuation/source.pdf` (Sanna, *On the
p-adic valuation of harmonic numbers*, Journal of Number Theory 166 (2016),
41--46; PDF p. 1, abstract and Introduction, for `J_p`, `J_5`, and the open
finiteness conjecture, and PDF p. 1, Lemma 1.2, for the valuation equivalence).
The current status check is also cross-checked against the downloaded primary
arXiv PDF `annexes/arxiv-2503-15714-harmonic-conjectures/source.pdf`, PDF
pp. 1--2 for the definitions, conjectures, and recursion, and PDF p. 3 for
the finite-range theorem and its limitations.  None of these sources states
the q-Apéry weighted transfer, the Casoratian block map, or the two corrected
`B_j` witnesses; those recurrence-specific reductions, finite replays, and
the explicit empirical-versus-conditional boundary are authored in this
repository.

## The superseded empirical law

The earlier lab stated the following generic/unit-class identification.  It is
retained as historical context, not as the current theorem: the Casoratian note
records why the statement needs both the `ε` correction and the `R`-zero
exception, while the fixed-prime route records the separate all-level transfer
boundary.

Let `p ≥ 5` be prime, `d = ord_p(3/2)`, and let

```
J_p  =  { K ≥ 1 : p divides the numerator of H_K },        H_K = Σ_{i≤K} 1/i
```

be the **Eswarathasan–Levine set** of harmonic zeros mod `p`. Then

> **Historical statement (superseded):** `p | B_j` for every `j ≥ d`, **except** on the whole blocks
> `[dK, dK+d−1]` with `K ∈ J_p`.

That was the loss-block structure `QAperyTailDenominatorLab.md` observed and
could not name. Its table

| prime | order | first loss block |
|---:|---:|---:|
| 5 | 2 | 8–9 |
| 19 | 3 | 54–56 |
| 13 | 4 | 48–51 |
| 7 | 6 | 36–41 |
| 29 | 7 | 91–97 |
| 97 | 8 | 88–95 |
| 23 | 11 | 242–252 |

is exactly `min J_p · d` in every row: `J_5 ∋ 4`, `J_{19} ∋ 18`, `J_{13} ∋ 12`,
`J_7 ∋ 6`, `J_{29} ∋ 13`, `J_{97} ∋ 11`, `J_{23} ∋ 22`. The sporadic ones are the
familiar small harmonic numerators — `H_3 = 11/6`, `H_5 = 137/60`,
`H_{10} = 7381/2520 = 11²·61/2520` — and indeed `min J_{11} = 3`,
`min J_{137} = 5`, `min J_{61} = 10`.

**Verification.** A p-adic run of the source recurrence (`erdos1049_padic_window_divisor_law.py`)
computes the loss blocks from `p | B_j ⟺ v_p(R_j) > v_p(L_j)` without ever
forming the 10⁶-bit rationals. Compared with `J_p` computed from harmonic
numerators alone: **62 primes below 400 checked to block index `K ≤ 130`,
agreement in both directions on every one, 0 mismatches** — including the
sporadic zeros (`min J_{11} = 3`, `min J_{137} = 5`, `min J_{199} = 38`) and the
primes with no zero in range (`J_{211} ∩ [1,130] = ∅`, which is exactly why 211
is the inherited divisor carrying the early windows). All seven lab rows above
and the regression anchor `211 | B_j` for `5 ≤ j ≤ 255` reproduce. Two
computations sharing no code, no arithmetic backend and no mathematical route.

## Why

At `q = 3/2` the q-integers are exactly the Lucas sequence of `3^m − 2^m`:

```
[m]_q = (1 − q^m)/(1 − q) = (3^m − 2^m)/2^{m−1},
(q)_n = (−1)^n 2^{−n(n+1)/2} ∏_{i≤n}(3^i − 2^i),
[n,k]_q = 2^{−k(n−k)} · D_n/(D_k D_{n−k}),   D_n = ∏_{i≤n}(3^i − 2^i),
```

so Zudilin's rows `b(n) = Σ_k (−1)^k q^{k(k+1)/2}[n+k,k]_q[n,k]_q` are Lucasnomials
and are `p`-integral, while the potential `c(n,k)` carries `Σ_{m≤n} 1/(1−q^m)`,
whose `p`-adic poles sit exactly at `d | m`. Writing `q^d = 1 + p^ε w` with
`p ∤ w` and `ε = v_p(3^d − 2^d)`,

```
1 − q^{di} = −i p^ε w (1 + O(p^ε)),
```

so at leading order

```
Σ_{i≤K} 1/(1 − q^{di})  =  −p^{−ε} w^{−1} H_K + O(1),        K = ⌊n/d⌋.
```

The leading coefficient has a harmonic numerator, so a zero of `H_K` is the
mechanism that can cancel the pole.  This is a leading-order computation, not a
proof of the selector; the exact runs confirm only the superseded empirical law
on their finite ranges.

## What remains classical

Three classical harmonic facts inform the conditional q-Apéry discussion.

**Wolstenholme (1862).** `p² | H_{p−1}` for every `p ≥ 5`, so `p−1 ∈ J_p`
**always**. Every prime therefore has a harmonic loss index at the block
`[d(p−1), dp−1]`.  This classical fact does not by itself refute a later
fixed-prime q-Apéry denominator tail: lifting a harmonic loss to `B_j` requires
the source-specific weighted transfer, which remains conditional.

**Eswarathasan–Levine (1991).** `{p−1, p²−p, p²−1} ⊆ J_p` for every `p ≥ 5`.
Under the historical/conditional transfer, these harmonic zeros predict loss
blocks at `k = p−1, p²−p, p²−1`; the exact runs give
`J_5 = {4,20,24}`, `J_7 = {6,42,48}`, `J_{13} = {12,156,168}` — the triple and
nothing else in those finite checks. They conjecture `J_p` is finite for all
`p`; that conjecture remains a harmonic-number statement, not a proof of an
all-index q-Apéry denominator law.

**Reflection.** `J_p ∩ [1, p−2]` is symmetric under `K ↦ p−1−K`. Proof: for
`1 ≤ K ≤ p−2`, `H_{p−1−K} = H_{p−1} − Σ_{i=p−K}^{p−1} 1/i ≡ 0 − Σ_{j≤K} 1/(−j)
= H_K (mod p)`. Checked: `J_{61} = {10,50,60}`, `J_{29} = {13,15,28}`,
`J_{11} ⊃ {3,7}`, `J_{97} ⊃ {11,85}`, `J_{137} ⊃ {5,131}` — every sporadic zero
comes in a mirror pair.

## The step-1 predicate under the superseded selector

The window at start `s` is `[s, s + W(s)]`, `W(s) = 3s² + 5s + 3`. Under the
historical generic/unit block model, a block `[dK, dK+d−1]` meets it iff
`1 ≤ K ≤ (s + W(s))/d`. Hence

> `p` is a window divisor at start `s`  ⟺  `d ≤ s` and
> `J_p ∩ [1, ⌊(s + W(s))/d⌋] = ∅`.

For a **primitive** prime — one with `ord_p(3/2) = s` exactly, which is what
"source-supported at first appearance" means, since `p | 3^{d}−2^{d}` for any
`d = ord | s` would have made `p` appear at the earlier start `d` — this is

> `J_p ∩ [1, 3s+6] = ∅`     (the bound is `3s + 6 + 3/s`).

These equivalences are a selector for the historical/conditional model; they
are not an unconditional q-Apéry criterion because the corrected transfer has
the `ε` threshold and `R`-zero exceptions.

## The residual as `WindowDivisorSupplyLab.md` stated it is false

That lab named the obligation as

> show that for every large `s` the prime `p_s | 3^s − 2^s` selected at first
> appearance has no loss block meeting `[s, s + 3s² + 5s + 3]`.

**It already fails, and the law says exactly why.** Failures at `s ≤ 260`:

| s | primitive prime | `J_p ∩ [1, kmax]` | cause |
|---:|---:|---|---|
| 2 | 5 | `{4}` | `p−1 = 4 ≤ 13` |
| 4 | 13 | `{12}` | `p−1 = 12 ≤ 18` |
| 6 | 7 | `{6}` | `p−1 = 6 ≤ 24` |
| 8 | 97 | `{11}` | **sporadic** zero `H_{11}` |
| 10 | 11 | `{3, 7, 10}` | **sporadic** `H_3 = 11/6` |
| 12 | 61 | `{10}` | **sporadic** `H_{10} = 11²·61/2520` |
| 18 | 577 | `{24}` | **sporadic** zero `H_{24}` |

Two distinct failure modes, both invisible to the earlier table. For
`s = 2, 4, 6` the prime is simply too small — the Wolstenholme block at `k = p−1`
lands inside a window of width `3s+6`, which needs only `p ≤ 3s+7`. For
`s = 8, 10, 12, 18` the prime is large (97, 11, 61, 577) but carries a sporadic
harmonic zero below `3s+6`.

The earlier lab could not see this because its first-appearance table listed only
the starts where a new prime **did** enter the window gcd — `3,5,7,9,11,13,14` —
so its "seven out of seven" is a statement about the successes only. At
`s = 6, 8, 10, 12` the window gcd is nontrivial but the divisor is **inherited**
(211, entering at `s = 5`), not source-supported at `s`. Its own
"only `s = 0,1,2,4` have gcd 1" is reproduced exactly here by both methods.

## What survives, certified, to s = 260

The correct predicate is the source-supported one with the failures admitted, and
it can be certified **without factoring `3^s − 2^s`**. Let `Q_s` be the primitive
part `∏_{m|s}(3^m − 2^m)^{μ(s/m)}` with all primes `≤ s` stripped (primitive
primes satisfy `p ≡ 1 mod s`, so `p > s`), and let
`G_s = ∏_{K ≤ 3s+6} numerator(H_K)`. Strip from `Q_s` every prime dividing `G_s`.
If the cofactor exceeds 1 it contains a primitive prime `p` with
`J_p ∩ [1, 3s+6] = ∅` — a source-supported window divisor at `s`.

| | |
|---|---|
| starts tested | `2 ≤ s ≤ 260` |
| certified | **252** |
| not certified | 7, exactly `{2, 4, 6, 8, 10, 12, 18}` |
| largest uncertified start | **18** |

**Every start from 19 to 260 carries a source-supported harmonic candidate**, and
the certificate is a gcd computation, not a factorisation.  This finite result
does not prove that the corresponding q-Apéry `B_j` window divisor exists
without the corrected all-level transfer.  The earlier lab reached `s ≤ 14`
with 677 exact rational rows near 10⁶ bits at the top.

## What the conditional residual is now

Under the corrected conditional transfer, the cofinal step-1 question reduces
to:

> for cofinally many `s`, some prime divisor `p` of `3^s − 2^s` with
> `ord_p(3/2) = s` divides no harmonic numerator `H_K` with `K ≤ 3s + 6`.

Three things are worth saying plainly about how much that is worth.

**It is not a counting theorem.** `G_s` has about `(3s)²/2` bits and so can
absorb up to `≈ 2.8 s²` primes, while the primes with `ord ≤ s` divide
`∏_{m≤s}(3^m − 2^m) < 3^{s(s+1)/2}` and number at most `≈ 0.34 s²`. A pigeonhole
between those two sets does not close, in either direction. The size bound
`p ≤ N_K < e^{1.04K}` is likewise too weak, since primitive primes are only
`≤ 3^s`.

**The heuristic is strong, and it is Boyd's.** A primitive prime meets a
harmonic zero below `3s+6` with probability `≈ (3s+6)/p`, and primitive primes of
`3^s − 2^s` have size `≈ 3^{φ(s)}`. Boyd's model for `J_p` gives the same answer.
This supports cofinality heuristically but does not establish it; the proof is
missing, and the source-specific transfer is an additional open boundary rather
than an unexamined feature of a recurrence.

**It changed which obstruction is live.** The loss blocks were the reason
`QAperyTailDenominatorLab.md` retired the fixed-tail divisor target, but that
retirement cannot be justified by Wolstenholme alone.  Wolstenholme supplies an
early harmonic loss; the q-Apéry fixed-tail implication remains conditional.
The failures above still give the sharp finite statement about where the moving
window is not source-supported.

## Replay

```sh
./repo-python formal_math/probes/erdos1049_padic_window_divisor_law.py --max-start 30
./repo-python formal_math/probes/erdos1049_harmonic_zero_certificate.py --max-start 260
```

The first runs the source recurrence p-adically and checks the block law against
the seven lab rows and the `211` anchor; the second runs the factoring-free
certificate. Exit code `0` iff every anchor reproduces and no falsifier fires.
