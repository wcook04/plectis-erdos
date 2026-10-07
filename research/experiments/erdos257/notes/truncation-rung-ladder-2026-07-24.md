<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Erdős #257 — truncation-rung ladder: witness exclusion theorem + exact certificates J = 3..22 (2026-07-24)

**Provenance.** Derived and machine-verified in a Claude Code session on 2026-07-24
(exact integer arithmetic, Python; script at
`formal_math/erdos257_period_noncollapse/scripts/check_truncation_rung_ladder.py`).
The theorems below are proved in ordinary mathematics in this document and audited
numerically; **none is Lean-formalised yet**. Certificates are exact-arithmetic
computations, not kernel objects. Nothing here claims Erdős #257 is decided.

## 1. Setting

For a rung `J ≥ 2` define truncated weights and tails on exponents `n ≥ 2`:

    w_n^(J) = Σ_{q=1..J} 2^(−qn),        T_{n+1}^(J) = Σ_{q=1..J} 2^(−qn) / (2^q − 1).

`HalfRung(J)` := ∃ A ⊆ {2,3,…} Boolean with Σ_{n∈A} w_n^(J) = 1/2.

**Lemma 1 (forced greedy).** For `J ≥ 2`, `w_n^(J) > T_{n+1}^(J)` (the q = 1 terms
are equal; every `q ≥ 2` term of the tail is the weight term divided by `2^q − 1`).
Hence the weights are strictly superincreasing, the greedy support is the unique
candidate for any target, and `HalfRung(J)` holds iff the greedy orbit for 1/2 never
lands in a fatal interval `(T_{n+1}, w_n)`. Rank 1 is always a safe skip
(`T_2 ≥ 1/2`, with the q = 1 term alone contributing 1/2); ranks 2, 3 are always takes.

**Lemma 2 (parity / infinite support).** No finite `A` attains 1/2: scaling by
`2^(J·max A)` makes the maximal element's contribution odd (its `q = J` term is 1)
while every other contribution and `2^(J·max A − 1)` are even. So a `HalfRung(J)`
support is infinite, and the greedy residual never hits 0.

## 2. Witness exclusion theorem

Define the **misalignment mass**

    μ_J(M) = Σ_{q=2..J} 2^(M mod q) / (2^q − 1).

**Theorem 3 (witness exclusion).** Let `J ≥ 3`, `n ≥ 4`, and suppose some
`M ∈ [n, 2n−2]` has `μ_J(M) ≤ 11/15`. Then **no** Boolean prefix
`D ⊆ {2,…,n−1}` satisfies `T_{n+1}^(J) < 1/2 − Σ_{d∈D} w_d^(J) < w_n^(J)`.
(Fatality at rank `n` is impossible for every prefix, in particular the greedy one.)

*Proof.* Put `E = J(n−1)`, `h = E − M ≥ (J−2)(n−1) ≥ n−1 ≥ 3`, and scale:
`Z = 2^E · (1/2 − Σ_D w_d) = 2^(E−1) − Σ_{d∈D} Σ_{q=1..J} 2^(E−qd) ∈ ℤ`.
Let `A = 2^(E−n)` (the q = 1 term of the scaled `w_n`, also the q = 1 part of the
scaled tail), and `Y = Z − A`. If `D` were fatal, subtracting the shared q = 1 term
gives `0 < Y < Σ_{q=2..J} 2^(E−qn)`.

Let `S = Σ_{d∈D} Σ_{q≥2, qd>M} 2^(E−qd) ≥ 0`. In
`Y + S = 2^(E−1) − A − Σ_{qd≤M} 2^(E−qd)` every term is divisible by
`2^h` (using `M ≥ 1`, `M ≥ n`, and `E − qd ≥ E − M` respectively; there are no
q = 1 crossing terms since `d ≤ n−1 < n ≤ M`). Hence `2^h | Y + S`.

Bounds: for each channel `q ≥ 2` the crossing exponents `qd > M` are
`≥ M + (q − (M mod q))`, so
`Σ_{qd>M} 2^(M−qd) ≤ 2^(M mod q)/(2^q − 1)`; summing, `S ≤ μ_J(M)·2^h`.
And `Y < Σ_{q≥2} 2^(M−qn) ≤ 2^(2n−2−2n) · 1/(1 − 2^(−n)) ≤ (1/4)(16/15) = 4/15 · 2^h`
for `n ≥ 4`. So `0 < Y + S < (11/15 + 4/15)·2^h = 2^h`, contradicting
`2^h | Y + S`. ∎

**Corollary 4 (half-LCM horizon).** With `L_J = lcm(2,…,J)`, taking `M` the least
multiple of `L_J` that is `≥ n` gives `M ≤ 2n−2` whenever `n ≥ L_J/2 + 1`, and
`μ_J(M) = Σ_{q=2..J} 1/(2^q − 1) < E_B − 1 < 0.6067 < 11/15`. So every rank
`n ≥ L_J/2 + 1` is witness-covered.

**Lemma 5 (mod-12 filter, `J ≥ 7`).** `μ_J(M) ≤ 11/15 ⇒ 12 | M`. Odd `M`:
`μ ≥ 2/3 + 1/7 > 11/15`. `M ≡ 2 (mod 4)`: `μ ≥ 1/3 + 1/7 + 4/15 = 78/105 > 11/15`.
`M ≡ 0 (mod 4)`, `3 ∤ M`: `μ ≥ 1/3 + 2/7 + 1/15 + (1/31 + 1/63 + 1/127) > 11/15`.
(Used to speed the good-set scan by 12×.)

## 3. Finite decision procedure

Call `n ∈ [4, L_J/2]` **bad** if no `M ∈ [n, 2n−2]` has `μ_J(M) ≤ 11/15`, and set
`B(J) = max(bad ∪ {3})`.

**Theorem 6 (decision).** `HalfRung(J)` ⇔ the greedy orbit for 1/2 survives ranks
`2..B(J)`. (Fatality is impossible at good ranks by Theorem 3 and at
`n > L_J/2` by Corollary 4; greedy death is absorbing, survival everywhere gives
residual `→ 0`, so the take-set sums to exactly 1/2 and is infinite by Lemma 2.)

## 4. Transfer to the full Mersenne series

**Theorem 7 (compactness transfer).** If `HalfRung(J)` holds for infinitely many
`J`, then some infinite `A ⊆ {2,3,…}` has `Σ_{n∈A} 1/(2^n − 1) = 1/2`, i.e.
`1/2 ∈ 𝒜`, and `UniversalMersenneSubseriesIrrationality` is **false**.

*Proof.* For any support `S`,
`0 ≤ Σ_{n∈S} (1/(2^n−1) − w_n^(J)) ≤ Σ_{q>J} 2^(−2q)/(1−2^(−q)) ≤ (2/3)·4^(−J)`.
So rung solutions `A_J` have full Mersenne value within `(2/3)·4^(−J)` of 1/2.
The map `A ↦ Σ_{n∈A} 1/(2^n−1)` is continuous on the compact space `{0,1}^{2,3,…}`
(uniformly summable weights). A coordinatewise-convergent subsequence of the `A_J`
has limit `A` with value exactly 1/2; `A` is infinite because a finite Mersenne
subset sum has odd reduced denominator. The problem-facing endpoint is the landed
consumer chain in `ErdosProblems/Erdos257` (half membership ⇒ ¬universal). ∎

**Corollary 8 (ladder dichotomy).** Exactly one of:
(a) infinitely many rungs survive — then #257 is **false**, with the limit support
explicit along the subsequence; or
(b) there is `J₀` with: for every `J ≥ J₀` the rung-`J` greedy dies at some **bad**
rank `≤ B(J)` — an infinite family of independent finite integer facts, each an
exact death certificate at an explicitly computable, thin set of ranks.
(b) does not by itself prove #257; it only kills this producer. Every verified rung
in (a)-direction is a permanent finite theorem.

## 5. Certificates (this session, exact integers)

All rungs `J = 3..22` **survive**: no fatal rank anywhere in `2..B(J)`; combined
with Theorems 3–6 this proves `HalfRung(J)` for `3 ≤ J ≤ 22`. Every skip
encountered was **dyadically safe** (`r ≤ 2^(−n)`); the exact tail comparison was
never even needed (`n_hard_skips = 0` throughout).

| J | L_J | analytic window L/2 | B(J) | #bad | #skips ≤ B | fatal |
|---|-----|--------------------|------|------|-----------|-------|
| 3 | 6 | 3 | 3 | 0 | 0 | none |
| 4 | 12 | 6 | 6 | 2 | 2 | none |
| 5 | 60 | 30 | 18 | 9 | 9 | none |
| 6 | 60 | 30 | 18 | 9 | 10 | none |
| 7 | 420 | 210 | 18 | 15 | 10 | none |
| 8 | 840 | 420 | 18 | 15 | 11 | none |
| 9 | 2520 | 1260 | 168 | 27 | 86 | none |
| 10 | 2520 | 1260 | 168 | 81 | 80 | none |
| 11 | 27720 | 13860 | 270 | 267 | 138 | none |
| 12 | 27720 | 13860 | 270 | 267 | 139 | none |
| 13 | 360360 | 180180 | 270 | 267 | 141 | none |
| 14 | 360360 | 180180 | 270 | 267 | 139 | none |
| 15 | 360360 | 180180 | 270 | 267 | 146 | none |
| 16 | 720720 | 360360 | 420 | 417 | 222 | none |
| 17 | 12252240 | 6126120 | 420 | 417 | 230 | none |
| 18 | 12252240 | 6126120 | 420 | 417 | 229 | none |
| 19 | 232792560 | 116396280 | 1008 | 585 | 531 | none |
| 20 | 232792560 | 116396280 | 1530 | 1107 | 795 | none |
| 21 | 232792560 | 116396280 | 1530 | 1107 | 839 | none |
| 22 | 232792560 | 116396280 | 1530 | 1107 | 835 | none |

`B(J)` compresses the certificate window by up to ~115,000× (J = 19: 1008 vs
116,396,280). Growth of `B(J)` is empirically very slow (roughly tracking the
largest good-set gap near the origin, itself far below `L_J`), which is what makes
the ladder pushable to much larger `J`.

## 6. Cross-validation performed

- The explicit `J = 3` collision-prepayment automaton (pulse `(1,1) ↦ (0,3)`,
  carry `K ∈ {1,2}`) reproduces the exact greedy take-set through depth 3000,
  element for element.
- Exhaustive prefix search (`J = 3, 4, 5`, all 131,071 prefixes per rung through
  rank 18): **zero** fatal prefixes anywhere — the fatal interval is unreachable
  even below the witness horizon at small ranks.
- The proof engine of Theorem 3 (`2^h | Y + S` and `S ≤ μ_J(M)·2^h`) audited on
  4000 random `(J, n, M, D)` configurations: zero failures.

## 7. Open producer and next steps

Open statement (the ladder's remaining wall):

    (∗)  HalfRung(J) holds for infinitely many J.

By Corollary 8, (∗) ⇒ #257 false. Conversely #257 ⇒ every large rung dies at a bad
rank ≤ B(J). All twenty tested rungs survive, and no skip in any certified window
was even dyadically tight. Next steps, in order of leverage:

1. **Push the ladder**: `J = 23` needs a chunked good-set scan (`L/12 ≈ 446M`);
   beyond that the scan cost is the only obstacle, since `B(J)` stays tiny.
   Any death found is itself a major finite theorem.
2. **B(J) growth law**: prove an upper bound on the largest good-gap (CRT structure
   of `μ_J ≤ 11/15`) — a polynomial bound would make certificates uniformly cheap.
3. **Lean formalisation**: Theorem 3 is a finite 2-adic cell argument
   (`truncationWitnessMass`, `no_fatal_of_witness`), Lemma 5, Theorem 6, and the
   `norm_num` certificates for small `B(J)`; Theorem 7 composes with the landed
   `HalfCounterexampleFrontier` consumer.
4. **Structural (∗)**: the `J = 3, 4` bounded-carry automata suggest a uniform
   carry-scheduler; the two-prime hot-core construction (session record) solves all
   two-prime channel boxes exactly — the first unsolved geometry is three
   independent prime directions (`111 ↦ 007` prepayment).

## 8. Reproduction

    /usr/bin/python3 formal_math/erdos257_period_noncollapse/scripts/check_truncation_rung_ladder.py ladder 3 4 5 6 7 8 9 10 11 12
    ./repo-python  formal_math/erdos257_period_noncollapse/scripts/check_truncation_rung_ladder.py ladder 13 14 15 16 17 18 19 20
    /usr/bin/python3 formal_math/erdos257_period_noncollapse/scripts/check_truncation_rung_ladder.py exhaustive 3 4 5
    /usr/bin/python3 formal_math/erdos257_period_noncollapse/scripts/check_truncation_rung_ladder.py xcheck3 3000

(`ladder` needs numpy for `J ≥ 17`; `./repo-python` has it.)
