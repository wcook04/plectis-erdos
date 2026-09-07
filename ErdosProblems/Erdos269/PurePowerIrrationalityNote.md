# Irrationality of the pure prime-power running-LCM series

**Claim boundary, stated first.** This is **not** Erdős #269. Erdős #269 asks
about `S = Σ_{smooth s ≥ 2} 1/H(s)`, which remains open. What is proved here is
the irrationality of the **one-channel sub-series** `Σ_p = Σ_{m≥1} 1/H(p^m)`,
carried by the pure powers of a single prime. The proof is elementary and
unconditional. Its interest is twofold: it is a genuine unconditional
irrationality theorem in the #269 family, and it isolates in one line exactly
what makes `S` hard.

Companion Lean module: `ErdosProblems.Erdos269.PurePowerIrrationality`
(green focused build, no `sorry`; four theorems, the arithmetic core).
Checker: `scripts/check_erdos269_pure_power_irrationality.py`.

**Novelty: UNVERIFIED.** The argument is elementary and of a standard type
(small nonzero linear forms, Sturmian right-special factors, Cantor series with
bounded radices). For `r = 2` the statement is already known and strictly
weaker than what is known — Hecke–Mahler gives transcendence there. Whether the
`r ≥ 3` case is new, folklore, or already in the Cantor-series / Ostrowski
literature has **not** been checked against external sources. Do not present
this as new until a prior-art pass has been run. What is verified is that the
proof is correct, and that it does not reach `S`.

## 0. Setting

Fix distinct primes `p_1 < … < p_r`, `r ≥ 2`, and let

    H(x) = ∏_i p_i^{⌊log_{p_i} x⌋}

be the running LCM of the smooth prefix. Fix one channel `p = p_i` and put

    Σ_p = Σ_{m≥1} 1/H(p^m),
    H_M = H(p^{M-1}),
    y_M = H_M · Σ_{m≥M} 1/H(p^m),
    b_m = H(p^{m+1}) / H(p^m).

For `{2,3,5}` with `p = 2`: `b_m ∈ {2,6,10,30}` and

    Σ_2 = 0.5931259677635827115280234…

**Theorem.** `Σ_p` is irrational.

Also verified exactly: `Σ_{p∈{2,3,5}} (p−1)·Σ_p = 1` (the landed telescope), so
the three channel values are rationally dependent even though each is irrational.

## 1. The three structural facts

**(C) Clearing.** For `m < M`, `H(p^m) ∣ H_M`, because every exponent
`⌊log_q p^m⌋` is monotone in `m`. Hence

    y_M = H_M·Σ_p − (integer).                                     (1)

**(R) Range and recurrence.** `0 < y_M < 1`, and

    y_{M+1} = b_{M-1}·y_M − 1.                                     (2)

(2) is just `b_{M-1}·y_M = 1 + y_{M+1}`, read off the definition. `y_M < 1`
because every `b ≥ 2` and not all of them equal `2`.

**(I) Interval confinement.** Combining (2) with `0 < y_{M+1} < 1`:

    y_M ∈ ( 1/b_{M-1} , 2/b_{M-1} ).                               (3)

For `{2,3,5}`, `p = 2`, this reads

| `b` | interval |
|---|---|
| 2 | (0.5000, 1.0000) |
| 6 | (0.1667, 0.3333) |
| 10 | (0.1000, 0.2000) |
| 30 | (0.0333, 0.0667) |

Two intervals are disjoint exactly when `max(b,b′) > 2·min(b,b′)`. Every pair
qualifies except `{6,10}` — and `{6,10}` is a *simultaneous* flip of both odd
channels, so it never arises from a single-channel flip.

**This is the whole point.** The confining interval of the state is determined by
the *current radix letter alone*. That is available only because every Cantor
digit here equals `1`. For `S` the digits are dyadic-shell lattice counts growing
like `n²`, the state grows like `a²`, and no interval confinement exists —
which is precisely why the same argument does not touch #269.

## 2. The combinatorial input

The radix word `(b_m)` is determined by the `r−1` Beatty sequences
`δ_q(m) = ⌊(m+1)log_q p⌋ − ⌊m log_q p⌋`, each a Sturmian word of irrational
slope. For `{2,3,5}` the joint word has exactly `(N+1)²` factors of length `N`
(measured; `|W_3| = |W_5| = N+1`, `|W_b| = (N+1)²`).

For every `L` there is a **right-special** factor `u` of length `L`: a word with
two distinct one-letter extensions `ua`, `ua′`. Take `u` right-special in one
odd channel, with the other channel's window fixed; density of
`{(m·log_3 2, m·log_5 2)}` in `T²` makes both product cells nonempty, so both
extensions occur. The two extensions then differ by exactly one prime factor
`q ≥ 3`, so `a′ = q·a` and the pair is separated in the sense of (3).

**Measured caution.** Two factors of length `N` at Hamming distance one exist
**only** at positions `0` and `N−1` — never in the interior. (Counts at
`N = 8, 12, 17`: positions `{0, N−1}` only.) An earlier version of this argument
tried to place the flip at depth `≈ N/2` and is false. The proof must use the
*right-special* (last-position) flip, and nothing else.

## 3. The proof

Fix `L`. Let `u` be right-special of length `L` with separated extensions
`a, a′ = q·a`, `q ≥ 3`, and let `M ≠ M′` be occurrences of `ua`, `ua′`. Write
`P = ∏ u` for the product of the common prefix, so `P ≥ 2^L`. Splitting both
states after the common prefix,

    y_M − y_{M′} = ( y_{M+L} − y_{M′+L} ) / P.                     (4)

By (3), `y_{M+L} ∈ (1/a, 2/a)` and `y_{M′+L} ∈ (1/(qa), 2/(qa))`, and since
`q ≥ 3`,

    y_{M+L} − y_{M′+L} > 1/a − 2/(3a) = 1/(3a) ≥ 1/(3·30).

Hence, with `κ = 1/90`,

    0 < κ/P ≤ | y_M − y_{M′} | ≤ 1/P ≤ 2^{−L}.                     (5)

By (1), `y_M − y_{M′} = (H_M − H_{M′})·Σ_p − (integer)`, and `H` is strictly
increasing so `n := H_M − H_{M′} ≠ 0`. Since `|y_M − y_{M′}| < 1`, the nearest
integer is the one above, so

    ‖ n·Σ_p ‖ = | y_M − y_{M′} | ∈ ( 0 , 2^{−L} ].                  (6)

Now suppose `Σ_p = A/B`. Then `‖n·Σ_p‖` lies in `(1/B)·Z`, so any nonzero value
is at least `1/B`. Taking `L` with `2^{−L} < 1/B` contradicts (6). ∎

The argument is the classical "arbitrarily small nonzero linear form" criterion;
all the work is in producing forms that are provably **nonzero**, which (3)+(4)
deliver and which no argument for `S` currently does.

## 4. What is checked

`scripts/check_erdos269_pure_power_irrationality.py`, integers and `Fraction`
only, no floating-point logarithms. Every state is bracketed rigorously by
`y_M ∈ (A, A + 1/P)` using `0 < y_{M+depth} < 1`.

* (T) telescope `Σ_p (p−1)Σ_p = 1` exact to the truncation cutoff;
* (C) clearing: 0 failures;
* (I) confinement `y_M ∈ (1/b, 2/b)`: 0 failures in 1,500 scales;
* (S) a separated right-special factor found at every tested length, scanning
  10,000 positions;
* (G) gaps, with exact rational brackets:

| L | M | M′ | a | a′ | 1/P | gap | nonzero | bits of \|n\| |
|---|---|---|---|---|---|---|---|---|
| 4 | 19 | 3 | 6 | 30 | 2.778e−04 | 3.703e−05 | yes | 52 |
| 8 | 1 | 540 | 2 | 10 | 1.286e−07 | 5.215e−08 | yes | 1617 |
| 12 | 4 | 1012 | 6 | 30 | 1.191e−11 | 1.588e−12 | yes | 3031 |
| 16 | 3 | 133 | 10 | 30 | 3.308e−15 | 2.205e−16 | yes | 394 |
| 20 | 3 | 1206 | 6 | 30 | 9.188e−19 | 1.225e−19 | yes | 3613 |
| 24 | 312 | 3 | 2 | 6 | 8.507e−23 | 2.836e−23 | yes | 931 |
| 28 | 2 | 2828 | 2 | 10 | 3.939e−26 | 1.575e−26 | yes | 8479 |

Each gap is a nonzero rational lying below `1/P`, and the multiplier
`n = H_M − H_{M′}` is a nonzero integer of up to 8,479 bits. So the linear forms
`n·Σ₂ − (integer)` are provably nonzero and shrink geometrically, which is the
whole content of the theorem.

## 5. Reach, and what it does not give

*Reach.* The argument uses only: clearing, `0 < y < 1`, the all-ones recurrence,
and the existence of right-special factors with a non-dyadic flip. So it proves
irrationality of `Σ_{m≥1} 1/H(p^m)` for **every** channel of **every** finite
prime support with `r ≥ 2`, and likewise for the merged pure-power series
`Σ_j 1/H(r_j)` over the ordered prime-power ladder, whose digits are also all
`1`. For `r = 2` the conclusion is already known and stronger (Hecke–Mahler
gives transcendence); the content is `r ≥ 3`.

*What it does not give.* Nothing about `S`. The single hypothesis that fails for
`S` is the all-ones digit sequence: `S`'s ladder digits `C_j` are counts of
smooth numbers in an inter-boundary gap, growing like `j²`, so the normalized
tail state grows like `a²` (`X_a ≥ (1/60)(⌊a/(2log₂3)⌋+1)(⌊a/(2log₂5)⌋+1)`) and
(3) has no analogue. In the mod-1 picture the state `θ_a = {X_a}` *is* confined
to `(0,1)`, but its digits `ε_a = ⌊b_a θ_a⌋` are then no longer constant and are
not a function of the radix word, so no right-special factor of the radix word
separates two `θ`-states. The gap between this theorem and #269 is exactly the
gap between a constant digit sequence and one of unknown subword complexity.

## 6. A criterion for `S` that this suggests

Under rationality `S = p/q`, the proper (carry-normalized) digit word
`ε_a = ⌊b_a{X_a}⌋` satisfies

    P_ε(n) ≤ q · P_b(n) ≤ q·(n+1)² ,

because the window `(ε_a,…,ε_{a+n−1})` is a function of `({X_a}, b_a,…,b_{a+n−1})`
and `{X_a}` takes at most `q` values, while the radix word is a product of two
Sturmian words. Contrapositive: **superquadratic subword complexity of the
proper digit word implies `S` is irrational**, and `q ≥ P_ε(n)/(n+1)²` for every
`n`. This is the corrected home for the entropy intuition: the retired
Adamczewski–Bugeaud route measured the complexity of the *radix* word, which is
`Θ(n²)` and therefore useless; the digit word is the object whose complexity is
unconstrained a priori.

---

## Correction, 2026-09-06: the headline theorem is conditional

**What is corrected.** The headline `**Theorem.** Σ_p is irrational` and the
reach sentence of §5, "it proves irrationality of `Σ_{m≥1} 1/H(p^m)` for
**every** channel of **every** finite prime support with `r ≥ 2`", are stated
unconditionally. The proof of §3 rests on one input that is not established.
No checked arithmetic anywhere in this note changes.

### The exact step

§2, one sentence:

> Take `u` right-special in one odd channel, with the other channel's window
> fixed; density of `{(m·log_3 2, m·log_5 2)}` in `T²` makes both product cells
> nonempty, so both extensions occur.

Density of that orbit in the **full** two-torus holds exactly when
`1, log_3 2, log_5 2` are ℚ-linearly independent. Dividing a relation
`p + q·log_3 2 + r·log_5 2 = 0` through by `ln 2` puts it in the equivalent
form `q/ln 3 + r/ln 5 + p/ln 2 = 0`, so the input is ℚ-independence of
`1/ln 2, 1/ln 3, 1/ln 5`. Clearing denominators instead gives

    p·ln3·ln5 + q·ln2·ln5 + r·ln2·ln3 = 0 ,

the vanishing of a `2×2` determinant of logarithms of algebraic numbers, which
is an instance of the **four exponentials conjecture**. This repository already
records that as unproved, at `BlockKernelProgrammeLab.md` §7.1: "That
independence is not unconditional … **OPEN.**" Baker's theorem does not reach
it, because the relation is quadratic in logarithms rather than a linear form
in them; the proved six exponentials theorem gives rank `≥ 2` of a `3×2` log
array and does not forbid a single vanishing `2×2` minor. Hofer and Kaltenböck
name the same independence as an unestablished input, and Karimov et al.
discuss this `{2,3,5}` coding and the role of Schanuel's conjecture. Those two
external attributions are `reported_prior`; they were supplied with the brief
and were not read this pass.

Individual irrationality of `log_3 2` and of `log_5 2` gives density of each
**coordinate** orbit on its own circle. It does not give density of the
**joint** orbit, and §2 needs an orbit point inside a prescribed product cell.

### No later source-specific proof exists in `P`

The twenty-three Lean modules and the ten notes in this directory were read for
any other derivation of the separated right-special extension. There is none.
`PurePowerIrrationality.lean` has zero importers anywhere in `P`, is absent
from `Root.lean` and from `AxiomAudit.lean`, and its own docstring already
states the boundary correctly: "The `clear` and `gaps` hypotheses of
`irrational_of_clearing_and_small_gaps` range over arbitrary sequences and are
not discharged in this file for `Σ₂` or for any other concrete series" and "No
theorem in this file establishes `Irrational Σ₂`." The Lean module is not
affected by this correction. The overclaim is in the prose.

### Corrected statement

> **Theorem (conditional).** Fix distinct primes `p_1 < … < p_r`, `r ≥ 2`, and
> one channel `p`. Suppose that for every `L` the radix word `(b_m)` has a
> right-special factor of length `L` whose two occurring extensions differ by
> exactly one non-dyadic prime factor. Then `Σ_p` is irrational.

Three regimes, stated separately.

* `r = 2`. The hypothesis holds unconditionally: the radix word is Sturmian, so
  it has exactly one right-special factor of every length and its two
  extensions differ by the single other prime. The conclusion is already known
  and strictly weaker than Hecke–Mahler transcendence, so this regime carries
  no content.
* `r = 3`, and `{2,3,5}` in particular. The hypothesis was derived here from
  full-torus density, which is unproved. The repair assessed below supplies it
  by a different route and does not need the independence.
* `r ≥ 4`, and the merged pure-power ladder of §5. The hypothesis has no proof
  here at all. The merged ladder is a different word from any single channel's
  radix word, so nothing in this note or in the repair applies to it.

### What is unaffected

* Every statement of §1: clearing (C), range and recurrence (R), interval
  confinement (I). These are exact and use no orbit input.
* Every theorem in `PurePowerIrrationality.lean`.
* Every line of §4. The telescope, zero clearing failures, zero confinement
  failures in 1,500 scales, a separated right-special factor found at every
  tested length over 10,000 scanned positions, and the seven exact gap brackets
  through `L = 28` all stand exactly as recorded. A scan that finds the
  extension pair at every tested length is evidence for the hypothesis and is
  not a proof of it at every length.
* The exact telescope `Σ_{p∈{2,3,5}} (p−1)·Σ_p = 1`. It is a prime-power
  telescope with no orbit input. It stands, and so does its consequence that
  the axis jump-correction of the torus Fourier representation is exactly
  `1/2` and the total correction exactly `17/2`. The channel values are now
  conditional and the exact linear relation between them is not; do not
  conflate the two when this correction propagates.
* §6's criterion for `S`. It uses `P_b(n) ≤ q·(n+1)²`, the **upper** bound,
  which is unconditional. `BlockKernelProgrammeLab.md` §A8 caution (a) is the
  matching record: only the claim that the count is *exactly* `(L+1)²`, or that
  the pair `(s₃,s₅)` equidistributes for product Haar measure, needs the
  independence.

### Downstream consumer

`RationalLatticeTorusSqueezeLab.md` §5a states that each fiber value `T_{j,k}`
is "**irrational** by the companion theorem (`PurePowerIrrationality.lean`)".
That sentence inherits this condition. A dated correction block is appended
there.

---

## Assessment of the proposed orbit-closure repair, 2026-09-06

The repair below was supplied with the integration brief. It is **not
Lean-checked and was not previously reviewed**. It is assessed here on the
mathematics.

**Verdict: sound.** Every step checks, including the two that carry the
argument. The write-up is a contour and needs ordinary care before it is a
proof on paper; no gap was found in it.

### The lemma

Let `α, β ∈ (0,1)` be irrational with `α ≠ β` and `α + β ≠ 1`, and put

    w_n = ( ⌊(n+1)α⌋ − ⌊nα⌋ , ⌊(n+1)β⌋ − ⌊nβ⌋ ) .

Then for every `L` there are two positions `n ≠ n′` at which the same length-`L`
word occurs and whose following symbols differ in exactly one coordinate.

### Why it is enough

The radix letter is `b_a = 2·3^{δ₃(a)}·5^{δ₅(a)}` with `δ_q(a) ∈ {0,1}` the two
Beatty increments, so a flip in exactly one coordinate multiplies the letter by
`3` or by `5`. Both are `≥ 3`, which is exactly what (3)+(4) of §3 need: the
two confining intervals `(1/a, 2/a)` and `(1/(qa), 2/(qa))` are then separated
by at least `1/(3a) ≥ 1/90`. The lemma delivers the flip at the **last**
position, which is what §2's measured caution requires: factors at Hamming
distance one occur only at positions `0` and `N−1`, never in the interior.

### The verification, step by step

*The coding.* Write `x_n = {nα}`, `y_n = {nβ}`. Then
`⌊(n+1)α⌋ − ⌊nα⌋ = 1` exactly when `x_n ∈ [1−α, 1)`, and likewise for `β`. So
the symbol at time `n` is the product-partition address of the point
`(x_n, y_n) = n·(α,β)` in `T²`.

*The boundaries.* The `j`-th symbol of the word starting at `n` flips when
`x_n + jα ∈ {0, 1−α}`, that is when `x_n ∈ {−jα, −(j+1)α}`. Over
`j = 0,…,L−1` the `x`-boundaries are `x = −jα` for `0 ≤ j ≤ L`, and the next
symbol adds exactly one new one, `x = −(L+1)α`. Same in `y`. The contour's
boundary bookkeeping is correct.

*The orbit closure.* Let `G` be the closure of `{n(α,β) : n ≥ 0}`. For a
rotation this is the closed subgroup generated by `(α,β)`, so `G = Λ^⊥` for
`Λ = {(A,B) ∈ ℤ² : Aα + Bβ ∈ ℤ}`, and the orbit is dense in every component of
`G`. Since `α` is irrational the first-coordinate projection of `G` is dense
and closed, hence onto, so `G` is infinite; an infinite closed subgroup of `T²`
has positive dimension. So `G` is `T²` or one-dimensional. This is the
"Kronecker–Weyl on the actual closed subgroup" of the contour, and it is the
same device this corpus already audited as airtight for `[P1′]`
(`BlockKernelProgrammeLab.md` §7.1, cited to Walters, Thm 6.20).

*Case `G = T²`.* Pick a point on the new `x`-boundary that is on no other
boundary. Two nearby points on opposite sides of it lie in the same cell of the
partition generated by all the old boundaries, so they carry the same length-`L`
word, and they differ in the `(L+1)`-st `x`-symbol only. Density supplies orbit
points in each of the two open regions. Correct.

*Case `dim G = 1`.* Then `Λ` has rank one, generated by some `(A,B)` with
`Aα + Bβ = C ∈ ℤ`, and `G = {(x,y) : Ax + By ≡ 0 (mod 1)}`, possibly with
`gcd(A,B)` components. `B = 0` would force `Aα ∈ ℤ` and `A = 0` would force
`Bβ ∈ ℤ`, so both are nonzero. The vertical circle `x = −(L+1)α` meets `G` in
`|B|` points and the horizontal circle `y = −(L+1)β` meets it in `|A|` points;
the two circles meet each other only at `(−(L+1)α, −(L+1)β)`, which is the
orbit point `−(L+1)·(α,β)` and lies on `G`. If `|A| = |B| = 1` then
`±α ± β = C`, and with `α, β ∈ (0,1)` that forces `α + β = 1` or `α = β`, both
excluded. So `max(|A|,|B|) ≥ 2` and at least one of the two new boundary sets
carries a point of `G` other than the shared one. **This is the step the two
hypotheses buy, and it is the only place they are used.**

*The chosen point is clean.* Take the unshared point on, say, the new
`x`-boundary. It is on no old `x`-boundary, since `x = −(L+1)α` equals
`x = −jα` only if `(L+1−j)α ∈ ℤ`. It is on no old `y`-boundary either: a point
of `G` with `x = −(L+1)α` and `y = −jβ` satisfies `−A(L+1)α − Bjβ ≡ 0`, and
subtracting `(L+1)` times `Aα + Bβ = C` gives `B(L+1−j)β ∈ ℤ`, impossible for
`j ≤ L` because `β` is irrational and `B(L+1−j) ≠ 0`. It is not the shared
point by choice. Correct, and this is the second load-bearing step.

*Crossing.* `G` has direction vector `(B, −A)`; `B ≠ 0` makes it transverse to
the vertical circle, and `A ≠ 0` makes it transverse to the horizontal one. Old
boundaries meet `G` in finitely many points, none equal to the chosen one, so a
small enough arc of `G` through it meets no old boundary. Its two halves
therefore carry the same length-`L` word and differ in exactly one
`(L+1)`-st symbol. Density of the orbit in that component of `G` supplies
occurrences on both sides. The two occurrences are at distinct positions
because they sit in disjoint open sets.

### The `{2,3,5}` channel-2 certificates

`α = log_3 2`, `β = log_5 2`. Both are irrational, and both lie in `(0,1)`
because `2 < 3` and `2 < 5`. The two exceptional cases are excluded by exact
integer comparisons:

| needed | certificate | conclusion |
|---|---|---|
| `α > 3/5` | `2^5 = 32 > 27 = 3^3` | `5·ln2 > 3·ln3` |
| `β > 2/5` | `2^5 = 32 > 25 = 5^2` | `5·ln2 > 2·ln5` |
| `β < 3/5` | `2^5 = 32 < 125 = 5^3` | `5·ln2 < 3·ln5` |

The first two give `α + β > 1`, and the first and third give `β < 3/5 < α`, so
`α ≠ β`. Both hypotheses hold, with finite integer witnesses and no
transcendence input.

### The channels `p = 3` and `p = 5` are not covered, and why

The lemma delivers a flip in exactly one coordinate and does not let the user
choose which coordinate. §3 needs the flipped prime to satisfy `q ≥ 3`, because
a factor of two puts the two confining intervals `(1/b, 2/b)` and
`(1/(2b), 1/b)` end to end and the separation constant collapses to zero. For
the channel `p = 2` of `{2,3,5}` the two available flips are by `3` and by `5`,
so the requirement is automatic. For `p = 3` the radix letter is
`b = 3·2^{δ₂}·5^{δ₅}` and a flip in the `2`-coordinate multiplies it by `2`;
the same happens for `p = 5`. Those two channels therefore stay open, even with
the lemma in hand, until either the lemma is strengthened to place the flip in a
named coordinate or §3 is strengthened to handle a factor-two flip.

The general form of the requirement is that every prime of the support other
than the channel prime is at least `3`. That holds when `p = 2`, and it holds
for every channel of a support that omits `2`.

Their fractional-part hypotheses do clear, and are recorded here so the work is
not repeated if the coordinate-choice gap is closed:

| channel | slopes | fractional parts | certificates |
|---|---|---|---|
| `p = 3` | `log_2 3, log_5 3` | `log_2(3/2), log_5 3` | `3^2 = 9 > 8 = 2·2^2` gives `log_2(3/2) > 1/2`; `3^2 = 9 > 5` gives `log_5 3 > 1/2`, hence sum `> 1`; `(3/2)^8 = 6561/256 < 32 = 2^5` gives `log_2(3/2) < 5/8` and `3^8 = 6561 > 3125 = 5^5` gives `log_5 3 > 5/8`, hence distinct |
| `p = 5` | `log_2 5, log_3 5` | `log_2(5/4), log_3(5/3)` | `(5/4)^3 = 125/64 < 2` gives `log_2(5/4) < 1/3`; `(5/3)^2 = 25/9 < 3` gives `log_3(5/3) < 1/2`, hence sum `< 5/6 < 1`; `(5/3)^3 = 125/27 > 3` gives `log_3(5/3) > 1/3 > log_2(5/4)`, hence distinct |

### Scope the repair restores

**Restored, unconditionally.** Irrationality of `Σ_2` for the support
`{2,3,5}`, which is the binary channel and the one the `#269` programme
actually uses. That is the whole of the unconditional gain, and it is the `r = 3`
content the note was after for the literal support.

**Restored, conditionally on a per-triple check.** Irrationality of `Σ_p` for a
three-prime support `{p, q₁, q₂}` with `q₁, q₂ ≥ 3` whose two slopes
`α = log_{q₁} p` and `β = log_{q₂} p` satisfy `{α} ≠ {β}` and `{α} + {β} ≠ 1`.
The two fractional-part conditions are decidable by exact integer comparisons in
every concrete case and are not automatic in general; a triple with
`{α} + {β} = 1` exactly would be a genuine relation of the excluded kind, and
nothing here rules one out abstractly.

**Not restored.** The channels `p = 3` and `p = 5` of `{2,3,5}`, for the
coordinate-choice reason above. Also `r ≥ 4`, and the merged pure-power ladder
of §5. For
`r ≥ 4` the coding is by `r−1` rotations on `T^{r−1}`, the orbit closure can
have any dimension from `1` to `r−1`, and the `|A| = |B| = 1` exclusion becomes
a condition on the annihilator lattice `Λ ⊂ ℤ^{r−1}` that has no two-line
proof. That is the separate higher-dimensional extension, and the note's §5
reach sentence stays conditional until it exists.

### Items the write-up must add

1. State the lemma as: *for every `L` there exist positions `n ≠ n′` at which
   the same length-`L` word occurs and whose successors differ in exactly one
   coordinate.* The brief's phrase "two occurring length-`L` words that agree"
   is one word occurring twice.
2. Fix the half-open convention for the arcs `[1−α, 1)` and say that both
   chosen orbit points lie strictly off every boundary.
3. Record that the old boundaries meet `G` in a finite set, so a small enough
   arc through the chosen point avoids all of them.
4. Record that `G` may be disconnected when `gcd(A,B) > 1`, and that the
   crossing argument runs inside the component of the chosen point, where the
   orbit is still dense.
5. Restate with `{α}` and `{β}` in place of `α` and `β`, so the lemma itself
   applies to channels whose slope exceeds `1`, and carry the hypotheses as
   `{α} ≠ {β}` and `{α} + {β} ≠ 1`. This widens the lemma and does not on its
   own widen the theorem: §3 still needs the flipped prime to be at least `3`.
7. Separately, decide whether the lemma can be strengthened to place the flip
   in a named coordinate, or whether §3 can be strengthened to extract a
   positive gap from a factor-two flip. Either one unlocks the channels
   `p = 3` and `p = 5`.
6. Then replace §2 of this note wholesale. §2's right-special construction and
   its full-torus density sentence are superseded by the lemma; §3 consumes the
   lemma unchanged.

### Formalisation note

`PurePowerIrrationality.lean` needs no change to accommodate the repair. The
lemma discharges the `gaps` hypothesis of `irrational_of_clearing_and_small_gaps`
for `Σ₂`, which is exactly the hypothesis the module was written to consume.
The Lean cost is the lemma itself: orbit closures of a rotation on `T²`,
subgroup classification, and a transversality argument, none of which exists in
`ErdosProblems/Shared` today. `IrrationalRotationStaircase.lean` is the nearest
neighbour and solves a different problem, so it is a stylistic model rather
than a dependency.
