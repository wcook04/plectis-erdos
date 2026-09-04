# Erdős 68: three producers are three level sets of one digit

## Claim boundary

The target is the irrationality of `S = Σ_{n≥2} 1/(n!−1)`, which is open. This
lab is finite exact computation over `m ≤ 50000`. It fixes the arithmetic of `S`
in that range, collapses three separately-tracked producer families into one
scalar, and eliminates one route. It settles no cofinal quantifier.

## The object

Write `P_m = Σ_{k=2}^m 1/(k!−1)` for the exact rational prefix and

```
N_m = strictFacTopRat(P_m, m) = ⌊m! P_m⌋ + 1
```

for the strict successor. `FactorialZeroPlateau.lean` proves

> `Irrational S` ⟺ for every `B` there is `m > B` with `m ∤ N_m`.

The strict successors satisfy an exact radix recurrence, and the whole problem
lives in its rounding digit

```
D_m := m·N_(m−1) − N_m ,        m ∤ N_m  ⟺  D_m ≠ 0 .
```

`D_m` ranges over `{−1, 0, …, m−2}`; Lean's `factorialGapStepCarry m` is
`D_m + 1`, so a unit carry is `D_m = 0`.

## What had been measured

Three computations existed and each kept one bit of this stream.

| Computation | Range | Retained |
|---|---|---|
| GMP strict-successor certificate | `m ≤ 300000` | the nine indices with `D_m = 0` |
| exact-`Fraction` predecessor-gap probe | `m ≤ 210` | the certificate's truth value |
| canonical-digit machinery | — | never evaluated |

The digits themselves were discarded at 300000 indices, and the canonical
factorial digits `d_m(S)` of the series had never been computed at all.

## The identities that collapse the families

Let `A_m = N_m − m! P_m ∈ (0,1]` be the scaled predecessor gap (Lean's
`factorialGapPredecessorGap (m+1)`), `ε_m = 1/(m!−1)`, and `G_m = N_m/m! − S`.
Then

```
A_m  = m·A_(m−1) − 1 − ε_m − D_m                       (radix recurrence)
G_m  = Σ_(j>m) D_j / j!                                 (the D_j are the
                                                         factorial digits of G)
```

Because `|Σ_(j>k) D_j·k!/j!| < 1` while a single nonzero digit at `k+1`
contributes at least `1/(k+1)`, the sign of `G_m` is the sign of the first
nonzero digit past `m`. So Lean's endpoint flag `f_m = [G_m > 0]` is one
backward scan of the same stream, and since `⌊m!S⌋ = N_m − f_m`,

```
d_m(S) = ⌊m!S⌋ − m⌊(m−1)!S⌋ = m·f_(m−1) − f_m − D_m .
```

The tail-free threshold of `cofinal_tailfree_predecessor_gap_threshold` is
`m·A_(m−1) ≥ 1 + ε_m + 2/m`; substituting the recurrence turns it into

```
D_m + A_m ≥ 2/m ,
```

which fails outright at `D_m = −1`, holds outright at `D_m ≥ 1`, and at
`D_m = 0` reduces to `A_m ≥ 2/m`, decided by the next digit through
`A_m > (D_(m+1)+1)/(m+1)`.

The exact endpoint theorem does **not** identify a unit carry with a maximal
canonical digit unconditionally. A unit carry has two branches: a zero digit
with both endpoint flags zero, or a maximal digit with both flags one. The table
below records the finite branch actually observed by the probe, not a universal
rationality convention:

| `D_m` | carry | tail-free threshold | observed `d_m(S)`, `m≤50000` |
|---|---|---|---|
| `−1` | non-unit | **fails** | `0` |
| `0` | **unit** | fires | `m−1` (maximal) |
| `≥ 1` | non-unit | fires | `1 … m−2` |

## Exact result, `m ≤ 50000`

`formal_math/probes/erdos68_digit_law.py` over the certificate stream
(GMP 6.3.0, 708453 precision bits, 96 guard bits, 49998 digits), cross-checked
against exact `Fraction` arithmetic on `m ≤ 200` with 0 mismatches.

Each family is null-expected `Σ_{3≤m≤50000} 1/m = 9.897` times.

* `D_m = −1`; at every such finite index the reconstructed digit is `0`, and
  the tail-free threshold fails — **10 indices**: `5, 9, 23, 60, 470, 3026,
  19222, 27472, 30324, 35366`.
  The first four reproduce the exact-`Fraction` probe's failure set.
* `D_m = 0`, equivalently a unit carry; all nine finite instances take the
  maximal branch `d_m(S)=m−1` — **9 indices**: `52, 591, 1030, 1407, 1438,
  2164, 4258, 10991, 21236`. This independently reproduces the landed GMP
  certificate's unit-carry list.
* `D_m = m−2` — **13 indices**: `3, 4, 12, 19, 138, 218, 404, 797, 1338, 3039,
  8736, 15079, 28482`.

The threshold fires at every one of the nine unit carries — the decisive next
digits are `31, 474, 681, 572, 147, 1772, 2894, 2824, 10170`, each giving
`A_m > 0.13` against a threshold of at most `2/52 = 0.038` — so the zero branch
of `factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch` is excluded at all
nine and the canonical digit there is maximal.

This finite maximal-branch observation must not be extrapolated to a rational
tail. `CanonicalFactorialDigits.lean` proves the opposite canonical boundary:
every rational number has eventually zero digits. Under a rationality
hypothesis, eventual unit carries therefore occupy the zero branch.

**Consistency check.** All 49996 reconstructed `d_m(S)` lie in `[0, m−1]`, with
zero range violations. That is a nontrivial constraint on 49996 independent
reconstructions and would fail loudly if the flag rule or the digit identity
were wrong.

## The digits are indistinguishable from generic

Statistic `(D_m + 1)/m`, null `Uniform[0,1)` independent.

| Test | Value | Null |
|---|---|---|
| mean | `0.5000233` (`z = +0.02`) | `0.5` |
| variance | `0.0829595` | `1/12 = 0.0833333` |
| Kolmogorov–Smirnov | `√n·D = 0.619` | `1.95` at 0.1% |
| lag-one correlation | `+0.00080` | sd `0.00447` (`z = 0.18`) |
| prime index | `z = −0.55` | — |
| composite index | `z = +0.21` | — |
| parity | `z = +0.11 / −0.08` | — |
| residues mod 5, mod 6 | worst `|z| = 1.00` | — |

Worst stratum `|z| = 1.00` against a predeclared falsifier of `4`. The null
survives on every test.

## What this changes

**Eliminated.** A *construction* route through the digits. If `D_m` carried an
arithmetic bias — at primes, at a residue class, at smooth indices — the
prime-indexed producers (`cofinal_prime_lower_endpoint_cylinder_escape`,
`cofinal_prime_grid_nonterminality`, `first_crossing_gap_denominator_upper_bound`)
would have a lever on the Archimedean side. There is no such bias at 49998
indices. The correctly indexed certificate at `m = 5` already showed primality is not an
automatic producer; this shows nothing else about `m` is either.

**Sharpened.** `cofinal_tailfree_predecessor_gap_threshold` and
`cofinal_exact_prefix_strict_successor_miss` are not two obstructions. They are
`D_m ≠ −1` and `D_m ≠ 0`: two adjacent `1/m`-windows of the same scalar
`A_(m−1)`, together with the canonical-digit lane as its third level set. One
non-concentration statement settles all three:

> for infinitely many `m`, `A_(m−1) = 1 − {(m−1)!·Σ_{k<m} 1/(k!−1)}` avoids the
> interval `((1+ε_m)/m, (2+ε_m)/m]`.

That is the whole remaining Archimedean input. It is weaker than
equidistribution and weaker than the tail-free threshold, which demands
`A_(m−1) ≥ (1 + ε_m + 2/m)/m` and so overshoots the window it needs to miss.

## Second result: the denominator exclusion was leaving smooth denominators open

`rational_denominator_ge_of_nonunit_carry` converts a non-unit carry at `m` into
`m ≤ q`. Its proof uses `q ≤ m−1` in exactly one line, to obtain `q ∣ (m−1)!`.
Only the divisibility is used. Generalising the hypothesis (and keeping the size
bound as a one-line corollary, so no existing consumer changes) gives

```
rational_denominator_not_dvd_pred_factorial_of_nonunit_carry :
  3 ≤ m → factorialGapStepCarry m ≠ 1 → 0 < q → S = a/q → ¬ (q ∣ (m−1)!)
```

Equivalently the Smarandache function (also called the Kempner function)
`min {k : q ∣ k!}` of any displayed denominator is at least `m`. This is strictly stronger: the size bound leaves every `q > m−1`
open, including every `(m−1)`-smooth denominator of any magnitude — `(m−1)!`
itself, the primorial below `m`, and infinitely many others. The divisibility
form excludes all of them at once.

Two instantiations:

* Fully Lean-checked, from the module's own exact prefix certificate at index 60:
  `rational_denominator_not_dvd_fiftynine_factorial` — no displayed denominator
  divides `59!`. The previous Lean-checked statement was `60 ≤ q`.
* From the landed GMP certificate, whose carry at `m = 300000` is non-unit:
  **`q ∤ 299999!`**, strengthening the packet's recorded `q ≥ 300000`. Since any
  `q ≤ 299999` divides `299999!`, the new statement implies the old one and
  additionally kills every `299999`-smooth denominator. Concretely, a displayed
  denominator must carry a prime factor above `299999`, or a prime power `p^e`
  with `e` exceeding the multiplicity of `p` in `299999!`.

The authority here is the same as before: a Lean-checked consumer plus a finite
GMP certificate as its input. Only the consumer got stronger.

## Replay

```
./repo-python formal_math/probes/erdos68_engine.py 200
./repo-python formal_math/probes/erdos68_digit_law.py --max-m 50000
./repo-python formal_math/probes/erdos68_publish_receipts.py --digit-law --max-m 50000
```

The engine builds the repository's GMP certificate on demand and asserts it
equal to exact `Fraction` arithmetic before any statistic is computed.
