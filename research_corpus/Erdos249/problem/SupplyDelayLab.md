# Erdős 249: the supply delay off the dyadic axis, and what it is measuring

## Claim boundary

The target is the irrationality of `S = Σ_{n≥1} φ(n)/2^n`, which is open. This
lab is finite exact computation. It measures a producer that Lean proves
*equivalent* to the target, on a region of the quantifier that had never been
computed, and identifies what that producer is measuring. It proves nothing
cofinal and no irrationality.

## The producer, exactly

`CyclotomicAnchoredKill.lean` proves

> `FullMersenneCanonicalBasepointResidueGapSupply ↔ Irrational S`

where the supply is

```
∀ c, ∀ odd v > 0, ∃ H > 0 :  φ(v) ∣ H,  M = (2^H − 1)/v,
                             B < (−totientBlock H c) mod M < M − B,
                             B = c + H + 1,
      totientBlock H N = Σ_{j<H} φ(N+1+j)·2^{H−1−j} .
```

The residue must **avoid** a band of radius `B` around zero. That is the easy
direction — a proportion `1 − 2B/M` of residues qualify — so the producer is not
about finding a rare event. It is about how long one waits.

Two heights matter. The *clearing height* `H₀(c,v)` is the least positive
multiple of `φ(v)` with `M > 2B`; below it the admissible arc is empty for
arithmetic reasons alone. The *delay* is `(H_min − H₀)/φ(v)`, counted in
admissible steps.

## What had been measured

One axis. Every #249 receipt in the corpus is named `pure_dyadic`, and the
packet's result is: on `v = 1`, the maximum post-clear delay over `c ≤ C` grows
like `log₂ C`, reproducing the witness of delay 19 at `c = 490794` and refuting
every uniform cap. The `v > 1` half of the quantifier — the odd part of the
denominator — was not computed.

## Result 1: the delay law is two-parameter

`formal_math/probes/erdos249_supply_delay.py`, over `c ≤ 60000` and the odd
moduli below, computing the Lean predicate literally.

| `v` | `φ(v)` | max delay (steps) | argmax `c` | `log₂C/φ(v)` | max height |
|---|---|---|---|---|---|
| 1 | 1 | 17 | 50490 | 15.87 | 34 |
| 3 | 2 | 8 | 4058 | 7.94 | 34 |
| 5 | 4 | 4 | 12787 | 3.97 | 36 |
| 7 | 6 | 3 | 7783 | 2.65 | 42 |
| 9 | 6 | 3 | 4058 | 2.65 | 36 |
| 11 | 10 | 2 | 7727 | 1.59 | 40 |
| 15 | 8 | 2 | 1176 | 1.98 | 40 |
| 31 | 30 | 1 | 4653 | 0.53 | 60 |

The observed maximum equals `⌈log₂C/φ(v)⌉` in seven of the eight cases and is
one higher at `v = 1`. The packet's `log₂ C` law is the `φ(v) = 1` case of

```
max_{c ≤ C} delay(c,v)  ≈  ⌈ log₂ C / φ(v) ⌉ .
```

**The Euler-multiple constraint is a help, not a hindrance.** It looks like a
restriction — only one height in `φ(v)` is admissible — but between consecutive
admissible heights the modulus multiplies by `2^{φ(v)}` while the band radius
grows only by `φ(v)`. So the failure probability per admissible step is about
`2^{−φ(v)}`, and the whole difficulty of the producer concentrates on small
`φ(v)`: at `φ(v) ≥ 12` the first geometrically possible height already works for
every `c` in range. In height units the requirement stays uniformly small — the
tallest height ever needed across all eight moduli and 480 000 instances is 60.

## Result 2: what the delay is measuring

Let `R_c = Σ_{j≥1} φ(c+j)·2^{−j}` be the binary totient tail. From
`R_c = 2R_{c−1} − φ(c)` and `R_0 = S`,

```
R_c = 2^c S − (integer),      so     ‖v·R_c‖ = ‖v·2^c·S‖ ,
```

where `‖·‖` is distance to the nearest integer. The Lean block identity
`2^H R_c = totientBlock(H,c) + R_{c+H}` — verified here exactly, difference 0 at
`(H,N) = (5,0), (11,37), (17,900)` — gives
`totientBlock(H,c)/(2^H−1) = R_c + O(c/2^H)`, and failure at height `H` is
`dist(totientBlock(H,c), MZ) ≤ B`. Both the correction and the threshold are of
order `vc/2^H`, so

```
H_min(c,v) = φ(v)·⌈L(c,v)/φ(v)⌉ + O(φ(v)),      L(c,v) = log₂( v·c / ‖v·2^c·S‖ ).
```

Measured against the exact Lean predicate across all eight moduli and five
decades of `c`: `H_min` tracks `φ(v)·⌈L/φ(v)⌉` to **within one admissible step**
in every case.

So the supply producer is an irrationality-measure statement for `S` restricted
to the denominator family `q = v·2^c`, and the height bound it needs is

```
H ≤ f(c,v)      ⟺      ‖v·2^c·S‖  ≥  v·c·2^{−f(c,v)+O(1)} .
```

## Result 3: the distance sits exactly at the generic edge

Measuring `‖v·2^c·S‖` directly over `c ≤ 200000` by the recurrence
`A_{c+1} ≡ 2A_c + φ(c+J+1) (mod 2^J)` at `J = 220`, whose truncation error
`(c+J+2)2^{−J} < 2^{−202}` is far below every measured distance:

| `v` | `−log₂ min_c ‖v·2^c·S‖` | argmin `c` | `C · min` |
|---|---|---|---|
| 1 | 18.03 | 50490 | 0.748 |
| 3 | 18.17 | 198205 | 0.677 |
| 5 | 18.54 | 90351 | 0.523 |
| 7 | 18.54 | 11779 | 0.523 |
| 9 | 17.39 | 171321 | 1.167 |
| 11 | 19.11 | 7727 | 0.354 |
| 15 | 16.96 | 90351 | 1.569 |
| 31 | 17.78 | 103237 | 0.887 |

`log₂ C = 17.61`, and `C·min ∈ [0.35, 1.57]` for every modulus. So

```
min_{c ≤ C} ‖v·2^c·S‖  ≍  1/C ,     with no dependence on v.
```

This is exactly the generic law: `C` samples of a uniform phase come within
about `1/C` of an integer at their closest. The `φ(v)` dependence of Result 1
disappears once the delay is translated — it was an artifact of the step size,
not of the arithmetic.

## Why every uniform cap had to die

A uniform cap of `N` steps is the claim `‖v·2^c·S‖ ≥ v·c·2^{−(H₀+Nφ(v))}`, i.e.
roughly `‖v·2^c·S‖ ≥ 2^{−Nφ(v)−1}`. Result 3 refutes it at `c ≈ 2^{Nφ(v)}`. The
packet retired the cap programme on the `v = 1` measurement; the same refutation
now holds on every axis, with the cap that dies at each `v` scaling as
`log₂C/φ(v)`.

It also bounds what can be hoped for. Since the minimum really is of order
`1/C`, no lower bound stronger than `‖v·2^c·S‖ ≫ 1/c` can hold, and that one is
at the observed edge. The usable target is

> `‖v·2^c·S‖ ≥ c^{−A}` for some fixed `A > 1`, uniformly in odd `v`,

which yields `H ≤ (A+1)log₂ c + log₂ v + O(φ(v))` and settles the supply. That is
a classical irrationality-measure statement about an explicit dyadic series, not
a Mersenne-residue or carry-trajectory statement. The producer's whole modular
apparatus is a change of coordinates on it.

## Cross-validation

The pure-dyadic axis was rerun to `c ≤ 500000` from this implementation, which
was written against the Lean definitions rather than against the earlier scan.
It returns **maximum delay 19 at `c = 490794`**, reproducing the packet's landed
witness exactly, with maximum height 39 over the whole range.

## Authority note

`fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational` is an
equivalence at the level of the full `∀c ∀v` statement. The *per-instance*
converse — that a verified gap at one `(c,v)` excludes the denominator `2^c v` —
is not a landed Lean theorem, so the 480 000 verified instances here are
recorded as instances of the producer, not as denominator exclusions.

Result 3 is a denominator exclusion on its own terms and does not go through the
producer: `‖v·2^c·S‖ ≥ 2^{−19.11}` for every `c ≤ 200000` and every tested odd
`v`, hence `S ≠ a/(v·2^c)` for those denominators, with an explicit margin and a
truncation error 180 binary orders below it.

## Replay

```
./repo-python formal_math/probes/erdos249_supply_delay.py --max-c 60000 --distance-max-c 200000
./repo-python formal_math/probes/erdos249_publish_receipts.py --supply-delay
```
