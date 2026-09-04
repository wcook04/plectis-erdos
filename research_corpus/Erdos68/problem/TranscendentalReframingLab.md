# Erdős 68: every recorded obstruction is a statement about the representation

## Claim boundary

Exact identities between convergent series, verified to 129 digits and termwise
in exact rational arithmetic. It proves no irrationality, it does not show the
new coordinate is tractable, and Erdős #68 remains open. That `e` is
transcendental and `I_0(2)` is irrational are cited classical facts, not outputs
of this lab.

## The observation

The packet closes the factorial-gap coordinate from four directions:

| obstruction | what it says | recorded at |
|---|---|---|
| fixed-prime p-adic | for fixed `Q` and every `n ≥ Q`, `n!−1 ≡ −1 (mod Q)`, so the terms do not tend to zero `Q`-adically | negative result 19 |
| growth-only | decreasing each `n!−1` by at most `n²+1` already gives a rational series (Kovač–Tao) | negative result 9 |
| digit bias | 49998 rounding digits indistinguishable from `Uniform[0,1)` on every tested statistic | negative result 25, `FactorialDigitLawLab.md` |
| primehood | first tail-free threshold failure at the prime `m = 5` | negative result 17 |

Each is sharp and each is believed. But **none of the four is a statement about
the number `S`.** All four are statements about the series `Σ 1/(n!−1)` — its
denominators, its perturbations, its digits, its indices. A different exact
representation of the same real number is not constrained by any of them.

## The identities

From `1/(n!−1) = 1/n! + 1/(n!(n!−1))` — exact, verified termwise as rationals
for `2 ≤ n ≤ 39` — applied once and then again:

```
(1)   S = (e − 2) + Σ_{n≥2} 1/(n!(n!−1))

(2)   S = e + I_0(2) − 4 + Σ_{n≥2} 1/((n!)²(n!−1))

(3)   S = Σ_{j≥1} Σ_{n≥2} (n!)^{−j}
```

where `I_0(2) = Σ_{n≥0} 1/(n!)²` is the modified Bessel value. Identity (3) is
the full geometric layering; (1) and (2) are its first and second partial sums,
with the `j = 1` layer summing to `e − 2` and the `j = 2` layer to `I_0(2) − 2`.

Residual gaps at 130-digit working precision: `−2.0e−129`, `2.0e−129`,
`2.0e−129`. All three below the predeclared `10^−100` falsifier.

## What (2) converts the problem into

`e` is transcendental and `I_0(2)` is irrational, both classically. So (2) says

> **Erdős #68 ⟺ `e + I_0(2) + Σ_{n≥2} 1/((n!)²(n!−1)) ∉ ℚ`.**

A ternary linear-independence question over `ℚ`, in which the residual converges
like `(n!)^{−3}`.

This is a coordinate change, not progress. Three things are worth stating
plainly about how much it is worth.

**It does not unlock the fast-series criteria.** The packet already records why
Duverney (negative 5) and Barreto–Kang–Kim–Kovač–Zhang (negative 6) do not
apply: `u_{n+1}/u_n²  → 0` rather than two-sided quadratic, and
`a_n^{1/2^n} → 1` rather than unbounded. Cubing the denominators does not repair
either: `v_n ~ (n!)³` still gives `v_{n+1}/v_n² → 0` and `v_n^{1/2^n} → 1`. The
residual in (2) is *faster* but not fast in the sense those theorems need.

**The classical inputs are the wrong shape on their own.** `e` transcendental
and `I_0(2)` irrational are statements about each number separately. (2) needs a
statement about a specific `ℚ`-combination of them together with a third number,
and no such joint statement is in hand.

**CORRECTED (same session, by `probes/erdos68_efunction_layer_race.py`).** An
earlier version of this lab said the third summand "is not an `E`-function value
at an algebraic point, so the theorem does not apply as stated". **That is the
wrong reason.** Reorganising identity (3) by layer, with
`E_j = Σ_{n≥0}(n!)^{−j}` so that `S = Σ_{j≥1}(E_j − 2)`, gives
`E_j = ₀F_{j−1}(;1,…,1;1)` — the value of an `E`-function at `z = 1` for every
`j`. So the third summand is `Σ_{j≥3}(E_j − 2)`, an infinite sum of `E`-function
values, and Siegel–Shidlovskii applies to every truncation. Applicability was
never the obstruction.

The route closes quantitatively instead. Truncating at `J`,
`S − Σ_{j≤J}(E_j − 2) = Σ_{n≥2}(n!)^{−J}/(n!−1)`, of size `≈ 2^{−J}`, so under
`S = p/q` the integer form `L_J = q·Σ_{j≤J}E_j − (p + 2Jq)` has
`|L_J| ≈ q·2^{−J}` against coefficient height `H ≈ q(1+2J)`. A Shidlovskii-type
measure `|L| ≫ H^{−κ(J)}` with `κ(J)` linear in `J` — the generic shape for `J`
`E`-functions — needs `2^J` to beat `q^{κ(J)} ≈ q^J`. That fails for every
`q ≥ 3`, and the packet's certified `q > 10^{12039}` makes it hopeless by roughly
12,039 orders of magnitude *per layer*.

So the coordinate is legitimate and the machinery does apply; what kills this
particular assembly is an exponent race, and any repair has to change the height
or the truncation rate, not the function class.

**What it does change** is which obstructions are live. The four in the table
above are all statements in the discarded coordinate. Whatever kills route (2),
it is not any of them, and they should not be cited against it.

## Why this was not already in the packet

Searched: `Bessel`, `I_0`, `E-function`, `Siegel`, `Shidlovskii`,
`linear independence` across `research_packet.json` and all sixteen Erdős 68
Lean modules — **zero occurrences of any of them**. Every one of the 95 exact
results, 14 open producers, and 26 negative results works inside the
factorial-gap coordinate. The packet has never left it.

That is the finding. Not that this coordinate wins, but that the corpus has
concentrated an entire proof programme in one representation, and its own
exhaustion notes are all indexed to that representation rather than to the
number.

## The invariant the perturbation destroys

Recorded here because it constrains any successor route and is checked by the
same probe: `a_n = n!−1` satisfies

```
a_{n+1} = (n+1)·a_n + n
```

verified for `2 ≤ n ≤ 399`. Kovač–Tao's rational selections `b_n ∈ [n!−n²−2, n!−1]`
cannot satisfy any such clean recurrence, so this is exactly the structure a
proof must consume to escape negative result 9 — and identity (1) is one exact
consequence of it, since the `1/n!` layer is what the recurrence's leading term
generates.

## Replay

```sh
./repo-python formal_math/probes/erdos68_transcendental_reframing.py
```

Exit code `0` iff all five checks pass: the three identities under the
`10^−100` falsifier, the termwise exact rational identity, and the endpoint
recurrence.
