# Erdős 68: where rationality actually lives, and how far the series has stayed from it

## Claim boundary

Exact scaled-integer recursion from an exactly seeded prefix, `13 ≤ m ≤ 22000`,
with the realised precision margin reported. A margin that has never dropped
below 31.6 is not a theorem that it never will. Erdős #68 remains open.

## 1. Which branch rationality is in

`factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch` splits a unit carry into
two endpoint cylinders:

* the **zero branch** — canonical digit `0`, both endpoint flags `0`;
* the **maximal branch** — canonical digit `m−1`, both endpoint flags `1`.

The packet records the dichotomy. It does not say which side is dangerous. The
proof of `irrational_factorialGapSeries_of_cofinal_predecessorGap_threshold`
answers it: under `S = a/q` with `q | (m−1)!` the Lean proof derives
`canonicalRemainder (m−1) = 0`, hence `canonicalDigit m = 0`, and then closes by
`omega` against `canonicalDigit m = m−1`.

> **Rationality lives in the zero branch.** The tail-free threshold is sufficient
> precisely because it excludes that branch, not because it produces a non-unit
> carry.

That is worth stating because the maximal branch — a unit carry with maximal
canonical digit — is *not* evidence of anything. Seven of the nine recorded unit
carries would look alarming if the branches were not distinguished. They are all
on the harmless side.

## 2. The dangerous set is summable

In gap coordinates, with `A_m = N_m − m!P_m ∈ (0,1]` and
`R_m = m!·Σ_{n>m} 1/(n!−1)`, the zero branch at `m` is

```
D_m = 0     and     A_m ≤ R_m .
```

Its width is `R_m/m = O(m^{−2})`. **Summable** — unlike the unit-carry window
itself, which is `O(1/m)` and divergent.

That difference is the whole reason to prefer this target. For the `1/m` window,
`Σ 1/m` diverges, so a generic orbit enters it infinitely often and "escapes
infinitely often" is true but not comfortable. For the zero branch,
`Σ R_m/m < ∞`, so Borel–Cantelli gives **finitely many entries almost surely**,
while rationality requires entering at **every** large `m`. The gap between those
two is far wider than anything the `1/m` window offers, and it is why
`cofinal_prime_lower_endpoint_cylinder_escape` is the sharpest producer on the
frontier.

## 3. A combinatorial reading of the same set

`A_m − R_m = Σ_{j>m} D_j·m!/j!`, whose leading term is `D_{m+1}/(m+1)`. So
`A_m ≤ R_m` says the first nonzero digit past `m` is `−1`, and

```
zero branch at m   ⟺   D_m = 0  and  the next nonzero digit is −1
```

with margin `A_m/R_m ≈ D_{next nonzero} + 1`, ranging over `[0, m)`. Hence the
`1/m²` joint probability, and a total expectation over all `m ≥ 3` of about
`Σ 1/(m(m+1)) = 1/3`.

## 4. The measurement

Exact recursion `A_m = m·A_{m−1} − 1 − 1/(m!−1) − D_m` in scaled integers,
`m = 13…22000` at 92,000-digit working precision. Realised error amplification
`10^{85973}`, leaving **6,027 digits of margin** — sound.

Unit carries reproduce the landed GMP certificate exactly — `52, 591, 1030, 1407,
1438, 2164, 4258, 10991, 21236` — from a completely different computation, and
`D_m = −1` at `23, 60, 470, 3026, 19222` matches the digit-law scan on the same
range. That is a genuine cross-check of both.

**Zero-branch hits: none.**

| `m` | `A_m` | `R_m` | margin `A_m/R_m` |
|---|---|---|---|
| 52 | 0.6074290 | 0.0192237988 | **31.6×** |
| 591 | 0.8037781 | 0.0016920425 | 475.0× |
| 1030 | 0.6620553 | 0.0009708729 | 681.9× |
| 1407 | 0.4074827 | 0.0007107317 | 573.3× |
| 1438 | 0.1033093 | 0.0006954100 | 148.6× |
| 2164 | 0.8193059 | 0.0004621071 | 1773.0× |
| 4258 | 0.6798152 | 0.0002348520 | 2894.7× |
| 10991 | 0.2570348 | 0.0000909835 | 2825.1× |
| 21236 | 0.4789535 | 0.0000470898 | 10171.1× |

**Closest approach ever: 31.6× the cylinder radius, at `m = 52`.**

The margins are `D_{next} + 1` to the digit — `31, 474, 681, 572, 147, 1772,
2894, 2824, 10170` are exactly the "decisive next digits"
`FactorialDigitLawLab.md` reported from the GMP stream. Two independent
computations, same numbers.

## 5. What it is worth, honestly

The margins grow roughly like `m`, which is what the `Uniform` reading predicts —
the margin is a factorial digit, and digits at index `m` range over `[0, m)`. So
the growth is not the series pulling away from rationality; it is the ordinary
scaling of the digit alphabet.

What the table does establish is a clean answer to the first question anyone asks:
**at its closest, `S` sat a factor of 31.6 outside the configuration rationality
requires, and never came nearer in 22,000 indices.** That is not evidence of
irrationality beyond what the null already predicts — the expected number of
zero-branch hits over *all* `m` is only about `1/3`, so observing zero is
unremarkable, exactly as for the no-repeat statistic. It is a scale, not a proof.

The useful residue is §2. Aim at the zero branch rather than the unit-carry
window, because that is where rationality lives and because its measure is
summable.

## Replay

```sh
./repo-python formal_math/probes/erdos68_rational_cylinder_margin.py --max-m 5000
./repo-python formal_math/probes/erdos68_rational_cylinder_margin.py --max-m 22000   # ~9 min
```

Exit code `0` iff there are no zero-branch hits, every margin is at least 2, and
more than 100 digits of precision margin survive the amplification.
