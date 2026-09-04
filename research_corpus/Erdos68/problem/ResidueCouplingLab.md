# Erdős 68: the requested Archimedean–profinite coupling, written down

## Claim boundary

The identity is exact algebra, verified for `3 ≤ m ≤ 90`. The band statistics
carry no significance claim, for the reason in §4. Erdős #68 remains open.

## 1. The producer asked for a coupling and never got a formula

`actual_cross_index_archimedean_profinite_coupling`, priority 2:

> Find a global invariant of the true divisor-factorial coefficients that rules
> out eventual `q_m = 1` and is absent from the synthetic congruence
> countermodels.

The coupling exists and is one line.

## 2. The identity

Write `a_n = n!−1` and `P_m = Σ_{n=2}^{m} 1/a_n`. Because `n! ≡ 1 (mod a_n)`,

```
m!  =  (m!/n!) · n!  ≡  m!/n!   (mod a_n)
```

so with `r_n(m) := m! mod a_n` every integer part splits off exactly and

```
{ m! P_m }  =  { Σ_{n=2}^{m}  r_n(m)/a_n }
```

giving, for the scaled predecessor gap that carries the whole problem,

```
A_m  =  1 − { Σ_{n=2}^{m}  (m! mod (n!−1)) / (n!−1) } .
```

Verified exactly for `3 ≤ m ≤ 90`, along with the congruence
`m!/n! ≡ m! (mod a_n)` that drives it.

**So the Archimedean quantity whose escape from a `1/m` window is equivalent to
Erdős #68 is a weighted sum of purely profinite data.** That is the coupling.

## 3. Three regimes, and where the mass is

Comparing `m!/n!` with `a_n` splits the sum:

| regime | condition | behaviour | at `m = 60` |
|---|---|---|---|
| absorbed | `a_n \| m!` | `r_n(m) = 0` **exactly** | `n = 2,3,4,5` |
| active | `m!/n! > a_n` | genuine reduction; carries essentially all the fractional part | `n ∈ [6,35]`, 30 terms |
| unreduced | `m! < (n!)²` | `r_n(m) = m!/n!`, term ≈ `m!/(n!)²`, collapses super-exponentially | `n ≥ 36`, 25 terms |

The absorbed head is exactly the Kempner condition — the same statement as the
packet's landed `q ∤ 299999!`. The unreduced tail is negligible. **The problem
lives entirely in an active band of about `m/2` terms.**

## 4. The measured bias, and why no significance is claimed

Active-band mean against `1/2`, with the nominal independence `z`:

| `m` | band | mean | nominal `z` |
|---|---|---|---|
| 40 | 19 | 0.4296 | −1.06 |
| 60 | 30 | 0.4953 | −0.09 |
| 80 | 42 | 0.3541 | −3.28 |
| 100 | 53 | 0.4031 | −2.44 |
| 120 | 64 | 0.4713 | −0.80 |

Five of five below `1/2`, two beyond `−2.4`. It is **not** a boundary artefact:
tightening the reduction threshold from one wrap to `10^12` wraps leaves
`m = 80` at `z ≈ −3.1` to `−3.6` and `m = 100` at `−2.4` to `−2.9`.

But the nominal `z` assumes the terms are independent across `n`, and **they are
not**: the moduli satisfy `a_{n+1} = (n+1)a_n + n`. The correlation that
recurrence induces is not quantified here and may account for the whole
deviation. So the numbers are reported and no significance is claimed.

Worth naming, because the direction matters: `A_m = 1 − {Σ}`, and the dangerous
configuration is `A_m` small, i.e. the sum landing just below an integer. A
systematic downward pull on the terms pushes the sum *away* from that boundary.
**If the bias is real it points the favourable way.** Settling it against a null
that respects the modulus recurrence is a live question this lab raises and does
not answer.

## 4b. The residues are a dynamical system, not a table

From `m! = (m+1)!/(m+1)`,

```
r_n(m+1) ≡ (m+1)·r_n(m)   (mod a_n)
```

verified for `n = 2…59`, `m = n…119`. So with `x_n(m) = r_n(m)/a_n`,

```
x_n(m+1) = { (m+1)·x_n(m) }      for every n simultaneously
```

**One multiplier drives every coordinate at each step.** The seed is
`r_n(n) = 1` for `n ≥ 3`, because `n! ≡ 1 (mod a_n)`; `n = 2` is degenerate
(`a_2 = 1`, every residue `0`), which is why the absorbed head always begins with
`n = 2`.

So `x_n(m)` is the orbit of `1/a_n` under multiplication by `n+1, n+2, …, m`, and
a coordinate is *absorbed* exactly when that orbit hits `0` — the Smarandache
(Kempner) function of `a_n`. Absorption is rare at these scales: `a_6 = 719` and `a_7 = 5039` are prime,
so nothing beyond `n ≤ 5` is absorbed until `m ≥ 719`.

That makes `A_m` the fractional part of a sum of coordinates on a product of
cyclic groups, all driven by the same growing multiplier — a simultaneous
`x ↦ kx` system. It is the same expanding structure as the `A_m` recurrence
itself, seen coordinatewise, which is why the two pictures agree.

## 5. Why this is the route, and the literature that was pointed at the wrong one

If the active band is jointly equidistributed, its sum mod 1 is uniform to within
an error shrinking far faster than the `1/m` window the problem needs, and
non-concentration follows. **Erdős #68 becomes an equidistribution statement
about factorials in residue classes modulo `n!−1`.**

**But equidistribution is more than is needed**, and the attribution matters.
`FactorialDigitLawLab.md` already states the surviving Archimedean input and says
in terms that it "is weaker than equidistribution and weaker than the tail-free
threshold" (line 151). That weakening is not new.

What `PredecessorGapRecursionScanLab.md` adds on top — after its own same-session
retraction of two novelty claims — is narrower and still useful: the **run** form.
Cofinality needs only *one* good `m` above each cutoff, so it follows from "no two
consecutive `m` both fail", whose heuristic probability is `1/m²` — summable,
hence a Borel–Cantelli target, and strictly weaker again than the
non-concentration statement. Aim at the run form, not at a bias.

**Two readings of the no-repeat data, and only one of them works.**

*As support for the summable statement, it is worth nothing.* Under the uniform
model the expected number of consecutive failure pairs in `m = 30…12000` is
`Σ 1/(m(m+1)) = 0.033`, so observing zero has probability `e^{−0.033} = 0.97`; to
`m ≤ 50000` the expectation is `0.333` and `P(0) = 0.72`. Observing no repeat is
what the null predicts. Worse, `Σ_{m>B} 1/(m(m+1)) = 1/B` telescopes, so the
*entire infinite tail* beyond any computed horizon contributes expected repeats
`1/B` — `8×10^{−5}` beyond `m = 12000`. **No finite computation will ever exhibit
a repeat, or ever be evidence about the cofinal statement.** Extending the scan to
strengthen it is wasted effort; the summable target is precisely the target
computation cannot support.

*As discrimination against rationality, it works — and it is a statement already
on the books.* `PredecessorGapRecursionScanLab.md` argues that rationality
predicts runs rather than isolated hits, and that is right, in the strongest form:
rationality means `D_m = 0` for **every** `m > B`, i.e. an infinite run of unit
carries. So observing no run of length two below `M` forces `B ≥ M − 1`. That is
exactly the Kempner-index exclusion `q ∤ (M−1)!` the packet already carries at
`M = 300000`. The run test re-derives the landed finite exclusion by a different
and much cheaper route — which is a real operational gain, and the lab is right
that it is the practical way to push the finite exclusions further — but it is a
finite exclusion, and no amount of it becomes a cofinal statement.

The distinction matters for how effort is spent: extend the run scan to push `q`,
by all means, and do not mistake either the extension or the no-repeat observation
for progress on the quantifier.

The packet already source-verified two papers on exactly that object:

* **Garaev–Luca–Shparlinski** — prime and prime-power hit bounds for `n!` mod `q`,
  controlling reuse by `O((x−y)log x/(a log p) + 1)` for `q = p^a`.
* **Garaev–García** (Theorem 1) — moments of the fibre counts
  `J(λ) = #{1 ≤ n ≤ N : n! ≡ λ mod p}`, with `J(λ_k) ≤ 3N^{2/3}k^{−1/3}` for the
  `k`-th largest fibre.

Both were imported for the **private support** route, and the packet's own claim
ceiling then closed that route as asymptotically impossible: a one-owner closing
inequality would force `(2p+1)L_p < 2p²((2p−1)!)²`, while Garaev–Luca–Shparlinski
Theorem 12 gives `log L_p ≫ p^{4/3} log p`, which eventually exceeds it.

The theorems survive their route's death. They are statements about the
distribution of factorial residues, and that is precisely what this formula
consumes. **The packet has the right literature filed against the wrong producer.**

What is missing is that both papers work modulo primes and prime powers, while
`a_n = n!−1` is a general modulus of unknown factorisation. Bridging that is the
concrete next obstacle, and it is a narrower one than anything else on the
frontier.

## Replay

```sh
./repo-python formal_math/probes/erdos68_residue_coupling.py
```

Exit code `0` iff the identity and its driving congruence hold. The band
statistics print without gating, by design.
