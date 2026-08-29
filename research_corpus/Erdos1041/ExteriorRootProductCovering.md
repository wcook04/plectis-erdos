# Erdős 1041: the exterior root-product covering lemma

## Status

One new exact auxiliary theorem with an ordinary proof, two exact fine glosses,
and one recorded open dual question. 2026-08-29. The theorem is the only
genuinely new verified mathematics in the two-return batch
`erdos1041_20260829_meanshift_fullparent` (Return B, section 2); it is landed
here **without a live parent consumer** — see §5 for the precise boundary.
**Erdős #1041 remains open.**

## 1. The statement

Let `m ≥ 1`, let `b_1,…,b_m ∈ D`, let `0 < r < 1`, and put `B = ∏_j |b_j|`
and

```text
F(z) = ∏_j (1 − r conj(b_j) z)/(1 − conj(b_j) z),      z in a neighbourhood of D̄.
```

`F` is rational with zeros `1/(r conj(b_j))` and poles `1/conj(b_j)`, all of
modulus `> 1`, so `F` is holomorphic on a neighbourhood of the closed unit
disk, and `F(0) = 1`.

> **Theorem (exterior root-product covering).** With
> `Λ = (1 − r^m B)/(1 − B)`:
>
> ```text
> (i)   Λ ∈ F(D̄);
> (ii)  max_{|z|=1} |F(z)| ≥ Λ, i.e.  max_{|z|=1} ∏_j |z − r b_j|/|z − b_j| ≥ Λ;
> (iii) the open Apollonius region {|λ : |λ − 1| < B |λ − r^m|} is contained in F(D).
> ```

The constant is **exact**: for the symmetric configuration
`b_j = ρ e^{i(θ + 2πj/m)}` the boundary modulus `|F|` is identically `Λ`
(§3). For `m = 1` the boundary maximum **equals** `Λ` for every `b` (§4).

## 2. Proof

If `B = 0` some `b_j = 0`; then `Λ = 1 = F(0)`, and (i)–(iii) are immediate.
Assume `B > 0` and set `β = ∏_j b_j`. Write

```text
N(z) = ∏_j (1 − r conj(b_j) z),      D(z) = ∏_j (1 − conj(b_j) z),
```

so `F = N/D` and `D` has no zero on `D̄`. For `λ ∈ C` consider
`H_λ(z) = N(z) − λD(z)`. Its constant coefficient is `1 − λ`; its leading
coefficient is `(−1)^m conj(β)(r^m − λ)`. For `λ ≠ r^m`, Vieta's product
formula applied to the zeros `ζ_1,…,ζ_m` of `H_λ` (counted with multiplicity)
gives

```text
∏_k |ζ_k| = |1 − λ| / (B |r^m − λ|).                                   (1)
```

Now take `λ = Λ`. Since `0 < r < 1` and `0 < B < 1`,

```text
Λ − 1 = B(1 − r^m)/(1 − B),      Λ − r^m = (1 − r^m)/(1 − B) > 0,
```

so `Λ > 1 > r^m` and `|Λ − 1| = B |Λ − r^m|`. Equation (1) gives
`∏_k |ζ_k| = 1`, hence some zero `z_0` of `H_Λ` satisfies `|z_0| ≤ 1`. Since
`D(z_0) ≠ 0`, `F(z_0) = Λ`. This proves (i).

`|F|` is continuous on `D̄` and holomorphic inside, so by the maximum modulus
principle its maximum over `D̄` is attained on `|z| = 1`; (ii) follows from (i).
On `|z| = 1` the identities `|1 − r conj(b_j) z| = |z − r b_j|` and
`|1 − conj(b_j) z| = |z − b_j|` translate (ii) into the root-product form.

For (iii), if `|λ − 1| < B|λ − r^m|` and `λ ≠ r^m`, then (1) gives
`∏_k |ζ_k| < 1`, so some zero of `H_λ` lies in `D`, where `F = λ`. If
`λ = r^m` the defining inequality reads `|r^m − 1| < B·0 = 0`, which is
false, so no case is missing. ∎

**Scalar identity used.** The only computational input is Vieta's product
formula for `H_λ`, whose constant and leading coefficients are explicit.
It is Lean-checked at kernel level in `ExteriorRootProductCovering.lean`
(`exterior_covering_scalar_kernel`).

## 3. Sharpness, exactly

Let `b_j = ρ e^{i(θ + 2πj/m)}` with `0 ≤ ρ < 1`, so `B = ρ^m`. With
`ω = e^{−2πi/m}`,

```text
D(z) = ∏_j (1 − ρ e^{−iθ} ω^j z) = 1 − ρ^m e^{−imθ} z^m = 1 − B e^{−imθ} z^m,
N(z) = 1 − r^m B e^{−imθ} z^m.
```

For `|z| = 1` with `e^{−imθ} z^m = 1` (and indeed for every `z` on the circle,
by the same identity applied to moduli: both `N` and `D` have constant
modulus on `|z| = 1` because `N/D` is a constant times a power) the ratio
`|F| = (1 − r^m B)/(1 − B) = Λ`. Hence no uniform constant larger than `Λ`
can hold, and the symmetric configuration is the exact extremiser of the
boundary-max problem at fixed `B`.

**Verification.** `scripts/check_erdos1041_exterior_root_product_covering.py`:
240 random configurations satisfy (ii) with the Vieta zero attaining `Λ` to
`0.0` error; 200 covering-region samples attain their `λ` inside `D` to
`4.7e−19`; 60 symmetric configurations give boundary max `= Λ` to `7.3e−15`.

## 4. The `m = 1` equality gloss

For `m = 1` the boundary function `ζ ↦ |ζ − rb|/|ζ − b|` (after rotating
`b = ρ > 0`) has logarithmic derivative proportional to
`sin θ · (r−1)(1 − rρ²)/((1+r²ρ²−2rρ cos θ)(1+ρ²−2ρ cos θ))`, whose only
critical points on the circle are `θ = 0, π`. Hence

```text
max_{|ζ|=1} |ζ − rb|/|ζ − b| = (1 − rρ)/(1 − ρ) = Λ      (m = 1, exactly),
```

with the maximum at `ζ = e^{i arg b}`. So the covering lemma is an equality
in every one-zero case; the strict cases `max > Λ` begin at `m ≥ 2` with
non-symmetric configurations. Verified to `1.3e−9` (refined grid) over 80
random single-zero configurations.

## 5. Parent-facing boundary: no live consumer

This lemma was returned as the closing step of a claimed full proof of
unrestricted Erdős #1041. The claim does not land. The returned §1 asserts an
"activated last-lobe reduction": that failure of the closed generic statement

> (1) every monic `Q` with zeros in `D̄` has two indexed zeros joined by a
> curve of length ≤ 2 in `{|Q| ≤ 1}`

produces an integer `m ≥ 1`, a real `x > 1`, exterior-block data
`a_1,…,a_m` with `|x a_j| < 1`, `A = ∏|a_j|`, and the strict obstruction

```text
max_{|ζ|=1} ∏_j |ζ − x^{−1}a_j|/|ζ − x a_j| < (1 − x^{−m}A)/(1 − x^m A).   (2)
```

Setting `b_j = x a_j`, `r = x^{−2}` makes the lemma's (ii) the exact negation
of (2), so the reduction + lemma would prove (1) generically, and the corpus's
`GenericSufficiencyClosure.md` (Theorem L, Corollaries D/S — occupied) plus
MEC scaling would finish the unrestricted theorem.

**The reduction is not established.** Verified on 2026-08-29:

* Neither the obstruction (2), the "activated last-lobe reduction", nor any
  exterior-block failure-extraction statement appears anywhere in
  `ErdosProblems/Erdos1041/` (Lean, notes, `research_packet.json` with 155
  exact results and 67 negative results) or in any outbound packet
  (`docs/formal_math/type_b_packets/erdos1041_*`, all revisions grepped).
* The corpus's reduction-bearing files state no such implication:
  `CapacityGeodesicConjecture.md` reduces #1041 to conjecture (C) at the
  **first** merge via `μ ≤ R^n`; `FirstMergeReductionState.md` isolates
  `L(c*) < 2` as the open row; `CapacitySaturationBridge.md` Theorem 3 gives a
  capacity-to-next-merge ceiling of **different polarity** (an upper bound via
  one radial direction with spectator factors dropped, not a boundary-product
  obstruction); `LastLobeCapacityLaw.md` and
  `ExteriorBlaschkeFibreCapacityGap.md` pin capacities and exterior
  coordinates at merges but produce no failure-to-obstruction extraction.
* The returned §1 spends no proof on the extraction; it only attributes the
  composite to "the packet's" results, none of which states it. This is the
  same failure class as the two earlier full-proof waves (the "activated
  closure package" of return 003 in batch
  `erdos1041_20260828_solution_octuple_returns_01`, and the "activated
  higher-tangent reduction" b03_r2_c01 of batch 03): an implication absent
  from the cited corpus carrying the entire difficulty.
* Structural reason the gap cannot be void: the lemma makes ¬(2) a universal
  theorem, so the composite is equivalent to the bare implication
  "failure of (1) ⟹ the extracted data satisfies (2)". Every ounce of the
  parent difficulty must live in that extraction, and no proof of it exists.

Accordingly the returned §1/§3 chain is recorded as **unproved composite
implication, band 4 advisory**; the parent completion class of Return B is
**not** `parent_solution_candidate`. What survives as new exact mathematics is
the covering lemma itself, landed here.

## 6. Recorded open question (dual covering)

The natural dual asks for the sharp constant of

```text
max_{|ζ|=1} ∏_j |ζ − b_j|/|ζ − r b_j|  ≥  ?(B, r, m),
```

i.e. the minimum over configurations of the boundary maximum of the reciprocal
product. The symmetric configuration gives `max = (1 − B)/(1 − r^m B) = 1/Λ`,
but it is **not** extremal for the dual: for `m = 1` the exact maximum is
`(1 + ρ)/(1 + rρ) > 1/Λ`. The naive aligned candidate
`∏_j (1 + |b_j|)/(1 + r|b_j|)` is **refuted** by search (deficit up to
`1.1e+2` over 240 random configurations — the factors cannot align their
maxima at a common `ζ` unless all `b_j` are collinear). The dual sharp
constant is open; it is not currently consumed by any corpus lane.

## 7. Collision check

* `ProperComponentCapacityGap.md` / `ExteriorBlaschkeFibreCapacityGap.md` use
  exterior Blaschke products with zeros `ξ_j`, `|ξ_j| > 1`, and prove the
  harmonic-measure fibre identity and the capacity product gap
  `cap^n/t < k/(2n−k)` — a different object (no uniform dilation `r`, no
  boundary-max statement).
* `CriticalBlaschkePairBound.md` bounds zero radii of zero-critical finite
  Blaschke products (`r_2^k ≤ (k−1)P`) — different statement.
* `radial_resultant_sweep_identity` and the root-ray product contraction are
  whole-root-set ray products, not boundary maxima of dilated quotients.
* No corpus row contains `∏|z − r b_j|/|z − b_j|` with `0 < r < 1`; greps over
  `*.md`, `*.lean`, `research_packet.json`, and all outbound packets return
  nothing.

## Claim boundary

The theorem and both glosses are repository-authored ordinary mathematics
proved in §2–§4; the proof uses only Vieta's product formula, the maximum
modulus principle, and one-variable calculus. No novelty is claimed against
the classical literature: the argument is elementary and the statement should
be assumed known until a priority search says otherwise. What is new **to this
directory** is the statement, its sharpness analysis, and the explicit
delimitation of the returned reduction. The lemma has **no live parent
consumer**; it does not prove (1), (C), COVER, PGLS, (AP), or the parent
theorem. **Erdős #1041 remains open.**

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_exterior_root_product_covering.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py \
  --jobs 2 --project-root formal_math/erdos257_period_noncollapse \
  ErdosProblems.Erdos1041.ExteriorRootProductCovering
```
