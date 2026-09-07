# Erdős #1041: a simple minimum does not force a two-root window

Status: ordinary exact refutation of a structural inference, 2026-09-07.
Not a counterexample to Erdős #1041. Rational cores replay from

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_r2_revision_exact_cores.py --quick
```

## Occupied theorems

- The descent-arc estimate (Theorem C of `BergmanSegmentLengthBound.md`)
  remains valid **when a level `t > μ` has a two-root component at the
  selected hub**. That hypothesis is not automatic.
- The disk-family theorem
  `disk_family_critical_value_separation_2026_09_02` already supplies a
  two-sheeted component under an explicit separation hypothesis, not from
  simplicity of a minimiser.
- The parent path conclusion for the witness below is untouched: the
  polynomial is a translated quartic with all roots real and inside the
  disc, so a real interval already joins three of them inside `K_μ`.

## The false inference

`MinimalHubWindowJoin.md` Lemma 1, and the short note's theorem
`res:minimal-hub-window`, inferred: if `c*` is a *simple* critical point
attaining `μ`, then the component born at `c*` has degree two throughout
`(μ, ν)`, where `ν` is the next *distinct* critical-value modulus.

Simplicity controls only the local Puiseux model at that one point. It
does not prevent other critical points from attaining the same modulus
`μ` in the same component. Root counts then jump by more than one at the
first nontrivial level.

## Exact witness

Let

```text
g(z) = z^4 − (4/15) z^3 − (4/25) z^2 + 1/750.
```

The derivative factors exactly as

```text
g'(z) = 4 z (z + 1/5) (z − 2/5).
```

The three critical points are simple (`g''` is nonzero at each), with
values

```text
g(−1/5) = −1/750,    g(0) = 1/750,    g(2/5) = −59/3750.
```

Thus `μ = 1/750` is attained twice, and the next distinct modulus is
`59/3750 = (59/5) μ`. On `|z| = 1` the lower-order terms have total
modulus `107/250 < 1`, so Rouché places all four roots in the open unit
disc. Sign changes on the four monotonic real intervals give four
distinct real roots in `(−1, 1)`.

Between the first three consecutive real roots, both intervening extrema
have modulus exactly `μ`. The full real interval joining those three
roots lies in `K_μ`. The first nontrivial component therefore already
has degree three. Neither simple minimiser has a two-root persistence
interval above `μ`.

## Replacement hypothesis

Any of the following restores a two-root window to which Theorem C
applies:

1. `c*` is the unique critical point attaining `μ`; or
2. the component containing `c*` has degree two throughout an explicitly
   named interval `(μ, T*)`; or
3. the disk-family separation hypothesis, which constructs a two-sheeted
   component by excluding other critical values from a disk rather than
   by reading the next distinct modulus.

If the next distinct modulus is used, every critical point of modulus
`μ` must be accounted for, including ties.

## Limit of `x_n*`

Write `Ψ_n(x) = x^{1/n} sqrt(2 log((x+1)/(x−1)))`. As `n → ∞` one has
`x^{1/n} → 1`, so `Ψ_n(x) = 2` tends to the equation
`log((x+1)/(x−1)) = 2`, whose solution is `x = coth 1`, not `1`. The
short note and Corollary 5 of `MinimalHubWindowJoin.md` had stated the
limit `1`; that sentence is false. The endpoint `coth 1` is already the
limiting cutoff of the disk-family coefficient.
