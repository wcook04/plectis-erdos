# Primitive Plücker compression lab

## Analytic question

The q-Apéry rows at `q = 3/2` have adjacent primitive determinants with large
`2`-adic and `3`-adic valuations.  Those valuations help a congruence collision
only if they compress the image of the *whole selected row family*.  For rows
`w_i = (A_i,B_i)`, the relevant integer is therefore

`D_I = gcd { A_i B_j - B_i A_j : i < j in I }`,

not the largest or most attractive adjacent determinant.  When one row has a
unit coordinate modulo `N = 2^S 3^R`, the Bézout--Plücker shear identifies the
two-coordinate image size as `N^2 / gcd(N,D_I)`.  Thus only the common
valuations `min(S,v_2(D_I))` and `min(R,v_3(D_I))` reduce selector entropy.

## Source and attribution boundary

The standard primitive-lattice and determinantal-divisor framework used here is
grounded in the downloaded primary source Magliveras--Trung--Wei, *Primitive
sets in a lattice*, Australasian Journal of Combinatorics 40 (2008), 173--186,
`annexes/magliveras-trung-wei-2008-primitive-sets-lattice/source.pdf`:
Lemma 3.2, printed p. 179 (also `extracted.md` lines 323--328), characterizes
primitivity through the gcd of maximal minors, while Theorem 4.1, printed
pp. 183--184 (also `extracted.md` lines 567--622), gives the unimodular
Hermite-completion framework and the invariance of that gcd.  Smith's
historical matrix terminology is retained in the downloaded primary source
Henry John Stephen Smith, *On systems of linear indeterminate equations and
congruences*, Philosophical Transactions 151 (1861),
`annexes/smith-1861-indeterminate-equations/source.pdf`, DOI
`10.1098/rstl.1861.0016`, printed pp. 293--294 (PDF pp. 2--3), where minor
determinants and the matrix's greatest divisor are defined.  These sources do
not state the q-Apéry rows, their exact three-row divisor `6`, the adjacent
valuation contrast, or the moving-tail boundary.  Those exact computations,
the Lean consumer connection, finite replay, and prefix-versus-tail
disposition are authored in this repository; no Plücker novelty or
irrationality theorem is claimed.

## Discriminating probe

`scripts/check_primitive_plucker_compression.py` reconstructs the exact
primitive q-Apéry rows already used by the remainder checker, computes every
pairwise minor, and records the determinantal divisor for all prefixes and
contiguous windows.  The problem-independent exact arithmetic lives in
`system/lib/formal_math_determinantal.py`, so later Padé and Hermite--Padé
experiments can make the same family-wide comparison without copying a
problem-local gcd loop.  Its falsifier is deliberately sharp: if a large
adjacent depth vanishes from the family gcd, that adjacent depth cannot justify
a family-wide collision threshold.

Canonical receipt:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_primitive_plucker_compression.py \
  --row-count 8 \
  --output state/formal_math/erdos257_period_noncollapse/erdos1049_primitive_plucker_receipt.json
```

## Consequence boundary

A one-way result appears immediately.  The first two primitive rows have
determinant `42`, so every prefix containing them has common `2`-adic and
`3`-adic Plücker depth at most one.  The first three rows have determinantal
divisor exactly `6`; adding any later rows can only gcd in more minors, so every
future prefix divisor must divide `6`.  This is not a longer-horizon guess: the
initial three rows irreversibly rule out growing family-wide `2/3` compression
along the natural expanding prefix, even though adjacent depths reach
`v_2 = 127` and `v_3 = 7` by the eighth row.

A surviving common divisor would open a smaller exact congruence image and
hand a lower selector threshold to `BezoutPluckerJets.lean`; analytic remainder
escape would still be required.  A collapse of the common divisor kills the
temptation to promote isolated adjacent valuations into an adelic family gain.
The computation is confined to the displayed q-Apéry specialization and says
nothing automatic about a genuinely independent Hermite--Padé deformation.

## Moving-tail opening

The prefix no-go does **not** survive deletion of the early anchors.  In the
same exact receipt, every computed contiguous window beginning at `s` preserves
the local depth of its first adjacent minor, through every available end:

`v_2(D_[s,e)) = 3s^2+3s+1`,  `v_3(D_[s,e)) = s+1`.

This is structurally different from merely finding a large adjacent minor: the
gcd includes every pairwise direction in each displayed tail window.  It opens
moving non-prefix selection as the only q-Apéry Plücker variant not killed by
the initial prefix certificate.

There is still a hard all-index boundary.  The finite scan does not prove that
the formula persists for arbitrary `e` by itself.  Here the source identities
close that extrapolation algebraically.  Write `d_n=n(3n+1)/2` for the exact
degree of the q-Apéry denominator and `E_n` for the clearing-factor degree.
The cleared denominator has width `W_n=d_n+E_n` and unit homogeneous endpoint,
so multiplying by `2^W_n` and primitive-normalising removes no factor `2` or
`3`.  The clearing factor itself has local valuations `(-E_n,0)`, while the
source Casoratian has local valuations `(-(n+1),n+1)`.  Consequently the
primitive adjacent determinant has

`v_2 = W_n+W_(n+1)-E_n-E_(n+1)-(n+1)`

`    = d_n+d_(n+1)-(n+1) = 3n^2+3n+1`,

and `v_3=n+1`, for every `n` covered by the source identities—not merely the
displayed scan.

Now fix a tail start `s` and reduce modulo
`M_s=2^(3s^2+3s+1) 3^(s+1)`.  Every later adjacent minor vanishes modulo `M_s`,
and every primitive denominator coordinate is a unit there.
`BezoutPluckerJets.lean` proves that these two facts force every pairwise tail
minor to vanish.  Since the first adjacent minor has exactly those depths, every
finite window `[s,e)` has exact local determinantal depths
`(3s^2+3s+1,s+1)`.  The same module composes this with the binary-selector
pigeonhole theorem: a window of width at least
`(3s^2+3s+1)+2(s+1)=3s^2+5s+3` has a nontrivial exact modular collision.  This
is an all-width arithmetic opening.  What remains
unproved is the decisive analytic condition that a collision escape the
polynomial-pair and remainder nullspaces; no irrationality conclusion is
claimed.

## Exact selector escape from both nullspaces

The existential collision theorem left a structural ambiguity: its selector
could have been forced into the zero coefficient-pair kernel or into the exact
analytic-remainder kernel.  The checker
`scripts/check_qapery_selector_remainder_escape.py` resolves that ambiguity at
the first four tail starts.  It generates primitive rows from the exact source
recurrence, cross-checks the first eight against the canonical symbolic rows,
reduces the rank-one modular image to scalar coordinates, recovers a short
signed relation by exact LLL, and brackets `F(3/2)` by rational interval
arithmetic.

At `s=2`, the width-`25` window contains the exact signed selector

`-w_2 - w_4 - w_7 + w_9 - w_11 + w_13 + w_15 + w_17`.

Both combined integer coordinates are divisible by
`2^19 3^3 = 14,155,776`, the combined coefficient pair is nonzero, and the
corresponding analytic remainder is strictly positive.  The smaller starts
escape both nullspaces as well; at `s=1`, one certificate is `w_10-w_8`, with
modulus `2^7 3^2 = 1,152` and positive remainder.

The first extension to `s=3` also exposed a computational distinction that is
now part of the durable contract.  SymPy's default exact LLL strength
`delta=0.75` returned no binary selector, despite the theorem-level cardinality
guarantee.  Weighting the modular coordinate by `2^16` and using `delta=0.99`
finds a support-12 selector in the width-45 window:

`w_3-w_4+w_8-w_10+w_12-w_16+w_19-w_21-w_27-w_28+w_40+w_42`.

Both coordinates vanish modulo `2^37 3^4 = 11,132,555,231,232`, and a
12,000-bit exact bracket proves the analytic remainder positive.  The LLL
strength and coordinate weight are now explicit receipt parameters, so a weak
reduction failure cannot be mistaken for absence of the guaranteed modular
relation.

The `s=3` extension is not counted as a new mathematical opening merely for
surviving one more finite start.  Its durable contribution is computational:
it removes a false-negative mode in the selector finder.  The earlier exact
result remains the mechanism opening: the moving-tail congruence
kernel is not structurally contained in either nullspace.  The remaining
analytic target is an all-start theorem that controls selector support and
height while preserving a nonzero real remainder.  No irrationality conclusion
is claimed.

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_qapery_selector_remainder_escape.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_qapery_selector_remainder_escape.py --check
```

Canonical receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1049_qapery_selector_remainder_escape_receipt.json`.

## Exact two-selector escape

Numerically bracketing one selected remainder is stronger than a bare modular
collision, but it is an awkward all-start target: the selector and the required
precision change with the tail.  There is an exact alternative.  For a signed
selector let `(A,B)` be its combined primitive row.  Its analytic remainder is
`B F-A`.  If two selectors have combined rows `(A₁,B₁)` and `(A₂,B₂)`
with `A₁B₂-A₂B₁ ≠ 0`, their remainders cannot both vanish for the
same real `F`; otherwise substituting `Aᵢ=BᵢF` would make that determinant
zero.  `TwoSelectorRemainderEscape.lean` checks this implication without any
q-Apéry or irrationality hypothesis.

`scripts/check_qapery_two_selector_escape.py` now retains every coefficient-
bounded relation exposed by one exact LLL-reduced modular-kernel basis, replays
both integer channels, and selects the first pair with nonzero exact
determinant.  At each already certified start `s=0,1,2,3`, it finds such a pair.
This is a structurally distinct opening: the all-start analytic target no
longer requires a numerical sign or interval for a particular remainder.  It
is enough to construct two bounded modular selectors whose exact image has
rank two, together with the height control needed by the irrationality
argument.

The first exact LLL basis at `s=4` exposed no coefficient-one vector, while it
exposed 23 coefficient-two relations and a non-collinear pair.  That apparent
cap separation was solver exposure, not arithmetic.  Replaying the same
rank-72 modular lattice with `fpylll` 0.6.4, LLL delta `0.99`, modular-coordinate
weight `2^16`, and BKZ block size `16` exposes six binary relations.  Two have
supports `24` and `28`; their exact integer row sums vanish in both channels
modulo `2^61 3^5` and have nonzero determinant.  The canonical checker stores
those two coefficient vectors and independently regenerates and replays the
q-Apéry rows, so the durable certificate does not trust BKZ output or floating
point arithmetic.

This kills the only observed distinction between binary rank-two supply and
coefficient-cap-two supply.  It also changes the computational route: a zero
count in one reduced LLL basis is now explicitly backend-relative, while a
stored selector becomes evidence only after exact two-channel replay.  The
receipt records both facts: the old SymPy basis still exposes zero binary
relations at `s=4`, and the replayed BKZ pair is binary and non-collinear.

The ceiling remains strict.  Five finite starts do not supply the all-start
pair, and BKZ is not a complete enumeration of bounded kernel vectors.  The
result proves neither the required height decay nor irrationality at `3/2`.

Replay:

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_qapery_two_selector_escape.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_qapery_two_selector_escape.py --check
```

Canonical receipt:
`state/formal_math/erdos257_period_noncollapse/erdos1049_qapery_two_selector_escape_receipt.json`.
