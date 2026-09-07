# Fixed-point boundary attack: what the binary map actually proves

This note tests the fixed-point picture from the corpus attachment against the
formal interfaces. It does not introduce a new state or claim a solution.

## 1. Exact map

For a Boolean word b = (b_n), put

    D(b) = sum_n b_n * 2^(-n)
    E(b) = sum_n b_n * ((2^n - 1)^(-1) - 2^(-n)).

The Mersenne value is exactly M(b) = D(b) + E(b). Hence M(b) = r forces

    D(b) = r - E(b).

Let beta(y) be the canonical binary digit word of y, with a chosen convention
at dyadic rationals. The proposed map is F_r(b) = beta(r - E(b)). On a
non-dyadic point, its first N digits are determined by the unique open dyadic
cell containing r - E(b). Explicitly, away from boundaries,

    d_(k+1) = floor(2^(k+1) y) - 2 floor(2^k y),  y = r - E(b),

and the residual update is y -> 2*y - d_(k+1), an expanding map.

The corpus expresses this without a global BinaryDigits definition:
`positiveMersenneSupportValue_eq_prefix_add_suffix` gives the Mersenne
prefix/suffix split; `supportDyadicCorrectionValue_eq_prefix_add_suffix` and
`target_sub_greedyCorrectionPrefix_eq_dyadicPrefix_add_remainder` give the
binary/correction split. For an actual support, the fixed-point equation is
packaged by `positiveMersenneSupportValue_eq_half_iff_correction_eq_complement`
for r = 1/2 and by
`positiveMersenneSupportValue_eq_target_iff_correction_eq_complement` in the
general-target Boolean/Mobius development.

## 2. Strongest true local statement

For a finite binary prefix p of depth d, let C_d(p) be its closed dyadic cell
[P_d(p), P_d(p) + 2^(-d)]. At stage K, the possible correction image is

    I_K = [P_K + r_K - eta_K, P_K + r_K],

where r_K is the greedy Mersenne remainder and eta_K is the Mersenne
correction tail. The exact theorem
`greedyCorrectionImage_subset_prefixCell_iff` says that I_K is contained in a
depth-d cell iff the two endpoint inequalities hold. Its coordinate form,
`greedyCorrectionImage_subset_prefixCell_iff_correctionBand`, rewrites those
inequalities as

    eta_K <= r_d + DeltaE_(K,d) <= 2^(-d).

This is the exact prefix-doubling/local-constancy law: once the whole
correction image lies in one deeper cell, every compatible correction has the
same first d binary digits.

The underlying binary fact is `positiveDyadicSupportValue_mem_greedyPrefixCell`.
The cofinal consumer is `TargetCorrectionImageForcingChain`; its theorem
`TargetCorrectionImageForcingChain.correctionImage_eq_dyadic` says that
cofinal shrinking cells force r - E(b) = D(b), hence M(b) = r. This is the
best surviving theorem candidate. It is already formalized as a consumer;
what is absent is a producer proving cofinal trapping for the live rationals.

## 3. Exact boundary failure

Local constancy fails exactly at dyadic boundaries. If y = q / 2^j, then
arbitrarily small perturbations on the two sides have different binary
prefixes at depth j. The familiar seam is

    0.01111... = 0.10000...

The Mersenne correction is positive and O(4^(-K)), but that does not imply
boundary avoidance. `correctionWindow_dyadic_crossing_unique` proves only
that a correction window meets at most one boundary at the relevant depth.
`IsStraddlePrefix.half_step_forced` and
`isStraddlePrefix_step_trichotomy` expose the take, skip, and fatal alternatives.

Thus the fixed-point statement has four exact cases:

* interior of a cell: binary prefixes are locally constant;
* boundary: the map is discontinuous and two one-sided words exist;
* cofinal interior trapping: the fixed-point identity follows;
* no current theorem excludes infinitely many boundary encounters for the live
  rational targets.

## 4. Adversarial exact tests

I evaluated E, greedy prefixes, and binary prefixes using exact Fraction
arithmetic. These tests target tempting but false strengthenings.

### False conjecture A: every finite word is locally fixed when correction is small

For r = 1/2 and b = 0^N, E(b) = 0 and r - E(b) = 1/2, exactly dyadic. Under
the terminating convention beta(1/2) begins 1000..., not 0^N. This persists
for every N.

### False conjecture B: rationality keeps the zero-prefix orbit away from seams

| target | zero prefix | exact r - E(b) | binary prefix | mismatch |
|---|---:|---:|---|---|
| 1/21 | 0^6 | 1/21 | 000010... | depth 5 |
| 1/9 | 0^4 | 1/9 | 0001... | depth 4 |
| 1/20 | 0^6 | 1/20 | 000011... | depth 5 |

These are not counterexamples to membership; they disprove a boundary-free
iteration from an arbitrary word.

### False conjecture C: a nonzero correction cannot reverse the current bit

For r = 1/21 and b = 0001,

    E(b) = e_4 = 1/240,
    r - E(b) = 1/21 - 1/240 = 73/1680 < 1/16.

The proposed fourth bit is 1, but the corrected value lies in the 0000 cell.
For r = 1/20 and b = 0001, the corresponding value is 11/240 < 1/16.

For the actual greedy prefixes of 1/2, 1/21, 1/9, 1/20, 2/17, 3/17, and
5/31, the first 50 exact binary digits of r - E(b) agreed with the computed
greedy bits. This is finite consistency only. It does not establish cofinal
trapping; the corpus records the scalar counterexamples
`safeBracket_and_numeratorMonotone_not_inductive_fixture`,
`lcmSaturated_safeBracket_not_inductive_fixture`, and
`rankThree_rawSafe_but_seamNotEscaped`.

## 5. Uniqueness versus existence

Uniqueness does not need a contraction argument. If two Boolean supports A and
B satisfy the same exact Mersenne target, then
`positiveMersenneSupportValue_injective_normalized` gives A = B. Any fixed
point representing r is therefore unique because Mersenne coding is strictly
superincreasing. This is injectivity, not existence for F_r.

A finite non-dyadic cell calculation also cannot prove existence: it fixes only
finitely many bits. The missing step is a cofinal family of compatible cell
inclusions, equivalently a `TargetCorrectionImageForcingChain`. At a boundary,
small correction cannot replace that missing global datum.

## 6. Conclusion

The discontinuous fixed-point idea survives in a precise but limited form. The
map b -> beta(r - E(b)) is exact on non-dyadic cells; its strongest true local
law is the two-endpoint correction-image trapping criterion. Forward residual
dynamics double distances while inverse prefix cells shrink. The remaining
obstruction is global cofinal boundary control, and the tested strengthenings
fail at explicit dyadic seams.
