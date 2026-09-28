# Why the minimum moment needs index eight

This checks the finite-support claims in the #68 short paper, lines 430–438
of public edition `551bae6d`. Coefficients are arbitrary signed integers.
For a vector supported at indices 2 through 7, write its factorial moment as
M and its divisor-channel numerators as V₂ and V₄.

The exact six basis rows give

    11M − 46V₂ + 12V₄ = 4140(c₆ + 7c₇).

Checking each basis row proves the identity for every choice of integer
coefficients by linearity. It is not a search over bounded coefficients.
When both channels vanish, the explicit identity
`3011 × 11 − 8 × 4140 = 1` yields

    M = 4140[3011(c₆ + 7c₇) − 8M].

Thus every such moment is divisible by 4,140. If support is at most five,
the first identity forces M = 0. The vector

    246e₂ − 112e₃ + 180e₄ − 66e₅ + 11e₆

has moment 4,140 and cancels all three channels V₂, V₃ and V₄. Scaling it
shows that the moment ideal is exactly 4140ℤ for support at most six or seven,
even with the third channel required. This also gives the positive minimum.

Since 4,140 does not divide 1,380, no vector with maximum index below eight
can attain moment 1,380 under V₂ = V₄ = 0. The paper's vector
`1482e₂ − 784e₃ − 136e₅ + 83e₆ − e₈` attains 1,380 and cancels all three
channels, so eight is the exact smallest possible maximum index.

Run `python3 lean/ErdosProblems/Erdos68/scripts/check_depth_four_short_support.py`. The retained certificate has
identical output under ordinary and optimized Python. Three corrupted dual
coefficient sets are rejected; explicit examples show that either vanishing
premise alone is insufficient, and that cancelling V₃ restricts vectors even
when the attainable moments are unchanged.

The integer checker proves the finite-support assertions by exact basis
arithmetic. The unrestricted assertion below uses a separate general theorem;
it does not follow from checking finitely many support rows.

## A short proof for unrestricted support

For every finitely supported signed integer vector with all indices at least
two, the existing universal channel theorem proves

    12 × channelLCM(D) divides M

when channels 2 through D vanish. At D = 4, `channelLCM(4) = 115`, so
1,380 divides every attainable moment. The explicit index-eight vector above
attains 1,380; multiplying it by any integer attains every multiple of 1,380.
These two directions prove that the unrestricted moment ideal is exactly
1380ℤ. This argument needs neither the scalar recurrence table nor the
quadratic horizon used by the general all-depth moment-ideal proof.

The companion `DepthFourShortSupport.lean` gives the following interfaces in
namespace `ErdosProblems.Erdos68.ShortSupport`:

- `dual_identity_seven` and `moment_dvd_seven`: the universal signed-coefficient
  identity and the 4,140 divisibility obstruction through index seven.
- `moment_zero_five` and `attainable_moment_iff`: moment zero through index five
  and exactly 4140ℤ through either index six or index seven.
- `attainable_1380_two_channels_iff`: with only V₂ = V₄ = 0, moment 1,380
  is attainable on indices 2 through N exactly when N is at least eight.
  `attainable_1380_iff` gives the same boundary when V₃ must vanish too.
- `all_support_attainable_iff`: exactly 1380ℤ with no upper support bound, using
  `twelve_channelLCM_dvd_factorialMoment_of_channels_zero` and the explicit vector.

Check the formal source with `lake build ErdosProblems.Erdos68.DepthFourShortSupport`
from the Lean project root. The Python certificate is a separate check and
cannot establish Lean acceptance.
None of these results proves irrationality of the infinite series.

## Source and downstream disposition

This note checks and explains an existing paper assertion; it makes no novelty
claim. The original finite-support proof and checker are retained in batch
`erdos68_short_support_20260927`; the checker here is byte-identical to its
committed audit source. The unrestricted proof specializes the existing
universal theorem in `DivisorChannelBasis.lean` and uses the same paper vector.

Paper route: `paper/68/erdos-68-factorial-denominator-irrationality.tex` at
public commit `551bae6dc6e732cf85172d66323c8d2bc77ba962`, in the paragraph
following `eq:depth-four-short-vector`, using `eq:depth-four-dual`. The
all-depth theorem in `PaperCompleteMomentIdeal.lean` remains useful; this
shorter depth-four proof does not replace its general statement or the scalar
form of the witness in `PaperCoverageV5/MomentExamples.lean`.

Comparator disposition: retain this under the existing exact low-channel
moment-ideal paper claim. A dedicated family is not selected merely because
additional support lemmas were formalized. Independent statement checking and
Comparator replay remain separate requirements for any selected interface.

Palomar disposition: retain this explanation under the existing #68 paper
family. Local Lean validation does not change a frozen prepared or submitted
entry, establish NanoDa replay, or supply external acceptance. Prove2Me and
published aiXiv/arXiv editions likewise retain their exact source identities
until a deliberate, separately validated update.
