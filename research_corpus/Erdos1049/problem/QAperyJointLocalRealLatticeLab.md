# q-Apéry joint local-real lattice

## Why the objective has to change

The modular selector search minimized coefficient size subject to

`(A,B) = 0 mod M_s`.

That is not the rationality consumer.  After exact division
`(A,B)=M_s(A',B')`, the consumer is the real form

`L=B'F-A'`.

The stored coefficient-one selectors show that local depth and rank-two supply
are available, but their normalized forms grow.  A useful construction must
therefore put `L` into the optimization rather than treat it as an audit after
the modular search.

## Source and attribution boundary

The q-Apéry/Lambert-series source boundary is the downloaded primary source
Tewodros Amdeberhan and Doron Zeilberger, *q-Apéry Irrationality Proofs by q-WZ
pairs*, Advances in Applied Mathematics 20 (1998), 275--283,
`annexes/arxiv-math9804122-amdeberhan-zeilberger/source.tex`, arXiv:math/9804122:
Section 1, source lines 72--95, defines the q-harmonic target and the two
q-WZ-derived sequences, and lines 97--119 give the source recurrence data;
Lemma 2 and Theorem 1, lines 196--207, state the source's decay and
integer-base irrationality conclusion.  Van Assche's downloaded primary source
Walter Van Assche, *Little q-Legendre polynomials and irrationality of certain
Lambert series*,
`annexes/arxiv-math0101187-van-assche-little-q-legendre-lambert/source.tex`,
arXiv:math/0101187, records the kernel/diagonal distinction in equations
`markovpn`, `padepn`, and `Pnpn` (source lines 276--304) and its integer-base
theorem at lines 497--504.  These sources ground the Lambert approximant
families and their integer-base boundary; they do not state the present
normalized-selector continued-fraction recombination, its finite q = 3/2
certificates, or the Lean height/gap consequences.  Those are authored and
replayed in this repository, and no all-start decay or irrationality theorem
is claimed here.

## A two-dimensional analytic-aware step

Let the two stored normalized rows at one tail be

`r_i=(A_i',B_i')`,  `L_i=B_i'F-A_i'`.

They are noncollinear.  If `p/q` is a continued-fraction convergent to
`-L_0/L_1`, then

`qL_0+pL_1`

is small.  Adjacent convergents have coefficient determinant `+1` or `-1`.
Consequently, applying two adjacent coefficient rows to `(r_0,r_1)` preserves
the absolute determinant exactly.  Local divisibility is already absorbed by
normalization, and lifting the recombination back before division preserves
the same modulus `M_s`.

The checker uses a rational bracket for `F`, not floating-point evaluation.  A
candidate is accepted only when its whole exact remainder bracket excludes
zero and lies strictly inside `(-1,1)`.  Thus the analytic coordinate, local
certificate, and rank-two consumer are replayed together.

## Exact result

The mechanism succeeds at every tested tail start `s=0,1,2,3`.

| `s` | adjacent convergent indices | coefficient bit lengths | log upper bounds for `|L|` |
|---:|---:|---:|---:|
| 0 | 0, 1 | `(1,0)`, `(3,1)` | `-2.223`, `-3.318` |
| 1 | 28, 29 | `(92,92)`, `(93,93)` | `-0.584`, `-0.631` |
| 2 | 184, 185 | `(708,292)`, `(711,295)` | `-0.485`, `-1.516` |
| 3 | 1104, 1105 | `(2260,1874)`, `(2261,1875)` | `-0.340`, `-1.065` |

Every displayed bracket excludes zero and lies inside `(-1,1)`.  Each adjacent
coefficient matrix has determinant `+1` or `-1`, so the magnitude of the exact
normalized row determinant is unchanged.  This opens the analytic-aware
mechanism and shows that the prior consumer failure belongs to the
modular-only objective, not to the stored rank-two supply itself.  The finite
certificate stops at `s=3`; it does not assert an all-start height law.

## The exact height--decay balance

The required comparison is now exact.  Let the normalized input rows be
`r_i=(A_i,B_i)`, let `Delta=A_0 B_1-A_1 B_0`, and let an integral unimodular
matrix of coefficient height `H` produce two rows with remainders of absolute
value at most `epsilon`.  Then

`|Delta| <= 2 H epsilon (|B_0|+|B_1|)`.

Indeed, for any two rows one has

`Delta = B_0 L_1-B_1 L_0`,

and the unimodular recombination preserves `|Delta|`.  The theorem is
kernel-checked as `twoSelector_det_height_decay_tradeoff` and
`twoSelector_unimodular_height_decay_tradeoff` in
`TwoSelectorRemainderEscape.lean`.

Replaying the four existing starts, without extending the scan, gives the
following exact-fraction lower bounds.  The logarithms shown are floors of
base-two logarithms; they are display summaries of the exact values stored in
the receipt.

| `s` | floor `log2 H` observed | floor `log2 H` forced | floor `log2` slack ratio | common remainder ceiling |
|---:|---:|---:|---:|---:|
| 0 | 2 | 0 | 1 | `0.108295822978...` |
| 1 | 92 | 52 | 39 | `0.557628534747...` |
| 2 | 710 | 293 | 416 | `0.615721627112...` |
| 3 | 2260 | 1873 | 387 | `0.711584167410...` |

At `s=3`, therefore, at least 1874 coefficient bits are already forced by the
preserved determinant, the normalized denominator height, and the certified
remainder ceiling.  The observed 2261-bit height is not primarily an LLL or
continued-fraction search artefact.

## The asymptotic verdict

There is a sharper logical obstruction.  At a rational target `F=a/q`, every
integral remainder is an integer divided by `q`.  Non-collinearity ensures
that at least one of the two remainders is nonzero, hence has absolute value at
least `1/q`.  Lean checks the pointwise gap and the sequence-level consequence:
two non-collinear integral forms cannot both tend to zero at a rational
target (`rational_twoSelector_remainder_gap` and
`rational_twoSelector_not_both_tendsto_zero`).

Thus generic continued-fraction recombination is not an independent
irrationality engine.  Its finite subunit success is real, but a theorem that
makes both forms tend to zero already contains the irrationality conclusion.
The surviving route must use source-specific q-Apery structure to define the
recombinations, prove an upper bound for their coefficient height, and prove
cofinal decay without assuming that the exact real-form ratio has an infinite
continued fraction.  Extending the finite start horizon cannot address this
logical gap.
