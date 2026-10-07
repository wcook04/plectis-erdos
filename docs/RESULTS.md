<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Results and limits

This repository formalises theorems, reductions, equivalences, and
obstructions related to eight Erdős problem programmes —
[#68](https://www.erdosproblems.com/68),
[#243](https://www.erdosproblems.com/243),
[#249](https://www.erdosproblems.com/249),
[#251](https://www.erdosproblems.com/251),
[#257](https://www.erdosproblems.com/257),
[#269](https://www.erdosproblems.com/269),
[#1041](https://www.erdosproblems.com/1041), and
[#1049](https://www.erdosproblems.com/1049).
Each problem has a short paper and a longer reasoning record; the retired
combined #249/#257 manuscript is archive/provenance only, not a current
gateway. Using the degree-seven polynomial constructed by the erdosproblems.com
contributor ani, Lean proves that every preconnected strict-lemniscate set
containing two distinct roots has one-dimensional Hausdorff measure greater
than two. This refutes the exact Formal Conjectures path-image-length
statement; the separate total-variation bound is also checked. The other
seven targets remain open. Independent human review of correspondence with
the 1958 wording has not been recorded. Comparator checks only selected exact
statements, axioms and kernel acceptance; it does not assess novelty or
historical correspondence.

Lean source checked by the pinned Lean kernel is proof authority. The audit log
reports the headline declarations below with kernel assumptions
`[propext, Classical.choice, Quot.sound]`. A theorem with hypotheses proves only
the displayed implication; it does not prove that its hypotheses occur.

## The short version

The [front-page #257 example](../README.md) gives a complete irrationality
theorem for restricted supports. The other programmes have direct results,
exact reductions, conditional routes and counterexamples to tempting methods.
The table gives one entry point per problem; the
[guide below](#problem-by-problem-guide) keeps each result beside its missing
step. Mathematical importance requires separate judgement.

| Problem | A result to start with | Where the result stops |
|---|---|---|
| [#68](#result-68) | Two exact finite denominator exclusions and a Lean-checked `3/2` lower growth exponent; the paper also gives a finite calculation of attainable factorial moments after prescribed cancellations. | Lean proves irrationality equivalent to cofinally many non-unit factorial carries; no cofinal supply of such carries has been produced, so irrationality is still unproved. |
| [#243](#result-243) | Lean checks irrationality under the precise cubic rate and every nonintegral regular rate above one; the paper transfers these zero-indexed statements to one-based indexing. Signed-error criteria also force eventual Sylvester behaviour under their stated premises. | The unrestricted Sylvester-tail hypotheses remain unproved. |
| [#249](#result-249) | The short paper and Lean classify the fixed-base-two totient-residue series for every positive modulus and every rational-valued observable at dyadic moduli. They also give the exact all-base totient-kernel rank `k^e+1`. | The original series with unreduced totients remains open; the conditional routes still need their cofinal arithmetic inputs. |
| [#251](#result-251) | Lean checks a rich synthetic prime-gap countermodel, and the paper gives a separate sparse-perturbation obstruction. | These are not actual prime gaps; the prime-specific producer for irrationality remains open. |
| [#257](#result-257) | Lean checks the finite-prime weighted-support theorem at every integer base, including supports with divergent reciprocal sum. | It does not cover every infinite support. [Palomar registered version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-09-25-000009&version=1) of the exact five-declaration `E257_01` selection. |
| [#269](#result-269) | Lean checks irrationality of the distinct-height sum `D_{2,3,5}`. Ordinary proofs give irrationality of `D_P` for every finite set of at least two primes and of each single-prime sub-sum `E_p`. | The general proofs were checked by a second AI agent, with no human review; the repeated catalogue sum `R_P` for three or more primes remains open. |
| [#1041](#result-1041) | Ani's degree-seven polynomial refutes the exact Formal Conjectures path-image-length statement in Lean; Lean also checks positive trinomial and sharp collinear families. | Independent review of correspondence with the 1958 wording is pending; other geometric results have their own hypotheses. |
| [#1049](#result-1049) | Lean checks irrationality in Zudilin's rational-base contour region and exact Hankel orders. | `3/2` and the all-rational-base claim remain open. |

To read further, the [paper catalogue](../paper/README.md#problem-papers)
has each short paper and longer reasoning record; the
[synthesis paper](../paper/synthesis/optimal-sparse-perturbations.pdf) reads
across the eight. To inspect a claim, use the [source map](reference/SOURCE_MAP.md),
[claim registry](claims.json), [prior art](PRIOR_ART.md) and
[verification dossier](EXTERNAL_VERIFICATION.md); Comparator covers selected
formal statements, not every theorem or its novelty. The
[reproduction guide](REPRODUCIBILITY.md) starts with one claim without Lean.
For the system's design and its open-source collaboration model, read
[the systems paper](../paper/systems/claim-faithful-publication-systems-paper.pdf).
The [systems paper index](../paper/systems/README.md) identifies the earlier
accounts retained for historical detail.
To improve a proof, explanation or the architecture itself, use the
[contribution route](../CONTRIBUTING.md),
[architecture guide](research-commons/ARCHITECTURE_CONTRIBUTIONS.md) and
[credit policy](research-commons/CREDIT_POLICY.md).

### Problem-by-problem guide

<a id="result-68"></a>

**[#68](https://www.erdosproblems.com/68).** Put
`S = ∑_{n≥2} 1/(n!−1)` and `L_N = lcm_{2≤n≤N}(n!−1)`. Any rational
`S = a/q` with `q>0` satisfies the two incomparable exclusions
`q ∤ 299999!` and `q ≥ 2^{39990} > 10^{12038}`. The first is a factorial
divisibility constraint from a fresh exact GMP carry census through
`m = 300000` together with a Lean consumer; that replay matches the previously
retained certificate, while an
independent replay through `4000` reproduces the unit-carry prefix. The second
is an independent continued-fraction size bound. Neither implication yields
the other, and neither proves irrationality. The paper and Lean proof give
`liminf log L_N/(N^(3/2) log N) ≥ 2√2/3`. This is a common-denominator theorem:
it shows why clearing every summand separately cannot make the positive tail
small, but says nothing by itself about the denominator after cancellation.
Lean separately checks that irrationality of `S` is equivalent to
cofinally many non-unit factorial carries, and checks a finite quotient-band
channel obstruction. The required cofinal carries are not produced. A local
exact calculation at the prime `12487` exhibits two critical roots for gap
`12`, so the earlier small-prime pattern of at most one critical root is not a
uniform theorem; those roots have factorial values `442` and `6300`, not `1`.
Lean checks the `3/2` theorem as `common_denominator_growth_liminf` in
`PaperCompleteLiminf.lean`. The separate public Lean release
[`wcook04/plectis-erdos-lean`](https://github.com/wcook04/plectis-erdos-lean/blob/52f29ad173b04e3bac941b3663f2b9aebe5de0bb/PalomarCorpus/E68/Challenge.lean#L249)
states the `3/2` bound at commit `52f29ad1` as `common_denominator_growth` in
its entry `PalomarCorpus/E68` and proves it; that repository's Linux replay of
Palomar's Comparator stage accepted the entry with both kernels
(run 34782407633).
Further conditional zero-branch and private-factor carry producers are in the
[formal evidence](EXTERNAL_VERIFICATION.md#programme-68); neither supplies the
cofinal property for the actual factorial-gap orbit. Read the
[short paper](../paper/68/erdos-68-factorial-denominator-irrationality.pdf) or
[long record](../paper/68/erdos68-factorial-reasoning-surface.pdf).
The channel results have a direct finite use. For a finitely supported integer
vector `λ` on indices `n≥2`, set `M(λ)=∑ n!λₙ` and let `V_d(λ)` be its
factorial channel at `d`, as defined in [Section 2 of the short
paper](../paper/68/erdos-68-factorial-denominator-irrationality.pdf).
Given a depth `D≥2`, the paper classifies the moments possible when
`V₂(λ)=⋯=V_D(λ)=0`. Its tail gcd needs only coefficients through
`H=D(2p−1)<2D²` for a prime `D/2<p≤D`; this makes the minimum positive
moment a finite calculation. At `D=4`, the minimum is **1380**, attained by
`λ=(-15318, 8176, -710, 1518, -253, -88, 11)` on indices `2,…,8`.
Direct substitution gives `M(λ)=1380` and `V₂(λ)=V₃(λ)=V₄(λ)=0`; the
coordinate and finite-gcd theorems prove minimality. This certificate answers
which moments survive a chosen finite cancellation. It does not establish
nonintegrality of the remaining tail or irrationality of `S`.
Run `python3 scripts/check_erdos68_channel_moment.py` for the
[exact integer replay](../scripts/check_erdos68_channel_moment.py) of the
recurrence, finite gcd, moment and three vanishing channels. The paper's
finite tail-gcd theorem extends the computed gcd to all later indices.

<a id="result-243"></a>

**[#243](https://www.erdosproblems.com/243).** Under the exact cubic rate
`a_n²/a_(n+1)=1+3/n+o(n⁻³)`, every strictly increasing positive integer
sequence has an irrational reciprocal sum. Lean checks the zero-indexed
theorem through a square-specialisation argument using Mathlib's
Dedekind-zeta simple pole; the short paper transfers it to one-based indexing
by an ordinary finite-prefix argument. Its printed proof uses classical
Chebotarev instead. This rate does not cover the unrestricted Sylvester-tail
question.

More generally, the [nonintegral regular-rate theorem](../lean/ErdosProblems/Erdos243/PaperCompleteR21/NonintegralRegularRate.lean)
checks irrationality when `λ > 1` is nonintegral and
`a_n²/a_(n+1)=1+λ/n+o(n⁻λ)`. Its Lean statement derives convergence
for a positive, strictly increasing sequence indexed from zero. The long
paper gives the ordinary finite-prefix transfer to one-based indexing.
The integer-extraction lemma rules out nonintegral coefficients; the
separate cubic argument rules out coefficient three. No rational examples
are asserted for the remaining integer coefficients.

The rounded sequence `a_1 = 8`,
`a_(n+1) = ⌈n a_n²/(n+3)⌉` has precisely this rate and product-ratio
increments of order `n²`. Thus the separate bounded-increment recurrence
criterion below gives no conclusion for it, while the cubic-rate theorem
proves its reciprocal sum irrational. Duverney's Corollary 3.2 supplies an
earlier signed recurrence criterion under its printed one-sided growth-defect
condition. In the all-positive, absolutely summable specialisation, the
product-ratio increments tend to zero. For the rounded example,
`a_(n+1)/a_n²−1 ∼ −3/n`, so its signed defect series diverges and that
absolutely summable specialisation does not apply. The exact `o(n⁻³)`
remainder matters to the polynomial-exclusion proof. These comparisons locate
the contribution without deciding its novelty or priority; the
[short paper's argument and example](papers/full-text/erdos-243-reciprocal-tail-rigidity.md#sec:secondaryrate)
give the proof and source locators.

The short paper also proves an ordinary original-sequence corollary. Let
`a_1<a_2<⋯` be positive integers,
`a_(n+1)/a_n²→1`, `∑ 1/a_n` rational, and `P_n=∏_{j<n} a_j`. If
`limsup (P_n/a_n)(a_n²/a_(n+1)−1)<+∞`, then
`a_(n+1)=a_n²−a_n+1` eventually. The needed limsup bound, or the paper's
alternative weighted record budget, is not proved for the unrestricted problem.
Take a positive denominator `q` of the full reciprocal sum and clear the nth
tail by `qP_n`. The resulting integer error is minus `q` times the scaled
defect, up to a term tending to zero. This
cancellation turns the upper bound in the original sequence into the lower
bound on the integer error used below.
The proof passes through a signed bounded-negative theorem. Lean checks
that theorem and the canonical tail transfer described below. Let `a,C,D : ℕ → ℕ` and
`E : ℕ → ℤ`. Assume
`a(n)>1`, `C(n)>0`, the exact recurrences
`C(n+1)+D(n)=a(n)C(n)` and `D(n+1)=a(n)D(n)`, and that `E(n)` is the exact
centered state with `|E(n)|<C(n)`. If one constant `B` satisfies `E(n)≥−B`
for every `n`, and for every `K` one eventually has `K|E(n)|<C(n)`, then
`E(n)=0` eventually (`boundedNegativePart_eventually_zero`). The checked
centered-zero theorem then gives the Sylvester recurrence once the exact
product-cleared orbit has an eventually nonzero next-tail state. Lean carries
that chain to the original denominators in
`boundedNegativePart_sylvesterNext_eventually`, and checks the LCM-weighted
bounded-defect corollary from the rational reciprocal sum in
`original_coordinate_lcm_bounded_defect`
(`ErdosProblems/Erdos243/PaperCompleteR7/LcmDefect.lean:49`); the paper derives
the displayed `P_n` form from that corollary by `A_n | P_n`. For the
state-system endpoint, no uniform lower bound on the centered error is proved.
Unbounded negative excursions and the full Erdős endpoint remain open. The
signed recovery develops Koizumi's canonical-tail framework under an additional
bounded-negative premise. Read the
[short paper](../paper/243/erdos-243-reciprocal-tail-rigidity.pdf),
[long record](../paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf), or
[selected formal checks](EXTERNAL_VERIFICATION.md#programme-243).

The long record also proves an exact maximal-gap theorem for a separate
static sieve. Let `m₀<m₁<⋯` be pairwise coprime integers at least `2`, with
`ℓ(m_j)=j+O(1)` for `ℓ(x)=log₂ log₂ max(4,x)`. If
`σ=∏_j(1−1/m_j)>0` and `u_n` lists the positive integers divisible by none
of the `m_j`, then
`limsup (u_(n+1)−u_n)/ℓ(u_n)=1/σ`. Lean checks the general theorem
`maximal_gap_limsup_eq_inv_sigma` with the convergence to `σ` stated
explicitly. The paper's finite-product calculation gives `σ=1/2` and thus
coefficient `2` for the Fermat moduli `m_j=2^(2^j)+1`. This concerns
[avoidance of whole moduli](papers/full-text/erdos243-reciprocal-tail-reasoning-surface.md#long243:res:gapconstant),
not coprimality to composite moduli or construction of a reciprocal-tail
orbit; the unrestricted #243 question remains open.

<a id="result-249"></a>

**[#249](https://www.erdosproblems.com/249).** The short paper and Lean
classify the fixed-base-two series with coefficients `φ(n) mod m`: it is `0`
for `m=1`, `3/4` for `m=2`, and irrational for every `m≥3`. More generally,
for `k≥1` and any rational-valued function `f` on the residues modulo `2^k`,
the series with coefficients `f(φ(n) mod 2^k)` is rational exactly when `f`
is constant on the even residue classes. If that constant is `c`, the value
is `3f(1)/4+c/4`. For example, at modulus four, the table
`f=(5,7,5,-2)` in residue order `0,1,2,3` gives `13/2`, while
`f=(0,0,1,0)` gives an irrational sum. The public Lean development checks the
[irrationality theorem](https://github.com/wcook04/plectis-erdos/blob/a14777b3219873bc8343205cca0bb3bb6530e8fa/lean/ErdosProblems/Erdos249/ResidueClassTotientSeries.lean#L566-L580)
and [dyadic classification](https://github.com/wcook04/plectis-erdos/blob/a14777b3219873bc8343205cca0bb3bb6530e8fa/lean/ErdosProblems/Erdos249/PaperCompleteR7/RationalObservableClassification.lean#L221-L233).
The series with unreduced totients remains open.

The short paper also proves the all-base finite-level totient-kernel rank
`k^e+1` for every `k≥2` and `e≥1`, with canonical integral coordinates and
a basis of all integral relations; at prime base the rank is exponential in
the depth `e`. A rational `5/4` control that agrees with totient on odd
arguments still has tempered carry rank at least `2^e−1` at every depth, so
a generic rationality-driven carry-rank ceiling is false. The strongest
checked structural result on the hypothetical rational totient branch is
carry anti-compression:
one carry would have uniformly eventually-periodic dyadic sections modulo its
multiplier while retaining canonical section rank at least `2^e − 1` at every
level. No finite-rank upper bound is proved, so this is a necessary
consequence rather than a contradiction. Finite denominator exclusions and
conditional actual-LCM, first-harmonic and strict natural-prime tail-gap
routes remain useful, but none supplies its missing cofinal producer. Coons
non-regularity, Martin affine
independence, and Yazdani–Shallit CRT–Dirichlet separation are credited
antecedents, not new claims of this release. Read the
[short paper](../paper/249/erdos-249-binary-totient-series.pdf),
[long record](../paper/249/erdos249-totient-reasoning-surface.pdf), and
[selected formal checks](EXTERNAL_VERIFICATION.md#programme-249). For a
concrete use of the basis, the short paper's
[base-six example](papers/full-text/erdos-249-binary-totient-series.md#sec:base-six-test)
reduces all
43 sections through depth two to 37 coordinates. The
[exact normal-form tool](../scripts/totient_kernel_normal_form.py) prints
those coordinates, the six relation coefficients, and an integer
counterexample at one of the first 37 inputs whenever a proposed identity
is false; its determinant check certifies that finite test.
For any integer base, the
[sparse normal-form command](../scripts/totient_kernel_sparse_normal_form.py)
reduces only the supplied sections to exact integral coordinates and decides
their identity by the all-base basis theorem. For example,
`--base 12 --term 8:29859840:1 --term 2:10:-1990656` returns an identity
without constructing the ambient depth-eight matrix. Its optional
`--witness-budget` searches for a concrete unequal input; exhaustion does not
change an exact nonidentity decision. The Python command is an implementation
of the paper's reduction, not a Lean-verified executable artifact.

<a id="result-251"></a>

**[#251](https://www.erdosproblems.com/251).** A
[public Lean declaration](../lean/ErdosProblems/Erdos251/AllResidueLogarithmicR9.lean)
constructs a synthetic sequence of positive even digits bounded by
`4 log(n+1)+24`. Its dyadic sum is exactly `6`, every complete scaled tail and
every tail shift is integral, the values `2` and `4` recur arbitrarily late in
every residue class, and its increasing odd cumulative positions satisfy
`P_n/(n log n) → 1`. The
[reasoning paper states the combined theorem explicitly](papers/full-text/erdos251-prime-gap-reasoning-surface.md#long251:res:all-residue-log-countermodel).
This rules out a much richer package of plausible soft inputs than
unboundedness or nonperiodicity alone, but these digits are not the actual
prime gaps. The declaration is source-backed and does not yet have a curated
claim row.

Independently, a sparse perturbation of the prime gaps can have a rational
dyadic sum while retaining the prime growth scale, every fixed eventual
congruence, and asymptotically the same short-block statistics. The later
positions are not asserted to be prime. This is complementary to Land's
conditional result, not a refutation. Lean checks the sparse rational-target
construction and the polylogarithmic schedule with growing-block transfer in
`SparsePaperR11.lean`. The printed construction additionally gives congruence
cutoffs uniform in the target; the linked Lean statement quantifies those
cutoffs after the target. The prime-growth corollary uses cited analytic results. This obstruction shows that those coarse
statistics alone do not force irrationality. Lean also checks a precise
conditional route: for one fixed shift, cofinally many adjacent tail shifts
strictly between `-1` and `1`, with unequal actual prime gaps, would prevent
eventual integrality of that shift. Those prime-specific mismatches are not
proved. The exact prime-gap summation-by-parts equivalence still proves
neither the prime-gap series nor the original series irrational. Read the
[short paper](../paper/251/erdos-251-prime-gap-dyadic-series.pdf),
[long record](../paper/251/erdos251-prime-gap-reasoning-surface.pdf), and
[selected formal checks](EXTERNAL_VERIFICATION.md#programme-251).

<a id="result-257"></a>

**[#257](https://www.erdosproblems.com/257).** Fix a finite nonempty set of
primes `P` and let `h(a)` be the largest divisor of `a` supported on `P`.
For an infinite support `A` and an integer base `b ≥ 2`, finiteness of
`∑_{a∈A} h(a)/(a(b^{h(a)}−1))` implies irrationality of
`∑_{a∈A} 1/(b^a−1)`. The
[long paper explains the proof](../paper/257/erdos257-mersenne-reasoning-surface.pdf):
if this sum were rational with denominator `v`, every positive displacement
from an integer would be at least `1/v`. Choose a finite part of `A` and make
its exponents divide an observation modulus `Q`, so their displacements vanish.
For the remaining exponents, a complete residue orbit gives the weighted main
term. Averaging over a finite block of dyadic observation lengths charges the
incomplete orbits by weighted reciprocal mass, uniformly over finite
subfamilies; this uniform bound permits the passage to the infinite support.
The [short paper](../paper/257/erdos-257-mersenne-support-subseries.pdf)
then chooses the modulus and block length so that its error charged to the
whole weighted mass tends to zero. The Lean proof first makes the remaining
tail weight small and uses a different block-length schedule. Both produce a
positive displacement below `1/v`; their parameter schedules should be read
with their respective error bounds.
Lean proves this as `divisibilityWeightedClaim` in
[`WeightedReturn.lean`](../lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean).
The short paper gives a shorter proof and an
explicit support with divergent reciprocal sum satisfying the criterion.
The comparison is with Erdős's earlier reciprocal-summable condition, which
he stated for every integer base after proving the pairwise-coprime case.
For `P = {2}`, write `a = 2^k m` with `m` odd: the weighted summand is
`1/[m(b^{2^k}−1)]`. In the short paper's example
`A★ = {2^k m : k ≥ 1, m odd, m ≤ 2^{2^k}}`, dyadic blocks show that the
odd reciprocals in the `k`th layer sum to between `2^k/4` and `2^k`.
The layer therefore contributes at least `1/4` to `∑_{a∈A★} 1/a`, but at
most `2^{1−k}` to the base-two weighted sum. The ordinary reciprocal sum
diverges while the weighted sum converges. The theorem gives irrationality
at every integer base for every infinite subset of `A★`. It does not cover
full support, all odd exponents, or the full prime support; Tao–Teräväinen
prove the latter at base two by another method.
The [#257 reader exercise](research-commons/PROVE2ME_WEIGHTED_257_PACKET.md#try-changing-a-hypothesis)
tests how changing a layer cutoff alters this certificate, and why a failed
weighted test is not a rationality result.
A [second test](research-commons/PROVE2ME_WEIGHTED_257_PACKET.md#try-a-changing-prime-set)
shows why a prime set fitted separately to each finite prefix cannot certify
the infinite hypothesis.
The [weighted-support transfer exercise](../research/experiments/weighted_support_transfer/README.md#a-host-that-needs-every-chosen-prime)
gives the complementary fixed-host phenomenon: for any prescribed finite
nonempty prime set, its binary weighted certificate can require every prime
in that set. This is a calculation about the sufficient criterion, not a
claim that each infinite subset needs the same witness or that the example
has been formalised separately in Lean.
The comparison identifies the added class and proof mechanism, but does not
settle independent novelty or priority assessment. See the
[short paper's theorem, example and sources](papers/full-text/erdos-257-mersenne-support-subseries.md#an-example-beyond-reciprocal-summability).
[One host realises any finite monotone witness rule](papers/full-text/erdos257-mersenne-reasoning-surface.md#sec:257-finite-witness-rules),
checked in Lean as `finite_monotone_witness_rule_realised`. Given a finite
set $E$ of primes and a nonconstant upward-closed rule on its subsets, a
finite union of prime-cofactor blocks has divergent reciprocal sum, its
weighted test converges at every base exactly when the witness primes in $E$
satisfy the rule, and every infinite subset has irrational subseries at every
integer base. For three primes, any two suffice and none is individually
mandatory. The [worked variants](../research/experiments/weighted_support_transfer/README.md#a-host-with-several-minimal-witnesses)
compare this host with a different required-prime construction. The
construction is AI-assisted and its novelty has not been independently
assessed.
At base two, the weighted condition can also be combined with the positive
divisor-cover criterion: the long paper proves that a common finite averaging
window makes both displacements small. Every infinite subset of their union
then has irrational subseries at every integer base. Lean proves this as
`mixedSupportClaim` in the same module. Neither theorem establishes the
separately proposed hosts separating the two classes.
Every infinite reciprocal-summable support satisfies it, yielding the
coprimality-free extension stated by Erdős. Full-support
irrationality at every integer base is classical (Erdős 1948) and
Lean-checked here, as are pairwise-coprime summable-reciprocal support and
Lebesgue measure one for the base-2 achievement set. Irrationality for
every infinite support and the `1/2` and `1/21` branches remain open.
The weighted theorem is Lean-checked. The exact five-declaration
`PalomarCorpus/E257_01` entry, which includes `divisibilityWeightedClaim`,
passed [Palomar mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/36009433226)
for source commit `b85ed30805188eb4390a686b111294b24363418e`.
Palomar [registered version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-09-25-000009&version=1)
as `PALOMAR-2026-09-25-000009` on 25 September 2026. The
[immutable record](https://data.palomar-registry.org/entries/PALOMAR-2026-09-25-000009-v1.json)
binds that version to submission `gid0ym5uu910`, the pinned source, and the
five selected declarations. Registration and mechanical verification cover
the selected interface, not every claim in the
paper or the unrestricted Erdős problem. Read the
[short paper](../paper/257/erdos-257-mersenne-support-subseries.pdf),
[long record](../paper/257/erdos257-mersenne-reasoning-surface.pdf), and
[separate Comparator verification status](EXTERNAL_VERIFICATION.md#programme-257).

<a id="result-269"></a>

**[#269](https://www.erdosproblems.com/269).** Distinguish the catalogue sum
`R_P`, which retains a reciprocal for every smooth-number prefix and therefore
repeats LCM values, from `D_P`, which counts each distinct running-LCM value
once. Lean checks irrationality of `D_{2,3,5}` in the
[short paper's five-map theorem](../paper/269/erdos-269-three-prime-running-lcm.pdf)
(`res:distinct-height-235`); Comparator has not yet been run for this result.
For every finite set `P` of at least two primes, the
[long record](../paper/269/erdos269-running-lcm-reasoning-surface.pdf)
gives an ordinary proof that `D_P` is irrational (`long269:res:distinct-height-all`),
checked by a second AI agent and awaiting formalisation, with no human review.
It also proves irrationality of each single-prime sub-sum `E_p` of the
catalogue sum under the same hypotheses and evidence class
(`long269:res:single-prime-subsums`). Erdős asserted the general `D_P`
conclusion without a printed argument in 1973; the paper claims no priority
for that conclusion. The repeated catalogue sum `R_P` remains unresolved for
three or more primes. Irrationality of individual sub-sums does not establish
irrationality of their sum.

For three pairwise distinct primes, the threshold-column argument produces nonsingular selected kernel
minors of every order and excludes every finite rational separated kernel
representation. The arbitrary-order theorem is present in the compiled
public Lean source, but the Wave-A receipt's named axiom audit does not audit
that rank declaration; Comparator checks only the displayed rank-two minor
`-1/15`. For the repeated catalogue `{2,3,5}` series, Lean checks the
rationality-to-positive-reduced-carry bridge. Cofinal local-window escape then
extinguishes such carries; under the explicit cap hypotheses recorded in the
claim registry, that escape statement is equivalent to irrationality. This is
an exact interface, not an easier theorem whose premise has been proved. The
source-specific escape and repeated three-prime catalogue sum remain open.

For every pair of distinct primes, both the repeated running-LCM reciprocal
sum and the version retaining one term at each distinct LCM value are
transcendental. The
[ordinary proof](../paper/269/erdos-269-three-prime-running-lcm.tex) expresses
them as nonconstant quadratic and affine polynomials in one transcendental
Hecke–Mahler value. Steve Fan posted the repeated-sum two-prime factorisation,
reduction and transcendence conclusion first, on the problem's forum on
26 June 2026; the note credits his priority, gives a proof found
independently, derives the de-duplicated formula, and uses the cited
Hecke–Mahler transcendence theorem. Lean also checks the two-prime affine and
quadratic formulas and derives transcendence from the cited Hecke–Mahler
result as an explicit named hypothesis; that external theorem itself is not
formalised here. Read the
[short paper](../paper/269/erdos-269-three-prime-running-lcm.pdf),
[long record](../paper/269/erdos269-running-lcm-reasoning-surface.pdf), and
[selected formal checks](EXTERNAL_VERIFICATION.md#programme-269).

<a id="result-1041"></a>

**[#1041](https://www.erdosproblems.com/1041).** A source-backed
[ordinary theorem](../research_corpus/Erdos1041/ConcyclicAlternation.md) covers
monic degree-`n` polynomials, `n≥3`, whose distinct zeros lie on a circle of
radius `ρ` and satisfy `2ρ^n≤1`: two adjacent zeros have chord length at most
`2ρ sin(π/n)<2`, and their straight chord lies in `{|f|<1}`. A repeated zero is
an immediate short connection. The
[reasoning record](papers/full-text/erdos1041-lemniscate-reasoning-surface.md#unformalised-remark-a-bounded-radius-concyclic-class)
explains the alternation and chord argument. The proof is outside Lean; an
[exact finite checker](../research_corpus/Erdos1041/scripts/check_erdos1041_concyclic_exact_witness.py)
tests load-bearing identities and configurations, and the theorem does not yet
have a curated claim row. At each fixed degree, the sharp arc constant `2`
leaves radii sufficiently close to `1` outside this method.

Every monic trinomial with roots in the open unit disc also has radial
root-to-origin segments inside `{|f|<1}`, so any two roots join through the
origin with length less than `2`; Lean checks the complete displayed
trinomial statement. For collinear roots, Lean checks a sharp Chebyshev
segment bound and the resulting `<2` connector when the roots lie in the
open unit disc. These are solved families, not a general connector theorem.
For a squarefree monic polynomial, write `μ = min_{f'(c)=0} |f(c)|`. An
ordinary theorem gives a connector of length less than `2` in the open unit
lemniscate whenever `μ ≤ 13/25`, with no root-location hypothesis; scaling
gives a connector of length less than `(5/2) μ^{1/n}` in `{|f| < (25/13)μ}`.
The sharp critical-value mean on the closed unit disc is Lean-checked with
[source-bound audit evidence](../verification/erdos1041-returned-r18-v5-full-audit-evidence.json),
and the paper also gives an ordinary proof. The mean controls critical values,
not connectors.

A further ordinary theorem gives a connector of length less than `2` in every
degree `n≥3` when a simple nonzero critical value admits the stated separated
critical-value disk at radius `4/3`; it asserts no existence of such a disk.
On the generic stratum where simple nonzero critical values have pairwise
distinct arguments and moduli, an ordinary slit-sheet theorem identifies the
inverse-ray root-connection tree but gives no uniform length bound. Lean checks
Newton-flow decay, ray-separating translations, and perturbative root
retention. Using one degree-seven polynomial constructed by the
erdosproblems.com contributor
[`ani`](https://www.erdosproblems.com/forum/thread/1041#post-8861), Lean proves
that every preconnected strict-lemniscate set joining two distinct roots has
one-dimensional Hausdorff measure greater than two. This refutes the exact
Formal Conjectures path-image-length statement and the separate total-variation
formulation; correspondence with the 1958 wording remains unreviewed.
The short paper also gives a cubic showing why a two-root first merger alone
does not force a capacity gap; its Lean capacity clause assumes the classical
transfinite-diameter formula. Read the
[short paper](../paper/1041/erdos-1041-lemniscate-newton-flow.pdf),
[long record](../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf), and
[selected formal checks](EXTERNAL_VERIFICATION.md#programme-1041).

<a id="result-1049"></a>

**[#1049](https://www.erdosproblems.com/1049).** For positive integers
`0<b<a` in the exact Zudilin contour region, Lean checks irrationality and
the stated irrationality-exponent bound for `F(a/b)`, including every positive
integral power of `31/4`. The short paper also gives an ordinary proof for
coprime `a,b` under `log b/log a < θ*`, where
`θ* ≈ 0.4056830214`, using Zudilin's 2004 forms and estimates. Zudilin's
prior work is credited; formalisation does not establish novelty. Lean also
checks the normalized Hankel determinant's order and leading coefficient at
every rank. Separately, for each real `p>1` and `1≤N≤8`, the Lean-checked
finite coefficient pencil has a positive definite first matrix, real roots
strictly below `F(p)`, and non-strict interlacing at adjacent ranks. The eight
unshifted determinant certificates are kernel checked; the shifted eight and
76 cyclotomic residue witnesses remain finite computations. These results
give no all-rank coefficient positivity or irrationality at `3/2`, which lies
outside the contour region. The universal rational-base question remains open.
Read the [short paper](../paper/1049/erdos-1049-rational-base-lambert.pdf),
[long record](../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf),
and [selected formal checks](EXTERNAL_VERIFICATION.md#programme-1049).

## Find the exact statement or continue the work

[Claims](claims.json) record selected public statements, assumptions and exact
open propositions. Query one programme or open question from the repository root:

```sh
python3 scripts/query_corpus.py --route erdos_257
python3 scripts/query_corpus.py --open
python3 scripts/query_expert_handoffs.py
```

Use the [source map](reference/SOURCE_MAP.md) for declarations and paper
passages, the [argument frontier](reference/ARGUMENT_FRONTIER.md) for named
missing inputs, and [prior art](PRIOR_ART.md) for attribution. The
[argument graph](agents/ARGUMENT_GRAPH.md) explains the technical tools.
[Reproducibility](REPRODUCIBILITY.md) gives replay commands;
[methodology](METHODOLOGY.md) governs scope and public claim transitions.
A finite certificate, an equivalent restatement or an unproved conditional
input does not discharge an infinite target.

The individual papers and longer records own detailed arguments, historical
corrections and unsuccessful approaches. This guide summarises current
conclusions; the archived joint manuscript is historical provenance.

The [documentation index](README.md) carries the question menu; the
[semantic reference](semantic/README.md#corpus-census) carries generated corpus diagnostics.
