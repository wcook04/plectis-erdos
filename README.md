<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

<a id="plectis-open-mathematical-research-with-lean"></a>

# Plectis: research on eight Erdős problems with Lean

Plectis brings together papers, formal proofs and experiments on eight Erdős
problems, maintained by Will Cook. Lean checks the formal statements. The
research environment and contributor workflow are prototypes.

**[Website](https://wcook04.github.io/plectis/) · [Interactive maths map](https://wcook04.github.io/plectis/maths/universe.html) · [Maths reading room](https://wcook04.github.io/plectis/maths/)**

[Read the #257 introduction](paper/257/erdos-257-mersenne-support-subseries.pdf#page=1) ·
[A reader's way in](docs/READING_GUIDE.md) ·
[All papers](paper/README.md) · [Results and limits](docs/RESULTS.md) ·
[Contribute or correct](CONTRIBUTING.md)

<a id="results-and-their-limits"></a>

Using the degree-seven polynomial constructed by the erdosproblems.com contributor ani, Lean proves that every preconnected strict-lemniscate set containing two distinct roots has one-dimensional Hausdorff measure greater than two. This refutes the exact Formal Conjectures path-image-length statement; the separate total-variation bound is also checked. The other seven targets remain open. Independent human review of correspondence with the 1958 wording has not been recorded. Comparator checks only selected exact statements, axioms and kernel acceptance; it does not assess novelty or historical correspondence.

See the [#1041 case study](docs/case-studies/formal-conjectures-1041.md) and [ani's original example](https://www.erdosproblems.com/forum/thread/1041#post-8861).

**Authorship and checking.** The problem papers report that Cook built and
directed the research infrastructure and reviewed claims when he could. AI
agents did most of their research and drafting; Cook did not independently
verify every claim. No independent human mathematical review has been recorded.
Do not infer results from private or unreleased work.

<a id="for-a-first-look-257"></a>

## Start with irrational subseries (#257)

[Problem 257](https://www.erdosproblems.com/257) asks whether adding
`1/(2^a − 1)` over **any infinite set of positive integers** always gives an
irrational number. The paper proves a sufficient condition on the exponents:
under that condition, every infinite subset gives an irrational sum at
**every integer base at least two**. It applies to some supports whose
reciprocal sum diverges, as well as to reciprocal-summable supports. The
unrestricted question remains open.

Read the introduction and **Theorem 1.2** in
[Irrationality criteria for Lambert subseries (PDF, 26 pages)](paper/257/erdos-257-mersenne-support-subseries.pdf),
then **section 2** for its proof. The [longer record](paper/257/erdos257-mersenne-reasoning-surface.pdf)
contains further proofs, computations and approaches.

**The precise condition.** Choose a finite nonempty set of primes `P`, and
let `h_P(a)` be the largest divisor of `a` whose prime factors lie in `P`.
For example, `P = {2}` gives `h_P(12) = 4`. If a set `H` of positive integers
satisfies

`∑_{a∈H} h_P(a)/(a(2^{h_P(a)}−1)) < ∞`,

then for every infinite `A ⊆ H` and every integer `b ≥ 2`,
`∑_{a∈A} 1/(b^a−1)` is irrational. Lean checks this criterion. The
paper's explicit reciprocal-divergent examples are ordinary proofs, without separate formal proofs of those examples.

**Why the proof works.** The argument averages a positive displacement
which rationality would keep bounded away from zero. Unfinished residue
periods lose the factor needed to sum over infinitely many exponents. A
second average, over window lengths that are powers of two, recovers that
factor and makes the displacement arbitrarily small.

To inspect the formal result, follow the
[declaration](lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L120),
its [statement interface](lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean#L61)
and the [weighted-mass definition](lean/ErdosProblems/Erdos257/PaperCompleteR7/PrimeWeightedDefinitions.lean#L25).
For formal comparison, see the [selected theorem replay](docs/verification/EXTERNAL_VERIFICATION_REPLAY.md#reviewer-replay). The
[weighted-support exercise](docs/research-commons/PROVE2ME_WEIGHTED_257_PACKET.md#try-changing-a-hypothesis)
lets you investigate how the hypotheses matter.

## Problem papers

The [results guide](docs/RESULTS.md#problem-by-problem-guide) keeps the statements
beside their qualifications and sources.

| Problem | Topic | Contribution and boundary | Papers |
|---|---|---|---|
| [#68](https://www.erdosproblems.com/68) | [Factorial-denominator irrationality](https://wcook04.github.io/plectis/maths/problems/erdos_68.html) | Integral cancellation basis and a finite gcd calculation. Irrationality still needs the required nonintegral forms. | [paper, 9 pages](paper/68/erdos-68-factorial-denominator-irrationality.pdf) · [longer paper](paper/68/erdos68-factorial-reasoning-surface.pdf) |
| [#243](https://www.erdosproblems.com/243) | [Cubic-rate irrationality and reciprocal tails](https://wcook04.github.io/plectis/maths/problems/erdos_243.html) | Irrationality when increasing positive integers satisfy `a_n²/a_{n+1} = 1 + 3/n + o(n⁻³)`, plus recurrence criteria. The unrestricted question remains open. | [paper, 21 pages](paper/243/erdos-243-reciprocal-tail-rigidity.pdf) · [longer paper](paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf) |
| [#249](https://www.erdosproblems.com/249) | [Binary totient series](https://wcook04.github.io/plectis/maths/problems/erdos_249.html) | A basis and all integral relations for totient sections. Irrationality of the unreduced binary series remains open. | [paper, 15 pages](paper/249/erdos-249-binary-totient-series.pdf) · [longer paper](paper/249/erdos249-totient-reasoning-surface.pdf) |
| [#251](https://www.erdosproblems.com/251) | [Prime-gap dyadic series](https://wcook04.github.io/plectis/maths/problems/erdos_251.html) | Sparse congruence-preserving perturbations and their prime-gap comparison. The cumulative positions need not be prime. | [paper, 14 pages](paper/251/erdos-251-prime-gap-dyadic-series.pdf) · [longer paper](paper/251/erdos251-prime-gap-reasoning-surface.pdf) |
| [#257](https://www.erdosproblems.com/257) | [Mersenne-support subseries](https://wcook04.github.io/plectis/maths/problems/erdos_257.html) | Weighted and divisor-cover irrationality criteria. Arbitrary infinite supports remain open. | [paper, 26 pages](paper/257/erdos-257-mersenne-support-subseries.pdf) · [longer paper](paper/257/erdos257-mersenne-reasoning-surface.pdf) |
| [#269](https://www.erdosproblems.com/269) | [Three-prime running LCM](https://wcook04.github.io/plectis/maths/problems/erdos_269.html) | Irrationality for distinct running LCMs of 5-smooth integers. The sum counted with multiplicity remains open here. | [paper, 17 pages](paper/269/erdos-269-three-prime-running-lcm.pdf) · [longer paper](paper/269/erdos269-running-lcm-reasoning-surface.pdf) |
| [#1041](https://www.erdosproblems.com/1041) | [Lemniscates and Newton flow](https://wcook04.github.io/plectis/maths/problems/erdos_1041.html) | Formalisation of ani's counterexample to the exact Formal Conjectures statement. Historical correspondence has no recorded independent review. | [paper, 18 pages](paper/1041/erdos-1041-lemniscate-newton-flow.pdf) · [longer paper](paper/1041/erdos1041-lemniscate-reasoning-surface.pdf) |
| [#1049](https://www.erdosproblems.com/1049) | [Rational-base Lambert series](https://wcook04.github.io/plectis/maths/problems/erdos_1049.html) | Fixed-base Hankel asymptotics and a sufficient rational-base region. The region excludes 3/2. | [paper, 20 pages](paper/1049/erdos-1049-rational-base-lambert.pdf) · [longer paper](paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf) |

[Reading Eight Erdős Problems Together](paper/synthesis/optimal-sparse-perturbations.pdf)
connects factorial series and Lambert subsums. Its main theorems are ordinary
proofs; Lean checks specified ingredients. See its [synthesis guide](paper/synthesis/README.md)
and the [paper index](paper/README.md) for other editions.

<a id="where-to-start"></a>

## Choose what to do

| Route | Start here | Outcome |
|---|---|---|
| **Read** | [Reading guide](docs/READING_GUIDE.md), [reading edition](docs/reading-edition/README.md), [work through an argument](docs/READING_GUIDE.md#work-through-an-argument) | Examine a statement and its proof. No installation or account needed. |
| **Trace** | [Follow one claim](docs/REPRODUCIBILITY.md#try-one-claim-without-lean), with Git and Python | Check recorded references and status. |
| **Experiment** | [#257 exact-rational example](docs/REPRODUCIBILITY.md#reproduce-the-257-exact-rational-example), with Python | Reproduce a specified finite exclusion test. |
| **Compile Lean** | [Clone and reproduce](docs/REPRODUCIBILITY.md) | Check the selected formal statement in its documented environment. |
| **Use an agent** | [Agent quickstart](docs/agents/README.md#start-with-current-public-work) and [architecture](docs/ARCHITECTURE.md) | Explain a result, investigate a question or improve a tool. |

After cloning, trace the featured claim with:

`python3 scripts/verify_claims.py --claim finite_prime_weighted_support`
(documented in the [reproducibility guide](docs/REPRODUCIBILITY.md#try-one-claim-without-lean)).

This checks references and status; it does not run Lean or Comparator.
The finite experiment does not reproduce the infinite weighted theorem.

<a id="what-the-checks-establish"></a>

## What Lean and Comparator verify

Lean checks the exact formal proposition in its source. The
[source map](docs/SOURCE_MAP.md), [claim records](docs/claims.json) and
[prior art](docs/PRIOR_ART.md) identify its statement, status and antecedents.
Comparator checks a solution against a separately declared statement with
permitted axioms. [`formalization.yaml`](formalization.yaml) and the
[verification dossier](docs/EXTERNAL_VERIFICATION.md) identify selected coverage.

Researchers still judge informal-to-formal correspondence, novelty and
usefulness. Reading, reference checks, finite calculations, formal acceptance
and independent human review establish different things.
[Methodology](docs/METHODOLOGY.md) explains how claims are reviewed.

<a id="about-the-project"></a>

## Why keep the whole research record?

I want other people to be able to work on these questions with me.
The longer records preserve calculations and precise obstructions, so
another reader can question an approach, repair it or use the idea elsewhere.
For #257, explaining why the first average fails and the second works is one
useful return. The [system paper](paper/systems/claim-faithful-publication-systems-paper.pdf)
and [design discussion](docs/ARCHITECTURE.md#why-preserve-explanations-and-failed-approaches)
explain how the record supports that work.

## Contribute

An explanation of the second average, a correction to a statement link,
an earlier reference or a precise obstruction is welcome. No solved problem,
Lean proof, clone or agent account is required.

- [Work on a paper](docs/CONTRIBUTE_BY_PAPER.md) or [a method across problems](paper/synthesis/README.md).
- Improve a tool through the [architecture contribution guide](docs/research-commons/ARCHITECTURE_CONTRIBUTIONS.md).
- Send a [question or correction](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml), [email me](https://wcook04.github.io/plectis/#contact), or return an agent investigation through the [frontier relay](docs/FRONTIER_RELAY.md).

[CONTRIBUTING](CONTRIBUTING.md) explains what to send: what you investigated,
what changed, inspectable evidence, remaining uncertainty and your credit
preference. Accepted contributions receive a public evidence and credit
record under the [credit policy](docs/research-commons/CREDIT_POLICY.md).
If you solve a problem, the credit for your solution is yours.

## Read or verify locally

[REPRODUCIBILITY](docs/REPRODUCIBILITY.md) owns installation, commands and build
requirements. The checkout is hundreds of megabytes; Lean builds download
additional toolchains and dependencies. The [security policy](.github/SECURITY.md)
explains the execution boundary. Agents enter through [AGENTS.md](AGENTS.md)
and the [agent workbench](docs/agents/AGENT_WORKBENCH.md). The
[architecture guide](docs/ARCHITECTURE.md#repository-map) explains the folder names.

<!-- BEGIN generated_corpus_at_a_glance -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
<details>
<summary>Corpus inventory and counting limits</summary>

## Corpus at a glance

The reviewed layer a mathematician should judge: 160 curated claim records in 38 contribution families, reaching Lean source through 478 principal declaration links. `docs/SCOPE.md` gives its shape and `docs/RESULTS.md` gives the strongest checked result per problem. The website and the papers are the human reading path.

The rest is engineering inventory. About 87% of the 164,639 declarations (142,668 across 695 modules) are machine-emitted certificate shards: one integer checked prime, one position excluded. The remainder is not all hand-written either.

| Engineering inventory | Current size |
|---|---:|
| Lean modules (the two library roots) | 1,903 |
| Formal results and supporting lemmas | 160,373 |
| Curated claim records | 160 |
| Contribution families | 38 |

Generated shards are counted as formal source and never as separate
mathematical claims. Claim records cover every status, including cited and
open, and are partitioned once.
These are navigation counts, not novelty claims. They still need expert validation.

</details>
<!-- END generated_corpus_at_a_glance -->

### Repository map

| Location | Contents |
|---|---|
| [paper/](paper/README.md) | PDFs and manuscript sources by problem. |
| [lean/](docs/SOURCE_MAP.md) | Formal proofs in the `Erdos249257` and `ErdosProblems` libraries. |
| [docs/](docs/README.md) | Guides, claim records and source maps. |
| [research/](research/README.md) | Experiments, examples and investigations. |
| [research_corpus/](research_corpus/README.md) | Dated research returns and unresolved obligations. |
| [computations/](computations/README.md) | Exact arithmetic certificates and scripts. |
| [verification/](verification/README.md) | Selected formal interfaces, solutions and replay configuration. |
| [evidence/](evidence/README.md) | Paper-to-proof records and stored Comparator reports. |
| [scripts/](scripts/README.md) | Query tools, projection builders and validation programs. |
| [skills/](skills/README.md) | Workflows for coding agents using this checkout. |





<!-- BEGIN generated_principal_declaration_anchors -->
<!-- Generated by scripts/build_corpus_descriptor.py; do not edit this region. -->
## Following a result into Lean

The paper links each headline result to the relevant source. For a particular
topic, start with the [source map](docs/SOURCE_MAP.md); it gives the module
order without asking you to decode Lean declaration names first.
<!-- END generated_principal_declaration_anchors -->

<a id="citation-and-prior-work"></a>

## Formal Conjectures contributions

Merged proof links for solved variants of Erdős's 1948 theorem:
[#257](https://github.com/google-deepmind/formal-conjectures/pull/6506),
[#258](https://github.com/google-deepmind/formal-conjectures/pull/5034) and
[#1049](https://github.com/google-deepmind/formal-conjectures/pull/6507);
plus the [#1041 correction](https://github.com/google-deepmind/formal-conjectures/pull/6505)
using ani's example. #258 is related work, not a ninth programme.

[Prove2Me packets](docs/research-commons/README.md#native-prove2me-theorems)
and [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean) provide
selected checks. The [paper catalogue](docs/papers/README.md) links archived
aiXiv editions; [verification guides](docs/verification/README.md) explain
recorded outcomes. Archived and current editions may differ.

## Credit

One mathematician's comments on the #243 note led to all sixteen problem
papers being rewritten for a first-time reader. The
[credit ledger](docs/research-commons/CREDIT_LEDGER.md) records advice and its
effects; names remain withheld until each person agrees to be named.

## Citation and licence

For the featured result, an edition-specific reference is:

> Will Cook, *Irrationality criteria for Lambert subseries*, 30 September
> 2026, Theorem 1.2 (`res:weighted-support`), Plectis commit
> `f9ad7e269da32d27ab71ddb3ae576a2844ac7b57`.

The [pinned source](https://github.com/wcook04/plectis-erdos/blob/f9ad7e269da32d27ab71ddb3ae576a2844ac7b57/paper/257/erdos-257-mersenne-support-subseries.tex)
identifies that edition. Cite the revision you actually used: [CITATION.cff](CITATION.cff)
for the repository, the relevant [paper](paper/README.md) for mathematics,
and its original sources. [Prior art](docs/PRIOR_ART.md) and
[source attributions](docs/research-commons/SOURCE_ATTRIBUTIONS.md) distinguish
earlier results and their formalisation here. Tagged releases carry their own citation file.

Code, scripts and documentation are Apache-2.0; manuscripts and PDFs are
CC-BY-4.0. [REUSE.toml](REUSE.toml) records exceptions. See
[scope](docs/SCOPE.md), [privacy](docs/PRIVACY.md) and the
[code of conduct](.github/CODE_OF_CONDUCT.md).
