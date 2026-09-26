<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# What proof length and reuse measure in this Lean corpus

On this public corpus, the paper-inspired interestingness ratio correlates
with a direct-use utility proxy at Spearman \(\rho=0.799\) across 9,289
eligible theorems. That number does not demonstrate that the ratio predicts
reuse: all 64 fixed-seed permutations of direct-user counts, each retaining
the same proof costs, produced a **higher** correlation (mean \(0.833\)).
The ratio's correlation with the direct-user count alone is \(-0.172\).
This is a negative control for the *local source-graph proxy*, not a
refutation of Patel et al.'s model, Mathlib measurement, or prospective
discovery results.

The dependency graph explains a second reason for caution. Generated
certificates are 3,008 of its 16,111 source-resolved declarations, yet
receive 19,989 of 69,276 direct proof-value references. Its nine most cited
declarations are generated certificate machinery. These counts are from
public commit `827cba0b`; the index resolves 16,111 of 163,604 atlas
declarations, with 8,865 unresolved public edges and 38,261 omitted internal
references. A raw reuse ranking promotes repeated certificate
infrastructure. It is not, by itself, a ranking of mathematical discoveries
or candidates to add to Mathlib.

This experiment tests a different, narrower question suggested by Patel,
Rammal, Hayat, Munos and Kempe, [*Learning to Discover Interesting Mathematics*
(arXiv:2609.28603)](https://arxiv.org/html/2609.28603): can a proof-cost to
description-length ratio help identify useful mathematical statements **after**
the corpus's proof machinery, duplicate statements and source-coverage limits
are accounted for? Its [source-bound profile](profile.json) records the
observations and controls on the pinned public checkout. It is an audit of
this corpus, not a replication of their trained conjecturer or an assessment
of human mathematical value.

## The definitions and the decisive control

The cited paper defines conditional description length as the characters in
the statement plus characters in all required definitions not supplied by the
premises, and conditional interestingness as

\[
L(T\mid P)=S(T)+\sum_{d\in C(T)\setminus C(P)}S(d),\qquad
I(T\mid P)=100\,V(T\mid P)/L(T\mid P).
\]

Its operational absolute-use proxy is
\(U_0(T)=|D(T)|V(T\mid\varnothing)\), where \(D(T)\) is the set of direct
users. The paper reports Spearman \(\rho=0.756\) between \(I_0\) and \(U_0\)
among Mathlib theorems with at least one user. These two quantities share the
same proof-cost factor \(V\). A high correlation can consequently arise even
when interestingness has no independent relation to reuse. The profile checks
that algebraic coupling by permuting direct-user counts against fixed proof
costs and lengths, and compares the ratio with simpler proof-cost and reuse
baselines. Here \(\rho(I,V_{\mathrm{obs}})=0.896\), so proof cost has a much
stronger rank relation to the ratio than direct reuse does. The measured
correlation cohort excludes zero-user targets, as does the paper's Figure 3
cohort; the profile records the exact selection rule.

Removing every target with generated certificate ancestry changes the
ratio–utility correlation to \(0.856\) for 8,022 targets. This is a
*different cohort* that still shares the proof-cost factor; the increase
does not establish better prediction. Removing wrappers with at most three
local proof lines gives \(0.770\) on 7,745 targets. These ablations show that
the score is sensitive to what counts as a theorem, proof work and reusable
infrastructure. Restricting to targets whose *entire resolved value ancestry*
has no omitted internal references leaves 2,417 targets and gives \(0.660\).
That smaller, selected cohort cannot be compared as a causal intervention,
but it makes the graph-coverage dependence visible. None of these cuts
identifies an optimal allocation policy.

For Plectis, the available numerator is an **indexed proof-source subtotal**:
sum the proof-code lines of each distinct source-resolved declaration in a
declaration's value-reference ancestry, counting shared ancestors once. It is
not the ideal shortest proof cost \(V\). The denominator follows available
type-reference paths to definitions and uses the atlas's signature strings;
those strings are truncated at 800 characters, and the dependency index does
not resolve every declaration. Thus the result is a Patel-inspired,
source-resolved proxy rather than the paper's exact \(I_0\). In particular,
its numeric score cannot be compared directly with a Mathlib score. The
profile finds 9,931 private atlas declarations in loaded modules, with
122,893 local proof-code lines outside the public source-joined graph.
Those lines are not silently assigned to adjacent public declarations, so
the measured expansion can omit real proof work. It is not a bound on the
length of an ideal shortest proof.

The graph's edge bits matter: bit 1 denotes a reference in a type, bit 2 a
reference in a proof value. The utility proxy counts bit-2 direct users, not
all edges. The profile reports certificate-inclusive and certificate-excluded
views, plus its eligible cohort and unresolved-source counts. A candidate
rank is meaningful only inside its stated cohort and graph cut.

## A theorem transfer is a conditional-cost question

The #251 to #269 synthesis has a concrete premise exchange. The proof in
[DyadicShiftEscape.lean](../../../lean/ErdosProblems/Synthesis/DyadicShiftEscape.lean)
uses #251's irrational-tail criterion and #269's bounded-radix escape after
proving that tail shifts obey the required recurrence. The interesting
measurement is the change in the **recorded proof graph** when those premises
are available. The profile identifies the exact declaration handles and
keeps a premise that remains required through another route in the expanded
closure. In the restricted graph, the first transfer has an indexed subtotal
of 337 code lines without either selected premise and 29 when both are
treated as available; its sharpened \(1/3\) version has 337 and 34. These
are neither complete proof costs nor actual lines saved by rewriting either
proof. The local bridge proofs themselves have 16 and 21 code lines
respectively, so the conditional subtotals also include other reachable
declarations.

Patel et al. prove a composition **inequality** for ideal proof cost,
\(V(T\mid P)\leq V(L\mid P)+V(T\mid P\cup\{L\})\). Their Bellman equality is
expected when \(L\) is a required intermediate in a shortest proof. A
decomposition of our written Lean proof does not establish that equality,
minimality, or the cost of an alternate proof. It does show which dependency
and premise are actually present in this checked transfer, a stronger basis
for choosing the next experiment than a corpus-wide score alone.

## How to reproduce and use the result

From the checkout root:

```sh
python3 research/experiments/interestingness/run.py
python3 research/experiments/interestingness/test_profile.py
```

The runner reads the tracked declaration atlas and Lean dependency index and
writes `profile.json`. It does not modify Lean source. The tests exercise
comment/private-helper parsing, duplicate paths in a dependency graph,
conditional graph cuts, cycles and rank ties. The profile's input fingerprints
identify the exact atlas and graph used; rebuild their owner projections if
the Lean corpus changes before interpreting the profile as current.

Use this profile as a **review queue**: remove generated certificate nodes,
inspect high-ranked statement families for duplicates and thin wrappers,
check a proposed public lemma against the pinned Mathlib revision, then read
the actual mathematical statement and proof. The paper's Mathlib-containment
rubric explicitly separates library containment from novelty, beauty,
importance and validity. A high score or many references is a reason to
inspect a declaration, never an upstreamability verdict. The distinct
conditional-cost case is the verified #251 to #269 transfer; testing whether
a proposed intermediate lemma reduces *future* proof work would require
another proof or a prospective intervention, not only this static graph.

## Choose premises for an actual workload

`conditional_reuse.py` asks a narrower question: which existing proofs could
be treated as available premises when inspecting a frozen set of eight
paper-linked declarations? It recomputes each marginal cut in the source
graph. Across the selected #251 and #269 proofs, counting a shared
prerequisite once gives 3,529 indexed lines; inspecting every target
independently gives 6,135. These are different workloads, not measured human
review times.

Within the same screened candidate pool, the leader by direct uses times
subtotal removes only 30 indexed lines from the shared workload. The largest
initial contextual cut removes 491. Source inspection shows that this winner
is an equivalence wrapper, so the report redirects explanation work toward
the actual staircase-minor, ambient-filling and support-cardinality proofs.
The metric proposes an inspection; reading the mathematics decides its value.

Premises can also be complementary. The #269 pair
`cofinalLocalWindowEscape_of_irrational` and
`value_ne_rat_of_cofinalLocalWindowEscape` remove 220 and 216 lines separately,
but 467 together. A shared dependency disappears only when both paths to it
are cut. Thus gains need not diminish, and greedy selection has no general
optimality guarantee. The report tests all 435 pairs among the 30 largest
initial cuts and finds 18 with positive complementarity.

A separate breadth check selects one explicit paper assertion per problem.
Six are present in the resolved graph; the selected #243 and #1049 declarations
are unavailable and remain named as missing. Those six indexed cones are
disjoint. Existing graph reuse therefore cannot supply the missing semantic
bridge between them; one must inspect their statements and representations.
All source hashes, selection reasons, coverage exclusions and proposed review
actions are in [conditional_reuse.json](conditional_reuse.json).

```sh
python3 research/experiments/interestingness/conditional_reuse.py
python3 research/experiments/interestingness/conditional_reuse.py --check
python3 research/experiments/interestingness/test_conditional_reuse.py
```

## A representation change that strengthens a theorem

Reading the #257/#1049 synthesis suggested grouping a repeated block of
divisibility ratios before applying the existing Mahler argument. The synthesis
theorem now proves transcendence of the Lambert subsum on every chain with
eventually periodic integer ratios, at every algebraic real base greater than
one. It previously stated only eventual doubling at rational bases. This is
an ordinary corollary of Nishioka's value theorem, with its proof in
`paper/synthesis/optimal-sparse-perturbations.tex`, Theorem `thm:chains`;
it is neither a new Lean result nor a historical novelty claim.

For alternating ratios 2,3, group the exponents as `6^k` and `2*6^k`.
The generating function satisfies
`G(z) - G(z^6) = z/(1-z) + z^2/(1-z^2)`.
The old doubling equation fails already at degree 4. The coefficient probe
checks five repeated blocks through degree 100,000, building coefficients
from support divisibility independently of the proposed functional equation.
It also rejects this particular base-6 equation for the explicit Thue–Morse
ratio word at degree 12. That rejection says nothing about other equations.
The infinite block decomposition and Mahler regularity check in the paper
prove transcendence; finite agreement does not.

```sh
python3 research/experiments/interestingness/periodic_chain_probe.py
```

This case motivates searching for a useful representation when the existing
dependency graph supplies no bridge. It does not show that the numeric
ranking discovered the theorem or that this workflow outperforms another one.
