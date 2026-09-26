<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# The argument graph

A theorem with a hypothesis that nothing proves is an unfinished argument: it
establishes its conclusion as soon as the hypothesis is supplied. The Lean tree
of this repository holds thousands of such theorems, written over months for
eight problems. The argument graph reads every one of them out of the
elaborated Lean environment and connects them, so that for any statement in
the corpus a reader or an agent can ask what already proves it, what it
reduces to, whether it is one of the open problems stated in other
coordinates, what its proof would settle, and what would fail without it.

The graph is computed from the kernel's own terms. It uses declaration names
only to link a theorem to the paper result and the Comparator entry that cite
it.

## How it is computed

**Export.** `scripts/export_argument_continuations.lean` loads both corpus
libraries and makes four passes.

1. For every theorem it records the hypothesis telescope. Each binder is
   classified as data, an instance or a proposition, and each proposition as
   *closed* (it mentions no earlier binder, so it is a standalone statement)
   or schematic.
2. For every closed statement it searches the corpus for theorems whose
   conclusion unifies with it. It introduces the statement's own binders first,
   reads a proved equivalence in either direction and a conjunction through
   either component, and discharges a producer's premises from the statement's
   own hypotheses where they match. What the producer still needs is closed
   over the binders it uses and searched in turn. A named proposition such as
   `def G : Prop := …` is merged with the term it names. For every hypothesis
   it also searches for theorems proving the negation. Unification is the
   kernel's `isDefEq` under a heartbeat budget for each attempt; an exhausted
   budget is recorded as such, never as a missing producer.
3. For every theorem whose closed hypotheses all have a producer with nothing
   left over, it builds the composed proof term and submits it to the kernel as
   a new declaration.
4. For every closed statement for which the search found no producer at all,
   it tries a fixed battery of standard closing tactics (`decide`, `omega`,
   `norm_num`, `simp_all`, `positivity`, `linarith`) after introducing binders
   and unfolding the corpus definitions the statement mentions, and then the
   same battery on its negation. A proof counts only if the kernel accepts it.

The export runs in continuous integration
([workflow](../.github/workflows/argument-continuations.yml)) because it needs
the whole corpus built, and its stream is uploaded as an artifact.

**Graph.** `scripts/build_argument_continuations.py --export <artifact>`
computes the following from that stream.

| Notion | Definition |
|---|---|
| Reduction | A theorem that supplies a statement once its remaining hypotheses are supplied |
| Supplied | Some reduction has every remaining hypothesis supplied (least fixpoint); the first such reduction is kept, so every supplied statement has a kernel witness chain |
| Refuted | A theorem proving the negation has every remaining hypothesis supplied, or the battery proves the negation |
| Vacuous theorem | A conditional theorem with a refuted closed hypothesis: it can never be applied |
| Implication | A reduction left with exactly one open hypothesis |
| Disguise class | Open statements that imply each other (a strongly connected component of implications): the same statement in different coordinates |
| Bundle | A minimal set of open statements whose supply supplies a given statement |
| Leverage | The open statements that become supplied when a given statement is supplied |
| Criticality | The supplied statements that lose every witness chain when a given statement or theorem is withdrawn |
| Composition | A statement supplied only by chaining a conditional theorem with hypotheses that other theorems prove |

The [barrier registry](semantic/barriers.json) lists the corpus's barrier
theorems: countermodels, endpoint equivalences, method ceilings, finite
blindness results and scoped failures, each checked against its source by
`scripts/check_barrier_registry.py`. The builder attaches each barrier to the
open statements that mention its route predicates. What a barrier rules out is
an authored reading of a kernel-checked declaration, and a formalised class of
arguments can be narrower than the methods a specialist would try.

Each theorem is joined to the paper results that cite it, short or long, with
the label, the TeX line and the Comparator status recorded in the
[paper-to-Lean ledger](paper_lean_coverage.json). The builder also checks two
authored layers against the graph. Every semantic node labelled as a
conditional implication should still depend on an open statement, and every
authored open antecedent in the [semantic frontier](semantic/frontier.json)
should still be open.

## Asking it questions

```sh
python3 scripts/query_continuations.py summary
python3 scripts/query_continuations.py problem 257
python3 scripts/query_continuations.py packet --problem 269
python3 scripts/query_continuations.py find "mersenneAchievementSet"
python3 scripts/query_continuations.py statement <key>
python3 scripts/query_continuations.py theorem <declaration>
python3 scripts/query_continuations.py why <key>
python3 scripts/query_continuations.py about <corpus constant>
python3 scripts/query_continuations.py near "<objects of a proposed statement>"
python3 scripts/query_continuations.py barriers --problem 249
python3 scripts/query_continuations.py criticality <key or declaration>
python3 scripts/query_continuations.py transfer
python3 scripts/query_continuations.py diff <old graph> <new graph>
```

`packet` writes a bounded research packet for one problem. It lists the open
targets with the theorems that reduce to them and the paper results that
assume them, the disguise classes, the members of bundles with two or more
open statements (each strictly weaker than the target it serves unless the
kernel also proves the converse), and the open statements with the largest
leverage.

## Checking a new statement without a local build

A corpus build needs several gigabytes. A research session without one can
push scratch files under `research/probes/` to a `claude/kernel-probe-*` or
`codex/kernel-probe-*` branch; the [kernel probe
workflow](../.github/workflows/kernel-probe.yml) builds the corpus roots from
the main-branch cache, runs each probe with `lake env lean` and uploads a
verdict per file (`scripts/run_kernel_probes.py`). A probe is accepted when
Lean exits cleanly with no error and no `sorry`; a result that matters moves
into `lean/` through the ordinary landing path.

## What it establishes and what it does not

A supplied statement cites the kernel theorems that supply it, and a
composition or battery proof has been accepted by the kernel. Those rows are
proofs; the rest of the graph is navigation.

The producer search is a lower bound. It tries only corpus theorems as
producers, prefilters them by the constants in their conclusions, and unfolds
only named propositions without arguments. A statement reported open may
therefore follow from an argument the search did not try, including a single
Mathlib lemma. Leverage counts consequences inside this corpus. Importance,
difficulty and interest remain judgements for a mathematician. A disguise class records proved equivalences; a statement
outside every class may still be equivalent to a target by an argument the
corpus does not contain. The novelty of a composed statement is unassessed.
Lean remains the proof authority, and the [claim record](claims.json) remains
the authority on what the project claims.
