<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# The argument graph

A theorem with a hypothesis that nothing proves is an unfinished argument: it
establishes its conclusion as soon as the hypothesis is supplied. The Lean tree
of this repository holds thousands of such theorems, written over months for
eight problems. The argument graph reads every one of them out of the
elaborated Lean environment and connects them, so that for any statement in
the corpus a reader or an agent can ask what already proves it, what refutes
it, what it reduces to, whether it is one of the open problems stated in other
coordinates, what its proof would settle, and what would fail without it.

A statement is identified by its elaborated Lean term, with the names and
annotations of bound variables and any metadata normalised away. Edges come
from corpus theorems matched by Lean's unifier and from proofs the kernel
checked. Declaration names join a theorem to the paper results and the
Comparator entry that cite it, and attribute a theorem to a problem when
nothing better does (see [Attribution](#attribution)).

## How it is computed

**Export.** `scripts/export_argument_continuations.lean` runs in an
environment that imports the two default roots (`Erdos249257` and
`ErdosProblems`) together with every target of the coverage build, whose list
belongs to the [coverage workflow](../.github/workflows/lean-coverage-build.yml)
and is printed by `scripts/coverage_build_targets.py`: many of the declarations
the paper-to-Lean ledger cites live in modules only the coverage build
compiles. When those targets cannot be built or imported together, the job
exports the default roots alone, and the stream's `meta` row lists the modules
the export imported. Theorems the elaborator generates (injectivity and
`sizeOf` lemmas, equation lemmas and internal details) are left out. The
export makes five passes.

1. **Telescopes.** For every theorem it records the hypothesis telescope. Each
   binder is classified as data, an instance or a proposition, and each
   proposition, instance binders such as `[Fact P]` included, as *closed* (it
   mentions no earlier binder, so it is a standalone statement) or schematic.
   For each data or instance binder the export records whether its type is
   known to be inhabited (the instance, or `Nonempty T`, synthesises). When it
   is not and the type is closed, the statement `Nonempty T` becomes one of the
   theorem's obligations: the theorem applies only once an element of `T` is
   supplied.
2. **Producer and refutation search**, in parallel waves. For every closed
   statement it searches the corpus for theorems whose conclusion unifies with
   it. It introduces the statement's own binders first, reads a proved
   equivalence in either direction, a conjunction through either component and
   a disequation `a ≠ b` as `¬ a = b`, and discharges a producer's premises
   from the statement's own hypotheses where they match. A producer's type is
   opened without unfolding its conclusion, so a conclusion such as `¬ P`,
   `a ≠ b` or a named ∀-proposition is matched as written. What the producer
   still needs is closed over the binders it uses and searched in turn. When
   unification leaves one of the producer's data arguments undetermined, the
   match counts only if that argument's type is known to be inhabited; any
   other such match is recorded as existential and supplies nothing. A named
   proposition such as `def G : Prop := …` is merged with the term it names.
   For every statement that is ever an antecedent (a hypothesis, a residual or
   a `Nonempty` obligation) it also searches for theorems proving the negation.
   Unification is the elaborator's `Meta.isDefEq` at default transparency, with
   a heartbeat budget for each attempt; an exhausted budget is recorded with
   its own status and kept apart from a missing producer.
3. **Compositions.** For every theorem whose closed hypotheses all have a
   producer with nothing left over, it builds the composed proof term and
   submits it to the kernel as a new declaration.
4. **Idle hypotheses.** For every theorem it finds the proposition binders
   (instance binders excepted) its proof never uses: the binder occurs neither
   in the proof term, nor in a later binder type, nor in the conclusion.
   Dropping them leaves a stronger statement with the same proof, and the
   kernel checks that statement (`idle` rows). The pass has a time budget, and
   the export's summary says when it ran out.
5. **Tactic battery.** For every closed statement for which the search found
   no usable producer, it tries a fixed battery of standard closing tactics
   (`decide`, `omega`, `norm_num`, `simp_all`, `positivity`, `linarith`) after
   introducing binders and unfolding the corpus definitions the statement
   mentions, and then the same battery on its negation. A proof counts only if
   the kernel accepts it.

The export runs in continuous integration
([workflow](../.github/workflows/argument-continuations.yml)) because it needs
the corpus built. Its stream is uploaded as an artifact together with
`argument_continuations_lean_tree.txt`, the git tree of `lean/` at the exported
commit, and `argument_continuations_source_revision.txt`, the commit itself.

**Graph.** `scripts/build_argument_continuations.py --export <artifact>`
computes the following from that stream. It reads the tree id from beside the
export (or from `--lean-tree`), and `query_continuations.py summary` reports the
graph stale when `git rev-parse HEAD:lean` differs from it; uncommitted edits
under `lean/` are not compared.

| Notion | Definition |
|---|---|
| Reduction | A theorem that supplies a statement once its remaining obligations are supplied |
| Idle reduction | A kernel-checked idle row: the conclusion from the obligations of the binders the proof uses |
| Supplied | Some reduction has every remaining obligation supplied (least fixpoint); the first such one is the witness |
| Refuted | Kernel: a theorem or battery proof of the negation, residuals supplied. Derived: supplying it supplies a refuted one |
| Open | Neither supplied nor refuted |
| Vacuous theorem | A conditional theorem with a refuted closed obligation: it can never be applied |
| Implication | A reduction left with exactly one open obligation |
| Disguise class | Open statements that imply each other (a strongly connected component of implications) |
| Bundle | A set of open statements whose supply supplies a given statement, with no smaller bundle found inside it |
| Leverage | The open statements that become supplied when a given statement is supplied |
| Criticality | The supplied statements that lose every witness chain when a given statement or theorem is withdrawn |
| Composition | A statement supplied only through a conditional theorem whose obligations other reductions supply |

A theorem with a closed conclusion reduces it to its closed proposition
binders, instance binders included, and to `Nonempty T` for each data binder
whose closed type is not known to be inhabited. A theorem with a schematic
obligation gives no reduction of its conclusion and is listed as existential.
The witnesses of a supplied statement form a witness chain of corpus theorems
joined by unification. A derived refutation is recorded with the refuted
statement it reaches and the theorems on the way. A disguise class holds
statements equivalent through recorded reductions: one statement in different
coordinates. A bundle never routes through a refuted statement; when a depth,
size or work limit prunes the enumeration the result says so
(`bundles_truncated`), and otherwise it lists every minimal bundle of at most
four statements. A composition is a witness chain, counted by
`\AGCompositions`; the compositions the exporter built and the kernel accepted
are counted by `\AGKernelCompositions`.

An idle reduction needs a closed conclusion; a kernel-checked idle row whose
conclusion mentions a binder gives none and is still listed. The projection
lists every kernel-checked idle row (`\AGIdle`), paper-cited theorems first,
and marks those that drop a statement the graph leaves open when idle
reductions are left out: a theorem stated conditionally on an open statement
whose proof never uses it (`\AGIdleOpen`).

The [barrier registry](semantic/barriers.json) lists the corpus's barrier
theorems: countermodels, endpoint equivalences, method ceilings, finite
blindness results and scoped failures, each checked against its source by
`scripts/check_barrier_registry.py`. The builder attaches each barrier to the
open statements that mention its route predicates. What a barrier rules out is
an authored reading of a kernel-checked declaration, and a formalised class of
arguments can be narrower than the methods a specialist would try. To test
whether a countermodel blocks a route you have in mind, state the route as a
Lean proposition (every property of the object the route would use, implying
the conclusion it needs) and prove its negation from the countermodel in a
kernel probe; a proof settles the question, and a failed attempt says only that
this countermodel does not obviously apply.

Each theorem is joined to the paper results that cite it, short or long, with
the label, the TeX line and the Comparator status recorded in the
[paper-to-Lean ledger](paper_lean_coverage.json). The builder also checks two
authored layers against the graph. Every semantic node labelled as a
conditional implication should still depend on a statement the graph does not
supply: an open or refuted closed hypothesis, or a schematic one, which counts
as a condition because the graph cannot tell a side condition on a variable
from an open assumption. The audit reports a node whose theorems depend only
on supplied statements, and a node whose open hypotheses the proofs never use
(by the idle rows). Every authored open antecedent in the
[semantic frontier](semantic/frontier.json) should still be open; this check
reads the graph statements that mention the antecedent's Lean constants, a set
that can be wider than the antecedent itself.

### Attribution

A theorem belongs to the problem of the paper rows that cite it; failing
those, to the problem the semantic corpus's authored evidence gives it; then to
the problem its module path names (`ErdosProblems.ErdosNNN`); and last to a
problem read from tokens in its module and declaration name (for example
`Totient` for #249, and `Mersenne`, `Half` or `Greedy` for #257). A
shared-library declaration with no token, or with tokens of both problems, goes
to `249_257`. A statement belongs to
the problems of the theorems that state it as a hypothesis or a conclusion.
The per-problem views also count the problems of the theorems that reduce it,
and `transfer` compares a producer's problem with the statement's own
attribution. Attribution is navigation and never changes an edge.

## Asking it questions

```sh
python3 scripts/query_continuations.py summary
python3 scripts/query_continuations.py problem 257
python3 scripts/query_continuations.py packet --problem 269
python3 scripts/query_continuations.py next --problem 249
python3 scripts/query_continuations.py find "mersenneAchievementSet"
python3 scripts/query_continuations.py statement <key>
python3 scripts/query_continuations.py theorem <declaration>
python3 scripts/query_continuations.py why <key>
python3 scripts/query_continuations.py about <corpus constant>
python3 scripts/query_continuations.py near "<objects of a proposed statement>"
python3 scripts/query_continuations.py barriers --problem 249
python3 scripts/query_continuations.py idle --problem 257
python3 scripts/query_continuations.py criticality <key or declaration>
python3 scripts/query_continuations.py transfer
python3 scripts/query_continuations.py diff <old graph> <new graph>
```

`packet` writes a bounded research packet for one problem. It lists the open
targets with the theorems that reduce to them and the paper results that
assume them, the disguise classes, the members of bundles with two or more
open statements, the problem's refuted statements, the hypotheses its theorems
assume without using, and the open statements with the largest leverage. The
graph records no reduction by which a member of a larger bundle supplies the
target alone, and it records nothing about whether the target implies that
member. A declaration name given to `theorem` or `criticality` may be a
suffix of the full name when exactly one theorem ends with it.

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

The kernel checked every corpus theorem the graph cites, every battery proof,
and every composition and idle row marked `kernel_checked`. A witness chain
joins kernel-checked theorems through the elaborator's unifier; the kernel
checked a whole chain as one term only where a composition row says so. A
derived refutation follows recorded reductions backwards from a kernel
refutation in the same way. The rest of the graph is navigation.

A unification step that is wrong can make the graph report anything, so the
builder watches for the plainest symptom. If `False`, or one of the registered
open targets in `SENTINELS` (1/2 and 1/21 in the Mersenne achievement set, the
irrationality of the #249 series), comes out supplied, or an open target comes
out refuted, the build writes its outputs, lists each such statement with its
witness chain under `sentinel_alarms`, exits with status 3 and writes no paper
macros. The stream exported before the adversarial review tripped all four:
producers that need a witness nobody has constructed had been counted as
unconditional. An alarm is either a defect or a solution, and in both cases a
person reads the witness chain before the graph is used.

The producer search is a lower bound. It tries only corpus theorems as
producers, prefilters them by the constants in their conclusions, and unfolds
only named propositions without arguments. A statement reported open may
therefore follow from an argument the search did not try, including a single
Mathlib lemma, and the refutations are a lower bound in the same way. Leverage
counts consequences inside this corpus. Importance, difficulty and interest
remain judgements for a mathematician. A disguise class records equivalences
through recorded reductions; a statement outside every class may still be
equivalent to a target by an argument the corpus does not contain. The novelty
of a composed statement is unassessed. Lean remains the proof authority, and
the [claim record](claims.json) remains the authority on what the project
claims.
