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
export makes six passes.

1. **Telescopes.** For every theorem it records the hypothesis telescope. Each
   binder is classified as data, an instance or a proposition, and each
   proposition, instance binders such as `[Fact P]` included, as *closed* (it
   mentions no earlier binder, so it is a standalone statement) or schematic.
   For each data or instance binder the export records whether its type is
   known to be inhabited (the instance, or `Nonempty T`, synthesises). When it
   is not and the type is closed, the statement `Nonempty T` becomes one of the
   theorem's obligations: the theorem applies only once an element of `T` is
   supplied.
2. **Used consequences.** For every closed hypothesis `h : H` of every
   theorem, the most-consumed hypotheses first and within a time budget, it
   asks what the proof derives from `h`. A *use site* is the largest
   application around an occurrence of `h` that mentions no variable bound
   inside the proof and no other binder of the theorem (`L h` for a lemma `L`,
   `h.2`, `h 3`), provided its type is a proposition that does not mention
   `H`, is not `H` up to unfolding and is not the theorem's own conclusion.
   When every occurrence of `h` lies in a use site, the theorem with `h`
   replaced by the propositions those sites prove, the *consequences* of `H`
   that the proof uses, is added to the environment and the kernel checks it
   on the way in; the kernel also checks `H → C` for each consequence `C`
   (`weakening` rows). The weakened theorem is a producer in the search like
   any corpus theorem. Each consequence is a statement: it is searched and
   refutation-searched, and it goes to the tactic battery and library search
   whatever producers the search found for it (the lemma at its use site
   always gives it one, from `H`). The consequences go first, with half the
   pass's budget as time of their own in each of the two, so the other leaves
   keep their whole allowance.
3. **Producer and refutation search**, in parallel waves. For every closed
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
4. **Compositions.** For every theorem (weakened ones included) whose closed hypotheses all have a
   producer with nothing left over, it builds the composed proof term and
   submits it to the kernel as a new declaration.
5. **Idle hypotheses.** For every theorem it finds the proposition binders
   (instance binders excepted) its proof never uses: the binder occurs neither
   in the proof term, nor in a later binder type, nor in the conclusion.
   Dropping them leaves a stronger statement with the same proof, and the
   kernel checks that statement (`idle` rows). The pass has a time budget, and
   the export's summary says when it ran out.
6. **Tactic battery.** A ground tier comes first: every discovered statement,
   searched or not, that is small (at most 400 term nodes) and ground (no λ, no
   `let`, every `∀` an implication between propositions) goes to `decide`,
   `norm_num` and `simp`, and so does its negation; a statement `Nonempty T`
   goes to an instance, `default` and a bounded search for a constructor
   application, and a failure never refutes it. Then, for every searched
   statement without a producer that needs nothing
   further (a producer with residuals does not exempt it), the most-consumed
   first, it tries a fixed battery of standard closing tactics (`decide`,
   `omega`, `norm_num`, `simp_all`, `positivity`, `linarith`) after
   introducing binders and unfolding the corpus definitions the statement
   mentions, and then the same battery on its negation. A proof counts only if
   the kernel accepts it.

Four further passes are off unless their variable is set (the exporter's
header lists them with their budgets). *Scope-aware used consequences*
(`PLECTIS_CONTINUATION_USED_V2=1`) extend pass 2 to use sites whose lemma is
applied under binders of the proof or to other hypotheses, abstracting them
into the consequence. *Literal generalisation*
(`PLECTIS_CONTINUATION_GENERALISE_SECONDS`) turns an ℕ, ℤ, ℚ or ℝ literal of a
theorem into a variable, assumes as obligations the closed facts its proof
used about that literal, discharges what the battery can, and keeps the
generalised theorem only when the kernel accepts it and a second value of the
variable satisfies the obligations; a literal the statement pins down, a
proof too large to traverse and a vacuous result are refused and recorded
with the reason. *Bounded counterexamples*
(`PLECTIS_CONTINUATION_NAT_REFUTE_SECONDS`) test statements that open with a
universal over ℕ on an initial segment; a refutation is the kernel-checked
negation of the statement. *Library producers*
(`PLECTIS_CONTINUATION_LIBRARY_PRODUCERS=1`) make every theorem of the
environment a producer.

The export runs in continuous integration
([workflow](../.github/workflows/argument-continuations.yml)) because it needs
the corpus built: on a push to `main` or to a `claude/argument-*` or
`codex/argument-*` branch that changes the exporter, or by hand
(`workflow_dispatch`) on any branch. Its stream is uploaded as an artifact together with
`argument_continuations_lean_tree.txt`, the git tree of `lean/` at the exported
commit, and `argument_continuations_source_revision.txt`, the commit itself.

**Graph.** `scripts/build_argument_continuations.py --export <artifact>`
computes the following from that stream. It reads the tree id from beside the
export (or from `--lean-tree`), and `query_continuations.py summary` reports the
graph stale when `git rev-parse HEAD:lean` differs from it; uncommitted edits
under `lean/` are not compared. Exports of the same Lean tree combine:
repeating `--export` (the latest last) builds the graph from the union of
their rows, since each row observes the same environment, and the graph's
`source` lists every export combined. A count in the combined summary is the
largest any export recorded, so a count of work done (statements tried) is a
lower bound. Exports of different trees are refused.
A kernel-checked generalisation supplies its statement and is credited to the
theorem it generalises.

| Notion | Definition |
|---|---|
| Reduction | A theorem that supplies a statement once its remaining obligations are supplied |
| Idle reduction | A kernel-checked idle row: the conclusion from the obligations of the binders the proof uses |
| Weakening | A kernel-checked weakening row: the conclusion from the other obligations and the consequences the proof uses of one hypothesis |
| Use-site reduction | A consequence `C` from the hypothesis `H` it is derived from (the kernel checked `H → C`): supplying `H` supplies `C`, and refuting `C` refutes `H` |
| Checked composition | A kernel-checked composition row: a closed proof term of its conclusion, so a reduction with no obligation, used after every other reduction |
| Supplied | Some reduction has every remaining obligation supplied (least fixpoint); the first such one is the witness |
| Refuted | Kernel: a theorem or battery proof of the negation, residuals supplied. Derived: supplying it supplies a refuted one. Conflict: supplying it supplies a statement together with the residuals of a recorded refutation of that statement |
| Open | Neither supplied nor refuted |
| Vacuous theorem | A conditional theorem with a refuted closed obligation: it can never be applied |
| Implication | A reduction left with exactly one open obligation |
| Disguise class | Open statements that imply each other (a strongly connected component of implications) |
| Bundle | A set of open statements whose supply supplies a given statement, with no smaller bundle found inside it |
| Joint check | Whether statements assumed together supply a refuted statement or `False` (jointly impossible), and whether a target they supply implies each of them back (the target restated) |
| Leverage | The open statements that become supplied when a given statement is supplied |
| Criticality | The supplied statements that lose every witness chain when a given statement or theorem is withdrawn |
| Composition | A statement supplied only through a conditional theorem whose obligations other reductions supply |
| Interface chain | What a theorem needs of a weakened hypothesis, level by level through the lemmas at its use sites (see [Interface chains](#interface-chains)) |

A theorem with a closed conclusion reduces it to its closed proposition
binders, instance binders included, and to `Nonempty T` for each data binder
whose closed type is not known to be inhabited. A theorem with a schematic
obligation gives no reduction of its conclusion and is listed as existential.
The witnesses of a supplied statement form a witness chain of corpus theorems
joined by unification. A derived refutation is recorded with the refuted
statement it reaches and the theorems on the way. A refutation by conflict is
recorded with the statement it would supply twice over and the theorem that
refutes that statement: the propagation of refutations reaches only
refutations whose residuals the graph already supplies, and this check
follows each open statement forward to the refutations its own supply
completes. A disguise class holds statements equivalent through recorded
reductions: one statement in different coordinates. A bundle never routes
through a refuted statement; when a depth, size or work limit prunes the
enumeration the result says so (`bundles_truncated`), and otherwise it lists
every minimal bundle of at most four statements.

Each bundle is then checked as a whole (`scripts/argument_graph_frontier.py`).
From `A ⇒ ¬B` and `A ∧ B ⇒ G` neither `A` nor `B` is refuted, yet `{A, B}`
can never supply `G`: such a bundle is dropped and listed under
`bundle_checks` with both derivations and the assumptions they use. From
`A ∧ B ⇒ G`, `G ⇒ A` and `G ⇒ B` no single member is equivalent to `G`, yet
`{A, B}` is `G` restated: such a bundle stays, labelled
`joint_endpoint_equivalence`. A check is a derivation over recorded edges
(its `evidence_class`), and "no recorded conflict" does not say that the
members can hold together. Checks count propagation steps, not seconds, so the
projection does not depend on the machine; a check that runs out of steps
reads `unknown_budget` and keeps its bundle.

A composition is a witness chain, counted by `\AGCompositions`; the
compositions the exporter built and the kernel accepted are counted by
`\AGKernelCompositions`. A kernel-checked composition is itself a proof of its
conclusion, so it supplies that conclusion even where no reduction does: when
a theorem's conclusion mentions its hypothesis (an `orderOf` of a unit built
from a coprimality proof, say), the composed term fixes that proof and its
conclusion is a closed statement of its own. Such a composition stops counting
when a theorem or statement it composed is withdrawn, and
`statements_supplied_only_by_checked_compositions` counts what only
compositions supply.

An idle reduction needs a closed conclusion; a kernel-checked idle row whose
conclusion mentions a binder gives none and is still listed. The projection
lists every kernel-checked idle row (`\AGIdle`), paper-cited theorems first,
and marks those that drop a statement the graph leaves open when idle
reductions are left out: a theorem stated conditionally on an open statement
whose proof never uses it (`\AGIdleOpen`).

The projection lists every kernel-checked weakening, theorems whose hypothesis
is open first, with the status of the hypothesis and of each consequence and
the lemmas at the use sites (`\AGWeakened` theorems, `\AGWeakenedOpen` with an
open hypothesis). A consequence is a weaker target than the input it comes
from: when the graph supplies every consequence a theorem uses of an open
input, the theorem's conclusion holds without that input, and
`\AGWeakeningGain` counts the statements the graph supplies only that way. A
consequence the battery or a corpus theorem refutes refutes the input. A
kernel-checked weakening row that names no consequence, a consequence without
a statement key, or a binder that is not the hypothesis it names is refused
(`weakenings_refused`): accepting it would drop an obligation without
replacing it.

### Interface chains

A weakening says what one proof uses of one hypothesis. When the lemma at a
use site is itself weakened, the chain goes one level further down:
`scripts/argument_graph_interfaces.py` follows it. Level 0 is the hypothesis
`H`; level 1 is the consequences the proof uses; level `k + 1` replaces each
member of level `k` whose use-site lemma has a kernel-checked weakening that
the export matched against that member (a recorded reduction from the
weakened lemma) by what that lemma uses, and drops a member whose own
refinement lies inside the rest of the level (listed as implied). Each level
is a set of statements from which the theorem's conclusion follows, given its
other obligations, and each member at level 1 or below records whether the
kernel checked that `H` implies it. A lemma at a use site whose weakened
theorem the export did not match against the member is listed as `unmatched`
and never used. The levels depend only on these recorded refinements, so they
do not move when a member is proved; statuses (supplied, refuted, open) lie
over them. Each level also carries its joint check: its open members jointly
impossible (when `H` implies each of them, `H` is refuted too), or the level
implying `H` back (it restates the hypothesis rather than weakening it).

Every level is kept, not only the deepest. On the #249 module
`ExcludedCofactorEstimate`, `prop_badcof` uses its prime-number-theorem input
only through `eventually_card_excluded_le` and `eventually_excluded_budget`
(level 1); those only through `eventually_card_excluded_le_of_upper` and
`eventually_excluded_budget_of_upper` (level 2, where the second follows from
the first and is listed as implied); the first only through the dyadic prime
count `eventually_card_primes_dyadic_le` with
constant `1 + ε` (level 3); and that one only through the two-sided bounds of
`nthPrime_two_sided` (level 4). The budget at `η = 1/1000` was later proved
with no hypothesis by supplying level 3 with the constant `log 4` from
Chebyshev's bound: the useful cut was a middle level, and the deepest level is
close to the prime number theorem itself. The projection lists the chains per
problem (paper-cited theorems first) under `interfaces`, and for every
interface statement the paper results whose chains need it (`needed_by`).

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
attribution. `next` and `packet` do not let a producer claim a statement:
there a statement belongs to the problems of the theorems that state it,
else to the problems of the corpus objects it mentions (read from their names
as a theorem's are), and only else to its producers' problems. A statement
that belongs elsewhere and that a theorem of this problem merely reduces
appears only under their cross-problem heading. Attribution is navigation and
never changes an edge.

The theorems the argument graph itself contributes to Lean (modules under
`ErdosProblems.ArgumentGraph`, which the coverage build imports) are left out
of the graph with every row that uses one as theorem or producer, and counted
in `argument_graph_derived_theorems_skipped`: the graph never reads its own
findings back as corpus theorems.

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
python3 scripts/query_continuations.py weakenings --problem 249
python3 scripts/query_continuations.py needs prop:badcof
python3 scripts/query_continuations.py papers --problem 257
python3 scripts/query_continuations.py criticality <key or declaration>
python3 scripts/query_continuations.py check-bundle <key> <key> --target <key>
python3 scripts/query_continuations.py cut <target key> --costs costs.json
python3 scripts/query_continuations.py transfer
python3 scripts/query_continuations.py diff <old graph> <new graph>
```

`packet` writes a bounded research packet for one problem, starting from its
paper results. Section 1 lists the problem's named inputs: the hypotheses of
the theorems its papers cite that the graph leaves open, each with the paper
results that assume it, the reductions into it, its bundles checked as a
whole, and what the proofs use of it level by level (interface chains). Then
come the open targets among the problem's own statements, the disguise
classes, the members of bundles with two or more open statements (marked when
the target itself supplies the member, which is then necessary for the target
as well as part of a route to it), the barriers, the refuted statements, the
hypotheses its theorems assume without using, what its other theorems use of
their open inputs, the open statements with the largest leverage, and last
the cross-problem statements: those that other problems' theorems state, or
that no attributed theorem states and that mention only other problems'
objects (read from the objects' names as theorems are). A statement whose
rendering does arithmetic nobody writes, a numeral subtracted from a numeral
(`0 - 1`, the `1 - 1` of `n - 1 + 1 - 1`) or zero added, multiplied or
divided (`0 / (0 + 0)`), is marked as a likely instantiation artifact and
listed last. The graph records no reduction by which a member of a larger
bundle supplies the target alone.

`next` ranks candidates in the same order: the named inputs and the open
levels of their interface chains, then members of the inputs' bundles, then
members of bundles of the problem's own targets and statements that settle
others, with literal arithmetic last in each tier and then the most paper
results and the most leverage first; cross-problem statements are listed
apart. A deeper interface level implies the levels above it, so it ranks
higher, but it is also a stronger statement, closer to the hypothesis: each
row names its level, and which level is the useful cut stays a judgement. `needs` takes a theorem name or suffix, a paper label or a
ledger row, and prints each chain with, on every member, the paper results
whose chains need it. `check-bundle` runs the joint check on any statements;
`cut` finds the cheapest set, within a pool of at most 32 statements with
integer or rational-string costs (a JSON object of keys to costs), that
supplies a target without a recorded conflict, paying for a statement shared
by several routes once; its optimality holds only over that pool, those costs
and the recorded edges. A declaration name given to `theorem` or
`criticality` may be a suffix of the full name when exactly one theorem ends
with it.

`scripts/argument_graph_contracts.py` handles the arithmetic side of a
weakening. When a consumer uses a constant only through linear inequalities,
it eliminates the auxiliary variables exactly (Fourier-Motzkin in rational
arithmetic) and returns the region of constants the consumer tolerates, each
row with the nonnegative multipliers that replay it, and can write the rows
as Lean lemmas closed by `linarith` for a kernel probe. `--case249` runs the
#249 budget: `eventually_excluded_budget_of_upper_of_dyadic` needs `1 ≤ K`
and `K · 3/1000 < 1/100`, so any dyadic-count constant `K` in `[1, 10/3)`
suffices, and the Chebyshev proof's `log 4 ≤ 3` leaves a margin of `1/1000`.
Binding each row to the hypothesis it stands for is the caller's work.

## Checking a new statement without a local build

A corpus build needs several gigabytes. A research session without one can
push scratch files under `research/probes/` to a `claude/kernel-probe-*` or
`codex/kernel-probe-*` branch; the [kernel probe
workflow](../.github/workflows/kernel-probe.yml) builds the corpus roots from
the main-branch cache, runs each probe with `lake env lean` and uploads a
verdict per file (`scripts/run_kernel_probes.py`). A probe is accepted when
Lean exits cleanly with no error and no `sorry`, the file declares no axiom,
and no `#print axioms` line in its output names an axiom beyond `propext`,
`Classical.choice` and `Quot.sound`; print the axioms of every declaration
that matters, since an axiom reached through an import shows nowhere else.
The verdict carries the SHA-256 of the probe source, and it keeps what Lean
printed before a timeout. Acceptance is a compilation receipt: it does not
check that the probe states the intended target, and it replays nothing. A
result that matters moves into `lean/` through the ordinary landing path,
where the exact statement checks apply.

## What it establishes and what it does not

The kernel checked every corpus theorem the graph cites, every battery proof,
every composition, idle and weakening row marked `kernel_checked`, and the
implication behind every use-site reduction. A witness chain
joins kernel-checked theorems through the elaborator's unifier; the kernel
checked a whole chain as one term only where a composition row says so. A
derived refutation, a refutation by conflict, a joint check and an interface
level follow recorded reductions and refutations in the same way. The rest of
the graph is navigation.

A unification step that is wrong can make the graph report anything, so the
builder watches for the plainest symptoms. If any statement comes out both
supplied and refuted, if `False` comes out supplied, or if one of the
registered open targets in `SENTINELS` (1/2 and 1/21 in the Mersenne
achievement set, the irrationality of the #249 series) comes out supplied or
refuted, the build writes its outputs, lists each such statement with its
witness chain under `sentinel_alarms`, exits with status 3 and writes no paper
macros. The stream exported before the adversarial review tripped all four
sentinels: producers that need a witness nobody has constructed had been
counted as unconditional. A settled open target is either a defect or a
solution; after a person has checked it, `--allow-sentinel-alarms`
acknowledges it (the target then leaves `SENTINELS` in a reviewed change). A
contradiction is never acknowledged. The macros are also refused, whoever
calls for them, for an export restricted by declaration-name prefix, to other
roots, or to selected declarations: those are not the corpus. A truncated
export is the corpus read to a budget; its totals are lower bounds, and the
summary says so (`export_truncated`).

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
