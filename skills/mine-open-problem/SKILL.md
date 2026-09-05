---
name: mine-open-problem
description: Select and attack one bounded open mathematical route from this clone using reading, computation, analytic reasoning, Lean, and optional subagents, then return the smallest evidence-bearing delta without overclaiming it.
---

# Mine an open problem

This skill turns a cold clone into a bounded research run. It may produce a
proof, but a correction, counterexample, no-go, exact computation, literature
connection, or reproducible failed route is also a valid result.

## Browser-only or enclosed Type B research

When the assignment is to solve a named problem, the deliverable is a complete
proof of that original statement. A suggested route is a starting point, not a
restriction. Use established mathematics to advance the proof; do not spend the
run reproving an available result or converting the assignment into a corpus audit.
If no proof is obtained, state that honestly and preserve the strongest exact delta.

For a solution assignment, derive every extra condition in a proposed criterion
from the original hypotheses. Boundedness, density, regularity, uniformity as a
parameter grows, auxiliary rationality and denominator savings are obligations,
unless a supplied theorem proves them. Compare source-linked countermodels:
which exact property of the original object excludes each relaxed model?
Use that distinction to construct the missing implication or change approach.
A new conditional criterion does not prove its own assumptions. An advisory
statement without a located proof must not silently become an established premise.
Use the length the complete proof needs; neither a page quota nor an attack log
substitutes for the original conclusion.

Use the research packet's `frontier_integrity` when it is present. Its original
target and canonical frontier are distinct from its inventory of possible
producers. Only `equivalent_to_target` routes can replace the target;
`target_deciding_but_stronger` routes are sufficient constructions whose failure
does not refute the target. Auxiliary results still need a proved implication.
The generated full research frontier displays these same source classifications,
and new enclosed packets carry them in their ask and manifest. An exact producer
identifier establishes source identity, not logical equivalence. For a universal
assertion, a rigorously proved counterexample is a valid resolution; verify every
original hypothesis, including any requirement that a support be infinite.
If an older snapshot has no classification, inspect the original statement and
the exact consumer implication rather than inferring equivalence from a title.
An opening may attack the original problem directly without selecting a named
producer. The existing producers do not exhaust the possible mathematics. Treat
the corpus as usable proof material and constraints on already falsified claims,
not a list of permitted approaches. Change routes when the mathematics warrants
it; preserve the original hypotheses and conclusion through that change.

No installation, terminal, or private repository is needed to read the corpus:

1. Open the [mathematical graph](../../docs/semantic/BROWSER.md), choose the
   problem, and follow its **full research frontier** link. This contains the
   exact established results, failed routes, open obligations, and source links.
2. Open the relevant named results and their proof sources. Read the hypotheses
   and evidence class: an ordinary proof, a Lean theorem, and a finite computation
   support different claims. Follow incoming and outgoing graph links when another
   result can help; the initial packet selection is not the boundary of the corpus.
3. Match the proposed lemma against the existing statements and known failures.
   Reuse a matching theorem, adapt a theorem with different hypotheses explicitly,
   or attack the genuinely missing implication. A title or empty search is not
   evidence that a result is absent. Use the full frontier when the compact graph
   does not surface a match.
4. Return to the original target and construct the missing proof. If the opening
   route fails, use its exact obstruction to select a different route. Do not
   silently weaken the theorem to fit an available helper result.

Read dependency-directed: locate the complete statements, proofs and dependencies used by the current argument, then return to construction. Exhaustive line-by-line reading of unrelated sources is not a prerequisite. In repeated attempts, preserve which supplied results were used and which opening mechanisms converged on the same auxiliary claim, so the next allocation can change on evidence.

For an enclosed packet, start with `00_ASK_TYPE_B.md` and its local dossiers.
The packet's manifest identifies the pinned public commit and browser links.
Use those links for missing sources or cross-problem connections; the shell
commands below are optional when your environment supports them. With no network,
work from the included full source texts and identify any exact missing dependency
without inventing its contents. Do not claim to have inspected an inaccessible file.

Keep citations at the packet's immutable commit. If an older packet's optional
checkout command fetches a moving branch, fetch the recorded commit explicitly
with `git fetch --filter=blob:none --depth=1 origin <published_commit>` before
checking out that commit. A later branch update must not change your proof context. If deliberately using newer
public work, record its commit and changed hypotheses separately. When returning
work, name the exact target, reused result ids and sources, new argument, proof
status, and any remaining gap; then follow the existing
[research-return skill](../erdos-research-return/SKILL.md). This works for a single
problem, several problems, or another attempt on the same problem.

## 1. Recover the current frontier

Do not begin from memory or the first interesting file.

```sh
python3 scripts/query_corpus.py --overview --format card
python3 scripts/query_corpus.py --papers
```

If the user named a problem, ask the corpus for that problem. Otherwise compare
several problem cards and choose the bounded route that best matches the
available tools, mathematical background, compute budget, and a decisive
first test:

```sh
python3 scripts/query_corpus.py --ask "What remains open for Erdős problem 249?"
python3 scripts/query_corpus.py --goal-support "<candidate mathematical goal>"
python3 scripts/query_corpus.py --proof-plan "<candidate mathematical goal>" --depth 4
```

Read the selected paper, the exact open statement, nearby source, known
counterexamples, computations, and no-go results. State the target,
hypotheses, evidence class, known obstruction, and stop condition before a
long run.

If a stewardship or consequence-propagation receipt exists, consume its
source-pinned frontier before selecting work. Treat its ranking as a reasoned
allocation input, not proof authority. Prefer the strongest attackable
transition, which may be a decisive no-go, a missing bridge, a counterexample,
or a computation that separates two serious mechanisms rather than the
nearest editable lemma.

## 2. Use parallel work without parallel authority

When the harness supports subagents, give them independent jobs such as:

- primary-source and prior-route reading;
- an exact computation designed to distinguish two hypotheses;
- one analytic or formal proof attempt;
- adversarial search for a counterexample, dropped hypothesis, or existing
  result.

Keep write scopes disjoint. Record each subagent's starting commit, question,
commands, evidence, and limit. The integrating agent must read and verify the
returned material. Agreement between agents is not independent proof.

## 3. Run the research loop

1. Re-read the current frontier and its relevant corpus neighbourhood.
2. Check whether the proposed route or failure is already recorded.
3. Compare structurally different attacks; do not rename the same residual.
4. Use exact computation where it can falsify or discriminate, not merely add
   more cases.
5. Carry out the analytic and incremental Lean work justified by the result.
6. Try to break the strongest candidate before promoting it.
7. Return the smallest evidence-bearing change and name the stronger statement
   that remains unproved.

The returned delta must be usable by a separate stewardship goal. Name the
source identity, exact statement or computation, evidence class, relation to
the previous frontier, failed routes it supersedes, plausible consumers, and
the next open boundary. Do not decide paper prominence or Palomar readiness
from inside the proof run; supply the evidence that lets the stewardship pass
make those decisions against the whole corpus.

Lean work follows `AGENTS.md`, the pinned toolchain, and focused validation.
Computation records its exact domain, program, inputs, outputs, and
interpretation. A finite search never changes an infinite quantifier.

## 4. Preserve local and reusable learning separately

Add problem-specific results, failures, and route edges to the owning problem
world. A lesson about navigation, computation, formalisation, or review may be
proposed as a reusable skill change only with its evidence, intended scope,
sibling examples, and an over-generalisation guard. One successful trick does
not become universal mathematical method by enthusiasm.

## 5. Validate, propagate, and return

Use the smallest relevant checks first. When a theorem, reduction,
counterexample, no-go, computation, correction, or architecture lesson becomes
stable, read `skills/propagate-research-consequences/SKILL.md` and inspect its
mathematical and repository consumers before packaging it.

The run has three honest exits. **Continue** when the recorded route and stop
condition still justify another discriminating step. **Suspend** when the
frontier, failed attempts, and re-entry condition are durable but the present
run should stop. **Close** when the smallest evidence-bearing delta has been
validated and its consequences have dispositions. For a resumable or
externally returned session, read `skills/erdos-research-return/SKILL.md` and
package the starting commit, contributor and tool roles, evidence, changed
paths, failures, stop condition, claim ceiling, and surviving boundary.

Report agent-generated endpoint claims as candidates. Lean acceptance does not
by itself establish intended meaning, novelty, significance, or community
acceptance. Comparator, Palomar, and the Erdős Problems community are
downstream review or record routes with their own stated limits.
