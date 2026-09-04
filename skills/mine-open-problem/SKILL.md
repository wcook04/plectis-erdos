---
name: mine-open-problem
description: Select and attack one bounded open mathematical route from this clone using reading, computation, analytic reasoning, Lean, and optional subagents, then return the smallest evidence-bearing delta without overclaiming it.
---

# Mine an open problem

This skill turns a cold clone into a bounded research run. It may produce a
proof, but a correction, counterexample, no-go, exact computation, literature
connection, or reproducible failed route is also a valid result.

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

When a problem card prints a `resume` command, run that exact
`scripts/query_route_memory.py --problem <number>` route for source-current
continuation state. Problem selection in `query_corpus.py` uses
`--route erdos_<number>` or ordinary-language `--ask`; it has no `--problem`
selector.

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
