---
name: run-coupled-research-goals
description: Coordinate an event-driven discovery goal and corpus-stewardship goal over one public mathematical frontier without collapsing proof, appraisal, exposition, or work-allocation authority.
---

# Run coupled research goals

Use this skill when a person or agent wants sustained work on an open problem
rather than one isolated attempt. It can be run in one agent session, in two
tasks, or across different people and harnesses. The contract is the same:
discovery changes the mathematical frontier; stewardship decides what that
change means for the source-current corpus and what should happen next.

This skill coordinates existing jobs. It does not replace their evidence and
authority rules.

## Orient and pin the state

If the operator does not yet understand the repository, first read
`skills/explain-public-system/SKILL.md` and explain the system at the requested
level. Do not require the operator to read every paper before the agent can
begin. The agent may read the papers and public corpus itself, then provide
exact routes for any claim the operator wants to inspect.

Before either goal works, record the shared starting commit, ultimate open
endpoint, current bounded frontier, claim ceiling, and available compute or
human-review budget. Obtain the frontier from the clone:

```sh
python3 scripts/query_corpus.py --overview --format card
python3 scripts/query_corpus.py --papers
python3 scripts/query_corpus.py --ask "<problem and current frontier>"
```

Use one source identity for both goals. A summary copied between chats is not
the shared state.

## Discovery goal

Read `skills/mine-open-problem/SKILL.md`. The discovery goal owns one bounded
attack and returns the smallest stable evidence-bearing delta: a theorem,
counterexample, no-go, exact computation, corrected statement, literature
connection, architecture repair, or durable failed route. It also returns the
stronger statement that remains open and the exact evidence needed for the
next transition.

The discovery goal may coordinate parallel analytic, computational, formal,
source, or adversarial lanes when they are genuinely independent. Their
returns remain candidates until the integrating agent verifies them.

## Stewardship goal

A stable delta is a wake event. Read
`skills/propagate-research-consequences/SKILL.md` and reconstruct the relevant
candidate universe from source authority. Do not appraise the new object in
isolation or assume the current paper already contains the strongest result.

The stewardship goal must return four distinct decisions:

- the evidence and authority status;
- the mathematical appraisal and surviving boundary;
- the exposition and public-surface dispositions; and
- the next allocation of compute or expert attention.

It updates or verifies every plausible consumer, including the problem
frontier, paper, query routes, Comparator or Palomar packet, and return
package. It then returns a source-pinned ranked frontier to discovery: the
strongest relevant result, exact missing bridge or falsifier, and cheapest
test capable of changing the current appraisal. Ranking directs attention; it
does not establish truth, novelty, or acceptance.

## Event-driven coupling

Wake stewardship after a stable mathematical, authority, exposition, or
external-review delta. Wake discovery after stewardship identifies a changed
frontier, missing implication, decisive falsifier, or discriminating test.
When the source-current state is unchanged, yield. Do not spend model turns
polling another goal or producing heartbeat prose.

A deployment with two tasks should exchange committed paths and receipts, not
free-form claims of progress. A one-session deployment performs the same hand-
off sequentially. Different models, subscriptions, local machines, and human
contributors may occupy either role; attribution follows the actual returned
objects and decisions.

## Exit and return

Continue while a new discriminating step is justified. Suspend with the
frontier, killed routes, receipts, and a concrete re-entry event when the next
step is unavailable. Close one cycle when the delta is validated, consumer
dispositions are recorded, and the next owner is named; this does not mean the
open problem is solved.

For work that leaves the clone, use `skills/erdos-research-return/SKILL.md`.
For a proposed upstream patch, use `skills/submit-pull-request/SKILL.md`.
External mathematical acceptance remains outside this controller.
