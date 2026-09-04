# Clone-local agent skills

These workflows travel with the public repository and use only tracked
clone-local files. Route the task before opening a skill:

```sh
python3 scripts/agent_entry.py --entry "<task>"
python3 scripts/agent_entry.py --skills
python3 scripts/agent_entry.py --skill mine-open-problem
```

`registry.json` owns families, task lanes, lifecycle relationships, and
complete coverage. Each `SKILL.md` owns its executable workflow and
frontmatter description. This index is generated from both, so it cannot
silently become a second catalog.

## Orientation and access

Enter, explain, and optionally install the public workflows without requiring a private system.

- [explain-public-system](explain-public-system/SKILL.md) — Explain this public mathematical research system to a lay reader, mathematician, formaliser, compute contributor, reviewer, or infrastructure contributor from clone-local evidence.
- [install-clone-skills](install-clone-skills/SKILL.md) — Preview, install, or verify the public Plectis skills in Codex, Claude, or another directory-based agent harness.

## Research and expansion

Select a bounded frontier, sustain discovery, or add a sourced problem world while preserving open boundaries.

- [add-open-problem](add-open-problem/SKILL.md) — Add a sourced mathematical problem as a new public problem world without silently promoting expansion work into a reviewed claim or pretending that the indexed roster is fixed.
- [mine-open-problem](mine-open-problem/SKILL.md) — Select and attack one bounded open mathematical route from this clone using reading, computation, analytic reasoning, Lean, and optional subagents, then return the smallest evidence-bearing delta without overclaiming it.
- [run-coupled-research-goals](run-coupled-research-goals/SKILL.md) — Coordinate an event-driven discovery goal and corpus-stewardship goal over one public mathematical frontier without collapsing proof, appraisal, exposition, or work-allocation authority.

## Validation

Coordinate reproducible Lean checks without turning build machinery into proof authority.

- [lean-concurrent-validation](lean-concurrent-validation/SKILL.md) — Run Lean validation from one or more public cold clones without duplicate builds, competing build writers, manual retry supervision, or private infrastructure.

## Return, propagation, and integration

Return work from any clone, preserve attribution, reconcile it with current main, propagate consequences, and prepare reviewable upstream changes.

- [erdos-research-return](erdos-research-return/SKILL.md) — Prepare, validate, assimilate, or update a provenance-preserving public research contribution in this Lean repository.
- [propagate-research-consequences](propagate-research-consequences/SKILL.md) — Trace the mathematical and repository consequences of one accepted or candidate result, record a disposition for every plausible downstream consumer, and rerun the trace when older-clone work is reconciled with current main.
- [submit-pull-request](submit-pull-request/SKILL.md) — Prepare, validate, commit, and, only when explicitly authorised, push and open a pull request that returns a mathematical, architecture, exposition, or clone-experience contribution to the public repository.

## Public communication

Explain checked mathematics in reader-facing prose without outrunning the evidence.

- [public-mathematical-writing](public-mathematical-writing/SKILL.md) — Write or revise reader-facing mathematics in this public Lean repository without outrunning checked source, claim status, or the exact open boundary.

## Infrastructure stewardship

Dogfood and maintain the public agent, query, validation, contribution, and generated-projection surfaces as one self-contained system.

- [maintain-public-infrastructure](maintain-public-infrastructure/SKILL.md) — Dogfood, organize, consolidate, and repair the public clone's agent, query, validation, contribution, credit, and projection infrastructure without depending on private systems.

## Maintain and dogfood

Treat a route that exists but misclassifies a real task as drift. Update the
registry or owning skill, regenerate this index, add the observed journey as a
fixture, and run the clone-local checks before propagation.

```sh
python3 scripts/agent_skill_catalog.py
python3 scripts/agent_skill_catalog.py --check
python3 scripts/test_agent_entry.py
python3 scripts/test_clone_skills.py
python3 scripts/check_cold_clone_comprehension.py --quick
```
