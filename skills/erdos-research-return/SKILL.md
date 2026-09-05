---
name: erdos-research-return
description: Prepare, validate, assimilate, or update a provenance-preserving public research contribution in this Lean repository.
---

# Erdős research return

Use this skill when work from a public clone should come back as a replayable
contribution with durable artifact credit. Work only from tracked files in this
repository; do not require a private checkout, private ledger, agent memory, or
unpublished evidence.

## Choose the return surface

If a person has supplied useful prose, a patch, or an issue, preserve that
material as the human account. Do not make them translate it into schema field
names. The repository agent may compile a structured return from the public
evidence. Use `CONTRIBUTING.md` and `docs/research-commons/README.md` for the
human contract.

For an agent-run or advanced reproducible session, read
`docs/research-commons/RETURN_PACKAGE_TEMPLATE.md` and the tracked receipt
schema. Start from one exact public commit and one bounded problem or tooling
question. Keep the contributor, material collaborators, tool operator, model,
and provider identities separate.

## Prepare and validate

Use `scripts/continue_research.py start` to bind the public origin, starting
commit, contributor, route, intent, and stop condition. Do the bounded work in
the same clone. Record positive, negative, inconclusive, and corrective results
with equal care; never promote a claim beyond its evidence.

The required arguments are maintained by the command itself:

```sh
python3 scripts/continue_research.py start --help
python3 scripts/continue_research.py check --help
python3 scripts/continue_research.py package --help
```

Use `scripts/continue_research.py check` before packaging. Then use
`scripts/continue_research.py package` to emit `return.json`,
`route-memory.json`, and the package manifest. Validate the pair with
the exact package pair:

```sh
python3 scripts/validate_research_return.py return.json \
  --route-memory-receipt route-memory.json \
  --require-submitted --check-git --require-route-memory-receipt
```

A pull request may carry the pair as transient intake artifacts; they do not
belong on the accepted main branch.

Before packaging a stable result, run
`skills/propagate-research-consequences/SKILL.md`. The return should distinguish
consequences updated now from those verified unchanged, deferred with a
re-entry condition, or outside scope.

## Reconcile an older starting commit

Upstream may advance while a contributor works. The recorded starting commit
remains the evidence context and common ancestor for the original delta. First
replay and inspect the contribution against that commit. Then integrate the
reviewed change onto current main with the ordinary Git operation appropriate
to the history: merge, rebase, or a focused commit transplant. Do not apply an
old patch blindly, and do not require access to a private backup. Fetch the
public history if a shallow clone does not contain the starting commit.

If the histories conflict, treat the resolution as a new integration delta.
Preserve the contributor's original authorship and credit the maintainer who
performed material reconciliation. Rerun current validation and consequence
propagation after integration; the original branch receipt does not certify the
new repository state.

## Assimilate accepted work

Acceptance is a local evidence decision, not a ritual gate. Determine whether
the exact returned artifact is suitable to land, which evidence was actually
checked, and whether any claim transition needs the methodology route. After
the contribution exists in an accepted public commit, use
`scripts/accept_research_return.py` to create the committed accepted receipt.
Preserve the submitted identity, evidence, limitations, and correction lineage.

Rebuild the accepted-only views with `scripts/build_research_contributions.py`
and `scripts/build_research_contribution_recognition.py`. Run their focused
tests and checkers. Confirm that an unaccepted return is absent, the accepted
commit is contained in the current public history, credited paths are exact,
and no receipt silently changes `docs/claims.json`.

## Return the result to other clones

Land the accepted artifact, receipt, and regenerated views together in public
history. Existing clones can then fetch and merge or rebase the public branch;
the contribution and its credit arrive in the same history. Do not perform a
push, publication, registration, or outreach action unless the current task
authorizes that external effect.

For a later correction, retain the earlier receipt and add explicit lineage
that says whether the earlier artifact is retained, superseded, or withdrawn.
Credit is evidence-bound and historical; it is not a leaderboard and is not
erased by ordinary revision.
