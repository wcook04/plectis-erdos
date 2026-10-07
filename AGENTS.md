<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Agent instructions

Work from this public checkout. [The repository map](README.md#repository-map)
locates folders; [the agent guide](docs/agents/AGENT_GUIDE.md) owns mutation,
claim review and validation. No public claim depends on private files.

## Route the actual task

Run from the repository root:

```sh
python3 scripts/agent_entry.py --entry "<task in ordinary language>"
```

Open the returned skill and smallest source set. `python3 scripts/agent_entry.py --skills` lists workflows.
For latest-work requests, run `python3 scripts/agent_entry.py --checkout --check-upstream`;
record the starting commit and preserve local edits. An unavailable comparison
means currentness is unknown. [Setup and prompts](docs/agents/README.md#start-with-current-public-work).

For mathematics or status, use `python3 scripts/query_corpus.py --ask "<question>"`.
For a corpus-wide question, use `python3 scripts/query_corpus.py --overview --format card` and its answer
contract; cover all requested programmes and their exact open boundaries.
Follow returned claim, paper and source handles. Routes locate evidence;
they do not prove applicability or settle a question.

## Evidence and research boundaries

- Lean checked with the pinned kernel establishes its exact formal statement
  under its assumptions. `docs/claims.json` owns selected public wording and
  status; `docs/methodology.json` governs claim transitions. Generated maps,
  papers and model output cannot replace those responsibilities.
- Respect requested learning depth. A hint request does not authorise revealing
  the proof or starting proof search. [Reading guidance](skills/explain-public-system/SKILL.md#help-a-reader-work-through-an-argument).
- Check the selected paper's references and [prior art](docs/PRIOR_ART.md), then
  primary sources. Cite the exact statement and edition; distinguish earlier
  results, formalisation, deduction and conjecture. State search limits.
  Agent agreement does not establish novelty.
- Preserve computation inputs, bounds, outputs and a recheck command. A finite
  search establishes only its finite conclusion. Dated research returns do not
  establish current claim status.
- Before Lean work, start from the exact goal: use `--goal-support` or
  `--proof-plan` on `query_corpus.py`, then verify applicability with Lean.
  The [proof-state compiler](docs/agents/PROOF_STATE_COMPILER.md) provides actual
  goal context. [Land Lean proofs](skills/land-lean-proofs/SKILL.md) governs consumers.
- Comparator checks selected statements and permitted axioms; it does not
  assess novelty, meaning or peer review. Palomar local qualification does not
  confer submission or acceptance. Use `--route comparator_assurance` or
  `--route palomar_qualification` for the recorded evidence.

## Change and validate

Preserve unrelated staged and unstaged work. Never reset, restore, clean or
broad-stage a shared checkout. Edit source authorities before generated
projections and run their owner builder. Do not add `sorry`, `admit`,
project-defined `axiom`, `native_decide`, unsafe/partial declarations or
unbounded kernel limits. Use the
[concurrent validation workflow](skills/lean-concurrent-validation/SKILL.md);
never overlap Lean builds.

The [agent guide](docs/agents/AGENT_GUIDE.md#validation) names focused checks and
the release boundary. Run checks proportionate to the change; do not rerun
components after a full gate passes. Infrastructure repairs follow
[maintenance](skills/maintain-public-infrastructure/SKILL.md); mathematical
exposition follows [public writing](skills/public-mathematical-writing/SKILL.md).
After a stable result or repair, follow the
[consequence workflow](skills/propagate-research-consequences/SKILL.md).

[Contributing](CONTRIBUTING.md) accepts ordinary issues and pull requests.
[Research returns](skills/erdos-research-return/SKILL.md) preserve resumable
investigations. Credit original contributions and later material integration
separately. [Submission](skills/submit-pull-request/SKILL.md) owns scoped commits
and release admission; pushing, opening a PR or external submission requires
explicit authorisation. For delegated work, give bounded questions and disjoint
write scopes; the integrating agent verifies evidence and makes final decisions.
