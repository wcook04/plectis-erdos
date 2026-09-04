<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Give your agent a research shift

Choose one unfinished question, attempt one bounded continuation, and leave
something another researcher can check and continue. A useful return can be an
argument, counterexample, correction, exact calculation, or a well-supported
failed route. The contributor keeps credit for their original contribution.
The public corpus does not claim to solve the eight original Erdős problems.

This entry packages the existing mining, propagation and return workflows. It
does not require Plectis's private system, a hosted service, a new account or a
particular model provider. Owner-authorised model use and optional Lean builds
have their own costs and dependencies.

## Start from a reviewed checkout

The portable wrapper lives at
[`.agents/skills/plectis-frontier`](../.agents/skills/plectis-frontier/SKILL.md).
Its four files travel together. Installing only `SKILL.md` is insufficient.
The wrapper's revision and the research-source revision are separate: the
latter is fixed in its `source.json`. Review both before execution.

In the reviewed repository checkout:

```sh
SKILL_DIR="$PWD/.agents/skills/plectis-frontier"
python3 "$SKILL_DIR/scripts/bootstrap.py" describe
```

Inspection makes no network request. Python 3.11+ and Git are required. Linux
is the initial CI target; macOS is an intended, separately testable target.
There is no Windows compatibility claim.

With the owner's permission, obtain the pinned research corpus in a **new**
directory under an existing writable parent:

```sh
RESEARCH_DIR="$HOME/plectis-research-shift"
python3 "$SKILL_DIR/scripts/bootstrap.py" prepare \
  --destination "$RESEARCH_DIR" --allow-network
```

That directory must not already exist. Choose a different path rather than
removing someone else's work. The download is a full source checkout, without
Lean or mathlib installation; it may be substantial. No private credentials or
API keys are needed. A failed download is retained, not automatically deleted.

After reviewing the fetched source and its `AGENTS.override.md`, authorise the
two Python entry commands:

```sh
python3 "$SKILL_DIR/scripts/bootstrap.py" smoke \
  --destination "$RESEARCH_DIR" --allow-execution
```

Save the JSON receipt outside the research checkout. A successful smoke check
means the routing and overview commands ran. It is not a Lean build, proof,
registry security verdict, or end-to-end agent compatibility result. Following
research edits will make the initial-clean-checkout verification fail by design;
use the established research-return workflow for subsequent validation.

## Install in OpenClaw or another skill client

On the appropriate OpenClaw Gateway host, with an already configured agent and
the owner's approval, install the reviewed local **skill directory**:

```sh
openclaw skills install "$SKILL_DIR" --as plectis-frontier
openclaw skills info plectis-frontier
openclaw skills check
```

These commands target the configured workspace. Use OpenClaw's `--agent <id>`
selector when the owner has chosen a named research agent; do not use
`--global` as a default. Start a new session and ask explicitly for a Plectis
research shift. Keep the installed skill and the research checkout separate.

Do **not** advertise `openclaw skills install git:wcook04/plectis-lean-erdos249-257`
as a working shortcut: direct Git installation expects `SKILL.md` at the
repository root, while this repository contains a nested skill directory.

The skills CLI can also discover this wrapper from a reviewed local checkout:

```sh
npx skills add . --skill plectis-frontier --agent openclaw
```

This executes an external CLI: review and record its exact version first. Select
only `plectis-frontier`, not every clone-local workflow. After the change is
merged and tested on public main, the corresponding repository-discovery route
is `npx skills add wcook04/plectis-lean-erdos249-257 --skill plectis-frontier`.
A directory being discoverable does not demonstrate a successful run in every
supported client. Keep each client test and version separate.

## Pick substantive work

Use the clone's agent entry and current public result ranking to choose an
exact target. Distinguish the most consequential completed result from the
most useful next research task and from a simple machinery demonstration.

For a first research shift, the #249 certificate programme is a useful starting
route. The #257 exact-support frontier is an alternative. Inspect each route's
actual remaining obligation and failed attempts before choosing; neither is an
invitation to relabel an equivalence or finite certificate as a solution.

```sh
cd "$RESEARCH_DIR"
python3 scripts/query_corpus.py --route erdos249_certificate_story
# Alternative, not an instruction to attempt both:
python3 scripts/query_corpus.py --route erdos257_half_story
```

Before work, state the exact target, evidence already available, known
obstruction, one discriminating test, authorised budget and stop condition.
Use the `mine-open-problem` skill selected by the clone. Do not install Lean or
start a costly proof build merely to obtain an overview.

## Return something checkable

Keep the human account in ordinary language. Record the starting commit, the
actual change or failed route, replay commands and outcomes, limitations, and
one next step. Identify human contributors, tool operators and the model and
agent system actually used. An untested suggestion is not a reproduced result;
a reproduced result is not automatically an accepted contribution.

Use [CONTRIBUTING](../CONTRIBUTING.md), the existing
[research progress form](../.github/ISSUE_TEMPLATE/research_progress.yml), or the
[research return form](../.github/ISSUE_TEMPLATE/research_return.yml).
GitHub Discussions is optional: issue and pull-request intake already exists.
Agents should follow the clone's `erdos-research-return` skill, preserve the
local package and obtain approval before publishing it. Maintainer review owns
acceptance and the existing accepted-contribution credit views.

Where Plectis materially helped, please cite the relevant release and explain
its role. This is a request for accurate attribution, not a claim to a solver's
mathematics or an additional condition on the MIT-0 wrapper.

## Trust and release boundaries

The newly authored wrapper is MIT-0 for ClawHub compatibility. The separately
fetched corpus keeps its existing Apache-2.0 software/documentation and
CC-BY-4.0 manuscript boundaries. No corpus text is silently relicensed.

The bootstrap uses an exact public commit, disables Git hooks and ambient Git
configuration for its commands, strips account credentials from child process
environments, refuses existing destinations and separates fetching from
executing repository Python. These controls are not an operating-system
sandbox, a proof of absence of malicious code, or protection from a compromised
host. Use an isolated account/container, restricted filesystem mounts and
network controls. The flags record operator intent; they are not an access
control system. Do not install this research skill in an agent with unrelated
private file access or outbound messaging authority.

Before a release is described as OpenClaw-tested, retain a receipt with the
wrapper commit, corpus commit, OpenClaw version, operating system, installation
route, entry outcome, budget, actual return and remaining failures. The local
fixture tests are not that receipt. Run the existing public release gate as
well as the new wrapper CI; keep failed checks visible.

For distribution and community-specific boundaries, see
[FRONTIER_DISTRIBUTION](FRONTIER_DISTRIBUTION.md).

## Packaging sources checked 4 September 2026

[OpenClaw skill CLI](https://docs.openclaw.ai/cli/skills),
[OpenClaw skill loading](https://docs.openclaw.ai/tools/skills),
[Agent Skills format](https://agentskills.io/specification), and
[skills CLI](https://github.com/vercel-labs/skills).
These are packaging references, not endorsements or compatibility receipts.
