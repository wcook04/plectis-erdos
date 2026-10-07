<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Give your agent a research shift

Choose one unfinished question, attempt one bounded continuation, and leave
something another researcher can check and continue. A useful return can be an
argument, counterexample, correction, exact calculation, or a well-supported
failed route. The contributor keeps credit for their original contribution.
The public corpus does not claim to solve the eight original Erdős problems.

This guide connects question selection, one bounded research attempt and a
checkable return. It works from the public checkout. Model use and optional
Lean builds retain their costs and dependencies.

## Or start from the mathematics

A shift does not have to begin from a listed question. You can ask your agent
to read the corpus and decide what is worth developing: a connection between
problems, a general theorem behind a recorded example, a change of
representation, or a new question with evidence for its value. The
[exploration skill](../../skills/explore-the-corpus/SKILL.md) owns that route in a
clone, and the [reading edition](../reading-edition/README.md) serves it without
one. Once a bounded statement emerges, the rest of this guide applies
unchanged. A return whose subject is wider than one problem names its subject
and lists the related problems.

## Pick a question first

If you already have a clone, this lists every open question in the repository,
grouped by problem, each with its statement and its place in the paper:

```sh
python3 scripts/query_corpus.py --open
```

Choose one row and open it. The packet names the checked results that bear on
the question and the routes that have already been recorded for it:

```sh
python3 scripts/query_corpus.py --open <id>
```

The list is a menu in registry order. It does not rank the questions by
difficulty or by value. Some rows are one of the eight original problems. Some
are restatements that Lean proves equivalent to one of them, so settling such a
row settles that whole problem. The rest are narrower questions whose answer
settles only what the row says. Open a row and read the checked results that
bear on it before judging which kind it is.
The rest of this guide covers packaging, the pinned wrapper, and the return.

## Start from a reviewed checkout

The [portable companion](PORTABLE_COMPANION.md) owns the reviewed wrapper,
source pin, installation and client observations. Follow its
[bootstrap recipe](PORTABLE_COMPANION.md#use-from-another-working-directory)
to inspect the pin, obtain a new checkout and run the actual task smoke.
Keep the wrapper version and mathematical source revision separate. Preserve
existing work and the starting receipt; the clean-checkout smoke is not the
validation gate for subsequent research edits.

For OpenClaw, inspect the current client documentation before choosing its
workspace installation route. A nested skill directory is not a root Git
installation target. Record the client version and actual entry outcome;
directory discovery does not establish a completed research shift.

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
python3 scripts/query_corpus.py --open
python3 scripts/query_corpus.py --route erdos249_certificate_story
# Alternative, not an instruction to attempt both:
python3 scripts/query_corpus.py --route erdos257_half_story
```

Before work, state the exact target, evidence already available, known
obstruction, one discriminating test, authorised budget and stop condition.
Use the `mine-open-problem` skill selected by the clone. Do not install Lean or
start a costly proof build merely to obtain an overview.

If you intend to return a structured package, [start the continuation session](../research-commons/RETURN_PACKAGE_TEMPLATE.md#start-a-structured-continuation)
**before editing or committing research changes**. The `start` command records
the current commit, contributor and selected question; it requires a clean
checkout by default. Keep its session name and generated files for the return.
An ordinary issue or pull request does not require this session or JSON files.

## Return something checkable

Keep the human account in ordinary language. Record the starting commit, the
actual change or failed route, replay commands and outcomes, limitations, and
one next step. Identify human contributors, tool operators and the model and
agent system actually used. An untested suggestion is not a reproduced result;
a reproduced result is not automatically an accepted contribution.

Use [CONTRIBUTING](../../CONTRIBUTING.md), the existing
[research progress form](../../.github/ISSUE_TEMPLATE/research_progress.yml), or the
[research return form](../../.github/ISSUE_TEMPLATE/research_return.yml).
GitHub Discussions is optional: issue and pull-request intake already exists.
For a structured return, follow the clone's
[`erdos-research-return` skill](../../skills/erdos-research-return/SKILL.md) and the
[packaging sequence](../research-commons/RETURN_PACKAGE_TEMPLATE.md#fill-and-package-the-structured-return).
Fill `return.json` and the route-memory sidecar, close the workbench session,
then run the validation and packaging commands. The packager copies those
inputs; it does not write the account of your work. Preserve the local package
and obtain approval before publishing it. Maintainers decide acceptance and
rebuild the accepted-contribution credit views from accepted receipts.

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

For offering the workflow to others, use the distribution section below.

## Packaging sources checked 4 September 2026

[OpenClaw skill CLI](https://docs.openclaw.ai/cli/skills),
[OpenClaw skill loading](https://docs.openclaw.ai/tools/skills),
[Agent Skills format](https://agentskills.io/specification), and
[skills CLI](https://github.com/vercel-labs/skills).
These are packaging references, not endorsements or compatibility receipts.

## Distribution and community operation

This is a maintainer runbook, not a record of a live listing, account, chat
room or hosted agent. Keep participant preparation and observed outcomes
separate from publication and promotion.

## Minimum evidence before inviting participants

Run the wrapper tests, the public-clone entry smoke check and the repository's
existing release checks. Then complete one actual owner-authorised OpenClaw
shift with a local return. Record versions, source and wrapper commits, commands,
outcomes and limits. An independently repeated attempt is a stronger public
example than another internal demonstration. Do not invent an independent user,
endorsement, accepted return or benchmark result.

Choose one public entry URL and one substantive task. A short demonstration
should show the question, evidence inherited, actual action, result and next
question. Existing system films can supply context; they do not substitute for
an installation or return test. Keep mathematical significance, tool operation
and audience response as separate claims.

## ClawHub: publish only the standalone wrapper

The 4 September 2026 source check recorded ClawHub's MIT-0 requirement with
no per-skill override; recheck its terms before publication. Publish
only `.agents/skills/plectis-frontier`, whose newly authored files have that
licence. Do not upload the Apache-2.0 clone-local skills or the corpus under
MIT-0. Review the package and its exact contents before any upload.

Use the current reviewed ClawHub CLI and account to preview the exact package.
Read the wrapper version from its current source or generated package manifest;
do not copy an old example version into a new release. A dry run does not
establish a published listing. Upload requires explicit release approval.
Confirm the actual owner-qualified registry identity, released version and
review state before advertising installation; retain warnings and review
outcomes as recorded evidence.

Retain the registry receipt and perform a clean install of that exact published
version. Do not enable unattended publishing or commit a registry token. The
repository source pin and wrapper version should change only through a reviewed
update with repeat tests.

## skills.sh and other clients

Use the single portable wrapper, not provider-specific behavioural forks. The
skills CLI discovers both `skills/` and `.agents/skills/`; the absence of an
`.agents` directory was never a universal listing blocker. The reason for this
wrapper is the complete installed-directory-to-checkout workflow.

Record actual installation and use, not just discoverability. Test OpenClaw
first, then one other client such as Hermes or a coding-agent skill client.
Do not advertise a compatibility matrix filled in solely from common file
format support. Installation telemetry is not a count of useful research runs;
never manufacture installations, votes or endorsements.

## Chat and community routes

| Surface | Appropriate use | Boundary |
|---|---|---|
| OpenClaw Discord showcase | Share a working research-shift example in the documented `#self-promotion` route, with repository/demo link and an explanatory image or clip. | Review that channel's current rules; no unsolicited direct-message campaign. The official showcase also offers tagging `@openclaw` on X. |
| A Plectis-owned chat room | Optional participant support, with human moderation and one thread per attempt linking to its issue/return. | A new server is not needed to begin. GitHub issues remain the durable intake; chat is not proof or acceptance authority. |
| Moltbook | A small disclosed experiment around an actual task, only after ownership verification and permitted-use review. | Its terms prohibit unauthorised advertising/spam and restrict scraping and gathering user/agent data. No unattended promotional heartbeat, fabricated fans, contact harvesting or credentials in posts. |
| Lean Zulip | A specific technical question or response that the community can use. | Its current guidelines prohibit LLM-written GitHub/Zulip comments and generic project promotion. Do not paste an AI draft there, even after light editing. The human writes the message. |
| Mathematics-focused social forums | Explain one exact result and limitation with an inspectable public source. | Check each forum's current rules before posting; no identical eight-problem announcement burst. |
| Hermes community | Offer a reproducible Hermes research shift after actually testing Hermes. | The user-stories page collects public stories; this is not evidence of a guaranteed submission form or feature. |

Public posting, joining a community, creating accounts and sending messages are
separate actions requiring their own approval. This runbook performs none.

## Connecting a chat bot later

A research skill and a chat-channel connection are separate layers. First prove
the local skill. Then use the current official channel setup for an explicitly
chosen server/channel and owner-controlled bot identity. No token belongs in
this repository, a prompt, issue, log or skill manifest.

Keep a community-facing bot separate from a research executor. The chat bot
should have no shell, research-machine filesystem, private repository or broad
account access. A human can approve a bounded task for the isolated executor
and review a proposed reply. Do not expose a command-executing Gateway directly
to a public channel or assume that a skill allowlist confines shell access.

For an authorised Discord setup, narrow the guild, channel and sender
allowlists, require explicit invocation/mentions, disable bot-to-bot replies
unless a specific bounded exchange is authorised, restrict tool access, pair
or deny direct messages, and run `openclaw security audit --deep` on the actual
host. Validate the configuration against the installed OpenClaw version; this
repository does not supply a token-bearing or universally safe configuration.
Budget and frequency limits are additional controls, not substitutes for
permission and moderation.

## What to measure

Record attempted installations, successful entry, an exact frontier inspected,
a checkable return, independent reproduction, maintainer acceptance and a
subsequent participant arriving through an accurate share. Preserve these as
separate stages. Use consented receipts and aggregate platform statistics; no
covert telemetry. An enthusiastic agent conversation is not itself a user or a
research contribution. Keep participant credit and correction history visible.

## Primary sources checked 4 September 2026

- [ClawHub publishing](https://docs.openclaw.ai/clawhub/publishing) and
  [skill licensing](https://docs.openclaw.ai/clawhub/skill-format).
- [skills CLI discovery](https://github.com/vercel-labs/skills) and
  [directory documentation](https://www.skills.sh/docs).
- [OpenClaw showcase](https://docs.openclaw.ai/start/showcase),
  [Discord setup](https://docs.openclaw.ai/channels/discord) and
  [security boundaries](https://docs.openclaw.ai/gateway/security).
- [Moltbook terms](https://www.moltbook.com/terms),
  [Lean community guidelines](https://leanprover-community.github.io/community_guidelines.html)
  and [Hermes user stories](https://hermes-agent.nousresearch.com/docs/user-stories).

Recheck rules and installed-version behaviour at action time. These references
do not establish audience reach, acceptance, or likely public recognition.
