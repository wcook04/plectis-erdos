<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Frontier distribution and community operation

This is a setup runbook, not a record that any account, listing, chat room or
hosted agent is live. The entry object is
[one checkable research shift](FRONTIER_RELAY.md). Use that object wherever a
community has a suitable, permitted route. Never copy private strategy,
correspondence, traces or credentials into the public package.

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

ClawHub's current skill terms require MIT-0 with no per-skill override. Publish
only `.agents/skills/plectis-frontier`, whose newly authored files have that
licence. Do not upload the Apache-2.0 clone-local skills or the corpus under
MIT-0. Review the package and its exact contents before any upload.

On the publishing owner's machine, using a reviewed, recorded ClawHub CLI
version and account:

```sh
clawhub login
clawhub skill publish .agents/skills/plectis-frontier \
  --slug plectis-frontier --name "Plectis Frontier" --version 0.1.0 \
  --categories research,development,agents \
  --topics lean,formal-mathematics,research-handoff,erdos,open-science \
  --dry-run
```

The dry run is preparation, not a published listing. Only after package review,
source smoke checks and explicit release approval should the same command run
without `--dry-run`. Confirm the actual owner-qualified registry identifier,
release version and review state before advertising installation. Do not assume
that the publisher handle is the same as the GitHub login or that a slug is
available. New uploads may be withheld while automated checks finish. Never
bypass warnings or use labels such as 'official', 'audited' or 'verified' as
unsupported marketing claims. Category/topic validation on upload is distinct
from a local dry run.

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
