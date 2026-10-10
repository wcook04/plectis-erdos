---
name: install-clone-skills
description: Preview, install, or verify the public Plectis skills in Codex, Claude, or another directory-based agent harness.
---

# Install clone skills

Use this skill when somebody wants the workflows in this clone to remain
available outside the repository. Installation is optional. An agent working
inside the clone can read `AGENTS.md` and `skills/*/SKILL.md` directly.

## Inspect before changing anything

List the tracked skills:

```sh
python3 scripts/install_agent_skills.py --list
```

Preview the namespaced companion at one supported host destination:

```sh
python3 scripts/install_agent_skills.py --target codex
python3 scripts/install_agent_skills.py --target claude
```

For Cursor, another coding agent, or a custom skills loader, use the directory
that harness documents:

```sh
python3 scripts/install_agent_skills.py --target-dir /absolute/path/to/skills
```

The preview reports `missing`, `current`, or `different`. It does not write.
Every destination operation without a selection flag selects only
`plectis-frontier`, including custom destinations and legacy hosts. Listing
without a destination still shows the clone catalog. Do not turn catalog
availability into permission to install every generic workflow globally.

Codex defaults to `~/.agents/skills`. Use `--target codex-legacy` explicitly
for `$CODEX_HOME/skills` (or `~/.codex/skills`) with an older client. Claude
uses `$CLAUDE_CONFIG_DIR/skills` (or `~/.claude/skills`). Restart the client
after installation. These destinations follow client conventions; successful
loading must still be tested with the actual client.

The explicit `--companion` selector is an alias for this default:

```sh
python3 scripts/install_agent_skills.py --target codex --companion
python3 scripts/install_agent_skills.py --target codex --companion --apply
python3 scripts/install_agent_skills.py --target codex --companion --check
```

The companion independently pins its research checkout. Read
[portable companion](../../docs/agents/PORTABLE_COMPANION.md) for packaging,
source verification and removal.

## Install and verify

Add `--apply` to perform the displayed copy. Use `--mode symlink` when the
harness may read links and the installed skill should follow this checkout.
Use `--skill NAME` repeatedly to select particular clone workflows. These
are an explicit expert choice; their generic names remain repo-local by default.
Use `--all-clone-skills` only when the owner wants the entire clone catalog.
It is mutually exclusive with `--companion` and `--skill`. Existing installed
workflows are preserved; changing the default does not migrate or remove them.

```sh
python3 scripts/install_agent_skills.py --target codex --apply
python3 scripts/install_agent_skills.py --target claude --mode symlink --apply
python3 scripts/install_agent_skills.py --target-dir /absolute/path/to/skills --apply
python3 scripts/install_agent_skills.py --target codex --check
python3 scripts/install_agent_skills.py --target codex --skill explain-public-system --apply
python3 scripts/install_agent_skills.py --target-dir /absolute/path/to/skills --all-clone-skills --apply
```

The installer refuses to replace different same-name material. Inspect the
destination first; use `--force --apply` only when the user explicitly wants
that replacement. Choose a destination outside the clone's source skill
directories; the installer rejects overlapping paths before changing any
selection, even with `--force`. Copy mode can be removed by deleting the installed skill
directories. Symlink mode can be removed by deleting the links. Neither action
changes this repository.

## Boundary

Installing a skill installs instructions, not dependencies, models, credits,
or mathematical authority. It also does not make repository commands runnable
from an unrelated directory: locate the intended Plectis Lean checkout and run
the workflow from its root. A harness may use a different skill convention; in
that case keep the workflows repo-local and point the agent at
`AGENTS.md`. Never claim support for a provider that has not loaded
and executed the installed skill.
