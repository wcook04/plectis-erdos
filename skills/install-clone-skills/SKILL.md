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

Preview one supported host destination:

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

## Install and verify

Add `--apply` to perform the displayed copy. Use `--mode symlink` when the
harness may read links and the installed skill should follow this checkout.
Use `--skill NAME` repeatedly to select only some skills.

```sh
python3 scripts/install_agent_skills.py --target codex --apply
python3 scripts/install_agent_skills.py --target claude --mode symlink --apply
python3 scripts/install_agent_skills.py --target-dir /absolute/path/to/skills --apply
python3 scripts/install_agent_skills.py --target codex --check
```

The installer refuses to replace different same-name material. Inspect the
destination first; use `--force --apply` only when the user explicitly wants
that replacement. Copy mode can be removed by deleting the installed skill
directories. Symlink mode can be removed by deleting the links. Neither action
changes this repository.

## Install the writing skill for another project

The writing skill includes both writing guides and a self-contained mode for
manuscripts in another repository. Preview only that skill, then install and
check the selected copy:

```sh
python3 scripts/install_agent_skills.py --target codex --skill public-mathematical-writing
python3 scripts/install_agent_skills.py --target codex --skill public-mathematical-writing --apply
python3 scripts/install_agent_skills.py --target codex --skill public-mathematical-writing --check
```

Use `--target claude` or your loader's `--target-dir` instead if appropriate.
You can also copy the `skills/public-mathematical-writing` folder yourself.
In another project, follow its **Use in another repository** section and the
destination project's own instructions. The general review needs no Plectis
commands or sibling skills; its further reading is optional.

## Boundary

Installing a skill installs instructions, not dependencies, models, credits,
or mathematical authority. Plectis-specific workflows still require the
intended Plectis checkout and must run from its root. The writing skill's
portable mode uses the destination project's sources and checks instead.
A harness may use a different skill convention; in
that case keep the workflows repo-local and point the agent at
`AGENTS.md`. Never claim support for a provider that has not loaded
and executed the installed skill.
