<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Portable Plectis companion

The single `plectis-frontier` skill routes learning, claim inspection, result
reuse and research through the public checkout's task router. It contains
instructions, one bootstrap script, a source pin and an MIT-0 licence. It adds
no hooks, MCP server or client configuration. This is a directory-based Agent
Skill archive, **not a Codex or Claude plugin**.

## Build and inspect

From the public checkout:

```sh
python3 scripts/build_plectis_companion.py --output /absolute/new/companion.zip
python3 scripts/build_plectis_companion.py --output /absolute/new/companion.zip --apply
```

Preview writes nothing. Apply refuses an existing output. The deterministic
archive has one `plectis-frontier/` directory and a generated `package.json`
with file SHA-256 hashes, companion version and separate research revision.
The builder allowlists four source files and excludes checkout history,
credentials, caches and unrelated instructions. It does not fetch or execute
research code. Verify archive hashes before copying it into a skills directory.
A source hash records identity; it is not a security audit.

Companion version `0.2.0` pins public research revision
`b7210894f41ce3dd7a2ea7b553424fb155fb0c65`. Releasing new instructions and
upgrading the mathematical checkout are separate decisions. The wrapper never
silently follows `main`. The research checkout retains its own licence map.

## Install one skill

From this checkout, preview, apply and check:

```sh
python3 scripts/install_agent_skills.py --target codex --companion
python3 scripts/install_agent_skills.py --target codex --companion --apply
python3 scripts/install_agent_skills.py --target codex --companion --check
```

Codex defaults to `~/.agents/skills`. Its [current skill documentation](https://learn.chatgpt.com/docs/build-skills)
identifies this user location and `.agents/skills` in projects. The explicit
`--target codex-legacy` destination is `$CODEX_HOME/skills` or `~/.codex/skills`.
Claude's [skill documentation](https://code.claude.com/docs/en/skills) identifies
`~/.claude/skills` and project `.claude/skills`; `--target claude` uses
`$CLAUDE_CONFIG_DIR/skills` when configured. Use `--target-dir` for an explicit
project skills directory or another client. Restart the client after copying.

Alternatively, inspect and extract the archive into a temporary directory,
then copy only its `plectis-frontier` directory into the chosen skills location.
Do not overwrite an existing same-name directory. The archive is not an input
to a client plugin installation command.

Ordinary apply refuses different same-name material. Preview reports the
collision, and `--check` fails. Preserve user edits before an explicitly chosen
`--force` replacement. For rollback of a new install, inspect the exact
installed namespace and remove only that `plectis-frontier` directory (or its
symlink in symlink mode). This does not remove or reset research work.

## Use from another working directory

Invoke `plectis-frontier` through the client's skill mechanism. Resolve its
loaded path and inspect `source.json`, then use the bundled bootstrap script's
`describe` action. With download authorisation, `prepare --destination ...
--allow-network` obtains the exact public research revision in a new directory.
An existing destination is refused, and failed downloads are retained.

With execution authorisation, `smoke --destination ... --allow-execution
--task "<actual request>"` verifies the source and runs the actual task router
plus corpus overview. Dirty checkouts are refused and preserved. This smoke
check establishes command routing; it does not check Lean or a theorem. After
research edits, keep the starting receipt and work through the checkout's own
return workflow rather than trying to make the initial clean-check smoke pass.

## Evidence as of 6 October 2026

Offline tests extract the archive outside the repository, execute its standalone
`describe`, check reproducibility and file hashes, and exercise installation
preview, conflict refusal, verification and removal. Disposable Git fixtures
exercise exact pins, dirty-work preservation and routing of an actual request.

A real outside-repository project installation was attempted with Claude Code
`2.1.178`, using only Skill and Read tools, no session persistence, project
settings, no MCP servers and a $0.10 limit. The invocation failed before
inference with OAuth HTTP 401 and consumed no tokens or charge. It does not
establish skill loading or behaviour. The Homebrew Codex launcher failed at `--version` because its vendor executable
was missing. The desktop-bundled Codex CLI in `ChatGPT.app`, version
`0.159.0-alpha.12.1`, successfully completed one outside-repository project
skill invocation. It used `.agents/skills/plectis-frontier`, an ephemeral
session, read-only sandbox, ignored user configuration and execution rules,
and the existing authentication without modification. Explicit
`$plectis-frontier` invocation read only `SKILL.md` and `source.json`; it
correctly reported version `0.2.0`, the exact research pin, and the supported
task types. No bootstrap or corpus code, clone, fetch, research or file write
ran. This establishes that client's project skill invocation and instruction
reading; user-level discovery and complete research workflows remain untested.
Claude behaviour remains unverified. No client credentials or installations
were changed to bypass failures.

Focused checks:

```sh
python3 scripts/test_frontier_skill.py
python3 scripts/test_clone_skills.py
python3 scripts/test_companion_package.py
```
