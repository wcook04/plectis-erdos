<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Claude Code entry

@AGENTS.override.md

`AGENTS.override.md` is the compact cold-clone router. `AGENTS.md` is the deep
project change and authority contract; open its relevant section after routing.
The legacy deep-import token is `@AGENTS.md`; do not expand it before the compact
router selects a lane. This file carries Claude-specific deltas only.

- Start with the bounded `docs/orientation.json` capsule named by the imported
  instructions; expand one claim or route at a time.
- For mathematics, Lean, status, or progress tasks, execute the shared
  machine-first `query_corpus.py --ask` route before plans, subagents, paper
  reading, or prose synthesis.
- Open a mathematical programme with
  `python3 scripts/query_corpus.py --route <programme_route_id>`.
- Treat auto-memory, plans, subagents, and model output as working aids, never
  as proof, claim, source-identity, or publication authority.
- Keep verification loops scoped to the selected change class. Use the public
  checks in `AGENTS.md`, and run `lake build` after Lean changes.
- This self-contained public repository is a projection from a larger ongoing
  formal-mathematics workflow. It is not an entrypoint into any private
  development system; do not infer private paths, claims, or machinery.
