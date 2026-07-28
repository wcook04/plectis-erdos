<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Claude Code entry

@AGENTS.md

`AGENTS.md` is the shared project instruction and authority-routing surface.
This file carries Claude-specific deltas only.

- Start with the bounded `docs/orientation.json` capsule named by the imported
  instructions; expand one claim or route at a time.
- The imported six-problem cold-start card is the complete fleet inventory; do
  not query merely to learn which problems exist or what they ask. Query only
  after selecting a problem or mathematical lane from that card.
- Open a mathematical programme with
  `python3 scripts/query_corpus.py --route <programme_route_id>`.
- Treat auto-memory, plans, subagents, and model output as working aids, never
  as proof, claim, source-identity, or publication authority.
- Keep verification loops scoped to the selected change class. Use the public
  checks in `AGENTS.md`, and run `lake build` after Lean changes.
- This self-contained public repository is a projection from a larger ongoing
  formal-mathematics workflow. It is not an entrypoint into any private
  development system; do not infer private paths, claims, or machinery.
