<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Claude Code entry

@AGENTS.override.md

`AGENTS.override.md` is the compact cold-clone entry and the first-contact
contract; `AGENTS.md` is the deep change, authority, and validation contract,
opened after the compact router names the section you need. Importing the deep
contract here spent a whole context window on the file the compact entry exists
to defer. This file carries Claude-specific deltas only.

- Start with the bounded `docs/orientation.json` capsule named by the imported
  instructions; expand one claim or route at a time.
- The imported eight-problem cold-start card is the complete fleet inventory; do
  not query merely to learn which problems exist or what they ask. Query only
  after selecting a problem or mathematical lane from that card.
- Open a mathematical programme with
  `python3 scripts/query_corpus.py --route <programme_route_id>`.
- Treat auto-memory, plans, subagents, and model output as working aids, never
  as proof, claim, source-identity, or publication authority.
- After Lean edits run `python3 scripts/lean_fast_build.py --jobs 2
  --changed-from HEAD`; full roots are release-only.
- This self-contained public repository is a projection from a larger ongoing
  formal-mathematics workflow. It is not an entrypoint into any private
  development system; do not infer private paths, claims, or machinery.
