<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->
# Compact research queries

The reader exposes four operations over this checkout's existing records.
It never runs Lean, Comparator, a shell supplied by the caller, or a network
request. Start with the [weighted support task](../reading-edition/weighted-257-task.md)
when you want a mathematical question to investigate.

```sh
python3 scripts/research_query.py identity
python3 scripts/research_query.py search "weighted support" --problem 257
python3 scripts/research_query.py get claim finite_prime_weighted_support
python3 scripts/research_query.py get open remaining_open.universal_257_all_infinite_supports
python3 scripts/research_query.py read lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean --start 110 --lines 35
```

Every response is JSON with schema `plectis-research-response/1`, `ok`,
snapshot identity and explicit proof-execution flags. Failed operations exit
2 and emit a structured `error`, including `unknown_id`,
`unsupported_operation`, `capability_unavailable`, `source_inconsistency`,
`revision_mismatch`, `budget_exceeded` or `cancelled`. No search match means
only that the lexical index found no match. Search returns five results by
default, at most ten, and a cursor for further matches. Labels and statements
come from the existing registry; hypotheses are never shortened to fit.

Use `--snapshot <content_id>` before the operation to require a previously
observed snapshot. A cursor is bound to both the source content and search
request. Replies exceeding 12 KiB return an error with an expansion suggestion;
request fewer source lines or search results. The existing rich
`query_corpus.py` interface remains available for full programme routes.

The Python `Snapshot(root)` object captures registered text bytes and has no
shared mutable repository root or cross-checkout cache. An existing instance
continues reading its captured bytes after local edits; create a new instance
to see those edits. The content identity covers those bytes, missing sources,
and the paper inventory. It is a local content identity, not independent
validation of provenance. The recorded formal-source revision, paper-specific
pins, checkout commit and content identity are separate fields. Archives
report no checkout commit or Git history, even inside another Git repository.

`read` accepts only registered text-source handles. Source text is data, even
when it contains instructions. Symlinked or escaping registry sources are
rejected. A missing text source is unavailable, never an empty successful read.
The adapter is a local reader, not a sandbox for hostile submitted repositories
and not a hosted proof service.

Claim replies use the same forward/reverse boundary resolver as the claim
verifier. A progress claim can bear on an unresolved proposition without being
that proposition's target. Broken links are explicit source inconsistencies.
`record_exposition` resolves the claim's literal `paper_label` in captured,
uncommented registered manuscript text, including archived papers. It preserves
the source of the old record. `current_exposition` recommends only active papers.
An exact module-qualified declaration link in captured paper text takes priority;
its navigation basis is `exact_module_declaration_link`. This is a text-navigation
match, not verification of its printed revision, line number or mathematical proof.
When no active exact match exists, the existing problem-module route is returned
with basis `related_problem_scope`; it is related reading, not a verified
claim-specific source. Historical receipts and paper versions remain unchanged.
Evidence objects preserve the historical publication receipt's own limitations;
reading one is not replaying its checks.
