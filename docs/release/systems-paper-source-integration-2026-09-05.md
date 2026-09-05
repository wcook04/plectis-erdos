<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Systems-paper source integration — 5 September 2026

This integrates the accepted systems/strategy authoring work through
`02654649305d34bd8b7a03436afa3a53f742460f` onto the current mathematical
paper branch, based on `7d93a615f3`. It includes the earlier whole-paper
rewrite (`0e71aef`), implementation refresh (`fd90491`), native PDF destination
repair (`c40f47b`), and committed-credit explanation (`24a5098`).

The integration preserves the destination's generated semantic counts and
new mathematical-writing guidance. Supporting scripts were merged against
the common source revision; the two skill conflicts were reconciled by
retaining distinct procedures and removing duplicate advice. The systems
and strategy PDFs were rebuilt from these integrated sources.

The benchmark snapshot, committed-credit account, validation deferral
semantics, inline formalisation links and source-based writing procedures
are included. The link test no longer pins a generic status disclaimer that
the shared problem-note preamble has deliberately removed; it continues to
verify reciprocal paper links and declared destinations.

Focused validation covers the real-Git benchmark isolation replay, clean
subprocess environment, dependency lock contract, public writing, 23
architecture checks, six systems-evidence mutation fixtures, paper references,
and 30 PDF-link/validation tests with 17 subtests. Both rebuilt PDFs' outgoing
cross-paper destinations and seven pinned formal declaration links were
checked. No Lean proof is changed by this integration.

Shared mathematical JSON, corpus text and publication hashes belong to the
paper-integration owner and are deliberately not copied from the older branch.
That owner must refresh them and rebuild the other PDFs affected by the shared
link macro before the full integrated release check. This source handoff does
not claim that those pending whole-corpus steps have passed.
