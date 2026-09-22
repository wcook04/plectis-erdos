<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Offline Prove2Me compatibility: one #249 theorem

`scripts/prove2me_compat.py` prepares a source-bound candidate for the
**unconditional finite-level all-base totient-kernel theorem** in the #249
paper. It reads `docs/claims.json`, the paper, the Lean theorem and its
unconditional rank dependency. It writes derived JSON outside the checkout.
It does not use a Prove2Me account or change any claim, proof, paper or
accepted-contribution record.

The chosen paper theorem is `thm:kkernelrank`, backed by
`ErdosProblems.Erdos249.PaperCompleteR8.displayed_all_base_kernel` in
`lean/ErdosProblems/Erdos249/PaperCompleteR8/FullKernelAssemblies.lean`.
`Erdos249257.finrank_allBaseThroughLevelFamily_eq` in
`lean/Erdos249257/AllBaseTotientKernel.lean` proves the exact rank
unconditionally. The registry claim
`all_base_totient_kernel_index_reduction` also documents a *separate*
conditional reusable interface. Neither object proves the irrationality of
the binary totient series. The paper credits Martin's broader affine
independence theorem as prior work; that theorem is not an axiom of this Lean
proof.

## Field map

| Local fact | Prove2Me object | Kept locally or omitted |
| --- | --- | --- |
| Bounded paper theorem, statement, title, source, tags | One native theorem via `submit-problem`; after publication, one proof via `verify` | Source file hashes, exact declaration, paper label and local claim ID remain attached to the packet. |
| Submission and verification responses | Native publish job, theorem ID and proof submission ID | The local response ledger retains status, error and correction lineage. A queued job is never treated as a theorem. |
| Paper passage, Martin credit, conditional-interface distinction and #249 open boundary | Source citation and human explanation where suitable | Full source hashes and the precise limitations remain local. |
| Failed research route or future open #249 continuation | A discussion reference or mission could be chosen in a later scoped project | No mission is created for this already-proved finite-level theorem. |
| Private parent state, credentials, novelty, priority and peer-review claims | None | Intentionally omitted. |

Prove2Me already supports native [theorem and proof publication](https://github.com/prove2me/prove2me_workspace/blob/main/SKILL.md),
[asynchronous publish jobs and correction/deprecation](https://github.com/prove2me/prove2me_workspace/blob/main/references/contribute.md),
and [verification verdicts](https://github.com/prove2me/prove2me_workspace/blob/main/references/prove.md).
This adapter maps to those objects; it does not recreate them.

## Prepare and validate

From a clone with `origin/main` available:

```sh
python3 scripts/prove2me_compat.py prepare --out /tmp/erdos249-p2m/packet.json
python3 scripts/prove2me_compat.py validate \
  --packet /tmp/erdos249-p2m/packet.json \
  --out /tmp/erdos249-p2m/validation.json
```

The second command exits `2` with blockers today. The local pin is Lean
v4.29.1 and Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
Prove2Me's public documentation shows other example environments; the live
list is the authenticated `GET /api/v1/environments` response. A matching
environment has not been observed for this source pin. Record an actual
response in an environment JSON file with `source_url` set to
`https://prove2.me/api/v1/environments`,
`captured_with_authenticated_request: true`, and the returned
`environments` array. That flag is an operator-supplied provenance note,
not cryptographic attestation. Do not invent a matching row.

The [official whole-project import guide](https://github.com/prove2me/prove2me_workspace/blob/main/references/upload_full_project.md)
requires a matching environment, compiled declaration graph and sketch
spans, skeleton subtraction, a locally compiled staged tree, and an exact
original-versus-staged Lean type comparison. This script does **not**
perform those transformations. A staged JSON may supply
`source_sha256`, `declaration_graph_receipt`, `sketch_info_receipt`,
`original_type`, `staged_type`, `compiled_exact_upload_text`,
`compiled_solution`, `formal_statement`, `preamble`, and `solution`.
`validate --environment ... --staged ...` checks the pins, source hash,
type equality and presence of those supplied receipts. It cannot attest
that the named Lean work actually ran; the operator must inspect the
receipts and replay the exact upload text before any submission.

`export` uses the same gates and writes a **draft for review** containing
the prospective `submit-problem` fields and a separate solution string.
It never sends either. The draft is blocked when the source, environment,
type or required receipt is missing or mismatched:

```sh
python3 scripts/prove2me_compat.py export \
  --packet /tmp/erdos249-p2m/packet.json \
  --environment /tmp/erdos249-p2m/environments.json \
  --staged /tmp/erdos249-p2m/staged.json \
  --out /tmp/erdos249-p2m/export.json
```

## Record a later external response

If an authorised person later supplies a saved API response, normalize it
and reconcile it into a packet-specific local attachment:

```sh
python3 scripts/prove2me_compat.py status --kind publish_job \
  --response /tmp/erdos249-p2m/job-response.json \
  --out /tmp/erdos249-p2m/job-event.json
python3 scripts/prove2me_compat.py reconcile \
  --packet /tmp/erdos249-p2m/packet.json \
  --event /tmp/erdos249-p2m/job-event.json \
  --state /tmp/erdos249-p2m/external-state.json
```

Use `--kind verification` for a saved `GET /verify?submission_id=...`
response. Reconciliation requires that its theorem ID was already recorded
from a `PUBLISHED` job. `PENDING` and `COMPILING` never create theorem IDs;
`FAILED` and `ERROR` remain distinct. Repeated events are idempotent, older
pending updates cannot undo terminal results, and conflicting terminal
responses are rejected. A corrected formal statement gets a **new** job and
theorem ID. Record its predecessor with `--replaces-theorem <old-id>` on
the new published event; retain the old record. The adapter does not call
Prove2Me's deprecation API or infer who may do so. The replacement edge is
marked `external_lineage_only_unverified`: it does not establish that the
corrected statement matches this packet. A material source correction needs
a new source-bound packet, a unique platform theorem name, and the same
environment and type checks before any new export.

These local statuses are imported evidence, not independent verification of
response authenticity. `ACCEPTED` records a Prove2Me proof verdict;
`SKETCH_ACCEPTED` records a reduction with open children. Neither changes
the mathematical claim in `docs/claims.json`, grants a novelty verdict, or
marks the #249 irrationality question solved.
