<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Offline Prove2Me compatibility: one theorem at a time

`scripts/prove2me_compat.py` prepares a source-bound, **offline** candidate for
one theorem. Its preferred showcase is the #257 reciprocal-summable support
result: if an infinite set of positive integers $A$ satisfies
$\sum_{a\in A}1/a<\infty$, then $\sum_{a\in A}1/(b^a-1)$ is irrational for
every integer base $b\ge2$. The exact Lean declaration is
`Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal` in
`lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean`; the paper states
it at `res:reciprocal-support` in
`paper/257/erdos-257-mersenne-support-subseries.tex`. The registered claim is
`reciprocal_summable_support`, with status `formalised here`. Erdős stated
this all-base extension after his pairwise-coprime case; the paper supplies
an averaging proof. The hypothesis does not cover every infinite support, so
the universal #257 assertion remains open.

The earlier #249 finite-level totient-kernel theorem remains selectable as a
technical prototype with `--unit erdos249_all_base_totient_kernel_paper_theorem`.
Its registered claim is `all_base_totient_kernel_index_reduction`, and it does
not settle the irrationality of the binary totient series. Each packet binds
one unit, claim row, Lean source, paper anchor, source hashes, local pin and
public-main source commit. The adapter never changes a mathematical claim,
proof, paper or accepted-contribution record.

## Field map

| Local fact | Prove2Me object | Local attachment or exclusion |
| --- | --- | --- |
| Selected theorem statement, title, source and tags | One native theorem via `submit-problem`; after publication, one proof via `verify` | Source hashes, exact declaration, paper label and claim ID stay in the packet. |
| Submission and verification responses | Native publish job, theorem ID and proof submission ID | Local response state retains status, error and correction lineage. A queued job is not a theorem. |
| Paper passage, Erdős attribution and exact open boundary | Source citation and human explanation where suitable | The full evidence and limitations stay local. |
| Private parent state, credentials, novelty, priority and peer-review claims | None | Omitted. |

Prove2Me documents native [theorem and proof publication](https://github.com/prove2me/prove2me_workspace/blob/main/SKILL.md),
[asynchronous publish jobs and correction/deprecation](https://github.com/prove2me/prove2me_workspace/blob/main/references/contribute.md),
and [verification verdicts](https://github.com/prove2me/prove2me_workspace/blob/main/references/prove.md).
The adapter maps to those objects; it does not recreate them.

## Prepare and validate

From a clone with `origin/main` available, write the preferred #257 packet
outside the checkout:

```sh
python3 scripts/prove2me_compat.py prepare --out /tmp/erdos257-p2m/packet.json
python3 scripts/prove2me_compat.py validate \
  --packet /tmp/erdos257-p2m/packet.json \
  --out /tmp/erdos257-p2m/validation.json
```

For the earlier #249 packet, use:

```sh
python3 scripts/prove2me_compat.py prepare \
  --unit erdos249_all_base_totient_kernel_paper_theorem \
  --out /tmp/erdos249-p2m/packet.json
```

The bare validation command exits `2` with blockers. The local pin is Lean
v4.29.1 and Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
An authenticated, read-only `GET /api/v1/environments` on 23 September 2026
(UK time) returned these available pairs:

| Lean | Mathlib revision |
| --- | --- |
| v4.33.1 | `0df444a360eaa60ab8c11dca51a86af692955474` |
| v4.29.0-rc3 | `777aaa61dcd2a1258d2b4962dbe983ede4d23b2e` |
| v4.30.0 | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |

None matches the repository pin. The available environments can change; check
the live endpoint again before a staged port. For a local validation receipt,
record an actual response with `source_url` set to
`https://prove2.me/api/v1/environments`,
`captured_with_authenticated_request: true`, and its returned `environments`
array. This is a provenance note, not cryptographic attestation. Do not invent
a matching row or treat a different environment as compatible. No theorem or
proof was submitted during this compatibility check.

The [official whole-project import guide](https://github.com/prove2me/prove2me_workspace/blob/main/references/upload_full_project.md)
requires a matching environment, compiled declaration graph and sketch spans,
skeleton subtraction, a locally compiled staged tree, and an exact
original-versus-staged Lean type comparison. This script does **not** perform
those transformations. A staged JSON may supply `source_sha256`,
`declaration_graph_receipt`, `sketch_info_receipt`, `original_type`,
`staged_type`, `compiled_exact_upload_text`, `compiled_solution`,
`formal_statement`, `preamble`, and `solution`. `validate --environment ...
--staged ...` checks the selected theorem name, source hash, pin, type equality
and presence of those supplied receipts. It cannot attest that the named Lean
work actually ran or that the staged statement represents the source theorem;
the operator must inspect the extractor output and replay the exact upload
text before any submission.

`export` uses the same gates and writes a **draft for review** containing the
prospective `submit-problem` fields and a separate solution string. It never
sends either. The draft is blocked when the source, environment, type or
required receipt is missing or mismatched:

```sh
python3 scripts/prove2me_compat.py export \
  --packet /tmp/erdos257-p2m/packet.json \
  --environment /tmp/erdos257-p2m/environments.json \
  --staged /tmp/erdos257-p2m/staged.json \
  --out /tmp/erdos257-p2m/export.json
```

## Record a later external response

If an authorised person later supplies a saved API response, normalize it
and reconcile it into a packet-specific local attachment:

```sh
python3 scripts/prove2me_compat.py status --kind publish_job \
  --response /tmp/erdos257-p2m/job-response.json \
  --out /tmp/erdos257-p2m/job-event.json
python3 scripts/prove2me_compat.py reconcile \
  --packet /tmp/erdos257-p2m/packet.json \
  --event /tmp/erdos257-p2m/job-event.json \
  --state /tmp/erdos257-p2m/external-state.json
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
marks the universal #257 or #249 question solved.
