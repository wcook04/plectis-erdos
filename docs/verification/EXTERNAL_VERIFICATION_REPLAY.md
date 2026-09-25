<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Independent replay and immutable release identity

GitHub Actions and independent replay answer different questions. The Actions
job checks the full selected interface set on the proposed source commit. The
replay command below lets a reviewer execute one bounded interface on a separate
Linux machine. Neither is mathematical peer review, a novelty assessment, or a
claim that an open Erdős problem has been solved.

## Pull-request merge gate

Before merging a release candidate, record the pull-request head commit and
tree. Wait for the latest `Lean CI` run for that exact head to conclude
`success`, and inspect the final conclusions of every applicable job and matrix
leg: `change_scope`, `build`, `external-verification`, `first-contact`,
`shallow-clone-is-an-environment-problem`, and `release-surfaces`. Accept a
skipped job only when the workflow's change-scope rule explicitly explains it.
If the head changes, repeat this check; queued, running, cancelled, or missing
conclusions are not a merge gate.

When `external-verification` applies, require its successful final conclusion
and download `external-verification-receipt-<head-commit>`. Its
`external-verification-receipt.json` must have `phase: final`, `result: pass`,
`repository_commit` and `expected_repository_commit` equal to that head,
`repository_tree` equal to its tree, and passing positive and adversarial
Comparator controls under the pinned toolchain and axiom budget. Retain the
receipt with the review record. An artifact upload or a green run for a
different commit does not satisfy this check.

`gh pr merge --auto --merge` does not enforce this order when branch protection
has no required status checks: the pull request can merge while CI is still
running. Complete the checks above before requesting merge. Required status
checks can enforce the order at GitHub, but their configuration must be
verified rather than inferred from the workflow file.

The bounded replay compares
`Erdos249257.ExternalVerification.finrank_totientKernelThroughLevelFamily_eq`
against the separately declared statement in `ExternalVerification.Challenge`.
It also runs the one-theorem mismatch fixture and requires Comparator's exact
statement-mismatch diagnostic. The configuration is
`verification/comparator-replay.json`; it is intentionally smaller than the
CI configuration.

The named `weighted-support` unit applies the same isolated runner to the
#257 theorem `Erdos249257.ExternalVerification.divisibilityWeightedClaim`.
Its positive configuration selects that theorem alone. Its negative solution
adds the theorem itself as a hypothesis, changing the statement while making
the altered declaration trivial. The replay passes only if the positive
comparison succeeds and Comparator rejects that exact mismatch. The unit's
configuration, negative Lean source, axiom budget, and tool revisions are in
the immutable release contract. The
[merged-main CI run at `7e33a58b`](https://github.com/wcook04/plectis-erdos/actions/runs/36096621946)
has a downloaded final `pass` receipt for commit
`7e33a58bb86180013b1fb855cdd8aaff1d7f9057` and tree
`86f3bed93955112257c1ecd1c4ca721468d1a870`. Its `weighted-support`
row records positive Comparator exit 0 and deliberate statement-mismatch exit
1 with the expected diagnostic observed. The receipt SHA-256 is
`3dc7a6c42db467dd9b6afba74bf4fd9a1facf5c92d346ce201d3c7e0bdc06699`.
This is source-bound verification in this repository's CI for that exact commit;
it is not an independent Linux replay or a result for every later source commit.

## Reviewer replay

Start from the `source.commit` and `source.tree` fields of an attached
`external-verification-release-manifest-<commit>.json`. Do not substitute
`main`, `HEAD`, a pull-request merge SHA, or the current tip of any branch.

On Linux with Git, Elan/Lake, Go, systemd, and a user systemd manager (or
passwordless permission to create a non-privileged system unit), inspect the
plan first:

```sh
python3 scripts/replay_external_verification.py plan \
  --source-commit <40-hex-source-commit> \
  --source-tree <40-hex-source-tree>
```

Then run the isolated replay:

```sh
python3 scripts/replay_external_verification.py run \
  --source-commit <40-hex-source-commit> \
  --source-tree <40-hex-source-tree> \
  --output external-verification-replay-receipt.json
```

For the weighted #257 theorem, select `--unit weighted-support`. From a clean
public clone at a selected committed revision, this copyable command obtains
that revision's immutable commit and tree:

```sh
python3 scripts/replay_external_verification.py run --unit weighted-support \
  --source-commit "$(git rev-parse HEAD^{commit})" \
  --source-tree "$(git rev-parse HEAD^{tree})" \
  --output weighted-support-replay-receipt.json
```

Run it on Linux with the systemd and pinned-tool prerequisites above. A
successful `weighted-support` command writes a receipt naming the source,
statement, axiom budget, checker revisions, positive verdict, deliberate
mismatch verdict, and four contract failure controls. Before building Comparator,
it runs
the source commit's adversarial release test from the isolated checkout. The
receipt binds that test file's digest and output digest and requires explicit
rejections of a changed challenge module, an undeclared axiom, duplicate
theorem IDs, and a missing runtime receipt. A missing or failed control makes
the replay fail. These four are configuration and release-manifest controls;
the deliberate statement mismatch is the separate negative Comparator run.
A missing or failing receipt cannot support a release claim. The
release-manifest validator rejects a missing runtime receipt, and the replay
contract rejects a changed challenge or axiom budget. These checks do not
establish novelty, historical correspondence, or mathematical peer review.

The selected `weighted-support` contract pins its challenge module as well as
its one theorem and axiom budget. The replay refuses a changed challenge in
either configuration, an extra or duplicate theorem name, and an undeclared
axiom before running Comparator. Its receipt records elapsed time, the isolated
source checkout, cache download time and digest, machine type, CPU count, and
the largest child-process memory high-water mark on Linux. Shared cache warmth
is reported as unmeasured; compare cold and warm runs explicitly if timing
matters.
The CI runtime receipt also names this one-theorem unit, its exact configuration
digests, and both Comparator verdicts. A CI receipt and a passing independent
Linux replay are separate evidence; the latter has its own receipt schema.

The runner fetches exactly the supplied commit, checks its tree, rejects the
synthetic merge-message form used by pull-request test merges, and builds these
exact tool revisions:

- Comparator `789279735fe44c1c05dc54bb9f46ba4d9b8c7611`
- lean4export `6f4e21dd70c3c11d7fbd07d39e3192792c657448`
- landrun `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`

Comparator runs in a systemd transient unit with network address families
restricted. There is no insecure fallback. The resulting receipt records the
source commit and tree, contract and configuration digests, observed tool
revisions and binary digests, sandbox mode, positive verdict, and adversarial
negative verdict. Its `execution_surface` explicitly distinguishes it from
GitHub Actions.

## Return a replay result

Use the existing [research progress or correction form](https://github.com/wcook04/plectis-erdos/issues/new?template=research_progress.yml)
for a successful, failed, or incomplete outside run. A completed independent
replay should include the full receipt JSON (attached or linked), its SHA-256,
the source commit and tree, Linux and systemd mode, the positive and deliberate
mismatch verdicts, and the `failure_controls` result with its four `observed`
control IDs for `weighted-support`. Say what was unclear on first use and how
you want the work credited. If setup stops before a receipt can be written,
give the exact command and diagnostic instead; do not select the
independent-replay evidence class for an uncompleted run. Do not post
credentials, private host details, or unpublished material.

## Release-cut contract

Local release validation can check a committed source candidate before it is
published. In `docs/claims.json`, that state is
`committed_checkpoint_pending_remote_publication` with `public_tag: null`.
It asserts a source identity, not a kernel pass or public release. A published
checkpoint instead requires an annotated `formal-source-...` tag resolving to
that exact source commit. The artifact procedure below applies to a published
release and retains its stronger tag requirement.

An Actions artifact is temporary evidence, not a durable release identity. A
release carrying the external-verification claim must attach both:

- `external-verification-receipt-<source-commit>.json`, the final successful
  full selected-interface runtime receipt; and
- `external-verification-release-manifest-<source-commit>.json`, the digest
  crosswalk for the receipt, manifest, Comparator inputs, public packet, and all
  eight problem papers. The same manifest binds the machine-readable paper
  inventory and the exact [Formal Conjectures statement
  crosswalk](FORMAL_CONJECTURES_CROSSWALK.md) used to place the eight
  programmes against the upstream corpus.

The source commit must already be tagged, and the tag must resolve to that exact
commit. From the tagged checkout, build the manifest with:

```sh
python3 scripts/external_verification_release.py build \
  --source-commit <40-hex-source-commit> \
  --source-tree <40-hex-source-tree> \
  --release-tag <release-tag> \
  --receipt <downloaded-final-pass-receipt.json> \
  --output external-verification-release-manifest-<source-commit>.json
```

Before upload, replay the validation from the same tagged checkout:

```sh
python3 scripts/external_verification_release.py validate \
  --manifest external-verification-release-manifest-<source-commit>.json \
  --receipt <downloaded-final-pass-receipt.json>
```

The builder refuses a non-passing or stale receipt, a checkout/commit/tree
mismatch, a floating release tag, a synthetic pull-request merge commit,
changed Comparator pins, an incomplete binary-digest set, a theorem-set or
axiom-budget mismatch, and stale paper or packet bytes. Every tracked-artifact
URL in the manifest uses the full source commit. The manifest is a release
asset rather than a tracked file because a file cannot truthfully contain the
commit id and digest of the commit that first contains its own bytes.

The release is not complete until both files are attached to the release and
their downloaded bytes match the manifest. Creating the tag, release, or assets
is deliberately outside these scripts; it remains an explicit publication
action.
