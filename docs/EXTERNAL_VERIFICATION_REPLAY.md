<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Independent replay and immutable release identity

GitHub Actions and independent replay answer different questions. The Actions
job checks all nineteen selected interfaces on the proposed source commit. The
replay command below lets a reviewer execute one bounded interface on a separate
Linux machine. Neither is mathematical peer review, a novelty assessment, or a
claim that an open Erdős problem has been solved.

The bounded replay compares
`Erdos249257.ExternalVerification.finrank_totientKernelThroughLevelFamily_eq`
against the separately declared statement in `ExternalVerification.Challenge`.
It also runs the one-theorem mismatch fixture and requires Comparator's exact
statement-mismatch diagnostic. The configuration is
`verification/comparator-replay.json`; it is intentionally smaller than the
nineteen-interface CI configuration.

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

## Release-cut contract

An Actions artifact is temporary evidence, not a durable release identity. A
release carrying the external-verification claim must attach both:

- `external-verification-receipt-<source-commit>.json`, the final successful
  nineteen-interface runtime receipt; and
- `external-verification-release-manifest-<source-commit>.json`, the digest
  crosswalk for the receipt, manifest, Comparator inputs, public packet, and all
  eight problem papers.

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
