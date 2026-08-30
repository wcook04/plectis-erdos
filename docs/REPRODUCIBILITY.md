<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Reproduce the public release

This page is the clean-clone runbook for the standalone
[`plectis-lean-erdos249-257`](https://github.com/wcook04/plectis-lean-erdos249-257)
repository. It uses only files in this checkout and ordinary public tools. The
private `ai_workflow` repository, a sibling checkout, an inherited shell state,
and a pre-existing build cache are not prerequisites.

## 1. Start with a complete committed checkout

Use a full clone when following source coordinates or any gate that compares
the pinned history. A shallow clone is intentionally an environment with
insufficient history; `verify_claims.py` reports that condition separately
and exits `2` rather than presenting it as a mathematical failure.

```sh
git clone https://github.com/wcook04/plectis-lean-erdos249-257.git
cd plectis-lean-erdos249-257
git fetch --tags --force
git status --short
```

Run the following static, no-Lean first impression. These commands use the
committed Python and JSON surfaces and do not need Lake, elan, or Mathlib:

```sh
python3 -VV
python3 scripts/test_dependency_lock_contract.py
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/build_module_graph.py --check
python3 scripts/refresh_source_coordinates.py --check
python3 scripts/test_downstream_example_contract.py
python3 scripts/query_corpus.py --tour --format card
```

The quick check is a bounded navigation check, not a proof build. It confirms
that the eight-problem entry surface, both public Lean roots, claim/source
routes, paper handles, open-boundary routes, and environment guidance are
present before any toolchain download.

## 2. Reproduce the pinned Lean environment

Install [elan](https://leanprover-community.github.io/get_started.html) once
using its documented installer. From the repository root, elan reads
[`lean-toolchain`](../lean-toolchain), which selects
`leanprover/lean4:v4.29.1`; [`lake-manifest.json`](../lake-manifest.json)
pins the Mathlib revision and its transitive dependencies.

```sh
lake --version
python3 scripts/test_dependency_lock_contract.py
lake exe cache get
```

The cache command is optional for correctness but avoids recompiling Mathlib
from source. It may download several gigabytes. A cache is an acceleration,
not authority: the toolchain file and manifest are the reproducibility inputs.

Build the two supported public roots first, then the explicitly supported
non-default consumers:

```sh
python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness
lake build ErdosProblems
lake build Examples
lake build FormalConjecturesAdapter
lake build FormalConjecturesVariants
lake build ResidualBench
python3 scripts/build_lean_dependency_index.py --check
```

`Erdos249257` and `ErdosProblems` are the default library targets. `Examples`
is a downstream consumer and is deliberately not a default target. The other
targets are separate adapter, variant, and residual-check surfaces; their
declarations do not enlarge the reviewed mathematical corpus.

## 3. Run the release-surface checks

These checks are ordered from cheap source/navigation checks to the broader
release gate. They remain repository-local and do not require the private
factory:

```sh
python3 scripts/check_release.py
python3 scripts/test_projection_checkout_independence.py
python3 scripts/test_root_import_closure.py
python3 scripts/test_check_release_ref.py
```

The clean-ref wrapper is the later immutable-snapshot gate. It resolves one
commit, creates a disposable local clone, and runs the configured release
checks there; uncommitted files in the caller's checkout are excluded. A
bounded snapshot probe can verify that preparation without replaying the full
gate:

```sh
python3 scripts/check_release_ref.py --ref HEAD --probe-only
```

Do not read a successful static check as a terminal release clearance. The
final release pair still requires one clean immutable SHA and the separately
managed terminal Palomar and Comparator receipts. Those gates may be
resource-intensive and are not substituted by this runbook.

## 4. Reproduce a changed checkout safely

Keep generated projections in dependency order. After changing an owning
source, use its builder and then its `--check` mode; do not hand-edit a
generated JSON or Markdown projection. Before a scoped commit, confirm that
the worktree contains no unrelated path changes and that every claimed path
is clean after landing.

The supported command vocabulary is intentionally environment-neutral:

```sh
python3 scripts/build_corpus_descriptor.py --check
python3 scripts/build_module_graph.py --check
python3 scripts/refresh_source_coordinates.py --check
python3 scripts/build_lean_dependency_index.py --check
```

If a command reports stale generated output, regenerate from the named owning
builder and commit the source plus all projections that builder declares. Do
not copy files from another checkout or rely on a developer's `.lake` state.

## Resource and boundary notes

- Python-only navigation is the fast cold-clone path; Python `3.11+` is
  required by the repository's TOML and standard-library interfaces.
- The pinned Mathlib cache is large. Allow the cache download and the Lean
  build their documented time and disk budget; `--jobs 2` is the supported
  bounded local build setting.
- `lake build` proves the checked Lean targets, not the open Erdős problems.
  The public claim registry and papers retain the exact conditional results
  and open boundary.
- `docs/problems.json`, `docs/claims.json`, the paper corpus, and the
  generated declaration/dependency projections are public evidence surfaces;
  this runbook describes how to replay them and is not proof authority.
