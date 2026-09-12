<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Reproduce the public release

Start by following one published result to its source. You can do that with
Git and Python, then install Lean if you want to check the proof yourself.
Everything below uses this public checkout and public tools.

| What you want to do | Start here | What you need |
|---|---|---|
| Follow one result to its evidence | [Try one claim](#try-one-claim-without-lean) | Git and Python 3.11 or later |
| Rerun a finite computation | [Reproduce the #251 computations](#reproduce-a-finite-computation) | Python 3.11 or later; the first run needs no extra packages |
| Check a documentation edit | [Check a documentation change](#check-a-documentation-change) | Python; no Lean installation |
| Compile a proof | [Set up Lean](#2-reproduce-the-pinned-lean-environment) | elan, the pinned dependencies, and space for several gigabytes of cache |
| Reproduce all public checks | [Release checks](#3-run-the-release-surface-checks) | Lean plus the pinned Python validation tools |

Commands run from the repository root. Shell setup below uses macOS/Linux
syntax; on Windows, use WSL for the same commands. To read the mathematics
without installing anything, return to [the papers](../paper/README.md).

## 1. Start with a complete committed checkout

Keep the commit history: some checks compare the current files with a recorded
source version. The following clone keeps that history while fetching old file
contents only when needed.

```sh
git clone --filter=blob:none https://github.com/wcook04/plectis-erdos.git
cd plectis-erdos
git fetch --tags --force
git status --short
```

The current checkout is hundreds of megabytes; its historical generated files
are much larger. `--filter=blob:none` reduces that initial transfer without
making the clone shallow. If you already used `--depth`, fetch the missing
history with `git fetch --unshallow --tags` before running commands that
compare pinned revisions. The default `verify_claims.py` environment
diagnostic reports missing required history as an environment problem
(exit `2`). That result does not mean a proof failed. In a shallow clone,
`--gates` skips the programs that require history. The `--claim` and
`--verify-all` modes inspect the current checkout and can succeed in a
shallow clone.

### Try one claim without Lean

After cloning, run:

```sh
python3 scripts/verify_claims.py --claim eb_full_support
```

The output shows the published statement, its declaration and source line,
the selected Comparator interface, the recorded release, and the claim's
limits. For this example, the status is **known mathematics formalised here**.
The command looks for the recorded declaration names near their recorded
source lines in your current checkout and tests whether the claim uses a
recognised status. It also prints the paper and Comparator references. It
does not load the recorded historical revision, run Lean or prove the
statement again.
[Section 2](#2-reproduce-the-pinned-lean-environment) gives the proof-build route.

For this claim, the verifier's `WRITTEN UP IN` entry points to the archived
joint manuscript used in the recorded release. For the current exposition,
read the [#257 short paper](../paper/257/erdos-257-mersenne-support-subseries.pdf).
The historical source anchor and the current reading route serve different
purposes; [the paper index](../paper/README.md) keeps the current papers together.

For the full claim inventory, use `python3 scripts/verify_claims.py --verify-all`.
This mode also uses the current checkout. It additionally reports missing
paper labels and references to claim IDs absent from the inventory.

### Reproduce a finite computation

The #251 paper includes three computations with saved results and public
programs. Start with the complete continued-fraction calculation:

```sh
python3 research/experiments/erdos251/replay.py
```

Expect `matched_recorded_result: true`; this takes about four seconds on the
maintainer's machine and uses only the Python standard library. The
[computation guide](../research/experiments/erdos251/README.md) explains the
other two runs, their memory and dependency requirements, and how to change
an input. Matching these finite results does not prove irrationality or
cofinality, and the programs do not run Lean.

### Check the clone's navigation and metadata

For a broader check of the reader routes, run:

```sh
python3 -VV
python3 scripts/check_cold_clone_comprehension.py --quick
python3 scripts/query_corpus.py --tour --format card
```

The quick command compares the documented problem selectors, entry commands
and file counts with the recorded indexes. For the large generated index,
it compares current file hashes with the saved hash record; if that record
is missing or stale, it recomputes the index for comparison. The tour lists
the available queries. Neither command compiles a proof.

To explore one problem, ask for its paper and source routes. For example:

```sh
python3 scripts/query_corpus.py --route erdos_251
```

Replace `251` with any of `68`, `243`, `249`, `257`, `269`, `1041` or `1049`
to follow another problem. The result links its paper, source modules and
remaining questions.
[The source map](SOURCE_MAP.md) offers a reading route through the same work;
[the query reference](agents/SEMANTIC_COMPILER.md) explains the more detailed
selectors.

### Check a documentation change

For a small documentation contribution, check the reader routes and their
links before opening a pull request:

```sh
python3 scripts/test_human_first_contact.py
```

For a tooling change, also run that tool's test and include the result in the
pull request. Changes to mathematical statements or Lean proofs require the
corresponding proof checks below.

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

Check one real published theorem module first. This is the short feedback path
for confirming that the toolchain, dependency cache, and project all work;
it uses a small #249 module:

```sh
python3 scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems.Erdos249.PeriodMultipleEscape
```

To follow the earlier `eb_full_support` claim into a proof build, its
declaration lives in the larger `CertificateKernel` module:

```sh
python3 scripts/lean_fast_build.py --jobs 2 Erdos249257.CertificateKernel
```

These commands build the current checkout. The claim verifier also names the
recorded source revision; keep that identity with any report about reproducing
a particular release. [External replay](verification/EXTERNAL_VERIFICATION_REPLAY.md)
describes checks tied to an immutable source commit.

For a complete release replay, build the two supported public roots and the
explicitly supported non-default consumers through one host-shared wrapper
invocation:

```sh
python3 scripts/lean_fast_build.py --jobs 2 --lake-staleness \
  Erdos249257 ErdosProblems Examples FormalConjecturesAdapter \
  FormalConjecturesVariants ResidualBench
python3 scripts/build_lean_dependency_index.py --check --full-check
```

`Erdos249257` and `ErdosProblems` are the default libraries. `Examples` checks
that another Lean project can use the library; read its imports and example
declarations in [research/examples/Examples.lean](../research/examples/Examples.lean).
The remaining targets check
adapters, statement variants and residual examples; building them does not
add reviewed claims to the mathematical record.

The wrapper coordinates builds on the same machine. Equivalent requests share
one running job; different heavy builds queue, and compatible clones can
reuse build files. Keep using the wrapper if another build is in progress.
The [concurrent-validation guide](../skills/lean-concurrent-validation/SKILL.md)
explains detached operation, cache locations, storage sharing and exit codes.
A successful build means Lean accepted the requested modules. The exact
statements and their limits are in the source and [claim record](claims.json).

## 3. Run the release-surface checks

The release checks inspect claim records, links, generated files, licences and
other published metadata. Install their Python dependencies in a local virtual
environment first. CI uses Python 3.12.9 with this hash-pinned requirements file.

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install --disable-pip-version-check --no-cache-dir --require-hashes \
  --requirement scripts/requirements-release.txt
python3 scripts/check_release.py
```

The Lean build and this Python check answer separate questions. A publication
also needs its selected external verification receipts, described in
[the verification guide](verification/README.md). A successful static check
alone is not the complete release decision.

The clean-ref wrapper is the later immutable-snapshot gate. It resolves one
commit, creates a disposable local clone, and runs the configured release
checks there; uncommitted files in the caller's checkout are excluded. A
bounded snapshot probe can verify that preparation without replaying the full
gate:

```sh
python3 scripts/check_release_ref.py --ref HEAD --probe-only
```

## 4. Reproduce a changed checkout safely

Keep generated projections in dependency order. After changing an owning
source, use its builder and then its `--check` mode; do not hand-edit a
generated JSON or Markdown projection. Review and commit only the files
belonging to your change. If other work is present in the checkout, preserve
it and keep it out of your commit.

These checks cover the dependency lock, generated indexes and source links:

```sh
python3 scripts/test_dependency_lock_contract.py
python3 scripts/build_corpus_descriptor.py --check
python3 scripts/build_module_graph.py --check
python3 scripts/refresh_source_coordinates.py --check
python3 scripts/build_lean_dependency_index.py --check
python3 scripts/test_downstream_example_contract.py
```

If a command reports stale generated output, regenerate from the named owning
builder and commit the source plus all projections that builder declares. Do
not copy files from another checkout or rely on a developer's `.lake` state.
For a full in-memory rebuild of the semantic index, use
`python3 scripts/build_semantic_corpus.py --check --full-check`. The ordinary
dependency-index `--check` never compiles; an intentional release
export uses `--check --full-check` after the coordinated Lean build above.

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

If a command fails, include the command, its output and `git rev-parse HEAD`
when [reporting the problem](../CONTRIBUTING.md). That gives someone else the
same source version and a way to reproduce it.

[Back to the documentation](README.md) · [How the repository works](ARCHITECTURE.md)
