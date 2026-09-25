<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Reproduce the public release

Start by following one published result to its source. You can do that with
Git and Python, then install Lean if you want to check the proof yourself.
Everything below uses this public checkout and public tools.

| What you want to do | Start here | What you need |
|---|---|---|
| Follow one result to its evidence | [Try one claim](#try-one-claim-without-lean) | Git and Python 3.11 or later |
| Inspect an accepted native #243 or #257 proof | [Native theorem reader routes](research-commons/README.md#native-prove2me-theorems) | A web browser; the public packets print the accepted Solutions without sign-in |
| Replay the #257 weighted theorem against a separate statement | [Weighted theorem replay](verification/EXTERNAL_VERIFICATION_REPLAY.md#reviewer-replay) | Linux, Git, Python 3.11+, Elan/Lake, Go, and systemd |
| Rerun the #257 exact-rational example | [Try the late rejection](#reproduce-the-257-exact-rational-example) | Python 3.11 or later; no extra packages |
| Rerun a #251 finite computation | [Reproduce the #251 computations](#reproduce-a-finite-computation) | Python 3.11 or later; the first run needs no extra packages |
| Check a documentation edit | [Check a documentation change](#check-a-documentation-change) | Python; no Lean installation |
| Compile a proof | [Set up Lean](#2-reproduce-the-pinned-lean-environment) | elan, the pinned dependencies, and space for several gigabytes of cache |
| Import the library in another project | [Use it as a dependency](#use-the-library-in-another-lean-project) | The same Lean toolchain and the library's dependencies |
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

### Reproduce the #257 exact-rational example

Run this from the repository root with Python 3.11 or later. It uses only the
standard library and needs no Lean installation:

```sh
python3 research/experiments/sparse_interpolation/late_rejection.py
```

In the JSON output, find the certificate with `"target": "189/388"`.
Expect `"first_rejection": 17`, with remainder
`9291822600689/1217890317075045460`, tail upper bound
`196609/25769803776`, and step-17 weight `1/131071`. The script checks
with exact fractions that the remainder is greater than the entire later
tail bound but smaller than the next weight. It also certifies the earlier
skips, checks the translated target `577/388`, and prints a separate finite
factorial-allowance example. A passing run excludes these particular targets
from the Mersenne subsum set; finite survival at an earlier step would not
establish membership.

This calculation does **not** reproduce the finite-prime weighted-support
irrationality theorem in the [#257 short paper](../paper/257/erdos-257-mersenne-support-subseries.pdf).
That theorem concerns infinite positive supports satisfying a weighted
summability hypothesis. The script proves neither that hypothesis nor the
theorem's irrationality conclusion. The [investigation](../research/experiments/choices_contraction/README.md)
explains why the late rejection corrects a proposed finite stopping rule;
the [experiment guide](../research/experiments/sparse_interpolation/README.md#exact-checks)
records its other checks.

If this command fails, confirm `python3 -VV`, rerun
`python3 scripts/test_choices_contraction_probe.py`, and report the exact
command, error, and `git rev-parse HEAD` through [CONTRIBUTING](../CONTRIBUTING.md).

To try a fraction of your own, use the single-target probe (replace `189/388`):

```sh
python3 research/experiments/choices_contraction/rational_membership_probe.py \
  --target 189/388 --depth 16 17 --horizon 160 --json
```

Here the depth-16 outcome is `not_excluded`; at depth 17 it is `excluded` with
the exact selected prefix and strict gap certificate. Other outcomes are
`finite_representation` (the remainder reached zero) and `not_excluded`
(no conclusion beyond the tested depth). The
[probe guide](../research/experiments/choices_contraction/README.md#the-probe)
defines the host choices and input limits. This is a finite membership probe
for the base-two subseries, not a test of the weighted irrationality theorem.

The [probe guide](../research/experiments/choices_contraction/README.md#the-probe)
also gives an inspected, commit-pinned single-file route before cloning. For
a terminal row in this checkout, make a JSON record with `--depth 17` alone
and check it independently:

```sh
python3 research/experiments/choices_contraction/rational_membership_probe.py \
  --target 189/388 --depth 17 --horizon 160 --json > witness.json
python3 research/experiments/choices_contraction/verify_terminal_witness.py witness.json
```

The receiver recomputes the prefix and tail bound; a `not_excluded` row is
refused because finite survival is no membership certificate.

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

For the weighted theorem used in the #257 reading route, first inspect its
current claim record, then build the module containing its proof:

```sh
python3 scripts/verify_claims.py --claim finite_prime_weighted_support
python3 scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn
```

[`DivisibilityWeightedClaim`](../lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean)
states the fixed-base and hereditary clauses. The proof declaration is
[`divisibilityWeightedClaim`](../lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L120).
The R7 interface file's preamble describes the earlier development stage;
its "missing" proof wording is not the current theorem status. Read the R8
proof and the claim record above for that status. The R7 source remains at
its pinned formal-source revision.
The first command checks the current claim's references and prints its
recorded formal-source revision; it does not run Lean. The second command
checks the current checkout with the pinned Lean toolchain. Record
`git rev-parse HEAD` alongside its result so that a build at one revision is
not attributed to another.

The [external-verification packet](EXTERNAL_VERIFICATION.md#programme-257)
and [`verification/comparator.json`](../verification/comparator.json) identify
the separately declared Comparator statement and axiom budget. Its legacy
Comparator replay record remains distinct from Palomar's
[successful mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/36009433226)
of the exact five-declaration `PalomarCorpus/E257_01` entry at source commit
`b85ed30805188eb4390a686b111294b24363418e`; that entry includes
`divisibilityWeightedClaim`. Palomar accepted a registration request for
submission `gid0ym5uu910` at 19:31 UTC on 24 September 2026. At the
authenticated status check at 19:42 UTC, no public ID or version had been
returned. This receipt applies to the
selected entry, not every theorem in the #257 paper. The
[replay guide](verification/EXTERNAL_VERIFICATION_REPLAY.md) explains the
separate source-bound Comparator receipt.

The replay guide now provides a one-theorem `weighted-support` unit for
`divisibilityWeightedClaim`. On Linux with the stated prerequisites, its
single `run --unit weighted-support` command fetches an exact commit, compares
the theorem with the separate challenge, and requires rejection of a
deliberately changed statement. The configuration is runnable, but a passing
receipt for the selected source commit has not been recorded here. The
`189/388` Python calculation above is a different finite result.

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
  FormalConjecturesVariants FC1049HeightRegion FC243CubicRate ResidualBench \
  ErdosProblems.Erdos251.PaperLargeAuditR7
lake env lean research/adapters/FC1049HeightRegion.lean
python3 scripts/build_lean_dependency_index.py --check --full-check
```

`Erdos249257` and `ErdosProblems` are the default libraries. `Examples` builds
consumer examples inside this package; read their imports and example
declarations in [research/examples/Examples.lean](../research/examples/Examples.lean).
The remaining targets check adapters, statement variants, residual examples,
and the separately compiled #251 paper audit; building them does not
add reviewed claims to the mathematical record.

The wrapper coordinates builds on the same machine. Equivalent requests share
one running job; different heavy builds queue, and compatible clones can
reuse build files. Keep using the wrapper if another build is in progress.
The [concurrent-validation guide](../skills/lean-concurrent-validation/SKILL.md)
explains detached operation, cache locations, storage sharing and exit codes.
A successful build means Lean accepted the requested modules. The exact
statements and their limits are in the source and [claim record](claims.json).

### Use the library in another Lean project

[The dependency guide](DOWNSTREAM_REUSE.md) gives the pinned Lake package
recipe and distinguishes a separate consumer from the internal `Examples`
target. After the complete build above, check that package boundary with:

```sh
python3 scripts/check_downstream_reuse.py
```

The checker creates a separate Lake project and checks the unchanged consumer
examples under the host build lock. A missing build or dependency is a failed
check; the checker does not rebuild or download dependencies.

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

The release check runs for several minutes and prints only its final
summary; it has not stalled. The Lean build and this Python check answer separate questions. A publication
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
