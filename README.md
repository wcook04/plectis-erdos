# Erdős Lean development

The source tree now has two entry libraries:

- `ErdosProblems` is the problem-centric home for new work, grouped by the
  actual Erdős problem number and mathematical object.
- `Erdos257PeriodNoncollapse` remains the compatibility root for the large
  historical #249/#257 development. Existing imports are not being renamed in
  place.

## Orient the corpus before opening a problem

From the repository root, start with the compact navigation card rather than
walking owner directories or opening every research packet:

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/corpus_navigation.py \
  --entry --json
```

Its `recommended_routes` separates the all-problem frontier chooser, source
topology, cross-problem computation map, and selected-problem evidence
neighborhood. The card is organizational only: it opens no packet, runs no
computation, and assigns no mathematical status. Once an exact problem number
is selected, obtain its bounded papers, comparator, and research-handoff
neighborhood before traversing broad evidence folders:

```sh
./repo-python -m system.lib.mathematical_working_memory \
  --query "Erdos #<number>" --problem-cockpit --context-budget 12000
```

For a task-oriented map of the problem packets, proof-bearing modules,
dependency planning, and validation commands, start with
[`ErdosProblems/WORKING_GUIDE.md`](ErdosProblems/WORKING_GUIDE.md). It points
to the live status authorities rather than maintaining a second status table.

Problem-owner routes are manifest-backed rather than duplicated here. From this
directory, list their current supported entries with:

```sh
jq -r '.problems[] | [.id, .directory, .lean_module] | @tsv' \
  ErdosProblems/assimilation_manifest.json
```

The manifest is the machine-readable index of packet owners and supported
entry modules; open obligations and public-review state remain with the
problem-owned sources it names. None of the open problems is marked solved
merely because an exact reduction, no-go theorem, strengthened subcase, or
finite certificate has been landed.

Public projection is downstream of private proof authority. A problem module
is eligible for the public corpus only after its focused Lean target passes,
its hypotheses and non-claims are reviewed, and the public claim registry can
name the surviving open proposition. Public mutation also requires a
source-current corpus identity and collision-free intended target paths.

Fetch the pinned Mathlib cache once:

```sh
lake exe cache get
```

For ordinary focused work, build the narrow module you changed:

```sh
../../repo-python scripts/lean_fast_build.py --jobs 2 \
  Erdos257PeriodNoncollapse.CertificateKernel
```

Build and audit the complete problem-owned root with:

```sh
../../repo-python scripts/lean_fast_build.py --jobs 1 ErdosProblems
```

`ErdosProblems.AxiomAudit` records the assumptions of the wave's principal
theorems during that build.

## Exact #1049 Comparator route

The repository also contains one bounded Comparator and Palomar-interface
fixture for the 7/2 numerical height inequality. The selected declaration is
`Erdos249257.ExternalVerification1049.comparator_sevenHalves_numericalHeight`;
it is not a proof of irrationality or a solution of Erdős #1049. The
statement-only Challenge is `ExternalVerification1049/Challenge.lean`, the
proved source transport is `ExternalVerification1049/Solution.lean`, and the
deliberate nearby mismatch is
`ExternalVerification1049/NegativeSolution.lean`.

From the selected project root `formal_math/erdos257_period_noncollapse`, run
the checked-in verifier on a supported Linux runner:

```sh
./scripts/verify-comparator.sh
```

The verifier bootstraps the pinned Comparator, Landrun, NanoDa, and the
v4.29.1-matched `lean4export`, then runs the canonical positive configuration
and the deliberate negative.  The positive run must terminate successfully;
the negative run must terminate unsuccessfully with a declaration name/type
mismatch naming
`Erdos249257.ExternalVerification1049.comparator_sevenHalves_numericalHeight`.
This is the supported replay route, not a replay receipt.
Until one immutable submitted commit contains this selected project and a
supported runner produces both terminal results, this preparation is neither
Comparator acceptance nor Palomar eligibility.

### Palomar intake boundary

Palomar treats this as a selected project below the repository root. An
operator-authorized submission must select the repository-relative project
directory `formal_math/erdos257_period_noncollapse` and explicitly provide
`formal_math/erdos257_period_noncollapse/comparator.json`; the selected
project's `formalization.yaml` is its default metadata file. The policy's
500 MiB limit applies to the complete checked-out repository, not just the
selected project, so selecting this nested directory does not make the current
monorepo an eligible submission. The operator must first provide a smaller
public repository and immutable commit containing the selected project; that
submission's single conventional licence file must remain at repository root
and match `project.license`. No Comparator or Palomar verdict is implied until
that repository-size condition and the terminal replay pair both hold.

This object also has a deliberate editorial ceiling: the selected declaration
is an elementary numerical entrance condition, and the metadata records it as
a subordinate Comparator audit fixture rather than a standalone Palomar
research claim. A Comparator replay cannot establish Palomar's separate
research-interest tests. Any future submission would therefore require an
operator-reviewed decision that the stated result could warrant a serious
research note and has a credible specialist audience; this preparation does
not make that decision on the operator's behalf.

## Contribution route for a public clone

A contributor can work from an immutable starting commit in a public clone or
in a smaller exported repository using Git, Lean, Lake, and the checked-in
replay script. For this selected fixture, return the starting commit, the
resulting commit, the repository-relative paths changed, and the exact command
output for both the positive and deliberate-negative replay on the same
commit. If the supported Linux environment is unavailable, return that result
as an environment-unavailable outcome rather than turning a local Lean build
into a Comparator verdict. Preserve the Challenge statement, the declared
axiom budget, the source attribution, and the explicit non-claims when making
changes, so another contributor can inspect the difference and continue from
the cited generation. A returned commit is review material until the selected
repository, configuration, and terminal replay pair satisfy the current
Palomar rules.

For low-level manual debugging, a Linux host with Comparator and its required
systemd sandbox can invoke the two configurations directly:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- bash -c \
  'lake env comparator comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- bash -c \
  'lake env comparator ExternalVerification1049/comparator-negative-mismatch.json'
```

Both configurations set `enable_nanoda: true`, so a supported replay also
checks the positive proof and deliberate negative mismatch with the additional
NanoDa kernel.

The first command must accept the exact name and type; the second must exit
nonzero with a declaration-mismatch diagnostic. These commands are a replay
recipe, not a replay receipt. The three fixtures can be compiled locally with
`lake env lean`, but that does not establish a Comparator verdict. Re-open the
[Palomar submission rules](https://palomar-registry.org/how-to-submit) and
[pinned current policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/d5a647db3757303b1d928cfae4d3d232eed3e79e/CONTRIBUTING.md)
before any operator-authorized registry action.

For a local Lean compilation check from the project root:

```sh
lake env lean ExternalVerification1049/Challenge.lean
lake env lean ExternalVerification1049/Solution.lean
lake env lean ExternalVerification1049/NegativeSolution.lean
```

The exact Erdős #249 interface is split across three focused targets:

```sh
../../repo-python scripts/lean_fast_build.py --jobs 2 \
  Erdos257PeriodNoncollapse.CyclicTensorMobiusShadow \
  Erdos257PeriodNoncollapse.MersenneShadowDenominatorGrowth \
  Erdos257PeriodNoncollapse.DiagonalPincerDecomposition \
  Erdos257PeriodNoncollapse.DiagonalFreshLossBridge \
  Erdos257PeriodNoncollapse.SquaredMersenneDiagonalEnclosure \
  Erdos257PeriodNoncollapse.ActualForeignResidueProjection \
  Erdos257PeriodNoncollapse.LambertDiagonalEnclosure
```

`CyclicTensorMobiusShadow` owns the prime-factor tensor product and integral
adjugate. `MersenneShadowDenominatorGrowth` exposes the exact reduced
denominator after replacing the large Möbius numerator by the odd Jordan
scalar. `DiagonalPincerDecomposition` turns that reduced rational shadow into
the complement-free target for `foreignDiagonalDefect`. These are finite
algebraic interfaces only: the unbounded full-target avoidance supply remains
the unresolved analytic input to Erdős #249. `DiagonalFreshLossBridge` keeps
that target constitutional while exposing the exact denominator-free `[1, 2]`
binary cone projection as a direct finite consumer. It proves that any firing
projection misses the full target and names the precise unbounded projection
supply that would close the irrationality theorem; it does not assert that the
supply is available.

`SquaredMersenneDiagonalEnclosure` is the canonical finite verifier for the
actual diagonal.  It exposes the exact rational centre, the sharp symmetric
square-tail radius, the reduced-denominator formula, and the first-support
directed interval consumer without a `2H ≤ D` precondition.
`ActualForeignResidueProjection` retains the residue-channel coordinates and
finite complement bound. `LambertDiagonalEnclosure` turns a supplied
`ForeignResidueTailLimit` into the residue consumer, but that limit is not on
the direct square verifier's critical path.

The companion exact evaluator supports `raw_residue`, `resummed_residue`,
`square_centre`, `offset_adversary`, `square_controls`, and `lcm_diagonal`:

```sh
../../repo-python scripts/check_actual_foreign_residue_projection.py \
  --mode square_centre --height 420 --cutoff 421
```

For the Erdős #257 adelic-height adjudication layer, build the scalar
localisation and linear-descent obstruction directly:

```sh
../../repo-python scripts/lean_fast_build.py --jobs 2 \
  Erdos257PeriodNoncollapse.AdelicHeightObstruction
../../repo-python scripts/check_adelic_height_obstruction.py
```

`AdelicHeightObstruction` proves that reducing a scalar multiple to a
surviving denominator channel transfers the full complementary denominator
into the coefficient, gives the corresponding numerator-multiple identity,
formalizes the elementary real/2-adic height bound, and shows that any linear
channel descending through scalar evaluation factors through that evaluation.
The exact script checks the denominator-parity fixtures and five dyadic-block
complement diagnostics. These are obstruction theorems and finite regression
receipts, not a universal irrationality theorem for arbitrary support.

For a wide generated-certificate target, use the memory-bounded wrapper:

```sh
../../repo-python scripts/lean_fast_build.py --jobs 2 \
  Erdos257PeriodNoncollapse.DiagonalPincerCertificatesT47
```

Run that command from this directory. The wrapper finds the target's local
import graph, prebuilds stale or missing modules in dependency order with at
most two concurrent Lean processes, and finishes with an ordinary `lake build`
of the requested target. The final Lake step remains the proof-authority check.
The complete local import partition is also the singleflight identity: an
identical concurrent request never starts a second dependency build.

After restoring `.lake` outputs from a CI or local cache, add
`--lake-staleness`. It asks Lake's content-trace checker which targets are
actually current instead of treating checkout timestamps as evidence that the
entire import cone must be rebuilt; incomplete restored outputs safely fall
back to the mtime planner.

`--plan` prints compact dependency-wave counts; use `--verbose-plan` only when
you need every planned module name. The import scan reads only Lean's header,
so generated proof bodies are not loaded merely to construct the local graph.

If an identical build is already running, or host capacity is currently
allocated, the wrapper returns exit `75` with a typed active-run or capacity
ticket receipt. That means validation is deferred or already owned, not that
the theorem failed. The caller should record the receipt, finish non-build
work, or move to a disjoint task instead of launching raw `lake build`. A
later integration owner must retry a capacity-deferred target; the ticket is
an admission receipt, not an autonomous background executor.

Do not run a focused target build and a full-project build concurrently. A
focused PASS is the source-lane proof for a scoped commit; the full root target
is a separate integration-validation state and must remain labelled pending
until it passes. `--wait-if-duplicate` is intentionally rejected with a typed
manual-reinvoke handoff: neither integration owners nor sibling agents should
keep a turn alive waiting on a build lease.

Do not use `lake -Kjobs=2 build` as a concurrency guard on Lake 5. `-K` sets a
package configuration option; it does not bound the build scheduler. Increase
`--jobs` only after measuring memory headroom, since the large certificate
modules can each occupy several gigabytes while elaborating.
