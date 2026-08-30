# Palomar qualification: exact current candidate

Status: **NOT READY**.

This is the repository-local qualification decision for the current
main-compatible candidate. It is not a Palomar submission, registration, or
editorial endorsement. The machine-readable source of this decision is
[`PALOMAR_POLICY_RECONCILIATION.json`](PALOMAR_POLICY_RECONCILIATION.json);
the result crosswalk is [`PALOMAR_RESULT_SHOWCASE.json`](PALOMAR_RESULT_SHOWCASE.json).

## Candidate selected by mathematical signal

The selected Comparator declaration is:

```text
Erdos249257.ExternalVerification.irrational_erdosSupportSeries_pairwise_coprime
```

It is the cleanest high-signal candidate in the committed current roster:
for every integer `b >= 2` and every infinite pairwise-coprime support `A`
whose reciprocal indicator is summable, it proves
`Irrational (erdosSupportSeries b A)`. The conclusion covers a broad
non-dilation class, not one convenient finite instance or a renamed adapter.

The hard step is visible in the source rather than hidden behind the
headline: `CertificateKernel.lean` supplies weighted coefficient certificates
through an adaptive CRT. Small support elements are absorbed into the first
block, unselected elements are controlled as residue strays, and summable
reciprocals pay for the weighted tail. The exact source declaration is at
`Erdos249257/CertificateKernel.lean:10776` and its proof consumes the
certificate producer at the following lines.

This beats the other plausible showcase choices on the combined review
criteria, not because it is easiest to check:

- `irrational_erdosSum_full_support` has a stronger direct consequence for
  the classical full-support subcase, but it is a narrower already-known
  theorem and hides the non-dilation support mechanism.
- `irrational_erdosSupportSeries_of_orthogonalPetalBouquet` exposes a deeper
  structural route, but its bouquet and uniform tail-selection predicates are
  conditional and are not constructed for arbitrary supports.
- `threeHalves_no_coordinatewiseCorridor` is a useful sharp obstruction, but
  it excludes one architecture and concludes no irrationality statement.

The selected theorem is still not a solution of Erdős #257. Its infinitude,
pairwise-coprimality, and summable-reciprocal hypotheses remain explicit, and
the universal infinite-support statement remains open. Local Lean provenance
and Comparator acceptance, once run for the final commit, are not novelty or
human-peer-review evidence.

## Current main-compatible evidence

The candidate is bound to the committed current tree observed at
`53c2e1f18641d6577c3e1e640eaeaf137a9046a7`:

- Comparator configuration: `verification/comparator.json`, 31 unique
  theorem names, SHA-256
  `7f3a36323877fcf4458f17abdec536d822edcf08fa3883c0b9a353b921523cb6`.
- Challenge: `ExternalVerification.Challenge`.
- Solution: `ExternalVerification.Solution`.
- Permitted Comparator axioms: `propext`, `Quot.sound`, and
  `Classical.choice`.
- Lean toolchain: `leanprover/lean4:v4.29.1`; the official minimum is
  `v4.28.0`.
- Root licence and declared project licence: `Apache-2.0`.
- `lakefile.toml` and `lake-manifest.json` are present.

The showcase records all 31 committed declarations across all eight open
programmes. It does not turn the roster count into a readiness claim.

## Qualification cells

| Cell | Current disposition | Evidence or remaining boundary |
| --- | --- | --- |
| Exact Challenge/Solution pair | pass | Distinct committed modules; configuration names both explicitly. |
| Comparator path and axiom ceiling | pass structurally | `verification/comparator.json`; the final mechanical axiom report is still withheld. |
| Toolchain, Lakefile, manifest | pass structurally | Current versions and committed dependency manifest are present. |
| Root licence | pass structurally | Apache-2.0 is declared and detected consistently. |
| Formalization metadata | **red** | Current `formalization.yaml` is v0.3, lacks current `responsible_maintainers` and classification fields, and uses pre-v0.4 source labels. |
| Informal account and boundaries | pass | The showcase gives the exact selected type, mechanism, attribution, limitations, and open frontier. |
| Challenge import closure and solution axiom audit | withheld | Requires one immutable terminal Palomar-compatible mechanical validation. |
| Independent NanoDa replay | withheld | Must be bound to the same immutable source commit. |
| Editorial review | withheld | External private Palomar pipeline; no human review is claimed. |
| Registration/publication | operator-only | Not performed and not authorized in this lane. |

The exact decision is therefore **NOT READY**. The local repair remaining is
to refresh the generated `formalization.yaml` from its owning claim source to
the official v0.4 profile without overwriting concurrent source work. After an
immutable product commit is named, one non-duplicated terminal mechanical and
independent-replay evidence bundle can replace the withheld cells. Submission
consent and registration remain operator actions.

## Official authority capture

All authority files below are pinned by both a full Git commit and a SHA-256
digest. The complete capture, including registry-view boundaries, is in the
JSON reconciliation file.

- [PalomarPolicy specification](https://raw.githubusercontent.com/PalomarRegistry/PalomarPolicy/d5a647db3757303b1d928cfae4d3d232eed3e79e/docs/specification.md)
  at `d5a647db3757303b1d928cfae4d3d232eed3e79e`.
- [PalomarPolicy submitting standard](https://raw.githubusercontent.com/PalomarRegistry/PalomarPolicy/d5a647db3757303b1d928cfae4d3d232eed3e79e/CONTRIBUTING.md)
  at the same commit.
- [PalomarSubmission toolchain contract](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/e215b184d1b659e8e3e641162a7d63708678016f/toolchains.json)
  at `e215b184d1b659e8e3e641162a7d63708678016f`.
- [PalomarSubmission formalization profile](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/e215b184d1b659e8e3e641162a7d63708678016f/formalization-profile.json)
  at the same commit.
- [PalomarWeb registry explanation](https://raw.githubusercontent.com/PalomarRegistry/PalomarWeb/2114a47adcbdb3d737133cd8898474d418b4bee2/about.html)
  at `2114a47adcbdb3d737133cd8898474d418b4bee2`.

The local `local-research-20260829` ref is intentionally not used: it has a
different root `comparator.json`, source modules absent from current main, and
incompatible Palomar surfaces. It is evidence of an alternate development,
not authority for this qualification.
