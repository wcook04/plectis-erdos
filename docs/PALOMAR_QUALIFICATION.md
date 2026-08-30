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
Erdos249257.ExternalVerification.irrational_erdosSum_full_support
```

It is the strongest current direct endpoint result in the committed
Comparator spine: for every integer `b >= 2`, it proves irrationality of the
full-support Erdős–Borwein series
`∑' k, 1 / (b^(k+1) - 1)`. This is a canonical member of Erdős #257, not a
convenient finite instance or a renamed adapter.

The hard step is visible in the source rather than hidden behind the
headline: `CertificateKernel.lean` closes a weighted divisor-block certificate
pipeline using a bounded Bertrand/CRT first-block frame, middle-window
divisor-pair averaging with pigeonhole selection, weighted tail control, and
explicit parameter closure. The exact source declaration is at
`Erdos249257/CertificateKernel.lean:8328`, with the mechanism documented at
the preceding source lines.

The value-selection record evaluates all 31 committed Comparator rows. Its
complete high-signal spine over that exact universe is:

1. `irrational_erdosSum_full_support` — selected: unconditional direct
   irrationality, a completed certificate mechanism, canonical endpoint, and
   exact source/Comparator evidence.
2. `irrational_erdosSupportSeries_pairwise_coprime` — strong runner-up: a
   distinct adaptive-CRT result for a broad non-dilation class, but with
   infinitude, pairwise-coprimality, and summable-reciprocal hypotheses.
3. `irrational_erdosSupportSeries_of_orthogonalPetalBouquet` — deep but
   conditional: the bouquet and uniform tail-selection predicates are not
   constructed for arbitrary supports.
4. `irrational_ratWeightSeries_eventuallyPeriodic` — direct structured
   irrationality, but for a coefficient class rather than the universal
   support endpoint and not the mixed-sign theorem.
5. `irrational_factorialGapSeries_iff_cofinal_nonunit_carries` and
   `irrational_tsum_primeDyadicTerm_iff_primeGap` — exact endpoint reductions
   with high routing value, but neither supplies the missing irrationality
   producer.
6. `not_finiteDimensional_span_fullTotientKernel` — deep independent #249
   structure, but farther from the irrationality endpoint.

This selection explicitly resists underclaim: a classical theorem is not
demoted merely because it is already known or because another row has a more
general-looking hypothesis. It also resists hype: the selected theorem proves
only full support, does not solve universal Erdős #257, and does not claim
novelty or human peer review. A newly committed source-checked row would
replace it only with a strictly stronger direct consequence, genuinely deeper
independent mechanism, equal-or-better evidence certainty, and no larger
hidden-hypothesis risk.

## Current main-compatible evidence

The candidate is bound to the committed current tree observed at
`2e02f3ad520df14e40938000909e0e44d7e0ef52` immediately before this evidence
refresh:

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

Classification authority is pinned to the PalomarSubmission arXiv and
MSC2020 taxonomy snapshots at commit
`e215b184d1b659e8e3e641162a7d63708678016f`; their SHA-256 digests and immutable
raw URLs are recorded in the policy reconciliation. The qualification checker
requires those authority bindings before classification metadata can be treated
as current.

The showcase records all 31 committed declarations across all eight open
programmes and includes a prose-ranked value-selection spine over that exact
universe. It does not turn the roster count into a readiness claim.

## Qualification cells

| Cell | Current disposition | Evidence or remaining boundary |
| --- | --- | --- |
| Exact Challenge/Solution pair | pass | Distinct committed modules; configuration names both explicitly. |
| Comparator path and axiom ceiling | pass structurally | `verification/comparator.json`; the final mechanical axiom report is still withheld. |
| Toolchain, Lakefile, manifest | pass structurally | Current versions and committed dependency manifest are present. |
| Root licence | pass structurally | Apache-2.0 is declared and detected consistently. |
| Formalization metadata | **red** | Current `formalization.yaml` is v0.3, lacks `project.description`, `responsible_maintainers`, and classification metadata, and its sources lack v0.4 relationships/origin evidence while using pre-v0.4 type labels. |
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
