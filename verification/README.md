<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Formal interfaces and replay configuration

This directory contains selected formal statements, solutions, negative
controls and configuration for verification runs. The
[verification dossier](../docs/EXTERNAL_VERIFICATION.md) explains what is checked;
the [verification guides](../docs/verification/README.md) give the replay
procedures and platform-specific requirements.

For one concrete replay, use the [#257 weighted theorem](../docs/verification/EXTERNAL_VERIFICATION_REPLAY.md#reviewer-replay).
Its prerequisites and deliberate failure controls are part of the procedure.

| Source or configuration | Role |
|---|---|
| [Root manifest](../formalization.yaml) and [root Comparator configuration](comparator.json) | Select the headline interfaces in [ExternalVerification](ExternalVerification/). The configuration owns the roster. |
| [Weighted-support configuration](comparator-weighted-support.json) | Focused #257 replay; use the reviewer procedure above. |
| [Feedback-policy configuration](comparator-feedback-policy.json) | Selected feedback-policy interface and its axiom budget. |
| [#1049 configuration](comparator-1049-numerical-height.json) and [metadata](comparator-1049-numerical-height.metadata.json) | Numerical-height packet in [ExternalVerification1049](ExternalVerification1049/); [replay guide](../docs/verification/COMPARATOR_1049_NUMERICAL_HEIGHT.md). |
| [#1041 solved-family packet](ExternalVerification1041SolvedFamilies/README.md) | Exact selected polynomial-family statements and their proof boundaries. |
| [#249 kernel-basis packet](ExternalVerification249TotientKernelBasis/README.md) | Independent Challenge statements and separate positive/negative solution libraries. |
| [Large #251 certificate](Erdos251LargeCertificate/) | Non-default Lake library for the restartable finite certificate. [Reproduction and limits](../research/experiments/erdos251/README.md); the library's explicit source ownership is in [lakefile.toml](../lakefile.toml). |
| [Solutions](Solutions/), [NegativeSolutions](NegativeSolutions/) and configurations named `negative-mismatch` | Proof-bearing wrappers and deliberately invalid rejection controls. Negative controls must not become ordinary proof sources. |
| [#243 density](erdos243-density-validation.json), [#249 validation](erdos249-v8-validation.json), [#269 validation](erdos269-wavea-validation.json), [#68 interval](erdos68-strict-successor.json), [#1041 audit](erdos1041-returned-r18-v5-full-audit-evidence.json) | Separate validation/export records, each with its own source and scope. |
| [Release contract](external-verification-release-contract.json) | Evidence required by the release checks. |

A configured interface is not a record of a successful replay. Consult the
dossier for the selected statement, source revision and recorded outcome.
[evidence/](../evidence/README.md) holds the paper-to-proof records and stored
Comparator reports. [docs/verification/](../docs/verification/README.md) holds
human instructions; the different directory roles are intentional.

Comparator checks the declared statement and permitted axioms. Mathematical
correspondence, novelty, significance and community acceptance require separate
judgements. [Methodology](../docs/METHODOLOGY.md) describes those boundaries.
