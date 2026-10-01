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

| Files | Role |
|---|---|
| [formalization.yaml](../formalization.yaml) | Root manifest selecting the formal interfaces. |
| [ExternalVerification/](ExternalVerification/) and other named Lean directories | Challenge statements, solution wrappers and supporting modules for selected checks. |
| [Solutions/](Solutions/) | Solutions for additional selected interfaces. |
| [NegativeSolutions/](NegativeSolutions/) and files named `NegativeSolution` | Deliberately invalid controls used to test rejection. |
| [comparator.json](comparator.json) and the other Comparator configurations | Selected modules and permitted assumptions for each replay. |
| [external-verification-release-contract.json](external-verification-release-contract.json) | The evidence required by the release checks. |

A configured interface is not a record of a successful replay. Consult the
dossier for the selected statement, source revision and recorded outcome.
[evidence/](../evidence/README.md) holds the paper-to-proof records and stored
Comparator reports. [docs/verification/](../docs/verification/README.md) holds
human instructions; the different directory roles are intentional.

Comparator checks the declared statement and permitted axioms. Mathematical
correspondence, novelty, significance and community acceptance require separate
judgements. [Methodology](../docs/METHODOLOGY.md) describes those boundaries.
