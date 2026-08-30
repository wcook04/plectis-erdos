<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Third-party source-artifact notices

This notice records third-party source artifacts retained as citation evidence
for the scholarly release. It is not a release allowlist: no artifact below
is included in the public candidate, because the repository has not verified an
authoritative redistribution grant for it. The machine-readable artifact
authority is
[`primary-sources/redistribution-dispositions.json`](primary-sources/redistribution-dispositions.json).

Retrieval, citation, attribution, DOI, arXiv availability, author hosting,
and the repository's Apache-2.0 or CC-BY-4.0 grants do not establish permission
to redistribute an upstream work. The digest is an integrity check for a
private acquisition copy, not a license.

## Current artifact disposition

Every current record is `working_tree_only`, `link_and_digest_only`, and
`permission_evidence_status: not_verified`. The public candidate therefore
contains none of these PDFs or source archives. Obtain a copy only through an
official route, review its current terms, and verify the manifest digest.

| Artifact | SHA-256 digest | Official retrieval route(s) | Evidence boundary |
| --- | --- | --- | --- |
| `docs/primary-sources/dyadic-carry/wang-2026-v4-source.tar.gz` | `2d507f030082dc5ca3f661d49fa96925cffe7fbe11287a897ed9b7b2efdfe6c2` | <https://arxiv.org/abs/2606.24972v4> | `docs/primary-sources/dyadic-carry/wang-2026-source-closure.md` |
| `docs/primary-sources/dyadic-carry/wang-2026-v4-sparse-polynomial-weighted-expansions.pdf` | `3a57af1af21e5e9d25793333383d30f89ceadb08c4e2009a1ac497dc118f8b5b` | <https://arxiv.org/pdf/2606.24972v4> | `docs/primary-sources/dyadic-carry/wang-2026-source-closure.md` |
| `docs/primary-sources/bergman-geodesic/pritsker-2011-inequalities-green-potentials.pdf` | `d256af21c33f92e155e9a7926c18f9c7219cc8839036a8cc4c5708d70f17094f` | <https://arxiv.org/abs/1307.6196>; <https://doi.org/10.1112/blms/bdq122> | `docs/primary-sources/bergman-geodesic/pritsker-2011-source-closure.md` |
| `docs/primary-sources/bergman-geodesic/erdos-herzog-piranian-1958-source.pdf` | `bff39876de5e152b5a0d2b622eb6f9ca0c747d401ceea68146cfa2b2b5f28ce9` | <https://link.springer.com/article/10.1007/BF02790232>; <https://doi.org/10.1007/BF02790232> | `docs/primary-sources/bergman-geodesic/erdos-herzog-piranian-1958-source-closure.md` |
| `docs/primary-sources/dyadic-carry/wang-2026-v2-positive-dyadic-density.pdf` | `c0b75ab662c82026b67ac0ce781c25f7d2f80e12c4b5cb6d63557add35a3ff25` | <https://arxiv.org/abs/2606.24972v2>; <https://arxiv.org/pdf/2606.24972v2> | `docs/primary-sources/dyadic-carry/wang-2026-v2-source-closure.md` |
| `docs/primary-sources/reciprocal-tail/koizumi-2026-integers-a28.pdf` | `9ad8561399e36bb4f17368064dc4765a90f164d85b65330c466e79fc716624df` | <https://math.colgate.edu/~integers/aa28/aa28.pdf>; <https://arxiv.org/abs/2504.05933>; <https://arxiv.org/pdf/2504.05933>; <https://doi.org/10.5281/zenodo.18714404> | `docs/primary-sources/reciprocal-tail/koizumi-2026-source-closure.md` |
| `docs/primary-sources/totient-kernel/martin-2006-simultaneous-phi-inequalities.pdf` | `8d967dc3018c325cf3b4a099fa916e369f4b9a915bf2ccad398d359e3b4f0705` | <https://arxiv.org/abs/math/0603053>; <https://arxiv.org/pdf/math/0603053>; <https://doi.org/10.48550/arXiv.math/0603053> | `docs/primary-sources/totient-kernel/martin-2006-source-closure.md` |

The evidence-boundary files state what each source supports and what it does
not support. They are citation/provenance records, not permission grants or
claims of equivalence with private development work.

## Dependency manifests

The public candidate contains project-authored manifests, not fetched
dependency trees or package archives:

| Manifest | Release evidence | Permission boundary |
| --- | --- | --- |
| [`requirements-release.txt`](../requirements-release.txt) | 24 exact `name==version` records, each with SHA-256 hashes; CI installs it with `pip --require-hashes`. | Package names, versions, hashes, and PyPI retrieval do not grant permission to redistribute a package payload. |
| [`lake-manifest.json`](../lake-manifest.json) | 9 HTTPS Git dependency records with full immutable revisions. | Git URLs and revisions identify build inputs; fetched dependency sources remain governed by their upstream terms. |
| [`lakefile.toml`](../lakefile.toml) and [`lean-toolchain`](../lean-toolchain) | The project’s Lake and Lean input declarations. | Build declarations are not upstream license text or redistribution grants. |

The release gate checks this notice against the disposition ledger and rejects
missing paths, digests, official routes, evidence boundaries, or manifest
boundaries. If an upstream term conflicts with a local acquisition copy, keep
the binary out of the public candidate and resolve the exact record through the
documented operator route.
