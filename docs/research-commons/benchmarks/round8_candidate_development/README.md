# Disclosed Round 8 relation candidates

This is a historical developmental candidate bank pinned to source commit
`0268dd8bfb2a556a0c93078337d42c6d07138fa2`. It contains 12 disclosed
questions in four dependent problem clusters, not 12 independent proof results.
`author_proposals.json` contains the return author's tentative labels and
perturbations; it is not mathematical gold. The Lean obligations in the return
were unrun, and no model responses or independent grades are reported.

The native route is `python3 scripts/benchmark_semantic_reasoning.py restatement
candidate validate`. Validation checks all 34 delivered source excerpt hashes.
`--source-root` additionally checks exact historical source bytes and the Git
commit, tracked inventory and cleanliness, and historical parser bytes against
the frozen Git object before that parser executes; a later checkout is
intentionally rejected. This does not authenticate all Python imports outside
that one parser file. `parse-responses` and
`parse-reviews` check schema, exact historical identity, allowed evidence
handles, and excerpt bytes without assigning scores. `export-review RESPONSES
--out DIR` writes label-free items plus the selected source excerpts and a
`review_manifest.json` binding the exact delivered bytes. A reviewer intake
uses `verify-review-export DIR --expected-manifest-sha256 SHA256` with the
manifest digest transmitted separately. Source text may itself reveal the
answer; byte binding does not establish reviewer independence or blinding.
`seal-gold` is deliberately refused.

The existing eight-row source-current developmental calibration remains a
separate native benchmark. This directory does not update its local Lean replay
or confer a current-source certificate on the historical 0268 rows.
