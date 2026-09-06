# Reachable-history release trust boundary

The public candidate is not release-safe merely because prohibited files are
absent from `HEAD`: every object reachable from a branch or tag can be
retrieved by a clone or ref checkout. The machine-readable audit at
`docs/release/reachable-history-audit.json` is the canonical redacted evidence
artifact for this boundary, but it is not a current release decision by itself:
its exact-commit freshness and release-gate checks must validate it before any
result is treated as current evidence.

The report also records a SHA-256 fingerprint of the scanner source. A change
to the scanner implementation therefore requires regenerated evidence even
when the changed file is otherwise part of the audit control plane.

## What blocks and what is reported

The scanner separates release hazards from history hygiene. Both are written
into the report; only the first kind turns the release decision red.

Release hazards block whenever they are reachable, in any commit: a credential
shape that is not a declared fixture, a third-party artifact whose disposition
is link-and-digest-only, an unmanifested primary-source binary, a pathless
direct-ref blob, a missing ref object, a custom third-party license marker,
an archive with a traversal or link member, a privacy-bearing ref name, and a
non-atomic scan.

History hygiene findings are `absolute_private_filesystem_path` and
`private_or_working_path`. A workstation path inside an old file, or a
filename containing a watch term, is retrievable by a clone but is not a
credential, and this document forbids the only operation that could remove it
from history. A policy that both forbids the fix and blocks on the finding can
never go green, so these kinds block only when the exact object is the blob at
the scanned tip, where an ordinary commit removes it. Exposure is decided per
object, not per path: an old version of a file that still exists is
historical, and the report records both `current_head_exposure` (the path is
still present) and `current_head_object` (this blob is the tip's blob).
Historical instances are listed under `accepted_findings` with the disposition
`retained_historical_review_finding_not_a_release_blocker`.

`oversized_blob` is reported and never gated. GitHub's push limit is the hard
ceiling on any object that reached the public remote, the release checker
owns current-tree size policy, and a generated index over the 50 MiB review
threshold is information for the operator rather than a hazard. Every such
object is listed with its exact size under `accepted_findings` as
`reported_size_review_finding_not_a_release_blocker`.

`docs/release/history-finding-dispositions.json` is the operator's reviewed
disposition data, consumed by the scanner and fingerprinted into the report.
It declares synthetic home segments that the release checker documents as
fixtures, fingerprints of the checker's own synthetic credential literals
(matched by SHA-256, never by value), exact reviewed paths whose watch-term
match is a mathematical identifier, and object rows for individually reviewed
findings. A dispositioned match is still reported, with its reason, under
`accepted_findings`; the file can only add explanation, never delete a row. A
credential shape whose fingerprint is not declared blocks regardless of path.

A compressed single stream such as `index.json.gz` has no member names and is
not an archive; only a real tar or zip is opened for member inspection, and a
stream that does not even decompress remains an `archive_parse_failure`.

The reachable-object walk retains the object ID of every ref, follows
annotated-tag targets, and reviews direct blob refs even when no tree pathname
exists. Such pathless objects receive a redacted ref binding; credential,
private-path, privacy-bearing-ref, and unsafe-archive findings remain release
blockers for operator review. A ref name is exposure evidence, not proof that
the referenced content is harmless.
Pathless direct-ref blobs are still eligible for bounded textual payload scans;
the synthetic `<reachable-ref:...>` label is not treated as proof that the
object is binary, so custom-license markers and other textual trust signals
cannot evade history review.

The payload audit covers reachable `blob`, `commit`, and annotated `tag`
objects. Credential assignments, private filesystem paths, and custom
third-party license markers in commit or tag messages are reported with
redacted reachable-ref labels; commit findings also bind the exact containing
branch and tag refs. Tree objects contribute structure and path reachability,
while blob payloads additionally receive archive-safety inspection.

Every object-backed finding records its object ID, object type and size,
introducing and removing commits, object-history commits, reachable refs,
retrievability from those refs, and a boolean `current_head_exposure` field.
For content and path findings, that boolean means that at least one named
real path is present in the scanned tip; redacted direct-ref labels do not
silently count as current-tree exposure. Privacy-bearing ref findings retain
their explicit ref exposure. The history gate requires this context even for
an otherwise valid non-atomic report, so a moving-checkout receipt cannot
silently omit the distinction between historical and current exposure.

The operator remediation packet carries the same object context for every
selected artifact, including its manifest SHA-256 digest, selection reason, and
governing disposition. A historical third-party artifact selection is therefore
bound to both the reachable Git object and the artifact-level provenance record;
an object ID alone is not a sufficient remediation instruction.
Manifest artifact history also incorporates blob IDs recovered from the
artifact path's introduced and removed commits, so a Git rename or pathname
deduplication cannot hide an older third-party copy from the history blocker.
Every object-backed release blocker, including a private filesystem path found
inside blob content, must have a matching `object_path_selection` entry with its
object identity and blocker kind; an incomplete selection packet is invalid
evidence and cannot pass the history consumer.

The history consumer also validates the shape of that context: `object_type`
must be a non-empty Git type, `size_bytes` must be a non-negative integer (or
null only for a missing ref object), every path must be a non-empty string,
lineage commit arrays must contain 40-character lowercase Git object IDs, and
each reachable-ref row must contain a non-empty `refs/*` name and ref class.
These rules apply to both the blocker and its remediation selection, so a
non-atomic report cannot turn malformed or null context into accepted evidence.

This audit establishes reachability and release risk, not redistribution rights.
An object being retrievable from a ref, or having a citation, DOI, arXiv record,
or official download route, is not permission to redistribute its PDF, scan,
source archive, or other third-party content. The repository's custom
`LicenseRef` likewise governs this project's original material only; it does
not relicense upstream sources. The canonical artifact-by-artifact disposition
in `docs/primary-sources/redistribution-dispositions.json` must therefore be
consulted separately, and link-and-digest-only records remain excluded from the
public candidate. A reachable custom third-party license marker is itself a
`historical_license_marker` release blocker and is copied into the operator
remediation selection for explicit review; no scanner result or custom marker
is an inference of redistribution permission.

Run the evidence check through the canonical local single-flight receipt:

```sh
history_check_receipt="$(python3 scripts/validation_singleflight.py submit --class reachable-history --target check)"
history_check_key="$(printf '%s\n' "$history_check_receipt" | python3 -c 'import json,sys; print(json.load(sys.stdin)["key"])')"
python3 scripts/validation_singleflight.py status --key "$history_check_key"
python3 scripts/validation_singleflight.py collect --key "$history_check_key" --wait
```

The release gate is intentionally stricter and uses its own exact receipt:

```sh
history_gate_receipt="$(python3 scripts/validation_singleflight.py submit --class reachable-history --target release-gate)"
history_gate_key="$(printf '%s\n' "$history_gate_receipt" | python3 -c 'import json,sys; print(json.load(sys.stdin)["key"])')"
python3 scripts/validation_singleflight.py status --key "$history_gate_key"
python3 scripts/validation_singleflight.py collect --key "$history_gate_key" --wait
```

It returns non-zero whenever a prohibited object remains reachable, even when
the current-tree disposition is link-only. Secret-like matches are represented
only by object IDs, paths, counts, and redacted SHA-256 fingerprints; payloads
are never printed into logs or public artifacts.

The cross-surface release checker, `python3 scripts/check_release.py`, does
not invoke this gate; the reachable-history workflow is the surface that
consumes it, and a red result there is a release finding in its own right
rather than something the top-level checker can waive or has already covered.
The workflow scans the exact checkout under test and validates that fresh
report; the committed `docs/release/reachable-history-audit.json` is the last
operator-anchored record, regenerated when the scanner or dispositions change.

The evidence comparison is clone-shape invariant: each branch name is compared
once whether it is seen as a local head or as origin's remote-tracking ref,
every tag is compared by the commit it peels to, and pull-request merge refs
and the symbolic origin HEAD are excluded from the comparison because no
reader can clone them. All of them are still scanned.

## Future-ingress enforcement

`.github/workflows/reachable-history-trust.yml` runs on every push and pull
request (and is available by manual dispatch). Its checkout fetches the full
history and tags, then scans that checkout, validates the fresh evidence, runs
the deleted-object, disposition and redaction fixtures, and applies the
public-clone release gate. There is no path-filter exception for a future
commit: a change anywhere in the repository re-enters this boundary, so a new
reachable object cannot be treated as safe merely because the current-tree
files look unchanged.

The workflow is assurance evidence, not authorization to mutate shared
history. A red result stays red until an operator-approved remediation is
performed and a fresh exact-commit, all-ref report is regenerated and
validated; CI cannot rewrite refs, delete recovery evidence, or waive the
decision.

No agent may rewrite history, delete refs/tags, force-push, or remove recovery
evidence. If the audit is blocked, its embedded operator decision is the
smallest reversible action packet: protected identities and refs, exact object
and path selection, expected commit/tag/receipt consequences, collaborator and
fork coordination, verification commands, rollback material, and the outbound
mutation that requires explicit operator approval.

The gate also rejects a stale report. For an atomic scan, only the owned audit
control-plane paths may differ after the report's scan anchor; a source or ref
change requires a fresh all-ref scan and a new exact release decision.

The scanner freezes the starting ref tips before traversing objects. If the
shared checkout moves during that traversal, the report records the complete
start/end ref delta and the end commit. Such evidence is accepted only as an
explicit red release decision with a `non_atomic_scan` blocker, unchanged
non-active refs since the scan ended, and no non-control-plane source delta.
The public-clone gate remains non-zero; this is evidence for the operator's
reversible remediation decision, never a way to turn a moving checkout green.

