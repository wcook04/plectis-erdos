# Long-record transfers and inherited lag

No long-record file was edited in this return. Locations below are either labels actually present in the supplied authored parts or **new insertion labels**, explicitly marked. The old record contains references to labels from earlier short-note versions; cross-document references must be reconciled as part of the paired release.

The principal authored file is `reasoning-parts/erdos269/extended_record.tex`. The family inventory is `reasoning-parts/erdos269/family_catalogue.tex`.

## Existing destinations and exact transfers

### `long:finite-geometry` — elementary geometry and worked examples

Move the live `sec:cells`, the full finite-box `sec:fibre`, and the finite-shell material from `sec:shell` here, merging with the examples already present. Preserve the statements labelled `res:cell`, `res:jump`, `res:count`, `res:drop`, `res:shell` and `res:short`, with their hypotheses and proofs. The short-note replacement retains only the height comparison, regrouping identity and simpler cap proof needed by its recurrence.

The old paragraph saying the ten smallest LCM values are tabulated in the short note becomes false after the cut; put that table directly here. Do not leave an inaccessible forward reference to an excised table. The existing eight-point fibre example can then follow it naturally.

### `long:general-carries`, `long:denominator-reduction`, `long:windowconsumer`

The current `long:denominator-reduction` is conditional cancellation of a common factor in an abstract carry. It is not the actual rationality-to-tail bridge. Retain it as a general algebra lemma, and insert the actual prefix identity and bridge under **new label** `long:actual-rationality-bridge`.

Transfer the removed symmetric prime-power half-height clearing, all-scale lattice, reduced-integrality and pinning refinements from the live `sec:actual-orbit`. Preserve the exact scales: `T_a` is raw; `X_a=H(2^a)T_a/2` is normalised. The old reference to `res:actual-cancellation` is stale: the current live note uses `res:denominator-reduction`. Repoint it to the new long-record actual bridge rather than pretending the old abstract lemma already supplies it.

Retain the generic extinction consumer under `long:windowconsumer`. Give its dependence on a supplied escape condition explicitly. The actual valid-cap equivalence belongs in an adjacent paragraph as a reformulation of the parent, not as an independent escape construction.

Transfer the full live window growth, necessary-depth, endpoint pinning and finite-depth telescope material under **new label** `long:actual-window-refinements`. Reconcile the old references `res:no-bounded-length`, `res:window-growth` and `res:consumer` with the retained local versions. Do not strengthen pointwise conditions or exchange start/depth quantifiers during transfer.

### `long:experiments` — preserve the cap and status of every experiment

Move the live bounded certificate rows and their definitions here. They use the exact smaller source cap at the endpoint jump index, not the simple `90B(a+1)^2` cap used by the shortened proof. Do not change one cap in the text while retaining the numerical certificate computed for another.

The older histogram records 3,869,934 tested pairs and a smaller earlier run of 106,666 pairs. Retain these as archived reports with their own parameters and provenance. Round 6 did not replay them. The new 29,073-check regression is a separate result and is not evidence that those earlier scans were reverified.

The phrase about what a reader should expect if residues behave generically is heuristic; keep it labelled as such or remove it. The histogram establishes a finite distribution, not a distribution theorem for the actual infinite residue sequence.

### `long:history`

Keep the existing de-duplicated-series historical correction and Fan attribution. These are already correct and are not new round-6 findings. The two-prime theorem remains attributed in the shortened note. Detailed comparison and chronology stay here.

### `long:sources`

After transfers, rebuild the source inventory against the actual source coordinates. In particular, `FiniteCutRank.lean` contains the interval-difference engine, not the full arithmetic normal-form theorem. The new uncompiled `R6WeightedChannelRedistribution.lean` must not appear as proof authority for the infinite interval or spectral theorem.

## Inherited omissions requiring named insertions

The old extended record contains an abstract denominator reduction and older examples, but does not contain all the ordinary results subsequently added to the live note. These are inherited lags, not new round-6 theorems.

**New insertion `long:finite-cut-classification`.** Copy the live proposition `res:finite-cut-rank` and its complete proof, followed by the already-established leading-four example. The new arithmetic normal form is separate below.

**New insertion `long:jump-constraint-majorant`.** Transfer the live proof of `Qtilde(n)=(1210n^2+9130n+18847)/11979`: the no-three-consecutive-two-jumps argument, its use in the denominator product, the generating function `(1+z/2+z^2/6)/(1-z^3/12)`, and the moment evaluation. This proof is not replaced by the weaker short-note constant. The associated Lean moment identities are supporting algebra, not on their own a proof of the actual-series inequality.

**New insertion `long:torus-fourier-value`.** Transfer the complete live theorem `res:torus-fourier-value`, equation `eq:torus-fourier-value`, its convergence assumptions and its correction term. The old abstract carry section is not a destination adequate to identify this independent representation. Keep it separate from the new continuum carry spectrum: they concern different functions and different analytic questions.

**New insertion `long:earlier-ordinary-results`.** Preserve the earlier fibre, floor-product, relation-classification, perturbation and constrained-digit results with their actual evidence/attribution status. In particular, the r5 thin-set theorem must retain its canonical one-sided correction range. Do not silently replace it with a statement about arbitrary signed shell-preserving perturbations.

## New round-6 proposals, pending independent review

**New insertion `long:cut-arithmetic-normal-form`.** Memorandum Section 2, Theorem 2.1 and Corollary 2.2, including image cardinalities, bad characteristics and the `(2,3,11)` fixed-layer example. The short corollary proposed for the note does not require importing all this module-theoretic material.

**New insertion `long:two-channel-redistribution`.** Memorandum Section 3 in full. Do not retain only the abstract Cantor-expansion argument and omit the actual positive-capacity proof: that would lose the main new source-specific content. Preserve the exact 3-point and 25-point certificates, the selected height ratio, the positivity check and the comparison with the existing all-three-channel theorem. The constants are deliberately non-optimal.

**New insertion `long:carry-spectrum`.** Memorandum Section 4, including the signed eigenvalue sequence, completeness argument, the fixed-rank sample limit and its norm. State explicitly that this is not the full nonstationary analytic theorem in the research mandate.

At `sec:erdos-269-complete-family-map` in `family_catalogue.tex`, add a pointer to these new ordinary insertions only after they are accepted. Do not change the parent endpoint or use the existence of this return as a formal receipt.

## Source extracts supplied

`edits/relocation_extracts.tex` preserves the exact original sections most heavily compressed by the main profile. The extracts include current label names and source links. They are intentionally not auto-inserted into the old long record: copying them blindly could duplicate existing definitions and create cross-document label collisions. Merge by the destinations above, retaining proofs and assumptions, then compile both documents and check their cross-references.
