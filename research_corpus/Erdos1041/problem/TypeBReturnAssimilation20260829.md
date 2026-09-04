# Erdős 1041: two-return assimilation (mean-shift containment + full-parent claim)

## Verdict and evidence boundary

Batch `erdos1041_20260829_meanshift_fullparent` is closed at two
operator-supplied returns. The immutable paths, byte lengths, and SHA-256
digests are recorded in
`state/formal_math/type_b_return_batches/erdos1041_20260829_meanshift_fullparent/intake.json`.
The returns are advisory evidence, not source authority.

Neither return proves unrestricted Erdős 1041.

* **Return A** (mean-shift containment) is a *rediscovery wave*: its Lemma 1,
  both corollaries, the critical-point disc, the radial estimate, and the
  root-disk identity are all occupied by corpus authority
  (`BarycentricEnvelope.md` §2 (C)/(D)/(E), `CriticalBudgetLab.md` (ID)).
  Its self-declared open step — the local graft inequality — remains open, and
  the new grid-Dijkstra search below shows it is **vacuous in the measurable
  small-μ regime**: there the (E)-disc already contains the merging roots and
  the pair joins by a chord of length ≤ 2ρ_c < 2 without any graft.
* **Return B** (`full_parent_proof`) labels itself a full proof. Its §4
  (genericity removal) and §5 (strictification) are occupied verbatim by
  `GenericSufficiencyClosure.md` (Theorem L, Corollaries D/S, Theorem Q). Its
  §2 covering lemma is the batch's only genuinely new verified mathematics and
  is landed in `ExteriorRootProductCovering.md` with a Lean-checked scalar
  kernel. Its §1 "activated last-lobe reduction" — the step that would consume
  the lemma — **is not established**: the obstruction (2) and the reduction
  appear nowhere in the corpus, the Lean modules, `research_packet.json`
  (155 exact results, 67 negative results), or any outbound packet (all
  `erdos1041_*` packet directories grepped). This is the third full-proof wave
  to fail on an "activated" composite implication absent from its cited
  sources, after return 003 of batch
  `erdos1041_20260828_solution_octuple_returns_01` and b03_r2_c01 of batch 03.

The parent claim ceiling remains open.

## Claim coverage ledger

Authority bands are: 1 formal/Lean, 2 exact certificate, 3 reviewed ordinary
proof, 4 advisory or conditional, 5 numerical, and 6 rejected.

| Claim | Normalized content | Band | Terminal disposition | Authority / residual |
|---|---|---:|---|---|
| rA_c01 | Lemma 1: `\|P(z+δ)\|^{2/n} ≤ \|P(z)\|^{2/n}(1 − \|H\|²/(nS) + (S/n)\|δ + conj(H)/S\|²)` via AM–GM. | 3 | `occupied_in_value` | The completed-square identity is exactly `BarycentricEnvelope.md` §2 (C)'s proof; formalized in `BarycentricEnvelope.lean`. Re-verified numerically (`MEANSHIFT.L1`, margin 1.8e+1). |
| rA_c02 | Corollary 2: the mean-shift homotopy `Φ_s(z) = z + s(M(z) − z)`, `M = z − conj(H)/S`, preserves every sublevel `\{|P| ≤ t\}`, `0 ≤ s ≤ 2`. | 3 | `occupied_in_value` | The `t = \|P(z)\|` member is corpus (C); the segment is its diameter; `BarycentricTargetDisc.md` already studies the inverse-square flow `z' = B(z) − z`. Re-verified (`MEANSHIFT.C2`). |
| rA_c03 | Corollary 3: slack disc `B(M(z), sqrt(\|H\|²/S² + (n/S)(t^{−2/n}−1))) ⊂ \{|P| < 1\}` at `\|P(z)\| = t < 1`. | 3 | `landed_minor` (fine gloss) | One-line consequence of the corpus's own completed-square identity with threshold `t^{−2/n}`; the corpus states the `t = \|P(z)\|` member (C) and the critical member (E) but not the interpolated family. Re-verified (`MEANSHIFT.C3`, min margin 2.1e−2). |
| rA_c04 | Critical-point disc `B(c, ρ_c) ⊂ \{|P| < 1\}`, `ρ_c² = (n/S_c)(μ^{−2/n} − 1)`. | 3 | `occupied_in_value` | Identical to `BarycentricEnvelope.md` §2 (E): `δ_c² = n(1 − ρ²)/(S_c ρ²)` with `ρ = μ^{1/n}`. |
| rA_c05 | Root-disk identity `(1 − \|c\|²)S_c = n + Σ_j (1 − \|a_j\|²)/\|c − a_j\|² > n` at critical points. | 3 | `occupied_in_value` | Exactly `CriticalBudgetLab.md` (ID), proved there with **no disk hypothesis**; (STAR) `(STAR)` follows there. Re-verified exactly (`MEANSHIFT.ID`, residual 0.0). |
| rA_c06 | Radial estimate `\|P(c+δ)\| ≤ μ(1 + (S_c/n)\|δ\|²)^{n/2}` at critical points. | 3 | `occupied_in_value` | Lemma 1 specialized at `c` (where `H(c) = 0`); same completed-square identity. |
| rA_c07 | Open step: graft inequality `d(a, B(c*, ρ)) + d(b, B(c*, ρ)) ≤ d_a + d_b − 2ρ` at the least-critical hub. | 4 | `blocked_external` (measured) | Not proved by the return. New discrimination evidence below: in every measurable configuration the merging roots already lie **inside** the critical disc (`d_a, d_b < ρ`), where the claim is vacuous and the pair joins by a disc chord of length ≤ 2ρ < 2. Also conditional on the merging-pair hub budget `d_a + d_b < 2`, itself open (`ClaimLRefutation.md` refuted the nearest-pair transfer). |
| rA_c08 | Premise "the hub budget gives `\|a − c*\| + \|b − c*\| < 2`" for the **merging** pair. | 4 | `blocked_external` | `CriticalBudgetLab.md` B1-global is the **nearest** pair; `ClaimLRefutation.md` refuted Claim L (merging ≠ nearest, tie-free witnesses); the merging-pair floor is an open producer in its own right. |
| rB_c01 | Exterior root-product covering lemma: `Λ = (1 − r^m B)/(1 − B) ∈ F(D̄)`; `max_{|ζ|=1} ∏|ζ − r b_j|/|ζ − b_j| ≥ Λ`; Apollonius covering `\{|λ − 1\| < B\|λ − r^m\|\} ⊂ F(D)`. | 3 | `landed` | **The batch's only new theorem.** Independently re-derived and landed in `ExteriorRootProductCovering.md` with sharpness (symmetric configuration, boundary modulus constant), the `m = 1` equality gloss, and the Lean scalar kernel `ExteriorRootProductCovering.lean` (Vieta modulus identity + root placement + covering kernel, zero build errors). Verified: Vieta-zero attains Λ to 0.0; 200/200 covering-region samples to 4.7e−19. No corpus collision (greps over notes, Lean, packet, packets). **No live parent consumer** — see rB_c02. |
| rB_c02 | §1 "activated last-lobe reduction": failure of the closed generic statement (1) produces an exterior block `(m, x, a_j)` with `\|x a_j\| < 1` satisfying obstruction (2); §3 then composes with the lemma. | 6 | `rejected_exactly` | The reduction is a bare attribution to "the packet's" results; none of the activated corpus rows (`CapacityGeodesicConjecture.md` first-merge reduction via `μ ≤ R^n`, `FirstMergeReductionState.md`, `CapacitySaturationBridge.md` Thm 3, `LastLobeCapacityLaw.md`, `ExteriorBlaschkeFibreCapacityGap.md`) states any failure-to-obstruction extraction, and the obstruction (2) appears nowhere in the repository or packets. Since the lemma makes ¬(2) universal, the composite is equivalent to that extraction alone — the entire parent difficulty would live there, and no proof of it exists. Same failure class as r003_c01 and b03_r2_c01. |
| rB_c03 | §4: Arzelà–Ascoli genericity removal (closed statement from generic dense subset). | 3 | `superseded_by_stronger_route` | `GenericSufficiencyClosure.md` Theorem L + Corollary D own it, with Lean kernel and the compact-witness projection. |
| rB_c04 | §5: MEC scaling strictification to the open theorem (`Q = R^{−n}P(Rw)`, length ≤ 2R < 2, `\|P\| ≤ R^n < 1`). | 3 | `superseded_by_stronger_route` | `GenericSufficiencyClosure.md` Corollary S / Theorem Q; also occupied rows t10_c02, b03_r2_c04. |
| rB_c05 | §2 sharpness claim: the covering constant is attained by the symmetric last-lobe configuration. | 3 | `landed` | Verified and sharpened in `ExteriorRootProductCovering.md` §3–§4: for the symmetric configuration `|F|` is **constant** on the circle; for `m = 1` the boundary maximum equals Λ for every configuration. |

Every distinct arrived claim has a terminal disposition. No majority voting was
used; each disposition is anchored to named source authority or a fresh proof.

## New computation: discriminating the graft residual (rA_c07)

`scripts/check_erdos1041_mean_shift_graft_search.py` (grid + 8-neighbour
Dijkstra inside `{|P| < 1}`, scipy labelling of the first-merge component at
bump ladder `μ(1 + 10^{-5..-2})`):

* **All 10 measurable random configurations (n = 3..6, boundary-clustered and
  interior moduli) land in the INSIDE-DISC case**: both merging roots satisfy
  `d_a, d_b < ρ_c`, so the (E)-disc `B(c*, ρ_c)` already contains the merging
  pair and joins it by a chord of length ≤ 2ρ_c — measured worst `2ρ_c = 1.37`
  at n = 3, far below 2. In this regime Return A's graft inequality is
  **vacuous**: no grafting decision is needed because the disc already
  connects the pair.
* The OUTSIDE-DISC case (`d_a, d_b ≥ ρ_c`, where the graft inequality has
  content) requires `μ^{2/n}` close to 1, i.e. the boundary-clustered
  near-Fekete regime — exactly the regime the corpus's own instruments own
  (`TrueGeodesicLab.md` geodesic measurements, `MonotoneTurningProof.md`,
  `BridgeIdentityProof.md`, `NearFeketeTransverseClosure.md`), where the
  measured geodesic ratios stay ≤ 1 (worst `0.9999999935` on `z³ − 0.99³`).
  The grid instrument cannot isolate the first-merge component there
  (near-tie stratum, all four near-Fekete rows skipped honestly) and the
  receipt records that boundary rather than manufacturing evidence.
* Residual shape after this batch: the first-merge route needs (i) the
  merging-pair hub budget `d_a + d_b < 2` (open producer, already isolated by
  `ClaimLRefutation.md`), and (ii) a length bound for the arms
  (`L(c*) < 2`, the corpus's open row) **or** an outside-disc graft bound —
  both only binding in the near-Fekete regime. Return A's corridor changes
  neither.

## Landed artifacts

* `ExteriorRootProductCovering.md` — the covering theorem with complete
  ordinary proof, exact sharpness, the `m = 1` equality gloss, the dual open
  question (naive aligned candidate refuted by search, deficit up to 1.1e+2),
  collision check, and the no-live-consumer claim boundary.
* `ExteriorRootProductCovering.lean` — Lean scalar kernel: Vieta modulus
  identity, root placement, the Λ identity, and the covering value-attainment
  kernel. Zero build errors; replay via `lean_fast_build.py --plan
  ErdosProblems.Erdos1041.ExteriorRootProductCovering`.
* `scripts/check_erdos1041_exterior_root_product_covering.py` — 11-arm
  receipt (COVER8 exact/grid, SHARP, M1EQ, COVER9, MEANSHIFT ×5, DUALPROBE).
* `scripts/check_erdos1041_mean_shift_graft_search.py` — graft discrimination
  search with honest SKIP rows.
* Intake capsule:
  `state/formal_math/type_b_return_batches/erdos1041_20260829_meanshift_fullparent/`.

## Claim ceiling after this batch

New ordinary exact mathematics: the exterior root-product covering lemma
(auxiliary, sharp, no live parent consumer) plus two fine glosses (m = 1
equality; the interpolated slack-disc family, one line from corpus (C)).
New computation: the graft-residual discrimination above. No new parent-facing
producer: (C), COVER, (AP), PGLS, the merging-pair hub budget, `L(c*) < 2`,
and unrestricted Erdős #1041 remain open. The smallest changed residual is
unchanged from the 2026-08-28 batches: a polynomial-coupled attachment or
length theorem binding in the near-Fekete regime.

## Packet feedback

Three successive full-proof waves have now failed on an "activated composite"
section-1 reduction attributed to the packet. A future packet must state
explicitly, in the rendered ask: (a) the corpus owns **no** failure-to-
obstruction extraction; any conditional chain must carry its own proof of the
extraction step; (b) the covering lemma of this batch is now corpus-side
auxiliary mathematics and must be consumed, not rediscovered; (c) the
merging-pair hub budget and `L(c*) < 2` are the named open producers of the
first-merge lane.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_exterior_root_product_covering.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_mean_shift_graft_search.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py \
  --jobs 2 --project-root formal_math/erdos257_period_noncollapse \
  ErdosProblems.Erdos1041.ExteriorRootProductCovering
```
