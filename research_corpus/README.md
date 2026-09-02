# Erdős research corpora — eight problems, one snapshot

This directory is a reading corpus, exported from one private authoring commit. Each
`Erdos<N>/` subtree carries that problem's committed Lean modules, lab notes, proof notes,
checkers, probes, pinned receipts, manuscript source, Comparator entry statements, and the
cross-problem synthesis documents.

It is **not** a Lake project. The kernel-checked, replayable entries live in the release
repository <https://github.com/wcook04/plectis-erdos-lean>; `Erdos<N>/entries/` here carries
the statement-isolated Challenge and Solution pairs so a reader can see exactly what is claimed.

**Every problem below is OPEN.** Nothing here is a solution claim. Each problem's
`problem/research_packet.json` is the non-claims ledger: target, exact results, negative
results, open producers, and the claim ceiling that governs what may be asserted. Receipts are
finite computations and are never cofinal evidence. Novelty is unassessed throughout.

## The eight problems

| Problem | What the corpus proves | Where the live obstruction sits |
|---|---|---|
| [#68](Erdos68/) | ExternalVerification68CompanionOrbitBoundary proves that the series is rational exactly when floor(m! C) is congruent to -2 modulo m for all sufficiently large m, where C is the sum over n at least 2 of 1/(n!(n! - 1)), and irrational exactly when that residue is missed cofinally, with the same equivalence at every real base point. | No producer supplies the cofinal residue misses, and exact computation of the strict-successor carries through m = 300000 gives only a finite denominator exclusion for any displayed rational representation. |
| [#243](Erdos243/) | ExternalVerification243PeriodicNegativeOrbit proves that for every offset N, every period h > 0 and every positive drift M, positivity of the negative-magnitude sequence together with e_n < a_n on the tail, the exact recurrence and the shape equation D_n + e_n = (a_n - 1) C_n are contradictory, so no eventually periodic negative-magnitude orbit with positive drift carries a rational value. | The surviving signed-state obstruction is cofinally unbounded negative excursions in the exact dynamic cocycle, and the decisive producer is a global negative-mass, cumulative-LCM or repair-payment theorem. |
| [#249](Erdos249/) | ExternalVerification249RankOneSharpFloor proves that every admissible rank-one quotient exceeds the Möbius Mersenne rung by more than 21/320, that the minimum is attained at a unique admissible pair, and that 1/16 is the largest unit fraction bounding the gap from below. | Irrationality of the binary totient series is equivalent in Lean to a residue-gap supply statement, that for every c and every positive odd v there exists H > 0 divisible by phi(v) whose canonical totient-block residue modulo (2^H - 1)/v lies in the central interval of radius c + H + 1, and no construction supplies that H. |
| [#251](Erdos251/) | ExternalVerification251PolynomialShiftCountermodel exhibits the explicit digit word g(n) = 2(n^2 + 4n + 2) with orbit T(n) = 2(n + 4)^2, which satisfies the dyadic tail recurrence at every index, is positive, even, strictly increasing, unbounded and nonperiodic, has every fixed tail shift integral, and has every adjacent difference past the first term at least fourteen. | The remaining producer is the cofinal adjacent small mismatch, that for each fixed h at least 1 and every N0 there is an index N at least N0 at which T(N+h) - T(N) and T(N+h+1) - T(N+1) both lie strictly between -1 and 1 while g(N+h+1) differs from g(N+1). |
| [#257](Erdos257/) | ExternalVerification257ReciprocalSupport proves that for every infinite exponent set A whose reciprocal sum converges and every integer base b at least two, the series with terms 1/(b^a - 1) supported on A is irrational, with no coprimality, periodicity, density or powerful-support hypothesis. | Every candidate counterexample support now has divergent reciprocal sum, and the surviving fatal branch at the rational target 1/21 is consistent with a permanent affine supercapacity regime, so no theorem forces the cofinal closed returns that would decide membership. |
| [#269](Erdos269/) | ExternalVerification269ThreePrimeStructure proves the exact three-prime running-LCM identity, that the reciprocal-height kernel is constant on every logarithmic cell with exactly 3m jump values across the first m positive jumps, and that the kernel admits injective minors of every order, so it has no finite separable representation. | The normalised infinite dyadic shell tail either reaches an exact integral state or returns cofinally at distance at least 1/31 from every integer, and excluding the exact-integral-state branch is the unresolved step. |
| [#1041](Erdos1041/) | ExternalVerification1041FirstMergeCriticalValueSeparation proves the exact all-degree critical-value separation thresholds C(n, 4) < 1 for every n at least 3, C(n, 3) < 1 for every n at least 4, and C(n, 2) < 1 for every n at least 6, where C(n, S) = (1 + S)^(2/n) log(S/(S - 1)), together with the sign-free consumer that a squared length at most 4 C(n, S) with C(n, S) < 1 forces length strictly below 2. | The sharp constant is settled in every degree only under the critical-spectrum separation hypothesis, and the two surviving unconditional routes are the componentwise combined-charge lemma, that every nontrivial connected component C of the admissible critical forest satisfies the sum over edges e in C of D_e + K_e being at least 0, and the covering statement COVER, that for monic g with roots in the closed unit disk there is a level lambda in [mu, 1] and a compact connected subset Gamma of the first-merge component of {/g/ <= lambda} carrying two roots with every point of Gamma within intrinsic distance 1 of a root. |
| [#1049](Erdos1049/) | ExternalVerification1049HermitePadeNoGo proves that on the admissible region rho at least 0 and sigma at least 1 + rho the rectangular two-function threshold of the explicit exponent model is at most 1/2 - 1/pi^2, with equality exactly at rho = 0 and sigma = 1. | At the base 3/2 the homogenisation ceiling caps every content lane on the fixed diagonal at a > b^2, rank two fails the model even at zero clearing, rank three would require kappa_3 < 0.10721, and no construction supplies a family, integrality, nonvanishing or remainder estimate. |

## Layout inside each `Erdos<N>/`

| Path | Contents |
|---|---|
| `problem/` | the problem directory: `research_packet.json`, Lean modules, labs, proof notes, checkers |
| `shared_lean/` | Lean modules filed under a sibling namespace that carry this problem's mathematics |
| `entries/` | statement-isolated Comparator entry packages (Challenge / Solution / AxiomAudit / formalization.yaml) |
| `probes/`, `probe_receipts/`, `receipts/` | executable probes and their pinned outputs |
| `paper/` | manuscript source |
| `docs/` | longitudinal truth, prior-art adjudication, situation map, contributor frontier |
| `annexes/` | distilled primary sources used as premises |
| `STRONGEST_RESULTS.json` | the activation map: strongest premises and exact no-gos, with public paths |
| `CORPUS_MANIFEST.json` | per-file source and published digests, so the sanitisation boundary is auditable |

## Reading order for a first pass

1. `Erdos<N>/problem/research_packet.json` — the frontier ledger for that problem.
2. `Erdos<N>/STRONGEST_RESULTS.json` — what is strongest, and what is refuted.
3. `Erdos<N>/docs/longitudinal_truth_2026_09_01.md` — how far up each hill the work actually is,
   which results a specialist would stop on, and which attacks have not been tried.
4. `Erdos<N>/docs/prior_art_adjudication_2026_09_02.md` — what the literature already prints.

## Sanitisation

Only content committed at the source ref is exported; the working tree never is. Absolute local
paths are rewritten to `public-source-redacted://` locators and a secret scan aborts the export on
any live-key shape. `CORPUS_MANIFEST.json` records the source digest and the published digest of
every file, so any divergence between them is visible.

