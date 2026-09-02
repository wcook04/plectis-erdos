# Erdős #1049 research corpus (source-current snapshot)

Exported from private authoring commit `084b929db29ad54ca081780ba758cda584014568` on 2026-09-02 for the Type B solve fleet
`erdos_solve_dodecuple_2026_09_02_r1`. This is a reading corpus: every committed problem-facing Lean module, lab note,
proof note, checker, probe, pinned receipt, the manuscript source, and the cross-problem synthesis
documents. It is NOT a Lake project; the kernel-checked, replayable Comparator entries live in the
release repository https://github.com/wcook04/plectis-erdos-lean (see `entries/` here for the
entry statements).

## Layout

- `problem/`: `ErdosProblems/Erdos1049/` (research_packet.json is the non-claims ledger: target, exact results, negative results, open producers, claim ceiling)
- `shared_lean/`: Lean modules filed under a sibling namespace that carry this problem's mathematics
- `entries/`: statement-isolated Comparator entry packages (Challenge / Solution / AxiomAudit / formalization.yaml)
- `probes/`, `probe_receipts/`, `receipts/`: executable probes and their pinned outputs
- `paper/`: manuscript source
- `docs/`: longitudinal truth, prior-art adjudication, situation map
- `STRONGEST_RESULTS.json`: the activation map (strongest premises and exact no-gos with public paths)
- `CORPUS_MANIFEST.json`: per-file source and published digests

## Target

Erdos Problem #1049 (a conjecture of Chowla) asks whether F(t) = sum_{n>=1} 1/(t^n - 1) = sum_{n>=1} tau(n)/t^n is irrational for EVERY rational t > 1, where tau(n) is the number of divisors of n (Erdos, New Advances in Transcendence Theory, CUP 1988, p. 102; catalogued open at erdosproblems.com/1049). A complete solution must decide this for all rational t > 1; the repository's own target field words it as 'Determine irrationality of the rational-base Lambert values, with 3/2 as the first resistant explicit base', and writing t = a/b in lowest terms with a > b >= 1 the least naive height H(a/b) = max(a,b) among resistant explicit bases is t = 3/2. The following are ALREADY SETTLED and are NOT the target: every integer base t >= 2 (Erdos 1948, J. Indian Math. Soc. 12, 63-66; reproved with Pade approximation by Borwein 1991/1992 and by Van Assche 2001, who also gives mu(F(p)) <= 2pi^2/(pi^2-2) = 2.50828...); every negative integer base with a finite nonzero digit alphabet (Vandehey, Integers 13 (2013) A58, Theorem 1.2); every rational base with log b / log a < 1/2 - 1/pi^2 = 0.398678816..., which includes 7/2 (Bundschuh-Vaananen, Compositio Math. 91 (1994) 175-199, Theorem 2, alpha = -1 case) and strictly contains Duverney's weaker rational region (1/3)(1 - 3/pi^2) = 0.2320... (J. Theor. Nombres Bordeaux 8 (1996) 173-181, Theoreme 2); and, conditional on Zudilin 2004 Lemmas 7 and 2, every rational base with log b / log a < theta* = C_0/C_1 = 0.40568302138406054..., which adds 31/4 and all its powers and no integer base. At 3/2 the ratio is log 2 / log 3 = 0.630929753..., so 3/2 is outside every region above by more than 0.2323. An acceptable deliverable is a complete proof of the parent, or a genuinely new UNCONDITIONAL irrationality theorem at a rational base not covered by Bundschuh-Vaananen (the smallest candidate above their region with a > b^2 is 5/2), or an exact no-go closing a whole class of constructions.

## Claim boundary

This snapshot is of an OPEN problem. Nothing here is a solution claim; the packet's `claim_ceiling`
field governs what is established. Receipts are finite computations and never cofinal evidence.

File count: 193.
