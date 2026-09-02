# Erdős #249 research corpus (source-current snapshot)

Exported from private authoring commit `084b929db29ad54ca081780ba758cda584014568` on 2026-09-02 for the Type B solve fleet
`erdos_solve_dodecuple_2026_09_02_r1`. This is a reading corpus: every committed problem-facing Lean module, lab note,
proof note, checker, probe, pinned receipt, the manuscript source, and the cross-problem synthesis
documents. It is NOT a Lake project; the kernel-checked, replayable Comparator entries live in the
release repository https://github.com/wcook04/plectis-erdos-lean (see `entries/` here for the
entry statements).

## Layout

- `problem/`: `ErdosProblems/Erdos249/` (research_packet.json is the non-claims ledger: target, exact results, negative results, open producers, claim ceiling)
- `shared_lean/`: Lean modules filed under a sibling namespace that carry this problem's mathematics
- `entries/`: statement-isolated Comparator entry packages (Challenge / Solution / AxiomAudit / formalization.yaml)
- `probes/`, `probe_receipts/`, `receipts/`: executable probes and their pinned outputs
- `paper/`: manuscript source
- `docs/`: longitudinal truth, prior-art adjudication, situation map
- `STRONGEST_RESULTS.json`: the activation map (strongest premises and exact no-gos with public paths)
- `CORPUS_MANIFEST.json`: per-file source and published digests

## Target

Erdős Problem #249 asks whether S = sum_{n>=1} phi(n)/2^n is irrational, where phi is Euler's totient function. The binary base is fixed; the coefficient is totient rather than divisor (tau) or sigma_1. A complete solution must decide irrationality of this single explicit series. ALREADY SETTLED and NOT the target: periodic nonnegative rational weights (Luca–Tachiya 2017 Theorem 1); the value sum_{gcd(a,b)=1} 1/(2^{a+b}-1) = 1 (geometric coprimality — shows that route cannot force irrationality); and rationality of sum mu(d)/(2^d-1)^2 via Postelmans–Van Assche (cited, not formalised). The repository's Lean frontier proves equivalence to FullMersenneCanonicalBasepointResidueGapSupply. Finite denominator exclusions (q > 7.96×10^34) and Schur/rank obstructions are evidence, not cofinal proofs.

## Claim boundary

This snapshot is of an OPEN problem. Nothing here is a solution claim; the packet's `claim_ceiling`
field governs what is established. Receipts are finite computations and never cofinal evidence.

File count: 109.
