# Erdős #249 research corpus (source-current snapshot)

Exported from private authoring commit `42de2bf94b8f6aeccfb1c5c0dc60626b1afc951a` on 2026-09-02 for the Type B solve fleet
`erdos_breakthrough_dodecuple_2026_09_02_r1`. This is a reading corpus: every committed problem-facing Lean module, lab note,
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

Two theorems about Euler's totient function that this corpus proves and that belong to fields other than irrationality. (A) EXACT k-KERNEL RANK: for every integer base k >= 2 and every e >= 1, the bounded-depth totient k-kernel has rational dimension exactly k^e + 1, with the explicit canonical basis indexed by the zero channel together with the residues r for which k does not divide r. Prove this unconditionally for every base, that is, prove the all-base linear independence of the canonical family, and determine the exact consequence for the k-regularity theory of phi. (B) THE MOBIUS-MERSENNE LADDER: the signed ladder Theta_r = sum_{d>=1} mu(d)/(2^(rd) - 1) satisfies Theta_r Theta_(r+2) < Theta_(r+1)^2 for every r >= 1, so it admits no representation as the moments of a nonnegative measure. Determine the exact Hankel rank of the ladder: prove or refute that every shifted Hankel determinant of every fixed order is nonzero, and decide whether the Hankel rank is infinite. Neither statement is the irrationality of sum phi(n)/2^n; do not substitute that target.

## Claim boundary

This snapshot is of an OPEN problem. Nothing here is a solution claim; the packet's `claim_ceiling`
field governs what is established. Receipts are finite computations and never cofinal evidence.

File count: 121.
