# Erdős #1041 research corpus (source-current snapshot)

Exported from private authoring commit `42de2bf94b8f6aeccfb1c5c0dc60626b1afc951a` on 2026-09-02 for the Type B solve fleet
`erdos_breakthrough_dodecuple_2026_09_02_r1`. This is a reading corpus: every committed problem-facing Lean module, lab note,
proof note, checker, probe, pinned receipt, the manuscript source, and the cross-problem synthesis
documents. It is NOT a Lake project; the kernel-checked, replayable Comparator entries live in the
release repository https://github.com/wcook04/plectis-erdos-lean (see `entries/` here for the
entry statements).

## Layout

- `problem/`: `ErdosProblems/Erdos1041/` (research_packet.json is the non-claims ledger: target, exact results, negative results, open producers, claim ceiling)
- `shared_lean/`: Lean modules filed under a sibling namespace that carry this problem's mathematics
- `entries/`: statement-isolated Comparator entry packages (Challenge / Solution / AxiomAudit / formalization.yaml)
- `probes/`, `probe_receipts/`, `receipts/`: executable probes and their pinned outputs
- `paper/`: manuscript source
- `docs/`: longitudinal truth, prior-art adjudication, situation map
- `STRONGEST_RESULTS.json`: the activation map (strongest premises and exact no-gos with public paths)
- `CORPUS_MANIFEST.json`: per-file source and published digests

## Target

Erdos Problem #1041 (Erdos, Herzog and Piranian 1958). If a monic polynomial f(z) = prod_i (z - z_i) has all of its roots in the open unit disk, prove that two of its roots can be joined by a curve of length less than 2 contained in the open lemniscate {z : |f(z)| < 1}. The constant 2 is sharp: z^n - r^n forces length tending to 2. The problem is open; no hypothesis on degree, root multiplicity, root configuration, or critical-value separation may be added to the statement being proved.

## Claim boundary

This snapshot is of an OPEN problem. Nothing here is a solution claim; the packet's `claim_ceiling`
field governs what is established. Receipts are finite computations and never cofinal evidence.

File count: 1316.
