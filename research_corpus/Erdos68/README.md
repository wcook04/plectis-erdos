# Erdős #68 research corpus (source-current snapshot)

Exported from private authoring commit `389d07b36683fe7eabfc29975ad6697ccb6629cf` on 2026-09-02 for the Type B solve fleet
`erdos_breakthrough_dodecuple_2026_09_02_r1`. This is a reading corpus: every committed problem-facing Lean module, lab note,
proof note, checker, probe, pinned receipt, the manuscript source, and the cross-problem synthesis
documents. It is NOT a Lake project; the kernel-checked, replayable Comparator entries live in the
release repository https://github.com/wcook04/plectis-erdos-lean (see `entries/` here for the
entry statements).

## Layout

- `problem/`: `ErdosProblems/Erdos68/` (research_packet.json is the non-claims ledger: target, exact results, negative results, open producers, claim ceiling)
- `shared_lean/`: Lean modules filed under a sibling namespace that carry this problem's mathematics
- `entries/`: statement-isolated Comparator entry packages (Challenge / Solution / AxiomAudit / formalization.yaml)
- `probes/`, `probe_receipts/`, `receipts/`: executable probes and their pinned outputs
- `paper/`: manuscript source
- `docs/`: longitudinal truth, prior-art adjudication, situation map
- `STRONGEST_RESULTS.json`: the activation map (strongest premises and exact no-gos with public paths)
- `CORPUS_MANIFEST.json`: per-file source and published digests

## Target

Erdos Problem #68. Prove that S = sum_{n >= 2} 1/(n! - 1) is irrational. Erdos further conjectured (Erdos 1988, p. 102) that sum_{n >= 2} 1/(n! + t) is irrational for every integer t, the case t = 0 being the classical irrationality of e - 2. The problem is open for every t other than 0; no periodicity, digit, or growth hypothesis may be added to the statement being proved.

## Claim boundary

This snapshot is of an OPEN problem. Nothing here is a solution claim; the packet's `claim_ceiling`
field governs what is established. Receipts are finite computations and never cofinal evidence.

File count: 147.
