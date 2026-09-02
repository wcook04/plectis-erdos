# Erdős #243 research corpus (source-current snapshot)

Exported from private authoring commit `ef1a3ec69dff2a10c9532307616df421618d17ef` on 2026-09-02 for the Type B solve fleet
`erdos_breakthrough_dodecuple_2026_09_02_r1`. This is a reading corpus: every committed problem-facing Lean module, lab note,
proof note, checker, probe, pinned receipt, the manuscript source, and the cross-problem synthesis
documents. It is NOT a Lake project; the kernel-checked, replayable Comparator entries live in the
release repository https://github.com/wcook04/plectis-erdos-lean (see `entries/` here for the
entry statements).

## Layout

- `problem/`: `ErdosProblems/Erdos243/` (research_packet.json is the non-claims ledger: target, exact results, negative results, open producers, claim ceiling)
- `shared_lean/`: Lean modules filed under a sibling namespace that carry this problem's mathematics
- `entries/`: statement-isolated Comparator entry packages (Challenge / Solution / AxiomAudit / formalization.yaml)
- `probes/`, `probe_receipts/`, `receipts/`: executable probes and their pinned outputs
- `paper/`: manuscript source
- `docs/`: longitudinal truth, prior-art adjudication, situation map
- `STRONGEST_RESULTS.json`: the activation map (strongest premises and exact no-gos with public paths)
- `CORPUS_MANIFEST.json`: per-file source and published digests

## Target

Erdos Problem #243. Let a_1 < a_2 < ... be a sequence of positive integers with a_{n+1}/a_n^2 -> 1. Prove that if sum_n 1/a_n is rational then a_{n+1} = a_n^2 - a_n + 1 for all sufficiently large n, that is, the sequence eventually satisfies the Sylvester recurrence. The problem is open in this generality; no boundedness, periodicity, sign, or rate hypothesis beyond a_{n+1}/a_n^2 -> 1 and rationality of the reciprocal sum may be added to the statement being proved.

## Claim boundary

This snapshot is of an OPEN problem. Nothing here is a solution claim; the packet's `claim_ceiling`
field governs what is established. Receipts are finite computations and never cofinal evidence.

File count: 105.
