# Erdős #1049 research corpus (source-current snapshot)

Exported from private authoring commit `42de2bf94b8f6aeccfb1c5c0dc60626b1afc951a` on 2026-09-02 for the Type B solve fleet
`erdos_breakthrough_dodecuple_2026_09_02_r1`. This is a reading corpus: every committed problem-facing Lean module, lab note,
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

Let v_m^* = sum_{t>=0} q^((m+1)t) (q;q)_m^3 (q^(t+1);q)_m / (q^(m+1+t);q)_(m+1) be Zudilin's normalized forms at x = z = 1, and let V_N^* = det(v_(i+j)^*)_{0 <= i,j < N} be the associated Hankel determinant. Zudilin (Research in Number Theory 2 (2016), Article 15, Section 4) proves ord_q V_N^* >= N(N-1)(2N-1)/6. Prove that this holds with EQUALITY for every N >= 1, and prove the exact leading coefficient of q^(N(N-1)(2N-1)/6) in V_N^*. Equivalently: prove that the associated-graded leading matrix is nonsingular for every N and identify its determinant exactly. This is a statement about a named construction in the q-series and Pade literature; it is NOT the irrationality of any Lambert value, and that parent must not be substituted for it.

## Claim boundary

This snapshot is of an OPEN problem. Nothing here is a solution claim; the packet's `claim_ceiling`
field governs what is established. Receipts are finite computations and never cofinal evidence.

File count: 185.
