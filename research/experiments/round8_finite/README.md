# Four exact finite controls from Round 8

These small standard-library programs adapt finite examples from the P1–P4
returns at public source commit
`0268dd8bfb2a556a0c93078337d42c6d07138fa2`. Their source-object,
returned-implementation, staged-program, and direct-output SHA-256 values are
in [manifest.json](manifest.json). Each command has a fixed small workload,
prints JSON, writes no data, and makes no network, Lean, model, or build call.

From the public repository root:

```sh
python3 research/experiments/chain_transcendence/round8_finite_cut.py
python3 research/experiments/erdos269/round8_affine_collision.py
python3 research/experiments/erdos1049/round8_calibrated_denominators.py
python3 research/experiments/erdos249/round8_signed_pulse.py
python3 research/experiments/round8_finite/test_round8_finite.py
python3 -O research/experiments/round8_finite/test_round8_finite.py
```

| Return | Finite observation | Evidence boundary |
| --- | --- | --- |
| P1, separated divisibility cuts | At `t=3/2`, finite `A={1,3}`, `X=46/19`, the correction `J=5/2` is not an integer although `2²J` is; a separate `L=2,M=6` cut has an exact cleared-prefix polynomial and positive bounded tail remainder. | This demonstrates the lost fixed integer lattice and one finite cut, not an infinite support or Subspace-Theorem conclusion. |
| P2, ordered-word transfer | A contextual swap defect is exactly `1/420`; distinct words `(5,7,3,2)` and `(7,2,3,5)` share the affine map `(B,D)=(210,51)`; periodic `(2,3)` has rational fixed point `4/5`. | Word spelling alone does not certify a nonzero late swap. No orbit-closure or irrationality claim follows from a finite map. |
| P3, calibrated height countermodel | At `q=2/3`, moment and normalized-tail denominator formulae hold for `n=1..5`; the rank-two naive row clearer leaves denominator `625`. | This is exact arithmetic of the returned countermodel, not the actual #1049 moments, all-rank asymptotic, or failure of a recurrence-specific criterion. |
| P4, signed totient packet | `139` small progression moments vanish, the next moment is nonzero, and one packet at genuine totient positions `1000,1004,1008` stays in `[0,n]`. | A finite stencil does not construct the simultaneous infinite sequence, preserve an entire Dirichlet defect, or decide the actual totient series. |

The controls deliberately do **not** compose into a solution. P2's discrete
lattice uses integer radices, while P1 records its failure at a rational base;
P1 uses an additional number-field route. P3's coefficient-height trap concerns
a different polynomial-value strategy and does not refute P1's product-formula
argument. P4's corrections are signed, so its example does not satisfy P1's
positive-support hypotheses. These finite results can falsify an invalid
transfer of assumptions; the ordinary proofs and source-specific claims remain
with the mathematical review and formal owners.

The [calibrated finite Lean probe](../../probes/Round8CalibratedFinite.lean)
proves the rational seed normalization and finite telescoping identity. Its
[full-file type and axiom receipt](calibrated_lean_receipt.json) applies only
to those finite statements; positive measures and Hankel height remain outside
its scope. Replay from the repository root with
`lake env lean research/probes/Round8CalibratedFinite.lean`.
