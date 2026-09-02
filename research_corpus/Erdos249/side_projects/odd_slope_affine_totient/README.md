# Odd-slope affine totient API

This directory contains two deliberately separate formal surfaces for the
totient `k`-kernel work. The Lean files are reusable arithmetic and affine-
family interfaces; the all-base finite-level rank theorem remains a paper
argument recorded in
[`docs/formal_math/odd_slope_affine_totient_independence.md`](../../docs/formal_math/odd_slope_affine_totient_independence.md).

## Import and namespace map

| Surface | Import root | Namespace | Evidence role |
| --- | --- | --- | --- |
| `TotientKernelReduction.lean` | `Mathlib.Data.Nat.Totient` | `Erdos249257` | Lean-checked reduction/spanning identities for every positive base |
| `OddSlopeAffineTotient.lean` | `Erdos249257.TotientMahlerDefect` | `Erdos249257.OddSlopeAffineFamily` | Lean formalisation of linear independence for the restricted odd-slope family |
| `verify_allbase_kernel.py` | Python + SymPy | n/a | finite exact-arithmetic/rank probe; not a formal proof |
| `verify_oddprime.py` | Python | n/a | finite odd-prime probe; not a formal proof |

Keep the two Lean files independently importable. A consumer that needs only
the arithmetic reduction layer should import `TotientKernelReduction`; it
should not inherit the heavier CRT--Dirichlet affine-family construction.

## Reusable Lean declarations

`TotientKernelReduction.lean` exposes:

- `Erdos249257.totient_mul_eq_of_primes_dvd`, the prime-support engine;
- `Erdos249257.totient_pow_mul_eq`, the zero-residue reduction
  `φ(k^j n) = k^(j-1) φ(k n)`;
- `Erdos249257.totient_pow_mul_gcd_cross_eq`, a division-free composite-base
  identity with the exact gcd correction;
- `Erdos249257.gcd_pow_mul_add_eq_gcd`, the affine gcd invariance lemma; and
- `Erdos249257.totient_pow_mul_affine_gcd_cross_eq`, the constant-along-a-
  section affine specialization.

`OddSlopeAffineTotient.lean` exposes the data shape
`Erdos249257.OddSlopeAffineFamily`, the sequence definitions `value` and
`family`, the witness structure `PrimeRow`, and the theorem
`Erdos249257.OddSlopeAffineFamily.linearIndependent_family`. The latter is a
restricted corollary formalisation: odd slopes, primitive residues, and
pairwise non-proportional forms are explicit hypotheses.

## Consumer and evidence boundaries

- The reduction declarations support the finite-level spanning half of the
  ordinary all-base kernel argument.
- The odd-slope declaration is a Lean formalisation of a restricted corollary
  of Martin's 2006 affine-ordering theorem; it is not a new theorem or a
  formalisation of Martin's full result.
- `verify_allbase_kernel.py` computes ranks over a finite field as a lower
  bound for the rational rank. Its output cannot promote the result to Lean
  proof status, an independent review, or an irrationality argument.
- None of these surfaces proves irrationality, a rational-tail upper bound,
  novelty, significance, or progress on Erdős #249.

The downstream source note and reviewer card remain the human-facing
consumers. Their source-result identifiers and claim ceiling are joined by
[`totient_kernel_finite_rank.review_unit.v3.json`](../../docs/formal_math/review_units/totient_kernel_finite_rank.review_unit.v3.json);
that review unit is an adapter, not a second theorem registry.

## Validation and replay

Run the narrow owner checks from the repository root:

```sh
./repo-python -m pytest tests/test_totient_kernel_api_surface.py
./repo-python formal_math/odd_slope_affine_totient/verify_allbase_kernel.py
./repo-python formal_math/odd_slope_affine_totient/verify_oddprime.py
```

The Python probes are bounded computational evidence. Preserve their receipt
files and read their finite-resource and claim-ceiling notes before reusing
their output. For formal validity, use the current Lean project build and
inspect the exact declarations named above; this README does not replace
source-owner validation.

The exact computational inputs, code/receipt hashes, environment snapshot,
resource rules, falsifying fixtures, archival policy, and downstream consumers
are bound in
[`computational_evidence_manifest.v2.json`](computational_evidence_manifest.v2.json).
That manifest is a replay descriptor and currentness handoff, not a result
registry or proof authority; changing a script, receipt, or consumer boundary
requires a new manifest generation.
