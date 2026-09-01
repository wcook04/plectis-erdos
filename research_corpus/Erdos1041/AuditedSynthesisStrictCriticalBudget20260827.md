# Erdős 1041: audited assimilation of the seventeen-dossier synthesis

## Verdict

The attached synthesis (SHA-256
`ce44d82aa03eb157c4476e874230216323ae4326c55ae788e1ff3f7a06abd435`)
is mathematically substantive but is not a solution of Erdős 1041.  Its
positive claims are already present in the corpus in stronger or more exact
form, while its proposed visibility bridge is already refuted by stronger
certificates.  Copying the prose into `research_packet.json` would therefore
create duplicate and weaker authority.

This pass assimilates it by a dominance crosswalk and one new formal consumer:
the strict critical-point budget is now Lean-checked with an explicit slack
certificate.

## Dominance crosswalk

| Attached claim | Source-current disposition |
|---|---|
| closed-disc reduction and strict rescaling | already owned by `GenericSufficiencyClosure.md` |
| convex-hull metric projection | already owned by `TypeBReturnAssimilation20260826.md`; auxiliary only |
| discriminant produces a critical value below one | already part of the critical-budget route; it does not supply containment |
| two nearest critical-point distances have sum below two | strictly strengthened by `CriticalTwoRootProximity.lean`: some pair has sum at most `2*r`, where `r^n` is the full distance product |
| nearest-root visibility can fail | strengthened by the five-distinct-root, unique-nearest exact certificate in `CriticalTwoRootProximity.lean` |
| simultaneous radial product inequality | already strengthened to the arbitrary-modulus exponential power-sum deficit in `TypeBReturnAssimilation20260826.md` |
| average inverse-ray length misses critical separatrices | already absorbed by the branch/attachment no-go corpus; the live residual is a non-pointwise attachment-compatible selector |

The attachment's repeated-root visibility example is therefore useful as an
intuition pump, but it is not the canonical obstruction.  The source-current
certificate removes both weaknesses: its roots are distinct and the escaping
spoke points to the unique nearest root.

## Formal delta

`AuditedSynthesisStrictCriticalBudget20260827.lean` proves
`exists_two_roots_dist_sum_lt_two_with_geomMean_slack`.

Let `c` be a non-root critical point, let the roots be `z_k`, and let

```text
r^n = product_k |c-z_k|,    0 < r < 1.
```

Then there are distinct `i,j` such that

```text
|c-z_i| + |c-z_j| < 2
```

and, more quantitatively,

```text
2(1-r) <= 2 - (|c-z_i| + |c-z_j|).
```

This is stronger than the attached nearest-pair lemma in two ways: it retains
the geometric-mean scale `2r`, and it exposes a certified amount of strict
metric slack.  It is not a new path theorem.  Exact visibility failures show
that metric slack cannot simply be spent on the two straight spokes.

## Three-route pressure test

1. **Critical metric route.** Survives, but the attachment's proof is dominated
   by the existing `2r` theorem.  The strict-slack consumer above is the only
   new proof-bearing delta.
2. **Radial cover route.** Survives only as an aggregate, moving-index
   statement.  The exact five-direction ONE-SPOKE countermodel forbids the
   fixed-index upgrade needed for a radial path.
3. **Visibility obstruction route.** The attachment's perturbative statement
   is replaced by the exact distinct-root, unique-nearest certificate already
   in Lean.  This deletes perturbation bookkeeping but does not decide the
   unrestricted problem.

The smallest honest frontier remains unchanged: construct a non-pointwise,
attachment-compatible consumer for descending/component geometry, or prove
COVER.  Erdős 1041 remains open.

## Validation

```sh
lake env lean research_corpus/Erdos1041/AuditedSynthesisStrictCriticalBudget20260827.lean
./repo-python -m system.lib.formal_math_frontier_integrity --repo-root . --check-currency
```
