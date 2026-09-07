# Erdős #243 — original-coordinate bounded product defect

A strictly increasing sequence of positive integers whose reciprocal series is
rational, whose growth satisfies `a (n+1) / a n ^ 2 → 1`, and whose product
defect `P n / a n * (a n ^ 2 / a (n+1) - 1)` is bounded above from some index
onward satisfies the Sylvester recurrence `a (n+1) = a n ^ 2 - a n + 1`
eventually. The theorem is kernel-checked in Lean 4 against Mathlib at the
pinned revision, in the original coordinates of the problem, with the integer
state and every analytic hypothesis derived rather than assumed.

The boundary is the third hypothesis: Erdős #243 asks for the same conclusion
without any bound on the product defect, and that problem remains open.

## Statement

Let `a : ℕ → ℕ` be strictly increasing with `a n > 0` for every `n`. Write
`P n = ∏_{j < n} a j` and

```
productDefect a n = P n / a n * (a n ^ 2 / a (n + 1) - 1)
```

Assume

1. the reciprocal series has a rational value: `HasSum (fun n ↦ 1 / a n) (p / q)`
   for an integer `p` and a positive natural `q`;
2. quadratic growth: `a (n + 1) / a n ^ 2 → 1`;
3. an eventually bounded product defect: there are `M` and `N` with
   `productDefect a n ≤ M` for every `n ≥ N`.

Then there is an `N` with `a (n + 1) = a n ^ 2 - a n + 1` for every `n ≥ N`.

## Mechanism

The rational value and the prefix product give an explicit integer state: the
denominator `D n = q * P n` and the cleared numerator

```
clearedIntegerNumerator a p q n = p * P n - ∑_{j < n} q * (P n / a j)
```

which is positive because it equals `D n` times the positive real tail. The
centred error `E n = D n - (a n - 1) * C n` then satisfies `C (n+1) = C n - E n`,
and quadratic growth makes `|E n| / C n → 0`.

The defect hypothesis enters through the dictionary
`E n + q * productDefect a n → 0`, which converts an upper bound on the defect
into a lower bound `-B ≤ E n`. Bounded negative part plus normalised vanishing
is exactly the hypothesis set of the corpus rigidity endpoint, and that endpoint
returns the Sylvester recurrence.

## Boundary

The conclusion is conditional on hypothesis 3. Erdős #243 asks for the same
conclusion from hypotheses 1 and 2 alone, with no bound on the product defect.
Nothing in this package supplies that bound for an arbitrary sequence, and
nothing here settles the parent problem, which remains open.

`Challenge.lean` restates the theorem in Mathlib-only vocabulary, repeating the
two definitions verbatim so that it depends on no source module.
`Solution.lean` proves it by transport: the local definitions agree with the
corpus definitions by `rfl`, so the corpus theorem
`ErdosProblems.Erdos243.PaperCompleteR7.original_coordinate_bounded_defect`
applies directly.

## Files

| File | Role |
|---|---|
| `Challenge.lean` | Mathlib-only statement, closed by `sorry` |
| `Solution.lean` | proof by transport from the live declaration |
| `AxiomAudit.lean` | `#print axioms` on the packaged theorem |
| `comparator.json` | theorem names and the three permitted axioms |
| `formalization.yaml` | provenance, status and boundary |
