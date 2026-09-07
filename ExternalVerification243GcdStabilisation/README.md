# Erdős #243 — gcd stabilisation and reduction

Along an exact product-cleared reciprocal-tail orbit whose negative centred
errors admit one common bound `B` along a cofinal set of indices, the tail gcd
`gcd (C n) (D n)` is eventually a constant positive `g`, and division by `g`
produces a genuine reduced exact tail: the quotients stay positive, become
coprime, and satisfy both original recurrences. The theorem is kernel-checked in
Lean 4 against Mathlib at the pinned revision, and its conclusion is a single
tuple, so the stable value, positivity, coprimality and both quotient
recurrences are all part of the statement.

The boundary is that this is one arithmetic ingredient of the rigidity argument.
It supplies the reduction step and nothing more. Erdős #243 remains open.

## Statement

Let `a C D : ℕ → ℕ` satisfy

```
C (n + 1) + D n = a n * C n        D (n + 1) = a n * D n
```

and let `E : ℕ → ℤ` be the centred error `E n = D n - (a n - 1) * C n`. Assume
there is a natural `B` such that for every `N` there is a `t ≥ N` with
`E t < 0` and `-B ≤ E t`.

Then there are `N` and `g` with `0 < g` such that for every `n ≥ N`:

- `gcd (C n) (D n) = g`;
- `0 < C n / g`;
- `Coprime (C n / g) (D n / g)`;
- `C (n + 1) / g + D n / g = a n * (C n / g)`;
- `D (n + 1) / g = a n * (D n / g)`.

## Mechanism

Both updates preserve common divisors, so `g n = gcd (C n) (D n)` divides
`g (n + 1)`: the gcds form a divisibility chain. Moreover `g n` divides `E n`,
so at a negative index `g n ≤ -E n ≤ B`. The chain is therefore bounded along a
cofinal set, hence bounded everywhere, and a bounded divisibility chain of
positive naturals is eventually constant.

Positivity of every `C n` is not assumed. It is derived: a vanishing numerator
propagates forward under the positive-coefficient dynamics, which is
incompatible with a later strictly negative centred error.

Once `g` is stable, `Nat.coprime_div_gcd_div_gcd` gives coprimality of the
quotients, and cancelling `g` from each recurrence gives the two reduced
recurrences.

## Boundary

The hypothesis is a cofinal bound on the negative errors. Supplying that bound
for an arbitrary orbit satisfying the growth and rationality hypotheses of
Erdős #243 is exactly what is missing, and this package does not supply it.
Nothing here settles the parent problem.

`Challenge.lean` restates the theorem in Mathlib-only vocabulary, repeating the
centred-error definition verbatim so that it depends on no source module.
`Solution.lean` proves it by transport from
`ErdosProblems.Erdos243.PaperCompleteR7.gcd_stabilises_and_reduces`.

## Files

| File | Role |
|---|---|
| `Challenge.lean` | Mathlib-only statement, closed by `sorry` |
| `Solution.lean` | proof by transport from the live declaration |
| `AxiomAudit.lean` | `#print axioms` on the packaged theorem |
| `comparator.json` | theorem names and the three permitted axioms |
| `formalization.yaml` | provenance, status and boundary |
