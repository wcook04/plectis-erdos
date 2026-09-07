# ExternalVerification249PeriodicFreezingAndPulse

A rational relation among totient sections of pairwise nonproportional
positive-slope affine forms, with eventually periodic coefficients, forces
every coefficient to vanish identically; and a bounded integer sequence with
cofinally many two-sided isolated nonzero letters has irrational binary value.
Both are compared declarations from the binary totient note for Erdős Problem
#249, which remains open.

## Statements

**`periodic_freezing`.** Let `L i (n) = a i * n + b i` be finitely many affine
forms with positive slopes and pairwise nonzero cross determinants
`a i * b j ≠ a j * b i`. Let `w i : ℕ → ℚ` be coefficient sequences, each
periodic with its own positive period. If
`∑ i, w i n * φ (a i * n + b i) = 0` for all sufficiently large `n`, then
`w i n = 0` for every `i` and every `n`.

**`bounded_isolated_pulse`.** Let `a : ℕ → ℤ` satisfy `|a n| ≤ C` for all `n`.
Suppose that for every height `L₀` there are `L ≥ L₀` and `N > L` with
`a N ≠ 0` and `a (N - j) = a (N + j) = 0` for every `j` with `0 < j ≤ L`.
Then `∑_{n ≥ 0} a (n+1) / 2 ^ (n+1)` is irrational.

## Mechanism

The freezing statement reduces an eventual relation to a relation at every
index by translating the basepoint into the intercepts, and reduces the
per-coefficient periods to a single common period by taking their product.
It then applies the affine independence theorem for totient sections, whose
proof selects one prime value per row by the Chinese remainder theorem and
Dirichlet's theorem, and reads the resulting evaluation matrix modulo an
auxiliary prime `ℓ`.

The pulse statement fixes the quantifier mismatch between the note's
convention `L < N` with cofinal lengths and the library interface, which asks
for every length and `L + 1 < N`, by selecting a strictly larger available
length. The `n = 0` term of the full binary value is an integer and is removed
explicitly, so the conclusion is about the sum over positive indices as
printed. The Diophantine core is the isolated-digit separation mechanism of
P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math.
Soc. 12 (1948).

## Boundary

`periodic_freezing` is a statement about relations among totient sections. It
supplies no value of any series. `bounded_isolated_pulse` is a criterion about
bounded integer sequences and asserts nothing about a particular arithmetic
function until pulses are supplied for it. Neither declaration concerns
`∑_{n ≥ 1} φ n / 2 ^ n`, and Erdős Problem 249 remains open.

## Files

| File | Role |
|---|---|
| `Challenge.lean` | Mathlib-only statements, bodies deliberately `sorry` |
| `Solution.lean` | transport from `ErdosProblems/Erdos249/PaperCompleteR7/PeriodicAndPulse.lean` |
| `comparator.json` | compared names and the permitted axiom budget |
| `formalization.yaml` | claim boundary, sources, status |
| `AxiomAudit.lean` | `#print axioms` for both compared names |
