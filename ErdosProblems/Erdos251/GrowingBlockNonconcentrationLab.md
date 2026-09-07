# Growing-block polynomial nonconcentration (advisory)

Type B file 05, Proposition C. **Not registered as a theorem.** The
product-polynomial transfer is elementary; the growing-block sieve *rate*
depends on a specialist reading of Kuperberg Theorem 4.1 (index versus
height, discriminant, uniformity in tuple cardinality). Type B withheld the
proposition from the manuscript. This lab records the ordinary transfer and
the blocked rate.

## Elementary transfer (ordinary)

If `F ∈ ℤ[x_0,…,x_k]` is not identically zero and `ε_n` takes values in a
finite set `A`, then for each `a ∈ A^{k+1}` the translate
`F(x + a)` is a polynomial. The set where `F(g_n+ε_n, …, g_{n+k}+ε_{n+k})=0`
is contained in a finite union of zero-sets of those translates. Finite
unions of density-zero sets are density zero. Nonzeroness of a polynomial is
invariant under translation of the variables by a constant tuple. Therefore
any finite-valued perturbation preserves *fixed-block* polynomial
nonconcentration.

This is already the mechanism of the live perturbation paragraph: the
rationalising digits lie in `{0,1}`, hence in a finite alphabet.

## Growing blocks (advisory; still `blocked_external`)

Round-3 Type B supplies a candidate ordinary proof of the rate `c+d<1` for
blocks of size `m(X) ≤ c log log X / log log log X` and degree
`(log X)^d`, together with an explicit write-up of the three uniformity
checks requested in r2, a simplex zero bound, and a discriminant-based
singular-series estimate. **Do not silently upgrade this to a landed
theorem.** Annex search for arXiv `2210.09775` / Kuperberg returned no
local annex. The three steps remain specialist-check items:

1. uniformity of Kuperberg Theorem 4.1 in tuple cardinality
   (`r = o((log Y)^{1/4})` after `Y ≪ X log X`);
2. discriminant dependence (`log log(3|D_H|) = O(log log log X)` on the
   block-span simplex);
3. height-to-index conversion (one factor of `log X` from counting
   translates up to `p_{2X+m}`).

Re-entry: independent confirmation of those three displayed steps from the
cited paper, then ordinary-proof registration. Formalising only the simplex
lemma with (6.1) as an explicit external hypothesis would be a faithful
intermediate; it would not be a Lean proof of the number-theoretic
corollary. Do not Lean-check the rate from this file.

A logarithmic-degree obstruction example (degree `≍ log X` vanishing on
half the gaps in a window) shows that a uniform claim cannot extend to any
fixed `d>1` even in one variable. It does not prove optimality of `c+d<1`.

The growing-block window `log log X / log log log X` and the phase-variance
window `log log X` do not compose to close #251: polynomial nonconcentration
does not yield unit-scale phase dispersion.
