# Erdős #269: admissible modular minors at every order

## Statement

For `(p,q,r) = (2,3,5)` let `H(x)` be the product of the largest pure `2`-, `3`-
and `5`-powers not exceeding `x`, and attach to an exponent vector `(i,j,k)` the
kernel value `H(2^i 3^j 5^k)⁻¹`.

For every order `n` there is one pair of injective index maps `I, J` such that,
simultaneously:

* the rational minor `det (K(I a, J b, k))` is nonzero for every layer `k`;
* for every `B ≥ 2` coprime to `30` and every layer `k`, the same minor reduced
  modulo `B` is a unit of `ZMod B`;
* the reduced matrix itself is invertible over `ZMod B`.

The index maps are chosen before both the modulus and the layer. That ordering
is the content of the phrase "the maps in Theorem 1" on the page, and it is what
makes the corollary a statement about one selection rather than about a family
of selections depending on `B`.

## Mechanism

Splitting the floor exponents factors the kernel as a diagonal row unit times a
carry staircase times a diagonal column unit. In any commutative ring where `2`,
`3` and `5` are units, all row and column factors are units, and the staircase
determinant is `5⁻¹(5⁻¹ - 1)^(n-1)`; since `5⁻¹ - 1 = -4·5⁻¹`, that is a unit
too. Admissibility, `B` coprime to `30`, is exactly what makes `2`, `3` and `5`
units of `ZMod B`, so the same computation runs over `ℚ` and over every
admissible `ZMod B` with the identical index choice.

Reduction is taken as the inverse of the natural height inside `ZMod B`. No ring
map from the rationals to `ZMod B` is used, and none exists.

## Boundary

This is a rank and invertibility statement about the kernel. It supplies no
irrationality argument, it says nothing about the running least common multiple
as a real series, and it does not settle Erdős Problem 269, which remains open.

`Challenge.lean` is Mathlib-only and carries one deliberate specification
`sorry`. `Solution.lean` is sorry-free and transports the theorem from
`ErdosProblems/Erdos269/PaperR7ModularMinors.lean`. No Comparator replay and no
Palomar submission has been performed for this package.
