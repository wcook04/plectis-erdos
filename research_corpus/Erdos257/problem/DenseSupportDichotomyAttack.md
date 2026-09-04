# Dense-support dichotomy attack

This audit concerns the live case: an infinite support A with divergent
reciprocal mass and a rational Mersenne subsum. It records what the existing
shifted-atom and carry modules actually prove, kills stronger tempting
combinatorial claims, and isolates one weighted carry statement that survives.
It does not edit Lean or claim a completion of the dense case.

## 1. Exact shifted atoms and the carry state

The atom at shift N and rank d is

    shiftedMersenneAtom(N,d) = 2^(N mod d) / (2^d - 1)   (d > 0),

and `shiftedSupportAtom A N d` is its Boolean restriction to A. The exact
bridge
`binaryCoeffTail_supportCoeff_eq_tsum_shiftedSupportAtom` identifies the
binary coefficient tail with the sum of these atoms. The orbit mean is

    shiftedMersenneOrbitMean(Q,d)
      = gcd(Q,d) / (d * (2^gcd(Q,d) - 1)),

and `shiftedMersenneOrbitMean_le_reciprocal` gives the universal upper bound
by 1/d. Sampling along a multiple of d freezes the atom:
`shiftedMersenneOrbitMean_eq_zero_of_dvd`.
The LCM-period theorems `tendsto_shiftedSupportOrbitMean_periodLcm` and
`tendsto_tsum_shiftedSupportOrbitMean_periodLcm` show how common multiples
expose these frozen atoms, but they give no lower bound from divergent mass by
themselves.

Under a rational support value p / (2^c v), the carry skeleton supplies a
positive integer state u with

    u(n+1) + v * supportCoeff A (c+n+1) = 2*u(n),
    u(n) = v * binaryCoeffTail(supportCoeff A)(c+n),

and a residue congruence modulo v. The existing theorem
`exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction` proves that
u is unbounded for every infinite support. This is an important distinction:
unbounded carry is proved, but a *small or tempered* carry row is not.

## 2. What the sunflower module already supplies

`SupportSunflowerDichotomy.lean` uses a much stronger object than arbitrary
dense support: an `OrthogonalPetalBouquet` has one finite core Q, exceptional
terms dividing Q, and pairwise-coprime nontrivial petals, with summable petal
reciprocals. The exact consumer
`irrational_erdosSupportSeries_of_orthogonalPetalBouquet` still requires
`SunflowerForcedSlotTailSelection`; the conversion from that selector to the
carry certificate is already proved. Thus “find a bouquet” is not itself the
missing theorem, and the carry selector is a landed conditional socket.

The reciprocal-summable route is also closed by
`irrational_erdosSupportSeries_two_of_summable_reciprocal` in
`ReciprocalSupportIrrationality.lean`. The present attack therefore cannot
reuse either a summable petal tail or the named forced-slot socket as if it
were new progress.

## 3. False universal dichotomies

### False claim A: divergent reciprocal mass forces an infinite pairwise-coprime subfamily

Take A = {2n : n >= 1}. Its reciprocal mass diverges, but every two members
have gcd at least 2. This is exactly the finite-core branch Q = 2, not a
coprime branch.

### False claim B: divergent reciprocal mass forces an orthogonal bouquet with summable petals

Take A = {2,3,4,...}. Any representation by one fixed finite core Q plus
pairwise-coprime petals and finitely many exceptions would have only finitely
many possible core divisors. Covering all sufficiently large integers then
forces a petal family carrying a divergent harmonic submass; it cannot satisfy
the bouquet's `summable_inv_petal` field. Divergence is therefore not enough to
enter the existing bouquet theorem.

### False claim C: unbounded carry contradicts rationality

It does not. Unboundedness is an explicit theorem of the rational carry
skeleton. The contradiction needed by the irrationality kernel is a structured
near-return, a bounded/tempered middle row, or a forced Boolean carry pattern,
not mere growth of u.

### False claim D: a common multiple automatically creates a useful small row

The common-multiple theorem goes in the opposite direction. If F is a finite
positive subset of A and every a in F divides L, then
`one_add_mul_card_le_two_mul_shifted_state` gives

    1 + v * card(F) <= 2 * u(L-c-1).

Thus LCMs force *large* carry states when they absorb many support elements.
They are pulses, not small-row certificates.

## 4. The true combinatorial content and its limitation

At the level of finite prime-factor sets, an infinite family always admits the
usual sunflower-or-disjoint extraction: if some prime occurs infinitely often,
pass to that branch and recurse on the residual factor; if every prime occurs
only finitely often, greedily choose pairwise-disjoint prime supports. But this
unweighted extraction says nothing about reciprocal mass. The selected
sunflower can have summable reciprocal mass even when the original support has
divergent mass.

The correct weighted question is therefore not “sunflower or LCM branch?” but:

    Can divergent reciprocal mass be retained on a sunflower branch, or does
    it repeatedly concentrate in finite common-factor frames?

The first alternative would need a *mass-preserving* orthogonal bouquet, still
with enough carry selection to invoke the existing consumer. The second does
not mean one fixed Q divides everything. It means that along a sequence of
finite frames Q_j, a positive amount of reciprocal mass is carried by elements
whose prime factors have already entered Q_j. The frames then produce LCM
pulses, but their relation to the residue state remains unproved.

## 5. Best surviving weighted carry lemma

There is one exact coupling stronger than the existing cardinality statement.
Let F be a finite positive subset of A, let every a in F divide L, and let
m = min(F). From the exact common-multiple inequality,

    1 + v*card(F) <= 2*u(L-c-1),

and from a >= m,

    sum_(a in F) 1/a <= card(F)/m.

Therefore

    (v*m/2) * sum_(a in F) 1/a
        <= v*card(F)/2
        <= u(L-c-1).

This is the best current theorem candidate:

> A divisor block with reciprocal mass mu and minimum rank m forces a carry
> row at least v*m*mu/2, up to the harmless additive 1/2 term.

It is exact, elementary, and genuinely couples reciprocal mass to a carry row.
For a top-half divisor block F subset (L/2,L], one can sharpen the first
comparison to card(F) >= (L/2)*mu, yielding

    u(L-c-1) >= v*L*mu/4.

This identifies the useful scale: a dense divisor block at its own LCM scale
creates a quantitatively large pulse. It does not provide the opposite small
row needed by the irrationality certificate.

## 6. What a real dichotomy would have to say

The strongest non-duplicative candidate is the following weighted frame
dichotomy, stated deliberately as open rather than attributed to Lean:

> For divergent reciprocal mass, either there is a sequence of finite
> pairwise-coprime petal blocks whose reciprocal mass remains divergent after
> removal of a finite core and whose correction tails satisfy the existing
> forced-slot selector, or there are finite frames Q_j and divisor blocks F_j
> with reciprocal mass mu_j such that every member of F_j divides an LCM L_j,
> m_j*mu_j is bounded below, and the corresponding carry pulses satisfy
> u(L_j-c-1) >= v*m_j*mu_j/2.

The first branch is only useful if its mass-preserving selector closes
`SunflowerForcedSlotTailSelection`; without that, it merely restates the
landed conditional route. The second branch is useful because it converts
reciprocal density into explicit LCM pulse lower bounds, but it still lacks a
tempered subsequence or a contradiction with the rational residue orbit.

The candidate is intentionally asymmetric: the dense case cannot be solved by
proving that all LCM pulses are small, since the exact inequality proves the
opposite whenever many divisors are present. The next missing theorem would
have to compare these lower pulses with the doubling recurrence and show that
their phase cannot remain compatible with rational residue dynamics.

## 7. Boundary of this attack

Proved and reused here:

* exact shifted-atom decomposition and orbit means;
* rational carry recurrence, residue class, and unbounded state;
* common-multiple lower bounds for finite divisor blocks;
* the weighted corollary above, by exact inequalities;
* existing sunflower and reciprocal-summable consumers, explicitly treated as
  conditional or already closed.

Not proved:

* a mass-preserving sunflower extraction;
* a universal finite-core dichotomy with divergent reciprocal mass;
* a small/tempered carry subsequence from the dense branch;
* incompatibility between the LCM pulse lower bound and the rational residue
  recurrence.

The durable lesson is that reciprocal divergence supplies mass, while common
divisors supply carry pulses. The missing mathematics is a theorem controlling
their *phase and scale together*, not another unweighted sunflower or another
unboundedness statement.
