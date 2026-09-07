# Cross-target defect search

This note compares the arithmetic which is genuinely target-dependent with the
arithmetic which belongs to the Mersenne clocks themselves.  The computation
below is exact integer arithmetic; it is a theorem-discovery audit, not a
finite verification of the Erdős problem.

## 1. Two different defects

For (d>1), the adjacent reciprocal atoms satisfy the exact identity

\[
 \frac1{2^{d-1}-1}-\frac1{2^d-1}
 =\frac{2^{d-1}}{(2^{d-1}-1)(2^d-1)}.
\]

Thus the quantity used in the search,

\[
 \delta_d=\frac1{(2^{d-1}-1)(2^d-1)},
\]

is the *normalised* adjacent defect (the preceding difference after division
by (2^{d-1})); it is not the unnormalised difference.  This distinction
matters when comparing a carry pulse with a binary suffix capacity.  The
defect is target-independent and decays on the (4^{-d}) scale.  Target
dependence enters through the rational floor orbit, not through (delta_d).

The target-independent local law is the checked theorem
`shiftedMersenneAtom_step` in `ReciprocalSupportIrrationality.lean`:

\[
 2\,\operatorname{atom}(N,d)-\operatorname{atom}(N+1,d)
 =\mathbf 1_{d\mid N+1}.
\]

After summing over a Boolean support (A), this is

\[
 2\Phi_A(N)-\Phi_A(N+1)=c_A(N+1),
 \qquad c_A(n)=\#\{d\in A:d\mid n\}.
\tag{1}
\]

Consequently every rational target has the same divisor-pulse operator.  A
target can help only by constraining the allowable integer carry orbit in (1).

## 2. Exact rational target words

Let (p/q) be reduced and define

\[
 B_{p/q}(N)=\left\lfloor\frac{2^{N+1}p}{q}\right\rfloor
 -2\left\lfloor\frac{2^Np}{q}\right\rfloor.
\]

Writing (r_N\equiv p2^N\pmod q), (0\le r_N<q), gives the exact formula

\[
 B_{p/q}(N)=\left\lfloor\frac{2r_N}{q}\right\rfloor\in\{0,1\}.
\tag{2}
\]

For odd (q), (r_N) runs on a multiplicative orbit and its period is the
order (h=\operatorname{ord}_q(2)) (or a divisor after restricting the
starting residue).  Hence the floor word is periodic with no approximation
involved.  The following exact words start at residue (1); the numerator
coprime to (q) merely selects another orbit or a cyclic translate.

\[
\begin{array}{c|c|c|c}
q&h&B\ \hline
3&2&01\\
5&4&0011\\
7&3&001\\
9&6&000111\\
11&10&0001011101\\
13&12&000100111011\\
15&4&0001\\
17&8&00001111\\
19&18&000011010111100101\\
21&6&000011\\
25&20&00001010001111010111\\
31&5&00001
\end{array}
\]

For (1/20), after the two initial binary places the odd denominator is (5),
so the eventual word has period (4), a shifted version of `0011`.  The
period-six, density-one-third word for (1/21) is therefore not exceptional
at the level of period alone: (1/9) has the same period and density one-half.

The two-step pulse is equally explicit:

\[
 \left\lfloor\frac{2^{N+2}p}{q}\right\rfloor
 -4\left\lfloor\frac{2^Np}{q}\right\rfloor
 =\left\lfloor\frac{4r_N}{q}\right\rfloor.
\tag{3}
\]

For (q=21,p=1), (3) gives the period-six word `000132` on the same orbit;
the existing `TwentyOneQuotientGreedy.lean` results isolate its even/three
pulse.  Formula (3), however, supplies an analogous pulse word for every
target and by itself gives no Boolean ancestry.

## 3. Why denominator period does not force a support

The Boolean coefficient sequence is divisor incidence, not a periodic floor
word.  If a rational carry state (u_N) is used in the normalization of
`RationalSupportCarrySkeleton.lean`, its exact support relation is

\[
 u_{N+1}+v c_A(c+N+1)=2u_N
\tag{4}
\]

and (u_N) is (v) times the binary tail.  Independently, the target floor
remainder (r_N=p2^N-q\lfloor p2^N/q\rfloor) satisfies

\[
 r_{N+1}+qB_{p/q}(N)=2r_N.
\tag{5}
\]

When the support sum is the target, appropriately shifted normalisations of
(u_N) and (r_N) are the same state.  Thus (B_{p/q}) is not an extra term in
(4): it is the digit forcing in the target remainder recurrence (5), whereas
(c_A) is recovered from the support coboundary (4).  A period or a density
for (5) cannot determine the Möbius ancestry of (c_A).

There is a concrete checked counterexample to every target-only assertion of
that kind.  Take (A=\{2,3\}).  Then

\[
 \sum_{a\in A}\frac1{2^a-1}=\frac13+\frac17=\frac{10}{21},
 \qquad c_A(n)=\mathbf1_{2\mid n}+\mathbf1_{3\mid n}.
\]

The `BooleanMobiusCarry.lean` results
`carryOrbit23_periodic`, `carryOrbit23_eq_twenty_one_mul_tail`, and
`mobius_carryOrbit23_recovers_support` certify a bounded period-six carry and
exact Boolean Möbius recovery.  Thus “denominator (21), period (6), or
density (1/3) forces irrationality/infinite support” is false.  The example
is finite and its value is (10/21), not (1/21); its role is precisely to
separate arithmetic of the denominator from the missing infinite-support
argument.

Likewise, a bounded carry does not imply finite support: (4) only bounds the
divisor count.  Infinite sets such as the primes have bounded divisor
incidence, while sets of multiples can have arbitrarily large reset loads.
The common-multiple inequalities
`one_add_mul_card_le_two_mul_shifted_state` and
`one_add_mul_card_half_le_shifted_state` make this distinction exact: if
every member of a finite (F\subset A) divides (L), then

\[
 1+v|F|\le 2u(L-c-1).
\tag{6}
\]

LCM pulses therefore constrain the carry from below; they do not supply a
small carry row automatically.

## 4. The strongest uniform law found

The following statement survives all target comparisons and is the useful
cross-coordinate reduction.

> **Periodic forcing / divisor ancestry law.**  For every reduced (p/q), the
> rational floor forcing (B_{p/q}) is periodic on the (2)-orbit modulo the
> odd part of (q), and every rational support representation must satisfy
> (4) and (5).  If, in addition, the integer carry (u_N) is eventually periodic,
> then (c_A) is eventually periodic, and its Boolean support is exactly the
> divisibility Möbius transform of that eventual coefficient sequence.

The first assertion is an immediate consequence of (2), and the second is an
ordinary finite-difference calculation from (4).  The final assertion uses
the checked Möbius identities `moebius_mul_supportCoeffAF` and
`mobius_supportCoeff_eq_one_iff` in `BooleanMobiusCarry.lean`.  This is a
conditional theorem, not a solution: rationality gives an unbounded carry in
the infinite-support setting (`exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`),
not eventual periodicity.

The exact obstruction is now visible.  To obtain the desired irrationality
one needs a theorem that turns the periodic forcing plus Boolean divisor
ancestry into a controlled recurrence for an *unbounded* carry, or else a
theorem showing that every unbounded carry has a forbidden LCM/defect
alignment.  Period, floor-bit density, and the (4^{-d}) defect scale do not
provide that theorem separately.

## 5. Exact computation and counterexample record

The table above was generated by the following short exact script; no floating
point arithmetic is used.

```python
from math import gcd
for q in [3,5,7,9,11,13,15,17,19,21,25,31]:
    if gcd(2,q) > 1: continue
    r, orbit = 1, []
    while r not in orbit:
        orbit.append(r); r = (2*r) % q
    word = [int(2*r >= q) for r in orbit]
    pulse = [(4*r)//q for r in orbit]
    print(q, len(orbit), ''.join(map(str, word)), sum(word), pulse)
```

The computation falsifies the candidate laws “period six is special”,
“density one-third is enough”, and “the two-step pulse determines Boolean
ancestry”.  It does not test the infinite case at larger depth; the exact
finite counterexample (A=\{2,3\}) already defeats those formulations.

## 6. Boundary

Proved ingredients used here are the shifted-atom step identity and orbit
means in `ReciprocalSupportIrrationality.lean`, the carry recurrence and
unbounded-state theorem in `RationalSupportCarrySkeleton.lean`, the Möbius
recovery and period-six example in `BooleanMobiusCarry.lean`, and the target-
specific period-six pulse lemmas in `TwentyOneQuotientGreedy.lean`.  The
cross-target conclusion is an exact synthesis of these ingredients plus the
displayed residue calculation.  No claim here proves the dense-support case.
The missing global statement is a genuine interaction theorem between the
periodic rational forcing, Boolean divisor ancestry, and the LCM lower pulses
in (6).
