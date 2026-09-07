# Integer clock ensemble attack

This note studies the exact shifted-atom clock

    Phi_A(N) = sum_{a in A} 2^(N mod a) / (2^a - 1).

The question is whether rationality can force q Phi_A(N) to remain in the
lattice Z for every N, and whether an infinite Boolean ensemble can do this
with a tempered reservoir. No Lean edit or kernel invocation is part of this
audit.

## 1. The exact atomwise solvency law

For one rank a, the existing theorem `shiftedMersenneAtom_step` is the exact
identity

    2*atom(N,a) - atom(N+1,a)
      = 1 if (a > 0 and a divides N+1), else 0.

Summing it is legal because `summable_shiftedSupportAtom` holds at every fixed
N. The theorem `tsum_shiftedSupportAtom_step` therefore gives

    2*Phi_A(N) - Phi_A(N+1) = supportCoeff(A)(N+1),                 (1)

where the right side is an integer divisor count. This is the exact solvency
identity: every fractional pulse is paid for by a Boolean divisor event, and
there is no untracked atomwise error.

If q*Phi_A(N) is an integer for every N, (1) implies the exact integer clock
recurrence

    q*Phi_A(N+1) = 2*q*Phi_A(N) - q*supportCoeff(A)(N+1).

Thus pulse and reservoir cannot be independently rounded. Their lattice
classes are linked at every step. The same identity is the shifted-atom form
of the rational carry recurrence in `RationalSupportCarrySkeleton.lean`.

At a reset Q divisible by every a <= P, each low atom is at its zero-shift
value:

    atom(Q,a) = 1/(2^a - 1)       (a <= P, a in A).

This is `shiftedSupportOrbitMean_eq_zero_of_dvd` applied pointwise. Hence

    Phi_A(Q) = sum_(a in A, a <= P) 1/(2^a-1) + R_A(P,Q),

where R_A(P,Q) is the exact high-rank reservoir over a > P. Rational lattice
persistence says q times the complete left side is integral; it does *not*
say that the low prefix or the reservoir is separately integral. This is the
precise pulse/reservoir alignment issue.

## 2. LCM filtration and the true limiting statement

Let Q_P = periodLcm(P). The existing theorems
`tendsto_shiftedSupportOrbitMean_periodLcm` and
`tendsto_tsum_shiftedSupportOrbitMean_periodLcm` show, in the
reciprocal-summable regime, that the orbit mean at Q_P converges to the reset
sum Phi_A(0). The proof uses dominated convergence with the majorant 1/a.

This does not extend to the dense case. At a reset Q_P, a high rank a>P has

    0 <= atom(Q_P,a) <= 1,

but the available rankwise majorant is 1/a only after averaging over a full
gcd orbit. A single LCM sample can have 2^(Q_P mod a) close to 2^a, so its
atom can be order one. The family of reset reservoirs is therefore not
uniformly integrable under divergent reciprocal mass. This is the exact place
where the summable theorem stops, not a missing algebraic identity.

The exact orbit mean is

    gcd(Q,a) / (a * (2^gcd(Q,a)-1)),

and is bounded by 1/a. Fourier or conditional-expectation averaging sees this
mean, while a reset sample sees the exceptional residue Q mod a. Any
anti-concentration theorem must control this discrepancy uniformly in the
high-rank tail.

## 3. False anti-concentration statements

### False claim A: every reset reservoir is small

False pointwise. If a>P and a divides Q_P (which can happen for a later rank
when P is enlarged), its atom is exactly 1/(2^a-1), but if Q_P mod a is near
a-1, the atom is close to its order-one maximum (about 1/2 for a > 1). The
reset condition controls only ranks already
inside the LCM filtration.

### False claim B: divergent reciprocal mass forces large Phi_A(N) at every N

False for sparse clocks and also false for many residue positions of dense
clocks. Each atom is nonnegative, but N mod a can be zero for many small a and
the remaining high atoms are phase-dependent. Reciprocal mass controls the
full-period mean, not every point of the orbit.

### False claim C: lattice persistence makes each pulse separately divisible by q

False. From (1), lattice persistence only gives q*supportCoeff(A)(N+1) as an
integer, which is automatic. The pulse itself is an integer before scaling;
the nontrivial information is the simultaneous integrality of the reservoir
values Phi_A(N), not a divisibility condition on supportCoeff.

### False claim D: Fourier cancellation alone forces irrationality

False without a tail norm. A periodic finite truncation has finitely many
Fourier characters and can be lattice-valued by accidental cancellation. For
an infinite support, passing from truncations to Phi_A requires a uniform
integrability or anti-concentration estimate; divergent reciprocal mass is
exactly where the standard 1/a majorant is non-summable.

## 4. Adversarial model supports

* Full support A = {1,2,3,...}: every divisor pulse is present at its natural
  rank, but the high-rank reset reservoir is not pointwise dominated by 1/a.
  This is the maximally dense stress test for any uniform reset claim.
* Multiples A = {m,2m,3m,...}: all clocks share a common factor. Resets at
  multiples of m freeze an increasing initial family, but the remaining clocks
  still have unrelated residues. A common factor does not align all pulses.
* Sparse chain A = {2^k : k >= 1}: reciprocal mass is summable, so the
  dominated-convergence route applies; nevertheless individual non-reset atoms
  can be large. This separates summability from pointwise anti-concentration.
* Prime support: the orbit means are approximately reciprocal prime weights,
  while each reset sees a different residue pattern. This is the cleanest
  coprime ensemble for testing Fourier claims.

These examples do not assert rationality. They show that any proposed theorem
must use the exact lattice recurrence and cannot infer pointwise behavior from
reciprocal density alone.

## 5. Best surviving theorem candidate

The strongest candidate that survives the adversarial tests is a conditional
finite-filtration statement:

> Suppose q*Phi_A(N) is integral for every N. If there is a sequence of reset
> scales Q_j and cutoffs P_j tending to infinity for which the high reservoirs
> R_A(P_j,Q_j) are uniformly integrable (for example, their tails have a
> common summable majorant), then the reset lattice values converge to the
> reset series Phi_A(0) along a subsequence. The exact solvency recurrence then
> transfers any nonzero limiting pulse pattern to the integer clock.

The first clause is already the mechanism of
`tendsto_tsum_shiftedSupportOrbitMean_periodLcm`; the genuinely new target is
to replace summability by a weaker anti-concentration condition on the reset
residues. A plausible formulation is a Fourier-energy bound on the high tail:

    sup_j sum_{a>P_j} |E[ exp(2*pi*i*t*Q_j/a) ]|/(2^a-1) -> 0

for every nontrivial character t in the relevant finite LCM quotient. This is
only a candidate, not a corpus theorem; it must be converted into a real
uniform-integrability bound before it can be used.

## 6. Durable conclusion

The atomwise identity (1) is the exact law forbidding pulse/reservoir
misalignment at one step. LCM resets expose the low atoms exactly, but the
dense high-rank reservoir can evade reset control because a single residue
sample has no 1/a domination. Fourier means, conditional expectations, and
LCM filtrations all encounter the same obstruction: exchanging the infinite
sum with the reset limit requires uniform integrability or a new
anti-concentration theorem. The best next theorem is therefore not “lattice
persistence is impossible” in isolation, but a dense-tail criterion forcing
uniform integrability of reset reservoirs from the Boolean support structure.
