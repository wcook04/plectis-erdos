# Dense p-adic cancellation attack

## Status and scope

This note tests one specific implication that is tempting in the dense-support
case:

> a primitive prime divisor attached to a selected exponent should force
> cancellation among the selected multiples of that exponent.

The finite common-denominator version of that statement is already present in
the Lean corpus.  It is not a new route.  The genuinely new result below is the
corresponding exact congruence for a rational infinite sum and its rational
tail.  That congruence also identifies the obstruction: rationality does not
force the finite leading layer to cancel.  The tail can, and necessarily does,
carry the opposite p-adic residue.

All claims about the cited Lean declarations are machine-checked.  The
infinite-tail proposition below is a paper deduction from those declarations
and elementary rational arithmetic; it has not been formalized in Lean.  The
finite computations in the table were performed with exact integers.  No
irrationality theorem or rational Boolean construction is claimed.

Throughout, the Boolean support is \(A\subseteq\mathbb N_{>0}\), and

\[
  r=\sum_{n\in A}\frac1{2^n-1}.
\]

The phrase reciprocal-divergent support means
\(\sum_{n\in A}1/n=\infty\), not divergence of the displayed Mersenne series.
The latter converges for every support.

## What the corpus already proves

The local prime calculation is not missing.

* [odd_prime_order_padicVal_pow_sub_one](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L340)
  is exact LTE at an odd prime of order \(d\):
  \[
    v_q(b^{dk}-1)=v_q(b^d-1)+v_q(k).
  \]
* [odd_prime_order_normalized_pow_sub_one_modEq](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L814)
  identifies the normalized unit modulo \(q\):
  \[
    \frac{b^{dk}-1}{q^{v_q(b^d-1)+v_q(k)}}
    \equiv
    \frac{b^d-1}{q^{v_q(b^d-1)}}\,
    \frac{k}{q^{v_q(k)}}\pmod q.
  \]
* [odd_prime_order_residue_formula](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L1032)
  gives the exact finite common-denominator residue formula.
  [odd_prime_order_residue_formula_not_dvd_sum](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L1102)
  converts a nonzero residue into nondivisibility of the finite numerator.
* [LocalLayerCertificate](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L1445)
  and
  [local_layer_residue_nonzero_implies_sum_valuation](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L1454)
  package the general fact that a nonzero first layer fixes the exact
  valuation of a finite sum.
* [exists_exactOrderPrimePowerWitness](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L4977)
  and
  [finite_period_noncollapse](../../Erdos257PeriodNoncollapse/CertificateKernel.lean#L5091)
  show that this local mechanism has already been driven through the finite
  periodic noncollapse argument.

The cyclotomic and height modules also already say exactly what survives and
what it costs.

* [mobiusNumerator_gcd_cyclotomicValue](../../Erdos257PeriodNoncollapse/CyclotomicProjectionOfShadow.lean#L350)
  and
  [cyclotomicValue_dvd_baseMobiusShadow_den](../../Erdos257PeriodNoncollapse/CyclotomicProjectionOfShadow.lean#L389)
  prove top-fibre denominator survival for the Möbius shadow.
* [scaledMobiusNumerator_den_exact](../../Erdos257PeriodNoncollapse/MersenneShadowCyclotomicNoncollapse.lean#L441)
  computes the exact cancellation by an external scale, while
  [upperHalfChannel_survivorProduct_dvd_den](../../Erdos257PeriodNoncollapse/MersenneShadowCyclotomicNoncollapse.lean#L766)
  retains a product of pairwise-coprime surviving channels.
* [scalarLocalization_complement_dvd](../../Erdos257PeriodNoncollapse/AdelicHeightObstruction.lean#L23)
  says that localizing a denominator moves the complementary factor into the
  scalar coefficient rather than deleting it.
  [positiveRat_numDivisor_mul_lt_two_mul_den](../../Erdos257PeriodNoncollapse/AdelicHeightObstruction.lean#L77)
  is the corresponding Archimedean denominator lower bound.
  [linearDescender_eq_smul_eval](../../Erdos257PeriodNoncollapse/AdelicHeightObstruction.lean#L120)
  rules out a rational-linear projection that kills every scalar relation
  while retaining independent denominator information.
* [prefixDenominator_shell_power_bound](../../Erdos257PeriodNoncollapse/PrimitiveSupportBridge.lean#L213)
  and
  [nextSupport_power_bound](../../Erdos257PeriodNoncollapse/PrimitiveSupportBridge.lean#L242)
  turn a positive rational gap and an analytic tail bound into another
  denominator lower bound.  The rational input is supplied with the actual
  denominator product by
  [positive_rational_difference_lower_bound](../../Erdos257PeriodNoncollapse/PrimitiveRationalGapSupply.lean#L32).

Thus a restatement of finite LTE, finite numerator survival, cyclotomic
survival, or denominator pressure would duplicate existing work.  The
unresolved junction is the boundary from real convergence of an infinite
tail to p-adic cancellation.

## Exact notation for the primitive channel

Assume \(r\in\mathbb Q\).  Fix \(a\in A\) and an odd primitive prime divisor
\(p\mid 2^a-1\).  Thus

\[
  \operatorname{ord}_p(2)=a.
\]

Put

\[
  \mu=v_p(2^a-1),\qquad
  U=\frac{2^a-1}{p^\mu}\pmod p,
\]

so \(U\in\mathbb F_p^\times\).  For an integer cutoff \(X\ge a\), let

\[
  S_X=\sum_{\substack{n\in A\\n\le X}}\frac1{2^n-1},
  \qquad
  \tau_X=r-S_X,
\]

and define the finite set of selected multipliers

\[
  E_X=\{k\ge1:ak\le X,\ ak\in A\}.
\]

It is nonempty because \(1\in E_X\).  Set

\[
  e_X=\max_{k\in E_X}v_p(k),\qquad
  k^\circ=\frac{k}{p^{v_p(k)}},
\]

and define the leading-layer residue

\[
  C_X=
  \sum_{\substack{k\in E_X\\v_p(k)=e_X}}
    (k^\circ)^{-1}\in\mathbb F_p.
\]

Finally let \(h=v_p(\operatorname{den}(r))\), where the denominator is
reduced.  If a rational number \(x=m/n\) is p-integral, write
\([x]_p\) for \(m n^{-1}\in\mathbb F_p\).

## New exact law: the tail absorbs the first finite layer

### Proposition

If \(X\ge a\) and

\[
  \mu+e_X>h,
\]

then \(p^{\mu+e_X}\tau_X\) is p-integral and

\[
  \boxed{
  [p^{\mu+e_X}\tau_X]_p=-U^{-1}C_X.
  }
  \tag{1}
\]

Consequently, if \(C_X\ne0\), then

\[
  \boxed{
  v_p(\tau_X)=-(\mu+e_X).
  }
  \tag{2}
\]

Equivalently, the reduced denominator of the rational tail \(\tau_X\) is
divisible by \(p^{\mu+e_X}\).

### Proof

Primitivity gives

\[
  p\mid 2^n-1\quad\Longleftrightarrow\quad a\mid n.
\]

For \(n=ak\), the cited LTE and normalized-unit theorems give

\[
  v_p(2^{ak}-1)=\mu+v_p(k)
  \tag{3}
\]

and

\[
  \frac{2^{ak}-1}{p^{\mu+v_p(k)}}
  \equiv U k^\circ\pmod p.
  \tag{4}
\]

Multiply the finite prefix by \(p^{\mu+e_X}\).  A term whose exponent is not
a multiple of \(a\) vanishes modulo \(p\), because its denominator is a
p-adic unit.  A term indexed by \(ak\) with \(v_p(k)<e_X\) also vanishes,
because after (3) it retains a positive power of \(p\).  By (4), a term on
the maximal layer has residue

\[
  U^{-1}(k^\circ)^{-1}.
\]

Therefore

\[
  [p^{\mu+e_X}S_X]_p=U^{-1}C_X.
  \tag{5}
\]

Since \(\mu+e_X>h\), the rational number \(p^{\mu+e_X}r\) has positive
p-adic valuation and hence residue zero.  Subtracting (5) from it proves
(1).  When \(C_X\ne0\), the scaled tail is a p-adic unit, which is exactly
(2).  \(\square\)

At the first cutoff \(X=a\), one has \(E_a=\{1\}\), \(e_a=0\), and
\(C_a=1\).  In particular, if \(p\nmid\operatorname{den}(r)\), then

\[
  v_p(\tau_a)=-v_p(2^a-1).
\]

This is the opposite of a forced-cancellation conclusion: at the earliest
cutoff the leading finite residue cannot cancel, and rationality prescribes
the exact denominator carried by the remaining tail.

## Finite common-numerator specialization

This subsection is a transparent specialization of the existing
CertificateKernel residue law, not a new theorem.

Let \(F\) be a finite set of selected exponents containing \(a\), let
\(L=\operatorname{lcm}(F)\), and write \(K=L/a\).  Define

\[
  N_F=\sum_{n\in F}\frac{2^L-1}{2^n-1}.
\]

For

\[
  e=\max\{v_p(k):ak\in F\},\quad
  f=v_p(K),\quad
  \delta=f-e,\quad
  K^\circ=K/p^f,
\]

the same leading-layer calculation yields

\[
  \boxed{
  \frac{N_F}{p^\delta}
  \equiv
  K^\circ
  \sum_{\substack{ak\in F\\v_p(k)=e}}
    (k^\circ)^{-1}\pmod p.
  }
  \tag{6}
\]

Terms whose exponents are not multiples of \(a\) lie strictly above the
first p-adic layer.  Formula (6) explains precisely when the finite common
numerator gains one additional factor of \(p\).

The following exact-integer checks use
\(F=\{a,2a,\ldots,Ma\}\).  The column \(C\) is the sum of inverses on the
maximal layer; \(N/p^\delta\) and \(K^\circ C\) are both reduced modulo \(p\).

| \(a\) | \(p\) | \(M\) | \(K=\operatorname{lcm}(1,\ldots,M)\) | maximal \(k\)-layer | \(C\) | \(N/p^\delta\) | \(K^\circ C\) |
|---:|---:|---:|---:|:---|---:|---:|---:|
| 2 | 3 | 1 | 1 | \(\{1\}\) | 1 | 1 | 1 |
| 2 | 3 | 2 | 2 | \(\{1,2\}\) | 0 | 0 | 0 |
| 2 | 3 | 3 | 6 | \(\{3\}\) | 1 | 2 | 2 |
| 2 | 3 | 6 | 60 | \(\{3,6\}\) | 0 | 0 | 0 |
| 3 | 7 | 1 | 1 | \(\{1\}\) | 1 | 1 | 1 |
| 3 | 7 | 6 | 60 | \(\{1,2,3,4,5,6\}\) | 0 | 0 | 0 |
| 3 | 7 | 7 | 420 | \(\{7\}\) | 1 | 4 | 4 |

These small rows show both behaviours.  They do not support a universal
first-layer cancellation law.

## Reciprocal divergence does not control the local layer

The following supports are explicit counterexamples to any attempt to infer
the needed local cancellation merely from
\(\sum_{n\in A}1/n=\infty\).  They are support-level examples only; no claim
is made that their Mersenne sums are rational.

### A dense support with a permanently nonzero channel

Fix \(a\), and take

\[
  A_0=\{a\}\cup\{n\ge1:a\nmid n\}.
\]

This support has natural density \(1-1/a\) and divergent reciprocal sum.
For the channel attached to \(a\), however,

\[
  E_X=\{1\},\qquad e_X=0,\qquad C_X=1
\]

for every \(X\ge a\).  Thus neither positive density nor reciprocal
divergence forces additional selected multiples of \(a\), let alone
cancellation among them.

### One dense support with cofinally zero and cofinally nonzero layers

Take

\[
  A_1=a\mathbb N_{>0}.
\]

It has natural density \(1/a\) and divergent reciprocal sum.  At

\[
  X=a(p-1)p^E,
\]

the maximal multiplier layer is

\[
  \{p^E,2p^E,\ldots,(p-1)p^E\},
\]

so

\[
  C_X=\sum_{u=1}^{p-1}u^{-1}
      =\sum_{u=1}^{p-1}u
      =0\pmod p.
\]

At the intervening cutoff \(X=ap^E\), the maximal layer is the singleton
\(\{p^E\}\), and \(C_X=1\).  Therefore the same positive-density support has
arbitrarily late zero layers and arbitrarily late nonzero layers.  A theorem
based only on density cannot select the needed behaviour at all cutoffs.

### Simultaneous primitive channels still fit the prefix denominator

Let \(A_{\mathrm{pr}}\) be the set of prime exponents.  Euler's theorem gives

\[
  \sum_{a\in A_{\mathrm{pr}}}\frac1a=\infty.
\]

For every prime exponent \(a\), every prime divisor \(p_a\mid2^a-1\) is
primitive: the order of \(2\) modulo \(p_a\) divides the prime \(a\) and
cannot be \(1\).  No other prime exponent is a multiple of \(a\).  Hence for
every \(X\ge a\),

\[
  e_X=0,\qquad C_X=1.
\]

Under the rationality assumption, for every such \(p_a\) not dividing
\(\operatorname{den}(r)\), equation (2) forces

\[
  v_{p_a}(\tau_X)=-v_{p_a}(2^a-1).
\]

Primitive primes attached to distinct exponents are distinct, because one
prime cannot give two different multiplicative orders.  Thus many primitive
prime powers simultaneously divide the reduced denominator of one late
tail.

This remains compatible with the elementary common denominator.  If

\[
  L_X=\operatorname{lcm}\{n\in A_{\mathrm{pr}}:n\le X\},
\]

then the prefix denominator divides \(2^{L_X}-1\), and every \(p_a\) above
already divides \(2^{L_X}-1\).  Since

\[
  \tau_X=r-S_X,
\]

its reduced denominator divides a common multiple of
\(\operatorname{den}(r)\) and \(2^{L_X}-1\).  The simultaneous primitive
channels therefore consume denominator factors that the prefix has already
made available.  They do not exceed an independent height budget.

## Why real convergence supplies no p-adic boundary condition

The false step can now be stated exactly.  From

\[
  \tau_X\longrightarrow0\quad\text{in }\mathbb R
\]

one cannot conclude that a fixed p-adic rescaling of \(\tau_X\) tends to
zero, or even becomes p-integral with zero residue.  Real convergence and
p-adic convergence are independent.

The geometric identity

\[
  \frac13=\sum_{j\ge1}\frac1{4^j}
\]

is already a decisive elementary model.  The partial sums converge in
\(\mathbb R\), while each summand is a 3-adic unit and the rational limit has
\(v_3(1/3)=-1\).  An infinite real identity is therefore not obtained by
passing finite congruences to a p-adic limit.

Equation (1) makes the same issue exact for the Mersenne problem.  When the
finite leading layer is nonzero, the rational tail is not an error term in
the p-adic channel.  It has precisely the opposite leading residue.

The current height theorems do not reverse this conclusion:

1. The p-adic law produces a divisor of \(\operatorname{den}(\tau_X)\).
2. Real smallness plus a numerator divisor produces another lower bound on
   \(\operatorname{den}(\tau_X)\).
3. The rational-gap adapters also retain the actual prefix and whole
   denominators.

None supplies an upper bound on the reduced tail denominator independent of
the prefix LCM.  The example \(p^{-m}\) can be arbitrarily small in
\(\mathbb R\) and have valuation \(-m\), so no such upper bound follows from
real size alone.

## Exact no-go and the missing input

The first primitive-prime congruence does not contradict rationality.
Rationality changes it into the tail identity (1).  Reciprocal divergence,
even positive natural density, controls neither the existence of later
selected multiples of a fixed exponent nor the value of their maximal
p-adic layer sum.  Simultaneous nonzero primitive channels can all be housed
inside the standard Mersenne prefix denominator.

Accordingly, this line can advance only with an additional theorem of one of
the following genuinely stronger forms:

* a p-integrality boundary theorem forcing
  \([p^{\mu+e_X}\tau_X]_p=0\) at a cutoff where \(C_X\ne0\);
* an upper bound for \(\operatorname{den}(\tau_X)\) that is smaller than the
  product of the primitive prime powers forced by (2), and that does not
  reintroduce \(2^{L_X}-1\);
* a cross-cutoff relation preventing the same rational tail sequence from
  absorbing the prescribed residues for many primitive channels, stronger
  than the tautological common-denominator divisibility.

No one of these statements follows from support reciprocal divergence,
positive density, the current finite CertificateKernel, or the existing
adelic/cyclotomic denominator-survival theorems.  Without such an additional
boundary law, first-order p-adic cancellation is a precise diagnostic of
where the rational tail stores the finite residue, not a route to a
contradiction.
