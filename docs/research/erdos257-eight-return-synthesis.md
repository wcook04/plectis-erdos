# Eight-return synthesis for Erdős 257

The universal irrationality problem remains open. The four analytic support
theorems below are reviewed ordinary proofs, not complete Lean formalizations.
The repair-window argument has a candidate Lean implementation, but its
focused check has not completed. All new infinite claims in this supplement
therefore remain ordinary proofs. Complete analytic proofs are retained in
[the proof supplement](erdos257-eight-return-proofs.md). The independently
regenerated finite certificate is in
[the exact audit](erdos257-eight-return-audit.json). Agreement between returns
is not used as proof: the repeated prime-cofactor obstruction is one family.

## 1. The mathematical target and the selected probes

For an infinite set of positive integers A, the target is irrationality of
S_b(A)=sum_{a in A} 1/(b^a-1), at b=2. A representation of 4/9 or 1/21 by
an infinite support would refute the target. Neither representation is proved.

Three different attacks were compared:

| Attack | Supporting source | Contrary evidence | Discriminating probe | Stop condition |
|---|---|---|---|---|
| Shifted-atom averaging | r1, r3, r8 and the reciprocal-support Lean kernel | Small positive returns fail for the full positive-integer support | Check the finite gcd bound, its tail domination, and the fractional interchange | Do not strengthen close returns into a universal target |
| Actual greedy repair | r2, r4, r5, r6 and the support-uniform square-root tail bound | All fixed multiplicative repair schedules have prime-cofactor obstructions | Exact prefix certification and a finite square-root repair deadline | A finite horizon with no failure does not establish survival |
| Prime-local dilation and correlation | r7 and Tao–Teräväinen Theorem 3.1 | Mixed divisors destroy prime-local errors | Check the analytic theorem's actual uniformity and every scale separation | Stop at prime-power supports unless mixed-divisor errors are controlled |

The selected new formal probe is the finite repair deadline in Section 2.
It turns the cofinal consumer into an exact equivalence with explicit finite
windows. The additional ordinary synthesis in Section 5 allows the fractional
moment exponent to vary between blocks. Both go beyond the individual returns.

## 2. A square-root repair deadline

**Theorem.** Let Q:N→N satisfy

    Q_N ≤ 2 sqrt(N) + 4  for every N.

Then for every K there is an N with

    K ≤ N < K + 2 floor(sqrt(K)) + 12,    Q_(N+1) ≤ Q_N.

**Proof.** Write s=floor(sqrt(K)) and T=2s+12. If every step in the window
strictly increased, integrality would imply Q_(K+T)≥Q_K+T≥T.
But K<(s+1)^2, so K+T<(s+4)^2. Consequently
Q_(K+T)<2s+12=T, a contradiction. This proof uses no recurrence.

For the actual 4/9 greedy support, let P_N be its binary Lambert prefix
numerator and Q_N=floor(4·2^N/9)-P_N. If 4/9 belongs to the achievement set,
uniqueness identifies its representing support with the greedy support A.
The full Lambert tail identity gives

    Q_N + {4·2^N/9} = sum_{r≥1} 2^(-r) f_A(N+r).

The existing support-uniform divisor-pair theorem bounds the right side by
2sqrt(N)+4. Thus the deadline applies at every rank, including selected ranks.
Conversely, one repair in every displayed window gives cofinal repairs, and
the existing cofinal consumer gives membership. Therefore

    4/9 ∈ K  iff  repairs are cofinal
              iff  every displayed square-root window contains a repair.

A single certified strict-increase window is a finite certificate of
nonmembership. Proving all windows contain repairs would instead give the
infinite rational-support counterexample through the existing finite-support
exclusion. The checked finite replay to rank 4096 finds no such nonmembership
certificate; that finite observation decides neither alternative.

## 3. Consolidated prime-cofactor obstruction

For any admissible selected support with sum at most x<1, let Q_N be its
nonnegative floor defect, t_n its target floor bit, and f(n) its selected
divisor count. Exact identities give

    Q_n = 2Q_(n-1) + t_n - f(n),
    4(Q_n-Q_(n-1)) = Q_(n+1)+f(n+1)-2f(n)+2t_n-t_(n+1).

If F is a finite selected subset coprime to M, Dirichlet supplies arbitrarily
large primes p with Mp≡-1 modulo lcm(F). At n=Mp we have f(n+1)≥|F| and
f(n)≤f(M)+τ(M). For the 4/9 target and 6|M, t_n=t_(n+1)=0. Hence

    Q_(Mp)-Q_(Mp-1) ≥ ceil((|F|-2f(M)-2τ(M))/4).

The exact integer-enclosure verifier identifies 80 selected exponents coprime
to 420 through rank 727, and f(120)=11, f(420)=13. Therefore the two reduced
prime progressions in the audit receipt give jumps at least **7** for M=120
and at least **2** for M=420. The first bound improves r6's 6 by spending r5's
five additional certified anchors. For M=420, the tetraprime union omits exactly
the selected divisor 420 and possibly 420p; its proposed inequality fails by
at least 3. These are failures of the actual greedy orbit regardless of its
survival. The finite prefix does not itself prove the infinitude of the prime
progression; that is the external Dirichlet input.

More generally, r2 removes the coprimality restriction on the anchors at the
cost of smaller contributions. For any infinite admissible support, any finite
nonempty set of positive multipliers M, and any H, choose sufficiently many
selected d>max(M)+1. At primes p≡-1 mod lcm(d), the fractional contribution at
Mp-1 is greater than 2^(-M-1) for every chosen d. Thus Q_(Mp-1)>H+2τ(M),
while f(Mp)≤2τ(M). This yields simultaneous arbitrarily large increases at all
the specified multipliers, and Q_(Mp)/Q_(Mp-1)→2 along a suitable prime
subsequence. It disproves an eventual finite menu of multiplicative repair
schedules. It does not disprove unrestricted cofinal repairs.

The r2/r3/r5/r6 fatal-orbit examples remain useful guards: x=3/4 selects every
rank ≥2 but leaves a positive remainder; every finite Boolean prefix can be
extended to a rational target in a later achievement-set gap. Neither example
represents that rational target. Finite compatibility and target-periodic digits
alone therefore cannot establish survival of the fixed target.

## 4. Strengthening the 1/21 divergence amplification

r4 uses the forced selected exponent 5 to identify six good R classes modulo
15. On these classes its fractional atom exceeds {2^(2R)/21}. Alignment of
the complete quotient-greedy word with the actual word, together with an
upper-half skip, would instead force Q_(2R)=0: the skipped pure binary coin
leaves a budget below that coin and the selected suffix spends exactly its
largest possible remaining integer budget. The atom inequality forces Q_(2R)>0,
so alignment is impossible.

There is a stronger finite certificate. Ranks 5 **and 7** are actually selected:
the remainder after 5 is 10/651, which is below 1/63 and above 1/127.
The exact inequality

    2^(2R mod 5)/31 + 2^(2R mod 7)/127 > (2^(2R) mod 21)/21

holds on **60 of the 105** residue classes of R modulo 105. The complete list
is regenerated by the audit script. For every actual skip k, all such classes
in ceil(k/2)≤R<k are divergent rows. Their count is at least (2/7)k-O(1).
Using arbitrarily large skips, the divergence set restricted to these classes
has upper density at least **2/7**, improving r4's **1/5**. Choosing disjoint
doubling windows also proves divergent reciprocal mass for this set. The
existing cofinal-divergence consumer supplies the reverse implication.

Thus membership of 1/21, infinitude of these restricted divergent rows,
upper density at least 2/7, and their divergent reciprocal sum are equivalent.
This is an ordinary assembled theorem with an exact finite phase certificate.
No positive lower density, positive logarithmic density, or actual membership
is asserted.

## 5. A variable-exponent fractional-cover theorem

This extension is derived during assimilation from r8's progression resolvent
and r1's insistence on a summable domination before interchanging averages.

Let F_j be finite sets of positive integers, let 0<α_j≤1, and let c_(j,d)≥0
majorize their fractional divisor incidences:

    f_(F_j)(n)^α_j ≤ sum_{d|n} c_(j,d).

Write C_j=sum_d c_(j,d)/d and B_j=2^α_j. If

    sum_j C_j · 2^(jα_j) · B_j/(B_j-1)^2 < ∞,                 (V)

then every infinite subset A of union_j F_j has irrational S_b(A) at every
integer base b≥2. A uniform positive lower bound on α_j is unnecessary.

**Proof.** For any fixed positive L and any j, subadditivity gives

    U_(F_j),2(n)^α_j ≤ V_j(n)
      := sum_{r≥1} B_j^(-r) sum_{d|n+r} c_(j,d).

On n=Lm, the divisibility frequency tends to gcd(d,L)/d if gcd(d,L)|r,
and to zero otherwise. The uniform finite-average bound is (L+r)/d.
Accordingly

    lim_X average_(m≤X) V_j(Lm)
      = sum_d c_(j,d) gcd(d,L)/(d(B_j^gcd(d,L)-1))
      ≤ C_j/(B_j-1).

Fix ε>0 and thresholds t_j=ε·2^(-j). Multiply by t_j^(-α_j) and sum over
j>J. The finite-average dominator is

    sum_(j>J) C_j t_j^(-α_j)
        [ L/(B_j-1) + B_j/(B_j-1)^2 ].

It is finite by (V), since ε^(-α_j)≤max(1,ε^(-1)). This explicitly justifies
the infinite j,d,r interchange and the limit: no unproved uniformity in j or
exchange of limsup and a series is used. The limiting average of
Z_J(n)=sum_(j>J) t_j^(-α_j)V_j(n) is at most
sum_(j>J) C_j t_j^(-α_j)/(B_j-1), tending to zero as J→∞.

Choose J making this limit less than 1 and choose L to freeze union_(j≤J)F_j
and any requested finite subset of A. There are arbitrarily large m with
Z_J(Lm)<1. At such points every U_(F_j),2(Lm)<t_j for j>J, and hence
U_(A minus union_(j≤J)F_j),2(Lm)≤sum_(j>J)t_j<ε. Frozen atoms have zero
displacement. The displacement for A is strictly positive by infinitude.
Thus it has cofinal positive returns tending to zero. The integer-lattice
identity rules out rationality. Binary displacement bounds transfer these
same returns to every integer base (with the corpus's factor 2).

For a fixed α, any summable-cost cover from r8 can be regrouped into finite
blocks with exponentially small tail costs; subadditivity preserves its
majorants. Thus (V) includes the fixed-exponent theorem after regrouping.

**A concrete varying-exponent family.** Take successive disjoint blocks of
primes after primes g_j≥16^j, stopping when
R_j=product_(p in block j)(1+1/p) first exceeds exp(g_j^(1/3)); let M_j be
their product and F_j=g_j D(M_j). Start the next block at the next prime after
the previous endpoint, increasing it further if necessary. Set α_j=g_j^(-1/3).
r8's positive divisor expansion and concavity give

    C_j = g_j^(-1) product_(p|M_j)(1+(2^α_j-1)/p)
        ≤ R_j^α_j/g_j ≤ 2e/g_j.

Because B_j-1≥α_j log 2, the j-th term of (V) is O(g_j^(-1/3)); hence it
is summable. The ordinary reciprocal mass of frame j is R_j/g_j→∞.
Every infinite sub-support of their union is nevertheless irrational at every
integer base. There is no persistent nontrivial divisor across these disjoint
prime frames, and a pairwise-coprime subfamily takes at most one element per
frame, so has summable reciprocals.

For every fixed α>0, the optimal positive-majorant costs of **this displayed
frame decomposition** diverge: with c=2^α-1,
log(1+c/p)≥c/(1+c/2)·1/p and log R_j≤sum_(p|M_j)1/p. Thus its cost is at
least R_j^(c/(1+c/2))/g_j→∞. This proves that varying the exponent extends
the usable frame criterion. It does not exclude every conceivable alternative
fixed-exponent cover of the same union.

## 6. The four admitted analytic families and their boundaries

1. **Divisibility-weighted supports (r1).** For a finite nonempty prime set P,
   h(a)=product_(p in P)p^v_p(a). Finite sum of
   h(a)/(a(b^h(a)-1)) gives cofinal positive displacements and irrationality.
   The same proof works for any nested divisibility chain. The double finite
   averaging, including the incomplete-period error, is essential. The example
   a≤2^(2^(2^v2(a)-v2(a))) has divergent reciprocal mass and O(log log a) gaps.
   Infinite subsets and reciprocal-summable additions are included.
2. **Sub-log-star reciprocal mass (r3).** A rational p/q forces
   liminf H_A(x)/ell(x)≥λ_b(p/q)/2, with λ the explicitly defined rational
   phase gap and ell the tower index. The finite inequality is
   Jλ<J H_L(M,X)+2L E_L(M,X)+4, X=L2^(J-1). Iterating a two-tower-step
   scale proves the assertion. This is a liminf theorem, not a density theorem.
   The square-background example has divergent reciprocals and escapes the
   displayed LCM-gap criterion.
3. **Prime-power supports (r7).** Every infinite subset of the prime powers,
   and every fixed dilation with finite modifications, has irrational sum.
   The reviewed argument uses Tao–Teräväinen arXiv:2512.01739v2, Theorem 3.1,
   with its equidistribution and small-prime hypotheses. The selected reciprocal
   mass, not log log X, sets the cube dimension; arbitrary slow divergence is
   retained. Higher prime-power errors are confined to prime-square events.
   Correlation, progression uniformity, and the moment comparison are analytic
   proof obligations, not Lean declarations. The authors' printed full-prime
   theorem and stated full-prime-power extension are attributed to them;
   arbitrary thinning is the returned extension. Priority remains unassessed.
4. **Fractional divisor covers (r8).** A fixed 0<α≤1 and summable positive
   divisor-majorant costs give hereditary irrationality at all bases. Complete
   divisor frames admit exact nonnegative multiplicative coefficients
   β_α(p^e)=(e+1)^α-e^α. Their cost is optimal among positive majorants of
   that frame. The constructed moving host is reciprocal-divergent and has
   no persistent core. Its no-large-gap addendum uses p_(k+1)/p_k→1 from the
   prime number theorem. For arbitrary frames the Möbius coefficients can
   be negative: {2,3} gives coefficient 2^α-2 at 6. Positivity is indispensable.

These are separate sufficient regimes. Irrationality of two component series
does not prove irrationality of their union. The common parent counterexample
space is the intersection of the complements of the proved regimes; it is
still nonempty as a class of candidate supports. No combination here settles
that space or forces survival of 4/9 or 1/21.

## 7. Delivery and verification

The exact audit script is
[eight_return_exact_audit.py](scripts/eight_return_exact_audit.py). Its default
run checks 4104 rational gcd-orbit inequalities, certifies the actual prefix,
and checks every complete proposed repair window through rank 4096. Finite
checks supplement the ordinary proofs; they do not verify infinite quantifiers.

The analytic proof source retains the load-bearing proofs, examples, and
external input, so a reader can inspect the ordinary claims without a network
connection or the private attachment store. Research-packet rows distinguish
these ordinary proofs from the Lean source and its terminal build. Comparator
and Palomar dispositions must refer to exact verified declarations; no broader
ordinary theorem is represented as a checked Challenge/Solution pair.

The returned theorem campaign is incomplete as a solution of Erdős 257. The
remaining positive producer is actual survival (equivalently cofinal repairs,
or the square-root windows) for the fixed rational target; the global alternative
requires irrationality outside the admitted support regimes. A successor
research ask must expose the fixed-schedule obstructions and these complete
ordinary proofs, rather than asking another agent to rediscover them.
