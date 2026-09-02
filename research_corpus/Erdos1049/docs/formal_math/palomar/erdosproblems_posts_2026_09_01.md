# Per-problem posts for erdosproblems.com, drafted 2026-09-01

Drafts only. Each was written by the discovery agent for that problem against the Challenge
statements and packet, in declarative paper register, boundary last, novelty stated as unassessed.
Before any is posted: read the existing comments on the page (the #243 page has seven, the #251
page four), confirm every named entry is launched, and replace `pending` wording. Posting is the
operator's act.

## #68

Every rational representation S = a/q of Σ_{n≥2} 1/(n!−1) satisfies q ∤ 299999! and q > 10^12039.
The first follows from a Lean-checked theorem applied to an exact GMP computation of every
strict-successor carry through m = 300000; the second from a bracket-certified continued fraction
of 23449 partial quotients. The two bounds are independent: one excludes all 299999-smooth
denominators, the other all denominators below 10^12039.

Lean also checks two exact coordinates. With Z_m the least integer above m!·Σ_{n≤m} 1/(n!−1), S is
irrational exactly when m ∤ Z_m for infinitely many m. With C = Σ 1/(n!(n!−1)) = S − e + 2, S is
rational exactly when ⌊m!C⌋ ≡ −2 (mod m) for all large m. Irrationality is therefore cofinal
escape of one explicit factorial orbit from one residue class. Rationality forces a target of width
O(m^−2); the computed orbit never enters it through 22000. No cofinal escape is proved. Novelty of
these coordinates is unassessed. The problem remains open.

Code: https://github.com/wcook04/plectis-erdos-lean, entry `ExternalVerification68ChannelRadius`;
source modules `ErdosProblems/Erdos68/FactorialZeroPlateau.lean`, `CompanionOrbitRationality.lean`
(the latter must be committed and shipped first).

## #243

Write the rational tail of Σ 1/a_n in product-cleared integer coordinates C_n, D_n with centred
error E_n = D_n − (a_n − 1)C_n. E_n = 0 for all large n is equivalent to the Sylvester recurrence
for all large n. Lean-checked theorems in the repository prove two rigidity statements for this
state system under the normalised vanishing E_n/C_n → 0. If E_n ≥ −B for all large n, then E_n = 0
eventually and a_{n+1} = a_n² − a_n + 1 eventually. If Σ(−E_n)₊/C_n converges, the same conclusion
holds. Koizumi's pseudo-greedy analysis (arXiv:2504.05933) supplies normalised vanishing for the
canonical orbit under the hypotheses of the problem. Any counterexample therefore has negative
canonical errors unbounded along a cofinal set with divergent normalised negative mass. Constant and
eventually periodic negative magnitudes are excluded unconditionally in the regime e_n < a_n. Exact
computation on the return family q₀(k) = 33 + 79833600k classifies its continuation through prime
heights 13 to 61. The problem remains open. Novelty of these statements is unassessed.
Repository: https://github.com/wcook04/plectis-erdos-lean, entry
`ExternalVerification243PeriodicNegativeOrbit`; the bounded-negative and summable-mass entries are
pending publication.

Site note: the page prints Erdős–Straus with a_n²/a_{n+1} − 1; the original 1964 indexing is
a_{n+1}²/a_{n+2} − 1. A one-line correction is a credible first comment.

## #249

The strongest theorem toward Problem 249 in this repository is a necessary condition. If
S = Σ φ(n)/2^n were rational, Lean proves that a tempered integral carry u(N+1) = 2u(N) − vφ(N+1)
would exist, eventually periodic modulo v, whose dyadic sections through level e span dimension at
least 2^e − 1 for every e. The structural input is an explicit rational basis of the 2-kernel of φ:
the sections φ(2^j n + r) with r odd, together with φ(n) and φ(2n), are linearly independent and
span every section, so the sections through level e have rank exactly 2^e + 1. Lean also proves
that irrationality of S is equivalent to a single decidable residue condition for each prospective
denominator 2^c v, and a certified continued-fraction prefix shows any rational S has denominator
above 10^12039. The problem remains open; the missing step is a cofinal anti-concentration estimate
along denominators v2^c. Novelty of the basis theorem is unassessed.
Repository: https://github.com/wcook04/plectis-erdos-lean, entries
`ExternalVerification249RankOneSharpFloor`, `ExternalVerification249BinaryCyclotomicAnchors`, with
`ExternalVerification249DyadicTotientKernel`, `ExternalVerification249CarryRankFrontier` and
`ExternalVerification249CanonicalMersenneFrontier` packaged.

## #251

Erdős asked whether Σ p_n/2^n is irrational. The problem is open. The repository below records what
is proved in Lean about this series. Lean proves the elementary bound p_n ≤ 1250(n+1)^4 and
unconditional convergence of the prime series and of the consecutive-gap series, with the exact
identity Σ_{n≥0} p_n/2^{n+1} = 2 + Σ_{n≥0} g_n/2^{n+1}. If the value were a rational S, Lean proves
that the rescaled tails form a rational sequence obeying T_{N+1} = 2T_N − g_{N+1}, that some
positive shift T_{N+h} − T_N is integral for all large N, and that the same shift leaves (−1, 1)
infinitely often. An explicit sequence g_n = 2(n² + 4n + 2), positive, even, unbounded and
nonperiodic, has rational dyadic sum with every shift integral, so no argument from gap size,
growth or periodicity alone can finish the proof. An exact computation certifies that any rational
value has reduced denominator above 10^12041. The remaining obstacle is a cofinal statement about
consecutive prime gaps at a fixed offset. Novelty of these statements is unassessed.
Repository: https://github.com/wcook04/plectis-erdos-lean, entries
`ExternalVerification251ActualPrimeGapTail` and `ExternalVerification251PolynomialShiftCountermodel`.

## #257

For every infinite set A of positive integers with Σ_{a∈A} 1/a < ∞, and every integer base b ≥ 2,
the series Σ_{a∈A} (b^a − 1)^{−1} is irrational. The statement carries no coprimality, periodicity
or density hypothesis. Erdős (Math. Student 36, 1968) printed the pairwise coprime case for every
integer base t ≥ 2 and stated that coprimality is superfluous without printing the argument; the
proof here establishes that stated extension in every integer base by an independent argument,
built from binary close returns transferred uniformly to every larger base. The theorem is checked
in Lean 4 over Mathlib. Every counterexample to the problem must therefore have divergent
reciprocal mass.

In the divergent region the repository proves an exact criterion: a nonnegative rational q is an
infinite Mersenne subsum if and only if its greedy expansion omits infinitely many exponents. For
q = 1/21 non-membership is equivalent to one explicit fatal branch whose late behaviour is a single
affine recurrence. Neither membership question is decided. A bounded search (2026-09-02) found no
printed proof of Erdős's stated extension; that non-location supports no priority claim.

Repository: https://github.com/wcook04/plectis-erdos-lean. Entries
`ExternalVerification257ReciprocalSupport`, `ExternalVerification257FinitePeriodNoncollapse`,
`ExternalVerification257RationalTailRigidity`.

## #269

For the prime set {2,3,5} we prove in Lean that the value of the series is rational only if the
normalized dyadic tail states X_a = (H(2^a)/2) Σ_{n≥a} m_n all lie on one lattice (1/q)ℤ and two
distinct scales collide modulo one. The actual infinite orbit satisfies X_{a+1} = b_a X_a − d_a with
b_a ∈ {2, 6, 10, 30}, and it either reaches an integer or returns cofinally to distance at least
1/31 from every integer. An integer seed that survives all exact windows equals the true state. No
first integral index below 6000 exists, and no denominator below 10^6768 exists, by exact
certificates. The running-LCM factorisation identity for every finite prime set, and the two-prime
case in which the series factorises and is transcendental by Hecke and Mahler, are due to Steve Fan
(comment on this page, 26 June 2026), who notes that the factorisation does not extend to three or
more primes. The structural result added here is that the three-prime running-LCM kernel has
nonsingular minors of every order, so no finite separable representation exists, while the
two-prime kernel is an outer product. The boundary is exact: the problem remains open, and the
missing input is an anti-concentration statement for the residues generated by the rotation of
the torus by (log_3 2, log_5 2). Novelty of the rank statements is unassessed. Repository: https://github.com/wcook04/plectis-erdos-lean, entries
`ExternalVerification269ThreePrimeStructure`, `ExternalVerification269ActualShellOrbit`,
`ExternalVerification269AllScaleLattice`, `ExternalVerification269IntegralBranchPinning` (only the
first is launched today; the other three must be launched before posting).

## #1041

Erdős Problem 1041 remains open. The strongest result applying to every degree and every root
geometry is a constant-factor version: two zero occurrences of a monic polynomial f are joined
inside {|f| ≤ 2μ} by a path of length at most (71/10) μ^{1/n}, where μ is the least critical-value
modulus; for roots in the unit disc with μ ≤ 1/2 the path lies in {|f| < 1} with length at most
5.7. The sharp constant 2 holds in every degree n ≥ 3 whenever a simple critical value v is
separated from the others by |1 − f(d)/v| ≥ 4, with 3 sufficing for n ≥ 4 and 2 for n ≥ 6 (sharp: C(5,2) = 1.0757 > 1). The
conjecture is proved for collinear roots with the sharp Chebyshev constant, for cubic quotient
fibres P((z−h)^q), for sparse quintics, and in degree three. The boundary is the regime of nearly
tied critical values, where the minimal-critical-value hub is shown to fail. Novelty of the
separation theorem is unassessed. Lean kernels: https://github.com/wcook04/plectis-erdos-lean,
entries `ExternalVerification1041SolvedFamilies`, `1041CriticalGeometry`,
`1041CyclicTrinomialFiber`, `1041QuarticQuotientFiber`, `1041TetranomialSpokes` (the separation
theorem's entry must be committed and launched before posting).

## #1049

Erdős Problem 1049 asks whether F(t) = Σ_{n≥1} 1/(t^n − 1) is irrational for every rational t > 1.
Erdős settled every integer base in 1948, and Bundschuh and Väänänen (1994) settle rational a/b
with log b / log a < 1/2 − 1/π² = 0.3987, which includes 7/2. The first resistant base is 3/2.

Homogenising Zudilin's permutation-group forms (Acta Arith. 111, 2004, direction (14,12,14;27)) at
a rational base a/b gives irrationality of F(a/b) whenever log b / log a < C₀/C₁ = 0.405683…, the
reciprocal of Zudilin's irrationality-exponent bound 2.46497868… for integer bases. The argument
uses his Lemma 7 in the polynomial ring Z[p], as printed, and his Lemma 2; the rest is a degree
count and positivity. In particular F((31/4)^r) is irrational for every r ≥ 1, since
log 4 / log 31 = 0.4037 lies outside the Bundschuh–Väänänen region and inside this one. The
integrality and degree structure is verified exactly for the first three forms and the constants to
25 digits; the general statement is an ordinary proof conditional on those two published lemmas,
not kernel-checked, and its priority is unsearched beyond Bundschuh–Väänänen.

Our work at 3/2 proves no irrationality result. It records where the standard constructions end. For the scalar q-Apéry Padé family at a/b the measured denominator exponent is
(3/2 + 3/π²) log a per j², so its linear forms decay exactly when log b / log a < 1/2 − 1/π², and a
Casoratian identity caps every content extraction on that diagonal at a > b². In Zudilin's Hankel
construction the normalized determinant has q-order exactly N(N−1)(2N−1)/6 with leading coefficient
(N!)²(N+1)!/2^N, so no extra analytic decay is available there. Lean checks the rectangular
Hermite–Padé threshold bound with its unique equality point, the coordinatewise clearing exclusion
at 3/2, the sharp 1/q prime-support gaps, and the four-jet collision thresholds. Novelty of these
statements is unassessed. Repository: https://github.com/wcook04/plectis-erdos-lean. Entries
`ExternalVerification1049AdelicHeightBridge`, `ExternalVerification1049RationalBaseBarrier`,
`ExternalVerification1049PrimeSupportSelectors`, `ExternalVerification1049HermitePadeNoGo`.
