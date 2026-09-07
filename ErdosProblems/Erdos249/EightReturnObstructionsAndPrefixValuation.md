# Erdős 249: eight-return assimilation, the 2-adic prefix coordinate, and the closure of every local mechanism

Batch `erdos249_20260905_eight_return_stream_01` (eight Type B returns pasted
on 2026-09-05, custody under
`state/formal_math/type_b_return_batches/erdos249_20260905_eight_return_stream_01/sources/`).
Verification by six wave-1 desks, five wave-2 desks and the conductor;
every statement below carries its evidence class. Erdős 249 remains open.
Nothing here is a proof of irrationality, and the note says at each point
where a claim stops.

Evidence classes used: `lean_checked` (kernel check in
`public-source-redacted://canonical-v1`, `lake env lean`,
exit 0, no `sorry`, axioms `propext, Classical.choice, Quot.sound` only, each
re-run by the conductor), `exact_computation` (exact integer or rational
arithmetic with rigorous enclosures, script named), `ordinary_proof`
(verified line by line by a desk and by the conductor where stated),
`measurement` (finite data; never a theorem), `fetched_primary` (literature
read from the source).

## 1. Target, coordinates, and the tautology audit

Target: $S=\sum_{n\ge1}\varphi(n)2^{-n}$ is irrational. Coordinates:

- prefix integer $P_n=\sum_{i\le n}2^{\,n-i}\varphi(i)$, so $P_0=0$ and
  $P_{n+1}=2P_n+\varphi(n+1)$; tail $R_n=2^nS-P_n=\sum_{j\ge1}\varphi(n+j)2^{-j}$,
  with $0<R_n\le n+2$;
- Möbius–Mersenne ladder $\Theta_r=\sum_d\mu(d)(2^d-1)^{-r}$, $\Theta_1=1/2$,
  $\Theta_2=S-1/2$; the literal Lambert rungs $\sum_d\mu(d)/(2^{jd}-1)=2^{-j}$;
- the residue form of the tail (conductor, verified exactly to $10^{-90}$ and
  by desk S3 with an absolute-convergence proof, `check_mobius_residue_rough_remainder.py`):
  $$R_n=\sum_{d\ge1}\mu(d)\,2^{\,n \bmod d}\Big[\frac{\lfloor n/d\rfloor+1}{2^d-1}+\frac1{(2^d-1)^2}\Big],$$
  equivalently $R_n=nA(n)+B(n)$ with $A(n)=\sum_d\mu(d)2^{n\bmod d}/(d(2^d-1))$
  and $B(n)$ depending on $n$ only through the residues $(n\bmod d)_d$.

Tautology audit (ordinary proof, all desks concur). Write $S=a/(2^cv)$ with
$v$ odd. Then $u_n:=vR_n=2^{\,n-c}a-vP_n$ is an integer in $(0,v(n+2)]$ for
$n\ge c$. Each return's "remaining implication" is this statement in another
coordinate: the canonical residue-gap supply (all returns), r02's
fractional-part condition (G), r03's exact-tail range dichotomy, r04's
exact-tail collapse, r08's consumer (U), and the difference coordinate
"$\sum_m(\varphi(m+h)-\varphi(m))2^{-m}$ is dyadic for some $h$". They are
coordinates of irrationality, and none is progress by itself.

Two conditions in the batch are genuinely one-way (sufficient, not
equivalent), and both are statements about the totient word alone:

- (CD) $\limsup_N D_N/N>0$ with $D_N=\#\{P_n\bmod2^{2\lceil\log_2N\rceil}:N\le n<2N\}$
  (r04; desk B proved sufficiency and showed the window length is a free
  parameter in $[\log_2N+\omega(1),N-\omega(1)]$, larger windows giving
  weaker consumers; necessity is open);
- (E10) $\limsup_n\big(v_2(P_n)-\log_2n\big)=+\infty$ (desk E; Lean consumer
  in §2).

Confinement theorem (ordinary proof; desks E, B, S1): under $S=a/(2^cv)$ and
$t\le n-c$, the residue $vP_n\bmod2^t$ lies in the $v$-dilated short interval
$(-v(n+2),0)$, so $P_n\bmod2^t$ takes at most $v(n+2)$ values. Every S-free
sufficient condition found in this batch is a statement that the 2-adic
residues of $P_n$ escape that confinement at some modulus $2^t$ with
$\log_2n\le t\le2\log_2n$.

## 2. The prefix 2-adic valuation lane

Theorem 2.1 (exclusion rectangle; Lean
`ErdosProblems.Erdos249.prefix_twoAdic_denominator_exclusion`,
`prefix_twoAdic_denominator_lower_bound`, `prefix_twoAdic_odd_denominator_floor`
in `PrefixValuationAndControlRigidity.lean`, with the integrality core
`oddPart_mul_prefixTail_eq_intCast` and a non-vacuity `example`). Let
$S=a/(2^cv)$, $v$ odd, $c+t\le n$ and $2^t\mid P_n$. Then $2^t\le vR_n$; with
$R_n\le n+2$, $2^t\le v(n+2)$ and $v\ge2^t/(n+2)$. Consequently one exact
2-adic valuation $t=v_2(P_n)$ excludes every denominator $2^cv$ with
$c\le n-t$ and odd $v<2^t/R_n$.

Generic-residue template (desk S1, `check_prefix_confinement_exclusion.py`).
Divisibility is only the case in which the least positive representative of
$-vP_n \bmod 2^t$ equals $2^t$; in general one residue $P_n\bmod2^t$ excludes
every $(c,v)$ with $c\le n-t$ for which that representative exceeds
$v(n+2)$, and this fails only for a fraction about $v(n+2)/2^t$ of the odd
$v$. Any $n$ with a modulus six bits above the band therefore kills every
odd $v$ below a threshold with probability about $0.85$; the reachable
rectangle grows like (largest factorable $n$) $\times2^{t/2}$ at the cost of
$t$ totient evaluations near $n$. Record: $n=10^{18}$, $t=2048$, all
$c\le10^{18}-2048$ and all odd $v\le10^{298.8}$ in under one second, agreeing
with brute force to $v\le200001$.

Witness (exact_computation, `check_totient_dyadic_window_staircase.py`): $n=2786632$,
$v_2(P_n)=29$, $R_n=2063273.474\ldots$ (rigorous), so $S\ne a/(2^cv)$ for
every $c\le2786603$ and every odd $v\le259$. Second witness $n=2146743$,
$t=28$, $R_n=1245594.133$, all $c\le2146715$, odd $v\le215$.

Records of the excess $v_2(P_n)-\log_2(n+2)$ to $3\cdot10^7$ (measurement):
$5.508$ at $n=88$ ($P_{88}=423261232184308675146117120$, $v_2=12$),
$6.966$ at $n=2146743$, $7.590$ at $n=2786632$, none later; extended to
$X=10^9$ with no new record (desk S1, 384 s). Measured law (S1): the
count $M_s(X)=\#\{n\le X:2^s\mid P_n\}$ satisfies $M_s(X)\approx C_kX2^{-s}$
with $C_k\approx0.54\,k^{0.96}$ for $X=2^k$, uniformly over
$6\le s\le\log_2X+7$, so the free 2-adic bias of the prefix is one factor
of $\log n$ over uniformity and the typical record excess grows like
$2\log_2\log_2X$ (predicted 7.22 at $10^9$ against 7.59 observed, 8.05 at
$10^{12}$); each further record costs a squaring of $X$, so (E10) is out of
computational reach. The free bias contributes only $m_n=\min_j(j+v_2\varphi(n-j))$
bits (4 of the 29 at $n=2786632$; the other 25 are cancellation), and CRT
plus a gamble on the top bits buys excess at most $1/2$. The sufficient
condition (E10) is therefore heuristically true and analytically out of
reach: it needs the first moment $M_s(X)$ uniformly up to $s=\log_2X+K$, a
correlation sum of $s$ shifted totients against an additive character of
2-power modulus; $s=1,2$ reduce to $\varphi(n)$ in residue classes modulo 4
(Dence–Pomerance), $s=3$ is the first genuinely two-index case.

Theorem 2.2 (termwise dyadic windows are vacuous; Lean
`termwise_dyadic_window_vacuous`; desk E claim E8 correcting the conductor).
If $2^t\mid\varphi(N+t)$ then $2^t\le\varphi(N+t)\le N+t-1<v(N+t+2)$ for every
$v\ge1$, so the Erdős-1948 window argument, in which the first $t$ tail terms
are made integral and the tail is bounded by size, excludes no denominator
at all, for any $(c,v)$. The measured staircase $t(X)\approx0.47\log_2X$
(longest window with $v_2\varphi(N+j)\ge j$ for $j\le t$, $N\le X$;
$t=11$ at $X=10^7$) is far above the independence heuristic
$\sqrt{2\log_2X}$ because $v_2\varphi(m)\ge\omega_{\rm odd}(m)$, and it is
irrelevant: the size arithmetic, not the supply of windows, is the
obstruction.

### 2.2 Wave-2 S1: the confinement theorem and its two corollaries

Theorem 2.3 (confinement; desk S1, ordinary proof verified on rational
surrogates, `check_prefix_confinement_exclusion.py`). Under $S=a/(2^cv)$ and
$t\le n-c$, the least positive representative $r_+$ of $-vP_n\bmod2^t$ satisfies $r_+\le u_n=vR_n\le v(n+2)$, with $u_n\equiv -vP_n\pmod{2^t}$. Equality $r_+=u_n$ needs a size hypothesis such as $u_n\le2^t$; the rational control $a_n=n$ at $n=3$, $t=1$ has $r_+=1\ne5=u_3$. The finite exclusion uses only the inequality. (E10) is the divisibility case and (CD) the density
case (the latter consuming r03's Lemma 1.1); they are one statement. The
odd-restricted (CD) has deficit at most 2 through $N=2^{24}$ with no
repeating collision family (`check_prefix_odd_collision_families.py`), and
the backward-window occupancy is generic at every tested $v$ and
resolution (observed/heuristic within 0.6 percent at $2^{20}$). Density-one
divisibility $2^s\mid P_n$ holds for every fixed $s$ and is useless: the
parent needs the modulus to grow with $n$.

## 3. Rational controls and the three rigidity theorems

The corpus's parity-perturbed control (value $5/4$) and density-zero control
(value $3/2$) are joined by four returns' controls (r01 Theorem 1, r02
Theorem 6, r03 Theorem 2, r04 §3). Desk A verified every proof (r01
§2.1–§2.5, Props 2–5, §4; r02 Lemmas 2–3, Theorem 1, Corollaries 4–5, Theorem
6, §3) and desk B verified r03 Theorem 2 with its constants exactly tight
(the chain $2^{g_i+1}\le(\varepsilon/2)2^{\lambda+C}$ closes precisely under
$2^{-C}\le\varepsilon/4$ and $g_i\le\lambda(m_i)$) and r04 §3.1–3.2. Facts
established:

Theorem 3.1 (precision–error frontier; desk A, ordinary proof with exact
probes `check_precision_error_rational_controls.py`). Every rational control
is a point on one two-parameter curve $2^{k(n)}\le|\delta(n)|$, with three
impossibility edges: bounded precision loss with $o(n)$ error (r01 §4), exact
even identities with $o(n)$ error (r03 Prop 5), and bounded error with
eventual congruence modulo every integer. r04 §3.2 is tight on the curve,
r01 sits $(\log\log n)^{\varepsilon/2}$ above it, and r03 Theorem 2 has the
least precision loss at the price of non-$o(n)$ error. r01's "eventually
modulo every $m$" threshold is a height-three tower $N_m\ge2^{2^{2^{4m!/\varepsilon}}}$;
r02 reaches the same property at one exponential. r03 Theorem 2 has no
finite witness (first free root above $2^{121}$).

Theorem 3.2 (combined control; desk A, ordinary proof, exact prefix probe).
r01's quantum on r02's nested-CRT support gives a single rational-valued
sequence $c\le n$ that is odd-exact, prefix-exact, density-zero supported,
congruent to $\varphi$ modulo every fixed $m$ eventually, exact near primes,
2-adically precise to $\log_2n-(1+\varepsilon)\log_2\log_2\log_2n$, of
$o(n)$ error and eventually prime-power exact. The two properties it
cannot carry are exact even identities and bounded error.

Theorem 3.3 (no finite set of prime laws suffices; desk A, ordinary proof,
`check_finite_prime_law_rational_controls.py` verifies the $p$-laws at every
argument for $P=\{2\},\{2,3\},\{2,3,5\}$ with zero failures). For every
finite set $P$ of primes there is a rational-valued $c\le n$, exact on any
prescribed prefix, satisfying $c(pn)=(p-1)c(n)$ for $p\nmid n$ and
$c(pn)=pc(n)$ for $p\mid n$, at every argument $n$ and every $p\in P$. This
subsumes r03 Theorem 2 as the case $P=\{2\}$ and answers r03's closing
question.

Rigidity theorems (Lean, `PrefixValuationAndControlRigidity.lean`):

- `one_prime_law_and_little_o_forces_totient` (desk A): one prime's exact
  law at every argument together with $|g(n)-\varphi(n)|\le\varepsilon n$
  eventually for every $\varepsilon>0$ forces $g=\varphi$ on $n\ge1$;
- `even_law_and_eventual_congruence_forces_totient` (desk B): the exact
  even identities together with eventual congruence modulo every fixed
  integer force $g=\varphi$; no odd-prime law and no size bound are needed,
  so r01's and r03's families are mutually exclusive;
- bounded precision loss with $o(n)$ error forces $\delta=0$ eventually
  (r01 §4, ordinary proof, desk A).

Consequence (the diagnosis of the batch, desks A and F). The controls fail
$\varphi$ only in prime uniformity at an $o(n)$ error scale: each obeys any
finite set of exact prime laws, and one prime law plus $o(n)$ error already
forces $\varphi$. In the Duverney–Tachiya coordinates of §7, $\varphi$ has
the multiplicative half (H1) that the controls lack, and shares with them
and with $\sigma$ the failure of the size half (H2).

Theorem 3.4 (residue-class series; Lean `ResidueClassTotientSeries.lean`).
Let $m\ge2$, let $f:\mathbb N\to\mathbb Z$ with $f(0)=0$, and let $r<m$ with
$\gcd(r+1,m)=1$ and $f(r)\ne0$. Then $\sum_n f(\varphi(n)\bmod m)2^{-n}$ is
irrational (`irrational_totientObservable`); at $m=2^k$ every even residue
qualifies (`fixed_resolution_observable_irrational`, the forward half of r02
Theorem 1); in particular $A_m=\sum_n(\varphi(n)\bmod m)2^{-n}$ is irrational
for every $m\ge3$ (`residue_series_irrational`, r02 Corollary 5). The proof
is Erdős's 1948 mechanism for bounded sequences: two-sided prime isolation
by the Chinese remainder theorem and Dirichlet
(`two_sided_prime_isolation`, Mathlib `Nat.forall_exists_prime_gt_and_modEq`)
and the quantitative pulse separation `isolated_pulse_separation`, packaged
as the number-theory-free criterion `irrational_dyadicValue_of_pulses` for
any bounded integer coefficient sequence with cofinal isolated pulses. Not
formalised: the converse of r02 Theorem 1 for rational-valued weights and
Corollary 4 (bit-plane independence), both routine. Prior art: the mechanism
is Erdős 1948; no exact prior statement of Theorem 3.4 was located
(nearest neighbours Vandehey arXiv:1206.0340 and the AFP Erdős–Straus entry).
Parent relevance: none in the forward direction; r02 §2's argument that the
pulse cannot pay the (G) budget assumed a prime centre, and desk A supplied
the general proof (centre at least $M+2$, deficit below a quarter of the
budget universally; smallest centres 9, 31, 33, 239, 385, 511, 513 for
$k=2,\dots,8$).

## 4. The Möbius–Mersenne denominator lattice

Theorem 4.1 (rank-uniform signed Hankel domination; r05 and r06, both proofs
verified by desk C, both certificates re-executed,
`verify_rank_uniform_hankel_domination.py`). With squarefree nodes
$x_j=1/(2^{q_j}-1)$, signs $\mu(q_j)$, truncation $M\ge N$ including $M=\infty$,
and every integer $s\ge2$,
$$\Big|\frac{D^{(M)}_N(s)}{L_N(s)}-1\Big|\le\kappa_0\,2^{\,2-s},\qquad
\kappa_0=0.9960657\ldots,$$
so every shifted determinant is nonzero with sign $\prod_{j\le N}\mu(q_j)$
and the matrices have the inertia of the sign pattern (r06 Corollary 2).
r05's constant $599/600$ has slack $1/239400$; r06's is $399/400$; the
sharp value comes from r06's unrounded certificate. Independent exact
check for $N\le12$, $M\le N+8$, $s\le6$ with a rigorous $M=\infty$ bracket:
maximal deviation $0.6413$. The hypothesis $s\ge2$ is sharp: the sign law
fails at $s=1$ ($N=5$, $M=6$, ratio $-0.2196$).

Theorem 4.2 (exact 2-adic valuation, corrected; r05 (4.4), desk C, conductor
re-verification). For every $s\ge1$ and odd atom count $M-N+1$,
$v_2D^{(M)}_N(s)=2\sum_{i<N}(N-i)q_i$ exactly; for even atom count the
valuation is strictly larger in every tested case (240 of 240, and the
conductor's independent run for $N\le5$, $s\le3$). The corpus advisory row
`finite_dyadic_hankel_valuation`, stated without the parity hypothesis, is
false as written and is corrected by this theorem.

Theorem 4.3 (denominator growth and the two-sided error; r05 Theorem 2 and
r06 Corollary 4, verified). For the coupled Schur approximants
$R_{N,r}=b^{T}H^{-1}b$ at even codimension $r\ge8$,
$x_{N+1}^2/16000<\mu(q_{N+1})(\Theta_2-R_{N,r})<3x_{N+1}^2$, and the reduced
denominators grow quadratically ($\log_2Q$ from 267 to 1808 bits at
$N=1,\dots,6$) while the error shrinks only linearly
($\log_2|\Theta_2-R|=-2q_{N+1}+O(1)$), so $Q|\Theta_2-R_{N,r}|$ is already
$2^{262.7}$ at $N=1$ and $2^{2444}$ at $N=6$; r05's floor
$(3/128000)2^{d_N^2/128}$ is correct and astronomically lossy, and its parity
restriction is a proof artefact (the divergence holds at $r=9$). Through
r06's inertia the coupled family escapes the Lean-checked rank-one floor
$21/320$ and converges ($|\Theta_2-R|=6.6\cdot10^{-2},5.3\cdot10^{-3},\dots,4\cdot10^{-7}$),
then dies on denominators: the corpus's two exclusions are independent.

Theorem 4.4 (prefix denominators; r07 Theorem 1, desk D,
`check_lambert_correction_denominator.py`). $\log_2\operatorname{den}(T_N)\sim\kappa N^2$
with $\kappa=\prod_p(1-2/p^2+1/p^3)=\zeta(2)^{-2}\prod_p\big(1+\frac1{(p-1)(p+1)^2}\big)=0.428249505677\ldots$
(a new corpus constant); $W_N^2\mid\operatorname{den}(T_N)\mid\prod_{m\le N}\Phi_m(2)^2$
at every $N\le120$; signed simple-pole Lambert corrections at heights
$j\le N$ keep $(\kappa-o(1))N^2$ bits (r07 §4), growing width forces height
$2^{cN^{3/2}}$ or prime-pair layers with $\log_2q\ge cN^{5/2}/\log N$ (r07 §5,
the $N=13$ example $C_{77}=2$ verified), and $NH_N2^{-N}\to0$ forces
$q_N|\Theta_2-R_N|\to\infty$ (r07 Theorem 2; the floor (48) is sharp within
four bits).

Theorem 4.5 (derivative rungs; desk E, exact reduced denominators,
`check_lambert_derivative_denominator_compression.py`). The exact identities
$\sum_d\mu(d)d^kA_k(2^{-jd})=2^{-j}$ ($k\ge0$, $j\ge1$, $A_k(y)=\sum_mm^ky^m$;
conductor identity (I5)) have pole order $(k+1)v_\ell(2^m-1)$ at the layer
$\Phi_m(2)$. The $k=1$ rung reaches $\Theta_2$'s double pole through one
congruence per layer $\ell\mid\operatorname{num}(D\sigma_2(m)-\sum_ja_{j,1}\tau(j,m))$
(valuation driven from 2 to 0 in every tested row); in the top prime band
$\tau(j,m)=-(m/j^2)\mu(m)$ is rank one in $(j,m)$, so at most one top-band
layer is cancellable below height $2^{(1-o(1))N/2}$ (15 of 15 prime pairs
unsolvable at every width $J\le5$); widening $j$ is a quadratic net loss
($N=38$: $\log_2q$ from 652 to 589 to 1202 to 2391); $k\ge2$ deepens the
pole. Consequently $\min\log_2(q|S-R|)$ over the graded family stays at
$0.31$–$0.37\,N^2$ against the prefix's $0.38\,N^2$ for $N\le38$ and never
falls below 1. r07's escape certificate (54) is the single-index accident
$1+d2^d=(2^d-1)^2$ at $d=2$ (desk D), and clearing layer $d$ needs height
$2^d/d-1$ (tight at $d=7$).

Convergent falsifier (desk C, exact). Over 204,631 Mersenne-smooth
denominators $q\le2^{70}$ the counts of $\|q\Theta_2\|$ below $0.1$, $0.05$,
$0.01$, $0.001$ match a uniform sample within two percent; $\Theta_2$'s
certified continued fraction (349 quotients) has maximal quotient 3010 and
is Gauss–Kuzmin generic. Unrestricted escape from the cyclotomic denominator class is not a distinction: every odd $q$ divides $2^{\varphi(q)}-1=\prod_{m\mid\varphi(q)}\Phi_m(2)$. The open producer must leave the explicitly bounded-order and bounded-height families already excluded, or cancel inside a family not covered by those exclusions.

### 4.6 Critical-height trade-off (wave-2 S2, `check_theta2_denominator_tradeoff.py`)

In the family $X=DT_N+a_0I_{1,0,N}+a_1I_{1,1,N}$ the layer part at
$\Phi_m(2)$ is exactly $(A+\varepsilon B)/\varepsilon^2$ with one integer
linear form $L_m(D,a_0,a_1)$, giving the depth law
$v_\ell(R)=\min(0,v_\ell(L_m)-2e)$: full double-pole removal at a layer
needs the modulus $P_m^2$ (204 of 204 exact rows; the sign in desk E's E1
prose is corrected, its code was right). Certified Lagrange–Gauss minima give
$\log_2H(M,t)/\log_2\prod P_m^t=0.46$–$0.49$ in every row: the lattice pays
one bit of coefficient height for every two bits of denominator removed, so
compression inside it is capped at half the primitive mass. Best
$\log_2(q|\Theta_2-R|)$ at $N=10,\dots,18$: $17.94,25.44,48.04,51.40,66.06$
against the prefix's $32.87,51.13,87.11,100.31,131.53$. At coefficient
height $2^N$ the minimum grows ($-9.41,+0.28,+2.81,+9.20,+24.31,+39.11,+54.72$
for $N=4,\dots,16$; $N=4,6$ certified global, the rest search minima), so r07
Theorem 2 and the free-parameter count agree once the usable arity (three)
is counted. The family reaches $q|\Theta_2-R|\le1/2$ only at
$\log_2H=\log_2C_N-N$, height $2^{\Theta(N^2)}$, the order of the denominator
mass removed, which is vacuous as a route. The convergent denominators of
$\Theta_2$ (900 certified partial quotients, maximal quotient 3010) are not
cyclotomic: the part supported on primes of 2-order at most 120 carries ten
percent of $\log_2q$ on average over the 48 large convergents.

Dominance fact. The dyadic prefixes $P_n/2^n$ have $q|S-p/q|=R_n\le n+2$,
which is $O(\log q)$ against the cyclotomic family's $2^{\Theta((\log q)^2)}$.
Since $R_n\ge\varphi(n+1)/2\ge1$, the unreduced prefixes never meet the
producer; with the 2-adic reduction $q=2^{\,n-v_2(P_n)}$ the quantity becomes
$R_n/2^{v_2(P_n)}$, so the compression producer on the prefix family is
exactly the unbounded-excess condition (E10) of §2. (Desk S2's phrasing
"$\liminf R_n=0$" is corrected here.)

## 5. The prime-exact sieve family (r08)

Definition and results verified by desk D (`check_prime_exact_sieve.py`).
For a finite prime set $P$ write $n=s_P(n)t_P(n)$ and put
$c_P(n)=\varphi(s_P(n))(t_P(n)-1)$ for $t_P(n)>1$, $c_P(n)=\varphi(s_P(n))$
otherwise; $C_P=\sum_nc_P(n)2^{-n}$. Then $\varphi\le c_P\le n$, $c_P$ is exact
at every prime and obeys the Euler law inside $P$; $C_\varnothing=3/2$;
$C_P-C_Q>0$ and irrational for $P\subsetneq Q$ (tail-limit transfer through
the smooth shift $N_L=\prod_{p\in U}p^{a_p(L)}$, Lean
`smooth_shift_padicValNat`, and sparse-support irrationality); with $2\in P$
and least omitted prime $r$, $C_P-S=(r-1)2^{-r^2}+E_P$ with
$0\le E_P\le(2r^2+4r+2)2^{-(r^2+2r)}$. Sharpening (desk D): the second nonzero
error index is exactly $rr'$ with coefficient $r+r'-2$ ($r'$ the next
prime), verified at $(15,6)$, $(35,10)$, $(77,16)$, $(143,22)$. The family
is new relative to the finite Euler sieve (first error at $r^2$ against
$r$); its consumer (U) is irrationality itself; its lattice-spacing
mechanism needs $2\prod_{p<r}p<r^2$, true only for $r=3,5$, and the measured
$\log_2(\operatorname{den}(A_P)|A_P-S|)$ runs $0.8,7.3,51.5,406.2$.

## 6. Structured basepoints and difference tails (wave-2 S3)

Desk S3, `check_mobius_residue_rough_remainder.py` and
`check_totient_difference_tail_near_zeros.py`. The residue form of §1 is
absolutely convergent with $\sum_d|{\rm Term}_d(n)|=O(n\log\log n)$; for
$L=\operatorname{lcm}(1..D)k$ the remainder $\Delta_{>D}(n,n+L)$ is the
difference of two dyadic tails of $\varphi_{>D}$ (the part of
$\varphi=\mu*\mathrm{id}$ on divisors above $D$), which vanishes on a sparse
radical-determined set (smallest radical 210) and cannot stay small on long
windows (a Størmer-type obstruction); no residue class modulo
$\operatorname{lcm}(1..D)$ makes $\Delta_{>D}$ small (median ratio to the
trivial bound $0.01$–$0.03$). Smooth-shift and primorial basepoints are null
structurally: the supply predicate at $(c,v)$ is a function of $\|v2^cS\|$
and $\log_2(vc)$ alone (predicted minus measured delay in $\{0,-\varphi(v)\}$
over 210 profiles), and geometry clearance is a size statistic.

Difference tails $T_h(m)=R_{m+h}-R_m$ satisfy $T_h(m+1)=2T_h(m)-(\varphi(m+1+h)-\varphi(m+1))$
and $-(m+2)<T_h(m)<m+h+2$; near-zeros $|T_h(m)|<1$ occur about $C_h\log X$
times up to $X$ (counts 26, 89, 96, 203, 138, 186 for $h=1,2,4,6,12,60$ at
$X=2\cdot10^6$); the record near-zeros ($h=6$, $m=1380810$; $h=60$, $m=6425$)
are certified nonzero at bracket width $2^{-491}$.

Theorem 6.1 (tail-only exclusion; desk S3, exact). Under $S=a/(2^cv)$ every
$vR_{c'}$ with $c'\ge c$ is an integer, so one exact tail at $c'=C$ excludes
every exponent $c\le C$ at once. Computed: $S\ne a/(2^cv)$ for every
$c\le10^{30}$, every odd $v\le999999$, and every divisor $v$ of $2^h-1$ for
$h\in\{6,12,24,36,60\}$ (worst margin $2^{-21}$ against a $2^{-200}$ bracket;
$J\le360$ totients near $C$; $C=10^{30}$ costs about 110 s). Finite dyadic
exclusions are thereby retired as a compute target; the mechanism of
Theorem 2.1 is a different certificate shape and its one-way sufficient
condition (E10) is unaffected.

## 7. Literature and the mechanism gap (desk F, fetched primary sources)

- erdosproblems.com/249 is open; erdosproblems.com/250, $\sum\sigma(n)2^{-n}$,
  is solved: irrationality by Duverney (1995, CRAS 321, a $q$-analogue of
  $\zeta(2)$), transcendence by Nesterenko (1996) through
  $\sum_n\sigma(n)q^n=(1-E_2(q))/24$ and the algebraic independence of
  $E_2,E_4,E_6$ at algebraic $q$. The corpus recorded neither before this
  batch.
- Erdős 1948 (read in full) is a three-zone forced-digit-block argument:
  a CRT window $t^{j+1}\mid d(m+j)$, a buffer where $d\le2^{k/4}$ obtained
  by a first-moment count over the free shift, and a far tail bounded by
  $d(r)<r$. The window is cheap; the size control is the whole content.
  Erdős [Er88c, p.102] grouped $\varphi$ and $\sigma$ together as beyond his
  method. Coordinate-free form: Duverney–Tachiya (2019) property
  X = (H1) multiplicative divisibility and (H2) $N^{o(1)}$ size just past the
  window. $d$ has both; $\sigma$ and $\varphi$ have (H1) and fail (H2); the
  batch controls fail (H2) and lack (H1). Measured deficit of the longest
  window against the required $\log_2X$: $3.97,6.29,7.61,9.93$ at
  $X=10^3,\dots,10^6$, widening (`check_erdos1948_mechanism_transfer.py`).
- Theorem 7.1 (no $\eta$-quotient target; desk F, ordinary proof). There is
  no integer sequence $(c_n)$ and $L\ge1$ with
  $-x\frac{d}{dx}\log\prod_n(1-x^n)^{c_n}=L\sum_n\varphi(n)x^n$: at an odd
  prime $p$ the coefficient identity reads $c_pp=L(p-2)$, so $p\mid2L$, which
  fails for $p>2L$. Duverney's mechanism for $\sigma$ (long zero blocks from
  the pentagonal lacunarity of $\eta$) has no analogue for $\varphi$.
- Exact bridge (`check_sigma_totient_lambert_bridge.py`):
  $\varphi=(\mu*\mu)*\sigma$, so $\sum\varphi(n)x^n=\sum_M(\mu*\mu)(M)\sum_n\sigma(n)x^{Mn}$;
  $S$ is an unbounded-level superposition of the solved $\#250$ object, which
  is the classical content of the corpus producer
  `uniform_growing_level_specialisation`.
- Nesterenko search (conductor, exact, order 200): $\sum\varphi(n)q^n$ lies
  in no $\mathbb Q$-span of level-one quasimodular monomials
  $E_2^aE_4^bE_6^c$ through weight 12, nor of $E_k(q^M)$ for $M\le6$, nor of
  their weight-two products; the cheap transcendence route is retired at
  this depth.
- The Padé lane (Borwein; Duverney–Tachiya; Koizumi–Yokoi 2026) is
  weight-free or periodic-weight; the Möbius weight on the squared
  Mersenne rung is outside it. Vandehey (2012) leaves the Chowla–Erdős
  growth threshold unknown; $\#249$ needs multiplier growth about
  $n/(\log n)^{\log2}$. The Kaneko–Suzuki–Tachiya (2026) support-sparsity
  criterion and the corpus density-zero control bound one frontier from
  opposite sides. The natural-boundary row's Banks–Luca–Shparlinski
  dependency is removable (Pólya–Carlson plus non-quasi-polynomiality).
  Sibling map: of the six problems Erdős grouped, only $\#249$ and $\#1049$
  remain open ($\#250$ Duverney/Nesterenko; $\#69$, $\#258$ Tao–Teräväinen).
  $\#257$ remains open; a blog remark attributing its resolution to
  Tao–Teräväinen is a slip for $\#69$.

## 8. Remaining implication and retired routes

The single remaining implication is unchanged: the actual consecutive
totient word forces the canonical residue-gap supply, equivalently the
2-adic residues of $P_n$ escape the $v$-dilated confinement of §1 for every
$(c,v)$. Any proof must transfer information across scales (relations
between $\varphi(n)$ and $\varphi(mn)$ for unboundedly many $m$; property
(H1) strengthened) and cannot rest on a size bound (H2), on any fixed
modulus, on density one, on near-prime agreement, on growing 2-adic
precision, on carry rank, on correlation asymptotics, or on finitely many
exact prime laws.

Retired in this batch (each by an exact computation or a short proof):
termwise dyadic windows for every $(c,v)$; higher derivative rungs;
width-widening in the Lambert family; finite prime-law substitutes;
smooth-shift and primorial basepoints; residue-class splitting of the tail
difference; the $\eta$-quotient analogue of Duverney's argument; a finite
quasimodular expression for $\sum\varphi(n)q^n$ through weight 12;
r08's lattice-spacing mechanism; restating the canonical normal form.

## 9. Evidence table

Lean (both re-run by the conductor, `lake env lean`, exit 0, zero output):

| module | declarations | content |
|---|---|---|
| `PrefixValuationAndControlRigidity.lean` | 21 (3 defs, 18 theorems, 1 example) | Theorems 2.1, 2.2, rigidity theorems of §3, `smooth_shift_padicValNat`, `topBand_prime_layer_cancellation_unique` |
| `ResidueClassTotientSeries.lean` | 13 public + private lemmas | Theorem 3.4 chain: `isolated_pulse_separation`, `irrational_dyadicValue_of_pulses`, `two_sided_prime_isolation`, `irrational_totientObservable`, `fixed_resolution_observable_irrational`, `residue_series_irrational` |

Scripts (all under `formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/`, stdlib only, deterministic `--quick`):

| script | owner | receipt |
|---|---|---|
| `check_residue_class_pulse_separation.py` | A | isolated pulses found for $m=3..6$, $L\le3$; Lemma 3 bound confirmed on a rational bracket |
| `check_precision_error_rational_controls.py` | A | r01/r02/r04 controls built to finite depth; divisibility and congruence properties verified |
| `check_finite_prime_law_rational_controls.py` | A | exact $p$-laws at every argument for $P=\{2\},\{2,3\},\{2,3,5\}$, zero failures |
| `check_backward_window_residue_diversity.py` | B | $D_N$, $E_N$ table $2^4..2^{20}$, $N-D_N\le4$; the two $N=64$ collision pairs |
| `check_even_identity_control_arithmetic.py` | B | r03 Theorem 2 control: even identities, prime powers, precision (15) |
| `check_quantised_rational_control_collapse.py` | B | r04 §3.2 control certified; relations (14)–(15) identical at every $N\le2^{13}$ |
| `verify_rank_uniform_hankel_domination.py` | C | max deviation $0.6413$; both certificates pass; $s=1$ counterexample; parity table |
| `check_lambert_correction_denominator.py` | D | $\kappa$ to 12 digits; divisibility chain to $N=120$; $N=13$ layers; Theorem 2 growth |
| `check_prime_exact_sieve.py` | D | $C_P$ brackets; error indices $r^2$, $rr'$; mechanism scale mismatch |
| `check_lambert_derivative_denominator_compression.py` | E | identity family 16/16; layer valuations; $\min\log_2q|S-R|$ per $N\le38$ |
| `check_totient_dyadic_window_staircase.py` | E | staircase law; $v_2(P_n)$ records; exclusion rectangle $c\le2786603$, odd $v\le259$ |
| `check_erdos1948_mechanism_transfer.py` | F | window deficit table |
| `check_sigma_totient_lambert_bridge.py` | F | $\varphi=(\mu*\mu)*\sigma$ exact |
| `check_mobius_residue_rough_remainder.py` | S3 | residue form 78/78; $\Delta_{>D}$ grid; vanishing criterion 140000 rows; smooth-shift null |
| `check_totient_difference_tail_near_zeros.py` | S3 | recurrence 30/30; near-zero census; record certification; tail-only exclusion ladder to $10^{30}$ |
| `check_theta2_denominator_tradeoff.py` | S2 | depth law 204/204; certified lattice minima ($\log_2H/\log_2$ modulus $0.46$–$0.49$); critical-height minima; convergent denominators of $\Theta_2$ |
| `check_quasimodular_relation_search.py` | conductor | $\sum\varphi(n)q^n$ not in any tested quasimodular span (order 200; quick mode order 120) |
| `check_prefix_confinement_exclusion.py` | S1 | confinement on rational surrogates (0 failures on 8 rows); generic-residue template; record $n=10^{18}$, $t=2048$, odd $v\le10^{298.8}$ |
| `check_totient_prefix_valuation_records.py` | S1 | excess records to $10^9$ (none beyond 7.59); $M_s(X)$ law $C_k\approx0.54k^{0.96}$; block divisibility densities |
| `check_prefix_odd_collision_families.py` | S1 | odd-restricted (CD) deficit $\le2$ to $2^{24}$; no repeating collision family; occupancy generic |

## 10. Correction, 2026-09-06 (Erdős 249 corrective-integration pass)

This block corrects labels and one number. Sections 1 to 9 are unedited.

### 10.1 "Retired in this batch" is one word doing five different jobs

Section 8 lists eleven items as retired. Retirement is not a single relation,
and the list mixes proofs with bounded searches. The precise label for each,
in the vocabulary the claim frontier now uses:

| item (§8 wording) | precise label | what is actually established |
|---|---|---|
| termwise dyadic windows for every `(c,v)` | `proved_class_obstruction` | one inequality: `2^t \| φ(N+t)` forces `2^t ≤ φ(N+t) ≤ N+t−1 < v(N+t+2)`, so the window half excludes no denominator at any `(c,v)`. The staircase measurement `t(X) ≈ 0.47 log₂X` is not part of it. |
| higher derivative rungs | `proved_class_obstruction` | `k ≥ 2` strictly deepens the pole at each layer `Φ_m(2)`, so the derivative family cannot reduce the denominator. |
| width-widening in the Lambert family | `proved_class_obstruction` | widening `j` is a quadratic net loss; at `N = 38` the reduced `log₂q` runs 652, 589, 1202, 2391. |
| finite prime-law substitutes | `counterexample_to_proposal` | for every finite prime set `P` an explicit rational-valued control obeys φ's exact `p`-law at every argument for every `p ∈ P`. This refutes a proposal about the coefficient sequence; it closes no route on `S`. |
| smooth-shift and primorial basepoints | `proved_class_obstruction` | the canonical supply predicate at `(c,v)` is a function of `‖v·2^c·S‖` and `log₂(vc)` alone, so the basepoint's arithmetic shape is structurally invisible. |
| residue-class splitting of the tail difference | `proved_class_obstruction` | `Δ_{>D}` vanishes exactly on a sparse radical-determined set and cannot stay small on long windows; no residue class modulo `lcm(1..D)` makes it small. |
| the η-quotient analogue of Duverney's argument | `proved_class_obstruction` | matching coefficients forces `c_p p = L(p−2)` at every odd prime `p`, hence `p \| 2L`, false for `p > 2L`. Complete proof. |
| a finite quasimodular expression through weight 12 | `empirical_deprioritisation` | a bounded exact search at expansion order 200 over weights ≤ 12 and the tested level and product families. Not a theorem for all weights and levels. A finite quasimodular expression at higher weight or level would reopen the Nesterenko route, and §7 says so. This row must never be cited as closing the modular lane. |
| r08's lattice-spacing mechanism | `proved_class_obstruction` | the mechanism needs `2∏_{p<r}p < r²`, true only at `r = 3` and `r = 5`. |
| restating the canonical normal form | `target_equivalent_reformulation` | an equivalence moves no truth value. Not a retirement at all; it belongs in a different column. |
| the Möbius–Mersenne denominator lattice (§4) | `proved_class_obstruction` plus `empirical_deprioritisation` | the `κN²` denominator growth, the rank-one top band and the quadratic width loss are proved. The genericity evidence (204,631 Mersenne-smooth `q ≤ 2^70` matching a uniform sample within two percent; Θ₂'s 349-quotient continued fraction with maximal quotient 3010) is sampling, and proves nothing. |

### 10.2 The certified continued-fraction floor: the exponents are off by one wherever they were copied

The receipt `state/formal_math/probes/erdos249_certified_cf_receipt.json` records
`denominator_lower_bound_power_of_two_exponent = 39989` and
`strict_decimal_power_lower_bound = 12038`, alongside
`denominator_lower_bound_bit_length = 39990` and
`denominator_lower_bound_decimal_digits = 12039`. The last two are the length
of the denominator, not exponents. The correct statement is

> if `S = a/q` in lowest terms with `q > 0`, then `q ≥ 2^39989` and `q > 10^12038`.

`research_packet.json` states this correctly and warns in the same sentence that
"bit length and decimal digit count are not exponents". The claim-frontier row
`erdos249.certified_cf_denominator_exclusion_10e12039` states `q ≥ 2^39990 >
10^12039` and is wrong by one in each base; so does the 2026-09-06 result audit.
The row id keeps its `10e12039` spelling for stability, and the statement is
corrected in
`docs/strategy/staging/rapid_breakout/audit/patches/frontier_249.json`.

### 10.3 Scope note on §3 and §5

The rigidity theorems of §3 are positive theorems about φ. Their use here is
negative, which is why they sit under a no-go heading, and the two facts should
not be merged: `even_law_and_eventual_congruence_forces_totient` needs no
odd-prime law and no size bound, and that is what makes the r01 and r03 control
families mutually exclusive. The prime-exact sieve family of §5 is
`counterexample_to_proposal` for the same reason as the finite prime-law
substitutes; its mechanism scale mismatch (`2∏_{p<r}p < r²`) is the proved part.
