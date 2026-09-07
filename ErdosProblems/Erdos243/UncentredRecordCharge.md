# Record charges without centring, and the arithmetic freedom of variable numerators

**Review r6, 7 September 2026.** The two principal results below are ordinary proofs developed in this review. They have not been independently refereed or checked in Lean. Their novelty relative to the full literature is not established. They concern a larger arithmetic class than the unit-numerator system of Erdős #243. The original problem is not resolved.

The supplied r6 corpus already contains coefficient-uniform bounded height, the positive-numerator bounded-defect criterion, the canonical analytic bridge, the centred weighted-record theorem, and the abstract arbitrary-envelope avoidance construction. Those are inputs and comparisons, not new results of this review.

## 1. The arithmetic system and the three different increments

Let `a_n >= 2`, `L_n > 0`, and `U_n > 0` be integers, and let `b_n` be arbitrary integers. Suppose

\[
L_{n+1}=\operatorname{lcm}(L_n,a_n),\qquad
\rho_n=\gcd(L_n,a_n),\qquad
\rho_nU_{n+1}=a_nU_n-b_nL_n=U_n-V_n,
\tag{1}
\]
where
\[
V_n=b_nL_n-(a_n-1)U_n.
\]
No centring, limit, reciprocal-series interpretation, sign bound on the coefficients, or growth condition is assumed.

Set
\[
R_n=\max_{0\le j\le n}U_j,\qquad
\mathcal R=\{n:U_{n+1}>R_n\}.
\]
At a record index write
\[
u=U_n,\quad y=U_{n+1},\quad R=R_n,\quad
d=y-u,\quad h=y-R,\quad r=-V_n=\rho_n y-u.
\tag{2}
\]
All three quantities `d`, `h`, and `r` are positive integers, but they have different meanings. The actual jump `d` includes recovery from a drawdown. The record increment `h` does not. The raw error magnitude satisfies
\[
r=d+(\rho_n-1)y.
\tag{3}
\]
Thus an overlap record can have a unit actual jump and a very large raw error.

Call a record *fresh* when `rho_n=1`. At a fresh record,
\[
d=(a_n-1)U_n-b_nL_n.
\tag{4}
\]
Any divisor of both `U_n` and `L_n` divides this jump. Earlier fresh record multipliers are pairwise coprime: `a_i` divides every later `L_j`, whereas `gcd(a_j,L_j)=1` at a fresh record. This supply argument is already available for the centred unit-numerator system in `LcmRecordExcess.md`, §3.

## 2. A weighted height theorem with no centring hypothesis

Fix an integer `B>=0`. On record indices define
\[
J_B(n)=
\begin{cases}
(U_{n+1}-U_n-B)_+,&\rho_n=1,\\
R_{n+1}-R_n,&\rho_n\ge2.
\end{cases}
\tag{5}
\]
The second line charges only the newly attained height, rather than the potentially much larger raw error.

### Theorem 1: the mixed record charge

For every finite nonnegative nonincreasing function `f:[1,infinity)->[0,infinity)` satisfying
\[
\int_1^\infty f(t)\,dt=\infty,
\]
the arithmetic system (1) satisfies
\[
\boxed{\quad
\sup_n U_n<\infty
\quad\Longleftrightarrow\quad
\sum_{n\in\mathcal R}J_B(n)f(U_n)<\infty.
\quad}
\tag{6}
\]
The statement holds for each fixed `B`, rather than merely for the existence of a suitable baseline. If `U` is unbounded, there are constants `c>0` and `H<infinity`, depending on the orbit and `B`, such that
\[
\sum_{\substack{n<N\\n\in\mathcal R}}J_B(n)f(U_n)
\ \ge\ c\int_H^{\max(H,R_N)} f(t)\,dt
\tag{7}
\]
for every sufficiently large `N`. No uniform lower bound for `c` over all orbits is asserted.

#### Proof: finitely many fresh records

Bounded integer height has only finitely many strict records, proving the forward direction.

Suppose height is unbounded. First suppose there are only finitely many fresh records. After an index `T`, every record is an overlap record. At such an index,
\[
J_B(n)f(U_n)=(R_{n+1}-R_n)f(U_n)
\ge\int_{R_n}^{R_{n+1}}f(t)\,dt,
\]
since `U_n<=R_n` and `f` is nonincreasing. The record intervals partition the increase from `R_T` to `R_N`. Their charges therefore dominate `int_(R_T)^(R_N) f`, which diverges. This gives (7) with `c=1`.

#### Proof: infinitely many fresh records

For `B=0`, `J_0(n)>=R_{n+1}-R_n` at every record, and the same argument suffices. Let `B>=1`.

Choose `B` earlier fresh record multipliers
\[
m_0,\ldots,m_{B-1}>B.
\]
They are pairwise coprime, and all divide `L_n` after some index `T`. Put `P=prod_i m_i`. Then `P>=B+1`. The Chinese remainder theorem supplies an integer `z` with `m_i | z+i`. Consider all integer translates
\[
\tau=z+B+kP>R_T.
\]
They are spaced by `P`, and every integer in `[tau-B,tau)` is divisible by one of the assigned old multipliers. Choosing all translates above `R_T` ensures that the first is at most `R_T+P`; restricting prematurely to a particular nonnegative range of `k` would require an additional cutoff.

Each such height reached by time `N` has one first crossing. Its source is below the height, and its endpoint is a strict running record. A fresh first crossing with `d<=B` would have
\[
\tau-B\le U_n<\tau.
\]
The assigned `m_i` divides `U_n` and `L_n`, so (4) gives `m_i|d`. This contradicts `0<d<=B<m_i`. Thus a fresh crossing has `d>B`.

If one fresh step first crosses `s>=1` selected heights, spacing gives
\[
(s-1)P<d.
\]
With `t=d-B>=1`, one has `d=B+t<=Pt`, so `s<=t=J_B(n)`. At an overlap step, the selected heights are distinct integers in `(R_n,R_{n+1}]`, so their number is at most `R_{n+1}-R_n=J_B(n)`. In either case, monotonicity gives
\[
\sum_{\tau\text{ first crossed at }n}f(\tau)
\le J_B(n)f(U_n).
\]
Every selected height is charged exactly once, even when the sequence has drawdowns and repeated recrossings. Consequently
\[
\sum_{\substack{T\le n<N\\n\in\mathcal R}}J_B(n)f(U_n)
\ge \sum_{\substack{R_T<\tau\le R_N\\\tau\equiv z+B\ (\mathrm{mod}\ P)}}f(\tau)
\ge {1\over P}\int_{R_T+P}^{\max(R_T+P,R_N)}f(t)\,dt.
\tag{8}
\]
For the last comparison, the intervals `[tau,tau+P]` following the sampled heights cover the integration interval and each has integral at most `P f(tau)`. This proves divergence and (7). ∎

### Corollary 2: the original raw-error charge also needs no centring

Under the same assumptions,
\[
\boxed{\quad
\sup_n U_n<\infty
\quad\Longleftrightarrow\quad
\sum_{n\in\mathcal R}(-V_n-B)_+ f(U_n)<\infty.
\quad}
\tag{9}
\]

**Proof.** On fresh records the two charges agree. On an overlap record with endpoint `y>=B`,
\[
(r-B)-(y-R)=(\rho_n-1)y+R-u-B\ge y-B\ge0.
\]
Only finitely many record endpoints can be below `B`. Thus the raw charge eventually dominates (5), and Theorem 1 applies. Bounded height again makes the sum finite. ∎

This is the actual extension of the supplied `LcmRecordExcess.md`, §3. That theorem assumes unit coefficients and lower centring `-U_n<=2V_n`. The new argument removes both restrictions. It also gives a smaller mixed charge, showing exactly how much of the overlap cost must be retained. On canonical unit-numerator orbits, sufficiently late records are fresh, so this does not add a new endpoint class beyond the already-admitted weighted criterion.

### Corollary 3: bounded errors and normalised vanishing

If `V_n>=-B` at all sufficiently late record indices, then `U` is bounded. This recovers the r5 coefficient-uniform bounded-height theorem as a special case of (9). It is not a second novelty claim.

If, in addition, `V_n/U_n->0`, then the integral `V_n` is eventually zero. Equation (1) becomes `rho_n U_(n+1)=U_n`. Positive integer height is then nonincreasing and eventually constant, and `rho_n=1` eventually. Normalised vanishing enters only in this final stationarity step.

## 3. Sharpness tests for the hypotheses and the observable

These examples are exact infinite arithmetic systems. Their displayed recurrences prove their validity; finite checks merely reproduce the algebra.

### 3.1 Actual-jump excess cannot replace the charge when centring is removed

For `n>=0`, put
\[
a_n=2^{n+2},\quad b_n=n+1,\quad
L_n=2^{n+1},\quad U_n=n+2.
\]
Then `rho_n=L_n`, (1) holds, and
\[
V_n=(n+2)-2^{n+1}(n+3).
\]
Every step is a record and every actual jump is one. Nevertheless `U_n` is unbounded. For `B=1`, actual-jump excess `(U_(n+1)-U_n-B)_+` is identically zero. The mixed charge is one, and the raw charge is much larger, as the theorem requires.

This is a genuine positive rational series:
\[
{U_n\over L_n}-{U_{n+1}\over L_{n+1}}
={n+1\over2^{n+2}},\qquad
\sum_{n\ge0}{n+1\over2^{n+2}}=1.
\]
`L_0=2` is an allowed, nonminimal clearing denominator for the integer sum. From the next index it agrees with the usual prefix LCM. The example does not satisfy normalised vanishing.

### 3.2 Divergent integral is essential

Put
\[
L_n=2^{2^n}-1,\quad U_n=2^n,\quad
a_n=L_n+2,\quad b_n=U_n.
\]
Then `L_(n+1)=L_n(L_n+2)`, `rho_n=1`, and `U_(n+1)=2U_n`, so `V_n=-U_n`. The identity
\[
{U_n\over L_n}-{2U_n\over L_n(L_n+2)}={U_n\over L_n+2}
\]
shows that this is another positive series of sum one. For every `epsilon>0`, the integrable weight `f(t)=t^(-1-epsilon)` gives a finite record-charge sum, although height is unbounded. This is an elementary telescoping example, not a claimed new special-function identity.

### 3.3 Smooth positivity cannot replace monotonicity

Use the orbit of §3.1 and
\[
f(t)=\sin^2(\pi t)+e^{-t^2}.
\]
This weight is smooth, strictly positive, and has divergent integral, but at the integer states `f(U_n)=exp(-(n+2)^2)`. The raw charges are `O(n2^n)`, so their weighted sum is finite. Monotonicity is what prevents the weight from avoiding the discrete states.

## 4. A local realisation principle using Dirichlet's theorem

### Lemma 4: prescribe the next numerator, then choose the prime denominator

Suppose `gcd(U,L)=gcd(v,L)=1`, with `U,L,v` positive integers. There are arbitrarily large primes `a` and positive integers `b` such that
\[
v=aU-bL,\qquad \gcd(v,aL)=1.
\tag{10}
\]
We may also require `v/(aL)<U/(2L)`.

**Proof.** Choose the reduced residue class `a == v U^(-1) (mod L)`, with the class modulo one interpreted as unrestricted. Dirichlet's theorem supplies arbitrarily large primes in this class. Choose one exceeding `v` and `2v/U`. Then `b=(aU-v)/L` is a positive integer, `a` does not divide `v`, and the displayed contraction holds. ∎

The precise external input is Dirichlet's theorem, stated as Theorem 18.1 in Sutherland's MIT 18.785 Lecture 18 [D1]. No bound on the least prime in a progression is used. The size of the chosen prime is deliberately free.

The lemma separates two constraints. The congruence enforces integrality of the new coefficient. Choosing a sufficiently large representative enforces positivity and tail contraction. The coefficient `b` is then forced by the equality. For unit fractions it must equal one, so the representative is no longer free: `aU-v=L`. This is the point where the construction stops applying to Erdős #243.

## 5. An exact rational-series version of the arbitrary-envelope counterexample

### Theorem 5: arbitrarily slowly unbounded negative errors with variable numerators

Let `omega:[1,infinity)->(0,infinity)` be nondecreasing and tend to infinity. There are strictly increasing prime denominators `a_n`, positive integers `1<=b_n<a_n`, and positive integral exact states `U_n,L_n` such that:

\[
\sum_{n\ge0}{b_n\over a_n}=1,\qquad
L_0=U_0=1,\qquad L_{n+1}=a_nL_n,
\tag{11}
\]
\[
U_{n+1}=a_nU_n-b_nL_n,\qquad
\gcd(U_n,L_n)=\gcd(a_n,L_n)=1,
\tag{12}
\]
\[
d_n=U_{n+1}-U_n>0,\qquad
\sup_n d_n=\infty,\qquad
{d_n\over\omega(U_n)}\longrightarrow0,\qquad
{d_n\over U_n}\longrightarrow0,
\tag{13}
\]
and
\[
\lambda_n={b_{n+1}a_n^2\over b_na_{n+1}}\longrightarrow1.
\tag{14}
\]
Every fraction is proper and reduced. The errors are `V_n=-d_n`, so they never vanish. We may simultaneously arrange `a_(n+1)/a_n^2->infinity`. Thus (14) is the weighted critical rate, not the unit-numerator growth assumption in #243.

The r4 corpus already constructs an abstract avoidance sequence with (13). The new content is an adaptive Dirichlet construction giving all the exact arithmetic, positivity, rational-tail, and weighted-rate conditions (11), (12), and (14) simultaneously.

#### Step 1: adaptive construction

Start with `U_0=L_0=1`. Given coprime positive `U_n,L_n`, let `v` be the least integer greater than `U_n` and coprime to `L_n`. Use Lemma 4 to select a prime `a_n` in the class
\[
a_n\equiv vU_n^{-1}\pmod{L_n}
\]
so large that
\[
a_n>2v,\qquad a_n\ge2^{n+4},\qquad
\omega(a_n/2)\ge(n+1)^2.
\tag{15}
\]
Also require strict increase; for `n>=1` one can impose the stronger condition `a_n>(n+1)a_(n-1)^2`. Set
\[
U_{n+1}=v,\quad L_{n+1}=a_nL_n,\quad
b_n={a_nU_n-v\over L_n}.
\tag{16}
\]
The coefficient is a positive integer. The choice `a_n>v` preserves primitive state and makes every step fresh.

#### Step 2: identify the whole avoidance set

Let
\[
\mathcal A=\{m\ge1:a_j\nmid m\text{ for every }j\}.
\]
Every chosen `U_n` avoids past primes by construction. Every future prime exceeds its own successor numerator, which is greater than `U_n`; thus it cannot divide `U_n` either. Every integer strictly between consecutive `U_n` is excluded by a past prime, by the least-choice rule. Since `U_n` increases without bound, it enumerates exactly `mathcal A`.

The reciprocal mass of the primes is at most `sum_(j>=0)2^(-j-4)=1/8`. In particular, a union bound gives positive lower density for `mathcal A` and `U_n=O(n)`. This observation is useful but not needed for the main estimates below.

#### Step 3: prove the small-rise estimate

For `u` in `mathcal A`, put
\[
k(u)=\#\{j:a_j\le2u\},\qquad H=2k(u)+2.
\]
The exponential lower bound in (15) gives `k(u)=O(log u)`, hence `H<=u` eventually. Only these `k(u)` primes can exclude integers of `(u,u+H]`. The number they exclude is at most
\[
\sum_{a_j\le2u}\left({H\over a_j}+1\right)
\le {H\over8}+k(u)<H.
\]
Therefore the next admissible integer is at most `u+H`, and
\[
d_n\le2k(U_n)+2=O(\log U_n).
\tag{17}
\]
If `k=k(u)>=1`, then `a_(k-1)<=2u`, and (15) gives `omega(u)>=k^2`. Since `k(U_n)->infinity`,
\[
0\le{d_n\over\omega(U_n)}\le{2k+2\over k^2}\longrightarrow0.
\]
Equation (17) also proves `d_n/U_n->0`.

For any `J`, CRT places `J` consecutive integers, arbitrarily far out, into distinct selected prime divisibility classes. No integer of that block belongs to `mathcal A`. Because `mathcal A` is infinite and has positive density, there are members on both sides of sufficiently late such a block. Thus the gaps of its enumeration are unbounded.

#### Step 4: rationality and reduced positive terms

Set `x_n=U_n/L_n`. By (15),
\[
{x_{n+1}\over x_n}={U_{n+1}\over a_nU_n}<\frac12.
\]
Thus `x_n->0`, and (16) gives
\[
{b_n\over a_n}=x_n-x_{n+1}>0.
\]
Summing proves (11). Since `x_n<=x_0=1` and `x_(n+1)>0`, every term is strictly smaller than one, so `b_n<a_n`; primality of `a_n` makes each fraction reduced. The exact tail is `x_n=sum_(j>=n)b_j/a_j`. Since the denominators are distinct primes and the sum is one, product and LCM clearances coincide. Thus these are also the raw states `C_n=U_n`, `D_n=L_n`; the small error is not obtained by removing an artificially large common factor.

#### Step 5: weighted critical rate

Let
\[
\epsilon_n={U_{n+1}\over a_nU_n},\qquad
 t_n={b_n\over a_n}=x_n(1-\epsilon_n).
\]
By (17), `U_(n+1)/U_n->1`, while `a_n->infinity`, so `epsilon_n->0`. Exact algebra gives
\[
\lambda_n=a_n{t_{n+1}\over t_n}
={U_{n+1}\over U_n}\,{1-\epsilon_{n+1}\over1-\epsilon_n}
\longrightarrow1.
\]
With the optional faster-than-quadratic denominator choice,
\[
\frac{b_{n+1}}{b_n}=\lambda_n\frac{a_{n+1}}{a_n^2}\longrightarrow\infty.
\]
Thus that version certainly uses unbounded coefficients; it is not a finite-alphabet example.
This proves the theorem. ∎

### What the example settles, and what it leaves untouched

There is no coefficient-uniform replacement of bounded negative error by an arbitrary prescribed unbounded allowance, even for positive rational series, primitive states, prime denominators, no overlap at all, and the weighted critical rate. For example, choose `omega(t)=log log(t+e^e)` to obtain negative magnitudes `o(log log U_n)` which are nevertheless unbounded.

Theorem 1 still applies to these examples. For each fixed baseline, their cumulative record excess has a positive linear lower bound in attained height, with an orbit-dependent constant. Individual jumps can grow arbitrarily slowly while their baseline excess still accumulates linearly. This is why a pointwise allowance cannot replace an accumulated budget.

No counterexample to the unit-fraction problem is constructed. The coefficients are adjustable and the bare denominator growth can be made much faster than quadratic. A proof using the exact unit coefficient or canonical modulus-growth synchronisation can distinguish these examples from #243.

## 6. The remaining unit-numerator problem

The supplied canonical notation is
\[
F_B(X)=\sum_{\substack{n\in\mathcal R\\U_n\le X}}(-V_n-B)_+.
\]
The remaining universal estimate is
\[
\exists B\ge0:\qquad \liminf_{X\to\infty}{F_B(X)\over X}=0.
\tag{18}
\]
The arithmetic already proves a positive linear lower bound on nonterminal canonical orbits. Neither theorem above proves (18). The new construction shows that the corresponding assertion fails badly when the coefficient is allowed to vary, despite exact rational tails and normalised vanishing.

A useful next question is therefore: which use of `b_n=1` gives information not preserved by Lemma 4? At a fresh step, that constraint is the exact equality `a_nU_n-U_(n+1)=L_n`; congruence alone loses the requirement that the quotient be one. A proof that replaces this equality by divisibility has already discarded the information that defeats the construction.

A second question is how much coefficient freedom is needed. The construction uses unbounded coefficients and freely growing primes. It does not decide the finite-alphabet version under normalised vanishing, nor a version imposing the canonical doubly exponential scale on the moduli. Those are separate constraints and should be tested separately before claiming that arithmetic realisability alone is sufficient.

## 7. Evidence, source collision, and external references

The candidate Lean file supplied with this review contains proposed proofs of the local nonfresh-record inequality, covered crossing, capacity estimate, and the composition of existing CRT supply with the coefficient fence. They contain no `sorry` or new axioms but have not been compiled. No global theorem above is labelled Lean checked.

The r6 `LcmRecordCrossing.lean` already supplies `exists_crt_covering_progression` from a finite coprime family. The r5 handoff's generic statement that all CRT supply is missing is too broad. The missing formal work is the correct global supply/composition and infinite analytic transfer; finite CRT construction should be reused.

[D1] A. V. Sutherland, *18.785 Number Theory I*, Lecture 18 (10 November 2021), Theorem 18.1. https://math.mit.edu/classes/18.785/2021fa/LectureNotes18.pdf . Directly read, including rendered first page, on 7 September 2026. The original result is P. G. L. Dirichlet (1837); English translation by R. Stephan, arXiv:0808.1408v2, https://arxiv.org/abs/0808.1408 .

The supplied coefficient bounded-height and weighted criteria overlap the general setting of Badea's weighted rational-series work. The terminal weighted recurrence itself is classical. No novelty claim is based on that recurrence. The new candidates here are the centring-free mixed/raw weighted charge and the adaptive exact arbitrary-envelope construction. A literature search did not identify an exact antecedent; that absence is not a priority determination.
