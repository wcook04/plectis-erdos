# Countable gluing of irrational Mersenne supports and actual failures of synchronisation

Research return, 7 September 2026. Ordinary proofs for independent adjudication; no new Lean or Comparator build and no historical priority claim. Numbering agrees with the companion PDF.

# The arithmetic quantity and the existing inputs

Write $\mathbb N=\{1,2,\ldots\}$. For $A\subseteq\mathbb N$ and an integer $b\ge2$, put $$X_A(b)=\sum_{a\in A}\frac1{b^a-1},\qquad
 \delta_{b,a}(N)=\frac{b^{N\bmod a}-1}{b^a-1},\qquad
 \Delta_{b,A}(N)=\sum_{a\in A}\delta_{b,a}(N).$$ These series converge for each fixed $N$. Dividing $N$ by $a$ gives $$\tag{1}
 \Delta_{b,A}(N)=(b^N-1)X_A(b)-J_{b,A}(N),\qquad J_{b,A}(N)\in\mathbb Z.$$ Indeed, if $N=qa+r$, then $$\frac{b^N-1}{b^a-1}
 =b^r\sum_{i=0}^{q-1}b^{ia}+\frac{b^r-1}{b^a-1},$$ and only $a\le N$ contribute to the integer sum. For infinite $A$ and $N\ge1$, an exponent $a>N$ gives $\Delta_{b,A}(N)>0$. If $X_A(b)=p/q$ with $q\ge1$, every positive displacement is at least $1/q$.

**Definition 1.1**. A support $A$ belongs to $\mathcal R$ if, for every $\varepsilon>0$ and positive integers $L,N_0$, there is $N\ge N_0$ such that $L\mid N$ and $\Delta_{2,A}(N)<\varepsilon$.

The prescribed-divisor condition is useful for adjoining finite supports. Finite sets belong to $\mathcal R$. The class is hereditary, and adjoining or deleting finitely many exponents preserves membership: include the least common multiple of the added exponents in $L$.

**Lemma 1.2**. *If $A\in\mathcal R$, then $X_B(b)$ is irrational for every infinite $B\subseteq A$ and every integer $b\ge2$.*

*Proof.* For $0<r<a$, $$\frac{b^r-1}{b^a-1}\le b^{-(a-r)}\le2^{-(a-r)}
 \le 2\frac{2^r-1}{2^a-1}.$$ For $r=0$ both displacements vanish. Thus $0<\Delta_{b,B}(N)\le2\Delta_{2,A}(N)$ for $N\ge1$ and infinite $B$. Arbitrarily small positive displacements contradict (1) under rationality. ◻

Here are the existing classes used below. For a finite nonempty prime set $P$, write $$h_P(a)=\prod_{p\in P}p^{v_p(a)},\qquad
 W_P(E)=\sum_{a\in E}\frac{h_P(a)}{a(2^{h_P(a)}-1)}.$$ Let $\mathcal W$ consist of supports $E$ with $W_P(E)<\infty$ for some such $P$. Let $\mathcal V$ consist of supports covered by finite sets $G_j$ for which there are $0<\alpha_j\le1$, $\eta_j>0$ with $\sum_j\eta_j=1$, and $c_{j,d}\ge0$ satisfying $$\tag{2}
 f_{G_j}(n)^{\alpha_j}\le\sum_{d\mid n}c_{j,d},\quad
 f_F(n)=\#\{a\in F:a\mid n\},\quad
 K=\sum_j\frac{C_j\eta_j^{-\alpha_j}}{2^{\alpha_j}-1}<\infty,
 \quad C_j=\sum_d\frac{c_{j,d}}d.$$ Define the mixed class $$\mathcal H=\{A:A\subseteq E\cup V\text{ for some }E\in\mathcal W,\ V\in\mathcal V\}.$$ Two results from the supplied, already accepted research are inputs, rather than new assertions of this return.

#### Existing input I: synchronisation.

The weighted/cover mixed theorem, including its freedom to impose an extra fixed divisor, proves $\mathcal H\subseteq\mathcal R$. Its finite estimate is $$\frac1M\sum_{j=R}^{R+M-1}\frac1{2^j}\sum_{m=1}^{2^j}
 \frac{B^{Lm\bmod d}}{B^d-1}
 \le\frac{1+4L/M}{d(B-1)},\qquad 1<B\le2.$$ The extra divisor is absorbed in the frozen prefix modulus in the proofs of the weighted and mixed estimates. Exact source: `MixedSupportSynchronisation.md`, Sections 3--5 in the r6 packet [1].

#### Existing input II: logarithmic cover obstruction.

Every cover of cost $K$ as in (2) satisfies, for finite $F$ in its host, $$\tag{3}
 K\ge \mathbb E_F\Psi(f_F)\ge e\,\mathbb E_F\log^+ f_F,
 \qquad
 \Psi(t)=\inf_{0<\alpha\le1}\frac{t^\alpha}{2^\alpha-1}\quad(t\ge1),
 \quad\Psi(0)=0.$$ Here $\mathbb E_F$ is uniform averaging modulo $\mathop{\mathrm{lcm}}(F)$, and $\log^+t=\log\max(1,t)$. Exact source: `CoverFirstLogarithmicMoment.md`, Section B.1 [2]. In particular, $$\tag{4}
 \mathcal L(F):=\mathbb E_F\log(1+f_F)\le\log2+K/e.$$ The last inequality follows from $\log(1+t)\le\log2+\log^+t$.

For clarity, $\mathcal H$ is an ideal under finite unions. Increasing $P$ decreases each weighted summand; for integer $h\ge1$, $h/(2^h-1)$ decreases with $h$. Two cover families can be interleaved, halving their $\eta$-weights; each cost increases by at most $2^{\alpha_j}\le2$. Both classes are hereditary and contain finite sets. These facts establish finite-union closure of $\mathcal H$ directly from its definition.

# A tail budget and countable gluing

**Lemma 2.1** (tail stability). *If $R\ge N\ge1$ and $S\subseteq\{a>R\}$, then $$\tag{5}
 \Delta_{2,S}(N)=(2^N-1)X_S(2)\le 2^{N+1-R}.$$ More generally, for $B\subseteq A$, $$\tag{6}
 \Delta_{2,A}(N)\le\Delta_{2,B}(N)+(2^N-1)X_{A\setminus B}(2).$$ If $A$ and $B$ agree on $[1,R]$, then $|\Delta_{2,A}(N)-\Delta_{2,B}(N)|\le2^{N+1-R}$ whenever $R\ge N$.*

*Proof.* For $a>R\ge N$ the residue is $N$. Also $1/(2^a-1)\le2^{1-a}$ and $\sum_{a>R}2^{1-a}=2^{1-R}$, proving (5). For arbitrary $a$, $N\bmod a\le N$, proving (6). For the last assertion sum over the symmetric difference and apply (5). ◻

**Proposition 2.2** (quantitative gluing criterion). *Let $B_j\subseteq A$. Suppose $N_j\to\infty$, every fixed positive integer divides $N_j$ eventually, and $$\Delta_{2,B_j}(N_j)\to0,\qquad
 2^{N_j}X_{A\setminus B_j}(2)\to0.$$ Then $A\in\mathcal R$. It suffices, for the second condition, that $A\setminus B_j\subseteq(R_j,\infty)$ and $R_j-N_j\to\infty$.*

*Proof.* Apply (6), or (5) for the sufficient condition. The divisibility and growth assumptions give every quantifier in Definition 1.1. ◻

The product in this statement is the relevant trade-off: at the chosen return time, the remaining geometric mass is amplified by at most $2^{N_j}$. A separate return theorem for each component contains no bound on that product.

**Theorem 2.3** (delayed countable gluing). *Let $E_1,E_2,\ldots$ belong to $\mathcal H$. There exist increasing integers $s_i\ge0$ such that $$A=\bigcup_{i\ge1}\bigl(E_i\cap(s_i,\infty)\bigr)\in\mathcal R.$$ Thus $A$ contains all but finitely many elements of each $E_i$, and every infinite subset of $A$ gives an irrational subseries at every integer base. The same conclusion holds for any sequence whose finite unions belong to $\mathcal R$.*

*Proof.* Set $s_1=0$. Having chosen $s_1,\ldots,s_j$, let $B_j=\bigcup_{i\le j}(E_i\cap(s_i,\infty))$. Finite-union closure and input I give $B_j\in\mathcal R$. Choose $N_j>N_{j-1}$, $N_j\ge j$, divisible by $j!$, with $$\Delta_{2,B_j}(N_j)<2^{-j-2}.$$ Set $$s_{j+1}=\max(s_j+1,N_j+j+3).$$ All components introduced after stage $j$ lie above $s_{j+1}$. Hence $$\Delta_{2,A}(N_j)
 \le\Delta_{2,B_j}(N_j)+2^{N_j+1-s_{j+1}}
 <2^{-j-1}.$$ Since every fixed $L$ divides $j!$ eventually, $A\in\mathcal R$. The proof of the final assertion is identical, using heredity of $\mathcal R$ for the finite truncations. Apply Lemma 1.2. ◻

The theorem constructs a host after the components are supplied. It does not assert that their original untruncated union has small displacements. Only finite pieces of each component are removed, but their sizes are chosen in response to the actual return times.

# A logarithmic obstruction stable under deletion

The next lemma makes it possible to rule out *every* mixed decomposition of the host built below.

**Lemma 3.1** (reciprocal-summable erasure). *Let $F$ be finite and $D\subseteq\mathbb N$. Then $$\tag{7}
 \mathcal L(F)\le\sum_{a\in F\cap D}\frac1a+\mathcal L(F\setminus D).$$ Consequently, if $\sup_{F\subseteq S,\ F\text{ finite}}\mathcal L(F)=\infty$ and $\sum_{a\in D}1/a<\infty$, then $$\sup_{F\subseteq S\setminus D,\ F\text{ finite}}\mathcal L(F)=\infty.$$*

*Proof.* Write $f_F=f_{F\cap D}+f_{F\setminus D}$. For $u,v\ge0$, $$\log(1+u+v)\le\log(1+u)+\log(1+v)\le u+\log(1+v).$$ Average over a common period. The mean of $\mathbf1_{a\mid n}$ is $1/a$, and the mean of each periodic marginal is unchanged by using that common period. This gives (7). A bounded first term cannot eliminate an unbounded family of left-hand sides. ◻

Thus a weighted component which is forced to pay ordinary reciprocal mass on a subfamily cannot remove its entire logarithmic obstruction at finite cost.

# A support beyond the entire finite mixed class

Choose distinct prime centres $q_i\ge2^{i+2}$. Their reciprocal sum converges. The remaining primes have divergent reciprocal sum. Enumerate pairs $(i,k)\in\mathbb N^2$ diagonally and successively choose disjoint finite blocks $P_{i,k}$ of remaining primes, none equal to any centre, satisfying $$\tag{8}
 \frac{q_i^k}{4}\le S_{i,k}:=\sum_{p\in P_{i,k}}\frac1p
 \le\frac{q_i^k}{4}+1.$$ Each finite stage is possible because only finitely many additional primes have been used, and crossing a target overshoots it by less than one. Put $$M_{i,k}=\prod_{p\in P_{i,k}}p,\qquad
 F_{i,k}=\{q_i^k d:d\mid M_{i,k}\},\qquad
 E_i=\bigcup_{k\ge1}F_{i,k}.$$

**Lemma 4.1**. *For every $i$, $E_i\in\mathcal W$. After deleting any finite collection of its frames, its finite subsets still have unbounded $\mathcal L$.*

*Proof.* Every exponent in $F_{i,k}$ has $q_i$-part $q_i^k$, so $$\begin{aligned}
 W_{\{q_i\}}(E_i)
 &=\sum_{k\ge1}\frac{\prod_{p\in P_{i,k}}(1+1/p)}{2^{q_i^k}-1}\\
 &\le2e\sum_{k\ge1}
 \exp\bigl(- (\log2-1/4)q_i^k\bigr)<\infty.
\end{aligned}$$ This proves the first assertion. For the second fix $k_0$ beyond the deleted frames and take $F=\bigcup_{k=k_0}^mF_{i,k}$, with $m>k_0$. Modulo $\mathop{\mathrm{lcm}}(F)$, the disjoint events $v_{q_i}(n)=k$ for $k_0\le k<m$ have densities $(q_i-1)/q_i^{k+1}$. On each such event, the $k$th frame contributes $$f_F(n)\ge2^{Z_{i,k}(n)},\qquad
 Z_{i,k}(n)=\sum_{p\in P_{i,k}}\mathbf1_{p\mid n}.$$ The Chinese remainder theorem gives $\mathbb E(8), $$\tag{9}
 \mathcal L(F)\ge\sum_{k=k_0}^{m-1}
 \frac{q_i-1}{q_i^{k+1}}S_{i,k}\log2
 \ge(m-k_0)\frac{q_i-1}{4q_i}\log2\longrightarrow\infty.$$ ◻

**Proposition 4.2** (a missing centre cannot be supplied at finite mixed cost). *Fix $i$ and a finite prime set $P$ with $q_i\notin P$. No cofinite subset of $E_i$ is contained in $U\cup V$ with $W_P(U)<\infty$ and $V\in\mathcal V$.*

*Proof.* Each prime of $P$ appears in at most one block $P_{i,k}$. Discard all frames meeting $P$, and all frames containing the finitely many omitted elements. The remaining tail $S$ of $E_i$ is coprime to every prime of $P$ and has unbounded finite logarithmic moments by Lemma 4.1. For $a\in U\cap S$, $h_P(a)=1$, whence $$\sum_{a\in U\cap S}\frac1a\le W_P(U)<\infty.$$ The erasure lemma implies unbounded logarithmic moments on $S\setminus U$. But $S\setminus U\subseteq V$, contradicting (4) for any finite-cost cover of $V$. ◻

**Theorem 4.3** (strict enlargement beyond finite mixing). *There exists a support $A\in\mathcal R\setminus\mathcal H$ with $\sum_{a\in A}1/a=\infty$ such that $$\text{for every infinite }B\subseteq A\text{ and integer }b\ge2,
 \qquad X_B(b)\notin\mathbb Q.$$ More specifically, apply Theorem 2.3 to the above $E_i$ and take its resulting host $A$.*

*Proof.* The gluing theorem gives $A\in\mathcal R$ and includes a cofinite subset of every $E_i$. If $A\in\mathcal H$, choose $A\subseteq U\cup V$ with $W_P(U)<\infty$ for one finite $P$, and $V\in\mathcal V$. Choose $q_i\notin P$. Proposition 4.2 gives a contradiction. Unbounded $\mathcal L$ on a cofinite subset of $E_i$ also implies divergent reciprocal mass, since $\log(1+f_F)\le f_F$ and $\mathbb E_Ff_F=\sum_{a\in F}1/a$. Hereditary all-base irrationality follows from Lemma 1.2. ◻

This excludes all choices of finite prime sets, all positive covers, and all splittings between them. Merely checking that a displayed construction fails one chosen cover would not prove Theorem 4.3. The theorem makes no claim that every previously published irrationality theorem has been excluded.

**Corollary 4.4** (robustness under the prime-power branch). *The host $A$ from Theorem 4.3 is not contained in $U\cup V\cup D$, where $U\in\mathcal W$, $V\in\mathcal V$, and $D$ is any finite union of fixed dilates of the prime powers, with finite modifications allowed.*

*Proof.* For a fixed centre $q_i$ and integer $m\ge1$, the set $E_i\cap\{mp^t:p\text{ prime},\ t\ge1\}$ has summable reciprocal mass. If $p\ne q_i$, the equality $q_i^k d=mp^t$ forces $k=v_{q_i}(m)$, so these intersections lie in one finite frame (or are empty). The $p=q_i$ part has reciprocal sum at most $\sum_{t\ge1}1/(mq_i^t)<\infty$. Finite unions and finite modifications preserve summability. Now choose $q_i$ absent from the prime set used for $U$, and repeat Proposition 4.2, erasing both $U\cap E_i$ and $D\cap E_i$. Lemma 3.1 still leaves an unbounded logarithmic obstruction inside $V$, a contradiction. ◻

This comparison concerns the explicitly stated support families. It does not claim exclusion of every analytic theorem in the literature.

*Remark 11* (comparison with the existing lcm-gap criterion). The constructed host also fails the prefix-lcm gap condition in `irrational_erdosSum_of_lcm_gap` [6]. It contains all sufficiently large powers of a centre $q$, and one selected $q^t p$ with $p>q$ prime. For a sufficiently late exponent $a_j$ in its increasing enumeration, choose the largest $q^k<a_j$. The prefix contains both $q^k$ and $q^t p$, so its lcm is at least $pq^k>q^{k+1}\ge a_j$. Thus the natural-number difference between the next exponent and the prefix lcm is eventually zero. This excludes that precise criterion, including a cofinal positive-gap variant, rather than all lcm-based methods.

# The exact coprime trace and an actual synchronisation failure

**Proposition 5.1** (coprime trace). *If $C\subseteq\{2,3,\ldots\}$ is pairwise coprime, then $$\mathcal H\cap2^C
 =\left\{A\subseteq C:\sum_{a\in A}\frac1a<\infty\right\}.$$*

*Proof.* For any finite $P$, at most $|P|$ members of $C$ have a prime factor in $P$. A subset of $C$ in $\mathcal W$ therefore has summable reciprocal mass. For $\mathcal V$, suppose instead that finite $F\subseteq C$ have sums $S_F=\sum_{a\in F}1/a$ tending to infinity. Under uniform averaging modulo $\mathop{\mathrm{lcm}}(F)$, the indicators $\mathbf1_{a\mid n}$ are independent by the Chinese remainder theorem. Their sum $Z=f_F$ has mean $S_F$ and variance at most $S_F$. Chebyshev's inequality gives $$\mathbb E\log^+Z\ge(1-4/S_F)\log(S_F/2)\longrightarrow\infty,$$ where the bound is used only for $S_F>4$. This contradicts (3). An $\mathcal H$ decomposition splits $A$ into two reciprocal-summable subsets, proving one inclusion. Conversely, $h/(2^h-1)\le1$ gives $W_P(A)\le\sum_{a\in A}1/a$ for any fixed nonempty $P$. ◻

**Lemma 5.2** (prime-core displacement). *For the full prime set $\mathbb P$, $$\Delta_{2,\mathbb P}(N)>\frac13\qquad(N\ge1).$$*

*Proof.* The Lambert coefficient is $\omega(n)$, the number of distinct prime factors, so nonnegative interchange gives $$\Delta_{2,\mathbb P}(N)=\sum_{r\ge1}\omega(N+r)2^{-r}-X_{\mathbb P}(2).$$ Since $N+r\ge2$, the first term is at least one. Also $$X_{\mathbb P}(2)\le\sum_{a\ge2}\frac1{2^a-1}
 <\frac43\sum_{a\ge2}2^{-a}=\frac23.$$ ◻

**Theorem 5.3** (actual two-colour counterexample). *There is a partition $\mathbb P=A_0\sqcup A_1$ such that $$A_0,A_1\in\mathcal R,\qquad
 \sum_{p\in A_0}\frac1p=\sum_{p\in A_1}\frac1p=\infty,
 \qquad
 \Delta_{2,A_0}(N)+\Delta_{2,A_1}(N)>\frac13\quad(N\ge1).$$ Any prescribed finite colouring of primes can be extended to such a partition. In particular, $\mathcal R$ is not closed under finite unions, and neither colour class is in $\mathcal H$.*

*Proof.* Start beyond the prescribed finite colouring, with all primes below a finite cutoff coloured. At stage $k$, use colour $k\bmod2$ as the active colour. Take a finite consecutive block of previously uncoloured primes with reciprocal sum at least one, and give the whole block the active colour. This is possible by divergence of the prime reciprocal sum. Let $F_k$ be all primes assigned that colour so far. Choose $N_k$ larger than the current cutoff and the preceding $N$, divisible by $k!\mathop{\mathrm{lcm}}(F_k)$. Put $$R_k=N_k+k+3.$$ Assign all still uncoloured primes up to $R_k$ the other colour. All future assignments occur above $R_k$. For the final active colour class, its elements at most $R_k$ are exactly $F_k$, whose displacement at $N_k$ is zero. Lemma 2.1 gives $$\Delta_{2,A_{k\bmod2}}(N_k)\le2^{N_k+1-R_k}=2^{-k-2}.$$ Each colour is active infinitely often, and $k!$ eventually contains every prescribed divisor. Thus both colours belong to $\mathcal R$. Each receives infinitely many disjoint blocks of reciprocal mass at least one, so both reciprocal sums diverge. The cutoffs tend to infinity and all primes are eventually coloured. Lemma 5.2 and additivity give the uniform gap for their union. Proposition 5.1 excludes both colour classes from $\mathcal H$. ◻

The counterexample concerns the small-displacement mechanism, not rationality of the union. The full prime-support series is irrational by Tao--Teräväinen, Theorem 1.3 [4]. Our construction proves that separate actual arithmetic return statements, even with every prescribed modulus allowed, do not supply synchronisation.

# Baire category and its arithmetic scope

**Proposition 6.1**. *For every infinite $S\subseteq\mathbb N$, the class $\mathcal R\cap2^S$ is a dense $G_\delta$ in the product space $2^S$. In particular, a residual set of hosts in $2^S$ has irrational subseries for *every* infinite thinning, simultaneously at every integer base.*

*Proof.* Lemma 2.1 makes $A\mapsto\Delta_{2,A}(N)$ continuous for each fixed $N$. For positive integers $k,L,M$ define $$U_{k,L,M}=\bigcup_{\substack{N\ge M\\L\mid N}}
 \{A\subseteq S:\Delta_{2,A}(N)<1/k\}.$$ This is open. Given a basic cylinder, let $F$ be exactly its finitely many prescribed included coordinates and exclude every other coordinate. Choose $N\ge M$ divisible by $L\mathop{\mathrm{lcm}}(F)$, taking $\mathop{\mathrm{lcm}}(\varnothing)=1$. Then $\Delta_{2,F}(N)=0$, so the cylinder meets $U_{k,L,M}$. Thus these sets are dense and $\mathcal R\cap2^S=\bigcap_{k,L,M\ge1}U_{k,L,M}$. The Baire category theorem proves density. Lemma 1.2 gives the final statement. ◻

**Corollary 6.2**. *In $2^{\mathbb P}$, $\mathcal H$ is meagre and $\mathcal R\setminus\mathcal H$ is residual. The partitions in Theorem 5.3 are themselves residual in the space of two-colourings of the primes.*

*Proof.* By Proposition 5.1, $\mathcal H\cap2^{\mathbb P}$ is the prime reciprocal-summable ideal. It is the union over positive integers $m$ of the closed sets $$C_m=\{A\subseteq\mathbb P:\sum_{p\in A}1/p\le m\}.$$ Each has empty interior, since arbitrarily large finite reciprocal mass can be included beyond any fixed cylinder. This proves meagreness. Complementation $A\mapsto\mathbb P\setminus A$ is a homeomorphism, so the two return conditions are simultaneously residual. Divergence of the reciprocal sums of both colours is also residual by the same finite-extension argument. The prime-core gap holds for every colouring. ◻

Kovač--Tao, Propositions 1 and 2 in arXiv v3, already give probabilistic and category-generic irrationality of individual subseries 6.1 is a direct Baire argument. Even hereditary generic irrationality follows from strict-tail injectivity: there are at most countably many infinite rational-valued supports across all integer bases, and the hosts containing any one fixed infinite support form a closed nowhere dense upper cone. Avoid their countable union. The additional conclusion proved here is return-admissibility itself, including prescribed divisibility and explicit construction of witnesses; no novelty is claimed for the generic-irrationality principle. A residual set need not have full measure for a specified random model. None of these category conclusions decides a fixed rational target.

# What this changes, and the remaining questions

There are two distinct choices. For two *fixed* supports, the existing mixed theorem synchronises their estimates on one finite averaging distribution. For a *constructed* countable union, Theorem 2.3 delays new exponents until their total future contribution is small at the chosen old return. Theorem 5.3 shows that the first operation cannot be inferred from separate membership in $\mathcal R$.

Theorem 4.3 extends the sufficient classes beyond their entire finite mixed ideal. Proposition 4.2 identifies the obstruction: a fixed finite prime set misses one centre, and on its frames the weighted component pays ordinary reciprocal mass. Erasing that much cannot suppress an unbounded logarithmic moment.

The actual greedy support for $x=1/2$ or $1/21$ cannot be altered to fit the delayed construction. With the notation of the current short note, its unresolved obligation remains $$\forall K\ \exists N\ge K:\qquad
 c_x(N+1)\ge Q_N+\beta_N.$$ The new results do not establish this inequality for either actual selector. Neither a residual family of hosts nor a freely constructed host supplies information about that distinguished one.

Three natural follow-up problems now have exact boundaries. First, for a prescribed untruncated countable union, seek a sufficient bound on $2^{N_j}X_{A\setminus B_j}(2)$ at compatible return times. Theorem 5.3 excludes any conclusion based only on separate return statements. Second, determine when the logarithmic cover obstruction admits a converse, respecting positivity of the divisor majorants; the exact cube calculation alone does not provide one. Third, in the prime-containing regime, seek an arithmetic functional other than small positive displacement, since Lemma 5.2 excludes that mechanism altogether.

A concrete connection with the sibling #251 programme is its capacity telescope and variable-alphabet tail filling [5]: both constructions freeze finite constraints and reserve a quantitative tail budget. There the digits remain free enough to enforce a rational sum. Here the return construction preserves a fixed rational lattice. This is a transfer of construction principles, not an implication between the original Erdős problems.

#### Evidence boundary.

All the new arguments above are ordinary mathematical proofs. The two existing inputs are explicitly stated and tied to the supplied source. Exact finite tests accompany the return; they do not certify the infinite constructions. No Lean or Comparator build was run.


# References

[1] Supplied r6 source, `ErdosProblems/Erdos257/MixedSupportSynchronisation.md`, Sections 3–5. Accepted ordinary mixed and prescribed-divisor estimates.

[2] Supplied r6 source, `ErdosProblems/Erdos257/CoverFirstLogarithmicMoment.md`, Section B.1. Accepted ordinary cover-independent logarithmic obstruction.

[3] Vjekoslav Kovač and Terence Tao, *On several irrationality problems for Ahmes series*, arXiv:2406.17593v3, Propositions 1 and 2. https://arxiv.org/abs/2406.17593

[4] Terence Tao and Joni Teräväinen, *Quantitative correlations and some problems on prime factors of consecutive integers*, arXiv:2512.01739v2, Theorem 1.3. https://arxiv.org/abs/2512.01739

[5] `ErdosProblems/Erdos251/SparseRationalisationCore.lean`, public commit `32545d77c4b5cfd72ebd36c8dcd2418bf7cc4d31`: `capacity_telescope`, `variableDigit_spec`, `greedyRemainder_bounds`. Its finite/capacity interfaces are separate from the full ordinary construction.

[6] `Erdos249257/CertificateKernel.lean`, same public pin, `irrational_erdosSum_of_lcm_gap`. Its hypothesis is divergence to infinity of the natural-number difference between the next exponent and the lcm of all predecessors.
