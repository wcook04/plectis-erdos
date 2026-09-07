# Sharp sparsity under arithmetic constraints
## A residue-feedback construction for dyadic rationalisation

Research memorandum, 7 September 2026

**Evidence.** The theorems below are ordinary mathematical arguments developed in this review. The complete sparse schedules, entropy calculation and dimension lower bound have not been checked in Lean or independently reviewed. The accompanying Lean implementation concerns the local interval selector and an abstract infinite-sum endpoint; it is uncompiled. No assertion here proves irrationality of the actual prime series. Priority for the construction and the sharp joint theorem has not been established by the literature search.

### 1. The joint theorem

All logarithms without a subscript are natural. Let $\alpha>\beta\ge0$. Let $M:\mathbb N\to\mathbb N_{>0}$ satisfy
\[
 M(n)\mid M(n+1),\qquad
 \frac{\log M(n)}{\log\log(n+3)}\longrightarrow\beta.
 \tag{1}
\]
Set $A(n)=\lfloor(\log(n+3))^\alpha\rfloor$. For a nonnegative integer correction $e=(e_n)$, write
\[
 C_e(n)=\sum_{i<n}e_i,\qquad
 v(e)=\sum_{n\ge0}\frac{e_n}{2^{n+1}}.
\]
The series defining $v(e)$ converges whenever $e_n\le A(n)$.

For $\delta\ge0$, let $\mathcal E_{\alpha,M}(\delta)$ be the set of values $v(e)$ of corrections satisfying, for every $n$,
\[
 0\le e_n\le A(n),\qquad M(n)\mid e_n,\qquad M(n)\mid C_e(n),
 \tag{2}
\]
and
\[
 \limsup_{N\to\infty}\frac{\log\log N}{N}
       \#\{n<N:e_n\ne0\}\le\delta.
 \tag{3}
\]
The convention in (3) only concerns sufficiently large $N$.

**Theorem 1 (sharp sparsity with cumulative congruences).** Under (1),
\[
 \boxed{\displaystyle
 \dim_H\mathcal E_{\alpha,M}(\delta)
 =\min\left\{1,\frac{(\alpha-\beta)\delta}{\log2}\right\}.}
 \tag{4}
\]
At the critical value
\[
 \delta_* =\frac{\log2}{\alpha-\beta},
 \tag{5}
\]
the set contains a nondegenerate closed interval lying strictly above zero. More precisely, for every cutoff $K$ there is a predetermined set $S\subseteq[K,\infty)$ and a nondegenerate interval $J\subset(0,\infty)$ such that every $y\in J$ is $v(e)$ for some correction satisfying (2), supported on $S$, and
\[
 \#(S\cap[0,N))=(\delta_*+o(1))\frac N{\log\log N}.
 \tag{6}
\]
The set $S$ has upper Banach density zero.

**Corollary 2 (a sharp universal-versus-exceptional transition).** Let $\mathcal R_{\alpha,M}(\delta)$ be the set of real $x$ for which $x+v(e)$ is rational for an allowed correction. Then
\[
 \dim_H\mathcal R_{\alpha,M}(\delta)
 =\min\left\{1,\frac{(\alpha-\beta)\delta}{\log2}\right\}.
 \tag{7}
\]
If $\delta<\delta_*$, this set has Lebesgue measure zero. If $\delta\ge\delta_*$, it is all of $\mathbb R$. In the latter case the correction can vanish before any prescribed cutoff.

Indeed, $\mathcal R=\bigcup_{q\in\mathbb Q}(q-\mathcal E)$. Translation invariance and countable stability of Hausdorff dimension give (7); the union contains $-\mathcal E$. At and above the threshold, choose a rational in $x+J$. Below the threshold, dimension is strictly smaller than one. The statement is about a uniform class of inputs, not a lower bound on the number of modifications needed for any one particular prime series.

The cumulative congruence requirement in (2) does not increase the leading sparsity cost beyond the cost of restricting the coefficient alphabet to multiples of $M(n)$. This is the additional conclusion not contained in the round-5 upper bound.

### 2. A common interval for every residue state

The preceding construction used two adjacent corrections with a fixed total, together with a separate congruence buffer. The following lemma allows the residue to depend on the accumulated correction, so that one site does all the work.

**Lemma 3 (residue-independent interval overlap).** Let $A_j,Q_j$ be positive integers, $w_j>0$, and suppose
\[
 A_j\ge4Q_j,\qquad \sum_j A_jw_j<\infty,
 \qquad Q_jw_j\le\sum_{i>j}(A_i-2Q_i)w_i.
 \tag{8}
\]
Define
\[
 L_j=\sum_{i\ge j}Q_iw_i,\qquad
 U_j=\sum_{i\ge j}(A_i-Q_i)w_i.
 \tag{9}
\]
At step $j$, allow any residue $r_j\in\{0,\ldots,Q_j-1\}$, even one selected as a function of the entire previous digit history. Every $y\in[L_0,U_0]$ has an expansion
\[
 y=\sum_jd_jw_j,\qquad 0\le d_j\le A_j,
 \qquad d_j\equiv r_j\pmod{Q_j},
 \tag{10}
\]
consistent with that history-dependent selection rule.

*Proof.* Fix a current history and therefore its current residue $r$. The allowed digits are
\[
 r,\ r+Q_j,\ldots,r+Q_j\left\lfloor\frac{A_j-r}{Q_j}\right\rfloor.
\]
For each digit $d$, attach the continuation interval
\[
 dw_j+[L_{j+1},U_{j+1}].
\]
Their consecutive left endpoints differ by $Q_jw_j$. Their common length is $U_{j+1}-L_{j+1}$, which is at least that difference by (8). Thus their union is an interval. Its first left endpoint is at most $Q_jw_j+L_{j+1}=L_j$. Its last right endpoint is at least $(A_j-Q_j)w_j+U_{j+1}=U_j$, because the largest permissible digit exceeds $A_j-Q_j$.

Consequently every current remainder $y_j\in[L_j,U_j]$ admits a digit for which $y_{j+1}=y_j-d_jw_j\in[L_{j+1},U_{j+1}]$. Inductively make these choices. The finite identity
\[
 \sum_{j<t}d_jw_j=y-y_t
\]
and $0\le y_t\le U_t\to0$ prove (10). No independence assumption on the residues was used. The proof retains the complete infinite remainder. $\square$

**A concrete selector.** For one step with residue $r$, let
\[
 D=\left\lfloor\frac{A-r}{Q}\right\rfloor,
 \quad z=x-rw-L',
 \quad k=\min\left\{D,\left\lfloor\frac z{Qw}\right\rfloor\right\},
 \quad d=r+Qk.
 \tag{11}
\]
On the common interval $Qw+L'\le x\le(A-Q)w+U'$ and under $U'-L'\ge Qw$, $z\ge0$, $0\le k\le D$, and $L'\le x-dw\le U'$. Thus no search over an infinite set is hidden in the one-step proof.

The interval-overlap mechanism is a state-dependent version of the classical term-versus-tail argument for achievement sets. The classical overlap principle is not new. The feature used here is a common continuation interval for every residue state, which permits arithmetic feedback without separate repair sites.

### 3. The critical schedule

Choose $n_0\ge K$ so large that, for every $n\ge n_0$,
\[
 A(n)\ge4M(2n),\qquad
 1\le\left\lfloor\log_2\frac{A(n)}{2M(2n)}\right\rfloor<n.
 \tag{12}
\]
These eventual inequalities follow from (1) and $\alpha>\beta$. Define
\[
 \ell_j=\left\lfloor\log_2\frac{A(n_j)}{2M(2n_j)}\right\rfloor,
 \qquad n_{j+1}=n_j+\ell_j,
 \tag{13}
\]
\[
 A_j=A(n_j),\qquad Q_j=M(n_{j+1}),\qquad w_j=2^{-n_j-1}.
 \tag{14}
\]
This schedule is chosen before the target real number or the input sequence. Looking ahead to $M(n_{j+1})$ is what will ensure the cumulative congruence at every intermediate index.

Since $n_{j+1}<2n_j$, (12) gives $A_j\ge4Q_j$. The function $A$ is nondecreasing. Therefore
\[
\begin{aligned}
 (A_{j+1}-2Q_{j+1})w_{j+1}
 &\ge \tfrac12 A_{j+1}2^{-\ell_j}w_j\\
 &\ge \tfrac12 A_j2^{-\ell_j}w_j\\
 &\ge M(2n_j)w_j\ge Q_jw_j.
\end{aligned}
 \tag{15}
\]
In particular the very next permitted site already supplies the overlap required in (8). Summability follows by comparison with $\sum_n(\log(n+3))^\alpha2^{-n-1}$.

Apply Lemma 3 with the residue rule
\[
 r_j\equiv-C_j\pmod{Q_j},\qquad
 0\le r_j<Q_j,\qquad C_j=\sum_{i<j}d_i.
 \tag{16}
\]
Then $Q_j\mid C_j+d_j=C_{j+1}$.

Put $e_{n_j}=d_j$ and $e_n=0$ elsewhere. At $n_j$, the incoming sum $C_j$ is divisible by $M(n_j)$: this is automatic at $j=0$, and thereafter follows from $Q_{j-1}=M(n_j)$. The outgoing sum is divisible by $Q_j=M(n_{j+1})$. Subtraction shows $M(n_j)\mid d_j$. For every $n_j<n\le n_{j+1}$, the cumulative sum is the same outgoing sum and is divisible by $M(n)$, since $M(n)\mid M(n_{j+1})$. Before $n_0$, all corrections and cumulative sums vanish. This proves both divisibilities in (2) at every index, not only at stage boundaries.

The interval $[L_0,U_0]$ is nondegenerate and lies above zero: $L_0>0$ and $U_0-L_0=\sum_j(A_j-2Q_j)w_j>0$. Its points satisfy (10), so this is the interval $J$ in Theorem 1.

### 4. Counting the sites

Equation (1) and $\log A(n)=\alpha\log\log n+o(1)$ imply
\[
 \ell_j=\left(\frac{\alpha-\beta}{\log2}+o(1)\right)\log\log n_j.
 \tag{17}
\]
To deduce (6) without suppressing an endpoint error, restrict first to sites in $[\sqrt N,N]$. Uniformly there, $\log\log n_j=(1+o(1))\log\log N$. The sum of their spacings is $N-\sqrt N+O(\log\log N)$, and each spacing is given by (17). The omitted prefix has at most $\sqrt N+1=o(N/\log\log N)$ sites. Division gives (6). Subtracting the asymptotics at $2X$ and $X$ gives
\[
 \#(S\cap[X,2X))=(\delta_*+o(1))\frac X{\log\log X}.
 \tag{18}
\]
Since the gaps $n_{j+1}-n_j$ tend to infinity, $S$ has upper Banach density zero. Explicitly, beyond a finite initial set its points are separated by any prescribed $H$. An interval of length $R$ therefore contains at most $R/H+1$ tail points plus the fixed initial number. Divide by $R$, take the supremum over locations, let $R\to\infty$, then let $H\to\infty$.

### 5. The entropy upper bound, allowing adaptive supports

Write $\gamma=\alpha-\beta>0$. For every $\eta>0$, the number of possible nonzero digits at index $n$, under $e_n\le A(n)$ and $M(n)\mid e_n$, is at most
\[
 C_\eta(\log(n+3))^{\gamma+\eta}.
 \tag{19}
\]
The cumulative congruence only reduces this number.

Fix $\delta'>\delta$ and a starting threshold $N_0$. Consider corrections with at most
\[
 k_N=\left\lfloor\frac{\delta'N}{\log\log N}\right\rfloor
\]
nonzero entries among their first $N$ entries, for every $N\ge N_0$. For large $N$, $k_N\le N/2$, and the number of possible prefixes, including all choices of support, is at most
\[
 (k_N+1)\left(\frac{eN}{k_N}\right)^{k_N}
 \left[C_\eta(\log(N+3))^{\gamma+\eta}\right]^{k_N}.
 \tag{20}
\]
Its logarithm is at most $(\gamma+\eta)\delta'N+o(N)$. The term choosing the locations contributes only $o(N)$.

Every continuation of one prefix lies in an interval of diameter
\[
 \sum_{n\ge N}A(n)2^{-n-1}
 =O_\alpha((\log(N+3))^\alpha2^{-N}).
 \tag{21}
\]
For completeness, the bound follows from $\log(N+r+3)\le\log(N+3)+r$ and summability of $r^\alpha2^{-r}$. Equations (20)--(21) give zero $s$-dimensional Hausdorff measure whenever $s\log2>(\gamma+\eta)\delta'$. Taking the countable union over $N_0$, then letting $\eta\downarrow0$ and $\delta'\downarrow\delta$, proves
\[
 \dim_H\mathcal E_{\alpha,M}(\delta)
 \le \min\{1,\gamma\delta/\log2\}.
 \tag{22}
\]
This includes supports selected separately for each target; it is not a fixed-support counting argument. In particular, no interval can be encoded with a smaller leading sparsity constant than (5), even if the cumulative condition is omitted.

### 6. The dimension lower bound below the threshold

It remains to prove equality in (22) for $0<\delta<\delta_*$. Choose sufficiently large $n_0$ and use the more widely spaced sites
\[
 n_{j+1}=n_j+\left\lfloor\delta^{-1}\log\log n_j\right\rfloor,
 \qquad Q_j=M(n_{j+1}),\quad A_j=A(n_j),\quad w_j=2^{-n_j-1}.
 \tag{23}
\]
At every node of the digit tree, permit **all** digits in $[0,A_j]$ congruent to the residue in (16). There is no interval-filling claim for this schedule. The congruence induction in Section 3 still applies verbatim. The permitted support has asymptotic count $\delta N/\log\log N$.

The number $B_j$ of children at a node is one of
\[
 \left\lfloor\frac{A_j}{Q_j}\right\rfloor,
 \qquad
 \left\lfloor\frac{A_j}{Q_j}\right\rfloor+1.
\]
Uniformly over histories,
\[
 \log B_j=(\gamma+o(1))\log\log n_j.
 \tag{24}
\]
Let $R_j=\sum_{i>j}A_iw_i$. The rough full-tail bound (21) gives
\[
 \frac{R_j}{Q_jw_j}
 \le(\log n_j)^{\gamma-\delta^{-1}\log2+o(1)}\longrightarrow0,
 \tag{25}
\]
because $\delta<\delta_*$. Thus two paths first differing at site $i$ have distinct values, separated by at least $Q_iw_i-R_i\ge Q_iw_i/2$, after increasing $n_0$ if necessary. Also $Q_{j+1}w_{j+1}/(Q_jw_j)\to0$: by (1) the logarithm of the modulus ratio is $o(\log\log n_j)$, whereas the logarithm of the weight ratio is $-(\delta^{-1}\log2+o(1))\log\log n_j$. Consequently any two distinct level-$j$ cylinders are separated by at least
\[
 s_j=\tfrac12Q_jw_j
   =\exp(-n_j\log2+o(n_j)).
 \tag{26}
\]
This is separation of their complete infinite-value sets, not just of truncated prefixes.

Give each child equal conditional probability within its node. This defines a probability measure on the compact set of infinite correction values. Equations (23)--(24) show that the mass of every level-$j$ cylinder is at most
\[
 \exp\bigl(-\gamma\delta n_j+o(n_j)\bigr).
 \tag{27}
\]
One way to check the exponent is to divide $\log B_i$ by the spacing $n_{i+1}-n_i$: the ratio tends to $\gamma\delta$, and summing spacings telescopes.

Given a small interval of length $r$, choose $j$ with $s_j\le r<s_{j-1}$. It meets at most two level-$(j-1)$ cylinders, so its measure is bounded by twice (27) at $j-1$. Since $n_j/n_{j-1}\to1$, for every $s<\gamma\delta/\log2$ this is at most $C_sr^s$, uniformly for small $r$. The elementary mass-distribution principle now gives dimension at least $s$: any interval cover has $\sum |I|^s\ge1/C_s$. Let $s\uparrow\gamma\delta/\log2$.

For $\delta=0$, the zero correction supplies a nonempty set and (22) gives dimension zero. For $\delta\ge\delta_*$, the interval construction gives dimension one. This completes Theorem 1. $\square$

### 7. Preserving every fixed modulus and applying the result to prime gaps

For a concrete chain with $\beta=0$, take
\[
 M(n)=\operatorname{lcm}\left(1,\ldots,
       \max\{1,\lfloor\sqrt{\log\log(n+3)}\rfloor\}\right).
 \tag{28}
\]
It satisfies (1), since $\log\operatorname{lcm}(1,\ldots,k)\le\log(k!)\le k\log k=o(\log\log n)$. Every fixed integer eventually divides $M(n)$.

For a prescribed $\beta>0$, multiply (28) by
\[
 2^{\lfloor\beta\log_2\log(n+3)\rfloor}.
 \tag{29}
\]
This remains a divisibility chain, and its logarithm is $(\beta+o(1))\log\log n$. Thus both fixed congruences and a growing power-of-two congruence can be imposed in the theorem.

Take $a_n=g_n=p_{n+1}-p_n$ and choose a rational in $\mathscr S(g)+J$. The resulting $b_n=g_n+e_n$ is positive, agrees with the prescribed finite prime-gap prefix, and has rational dyadic sum. Put
\[
 P_n=2+\sum_{i<n}b_i=p_n+C_e(n).
\]
Then $M(n)\mid(P_n-p_n)$ and $M(n)\mid(b_n-g_n)$ for every $n$. For any $0<\alpha\le1$,
\[
 P_n-p_n\le A(n)\#(S\cap[0,n))
 =O\left(\frac{n(\log n)^\alpha}{\log\log n}\right)
 =o(n\log n).
 \tag{30}
\]
Hence $P_n\sim n\log n$, using the classical prime-number-theorem asymptotic for $p_n$. The exact Abel identity gives
\[
 \sum_{n\ge0}\frac{P_n}{2^{n+1}}
 =2+\sum_{n\ge0}\frac{b_n}{2^{n+1}}\in\mathbb Q.
 \tag{31}
\]
Neither primality of $P_n$ nor a new distribution theorem for the actual gaps is claimed.

For any bounded block test $\Phi_X:\mathbb N^m\to[-1,1]$, coupling the two words at the same starting indices gives
\[
 \left|\frac1X\sum_{X\le N<2X}
   [\Phi_X(b_N,\ldots,b_{N+m-1})-\Phi_X(g_N,\ldots,g_{N+m-1})]\right|
 \le\frac{2m}{X}\#(S\cap[X,2X+m)).
 \tag{32}
\]
Thus for $m=o(\log\log X)$ every such test has the same asymptotic average. The corresponding total-variation distance is at most $m\#(S\cap[X,2X+m))/X$, without the factor two. Tests may depend on $N$; no relative error on every small residue class follows. Rare events with counts below this error budget need not be preserved.

### 8. What this changes about the finite-dispersion programme

The current packet already contains the ordinary first-moment estimate
\[
 \sum_{X\le N<2X}T_{N+L}\ll X\log X,\qquad
 T_N=\sum_{j\ge1}g_{N+j}2^{-j},\quad L\le X.
 \tag{33}
\]
For the circular-arc deficiency $E_t(X,L,K)$, rationality with a compatible shift order forces
\[
 E_t(X,L,K)\le C_T X\log X/K.
 \tag{34}
\]
This is an occupied sufficient criterion, not a new theorem of this return.

The sharp construction preserves every bounded unnormalised test for $L=o(\log\log X)$. It also changes $E_t$ by at most the number of changed length-$L$ windows, because moving one residue observation changes the maximal arc count in that class by at most one. Conversely, obtaining $o(X)$ in (34) with a nontrivial arc requires $K\gg\log X$ and $K<2^L$, so $L$ must be at least of order $\log_2\log X$.

The matching order of these scales is explanatory, not a universal impossibility theorem for all approaches to #251. The new result optimises the information-preserving construction. It does not improve (34) or prove a lower bound for the actual-prime statistic. A rare-event argument or an exact primality constraint may use information not protected by (32).

### 9. Cheap generalisation and remaining questions

Replace $2^{-n-1}$ throughout by $b^{-n-1}$ for any fixed real $b>1$. The one-step lemma is unchanged; use $\log_b$ in the site schedule. The critical constant and dimension formula become
\[
 \delta_* =\frac{\log b}{\alpha-\beta},\qquad
 \dim_H\mathcal E=\min\{1,(\alpha-\beta)\delta/\log b\}.
\]
This concerns freely chosen coefficient corrections. It makes no assertion about the fixed divisor coefficients in a Lambert or Mersenne series.

The remaining substantive questions are now different from the round-5 constant question, which Theorem 1 answers. They include a prescribed forbidden set of correction sites, simultaneous control of more than one weighted sum, and prime-specific statistics exceeding the finite-tail error budget. For a forbidden set, having infinitely many available sites is not enough: spacing must be compatible with the remaining digit capacity. The common-interval criterion in Lemma 3 is a concrete sufficient test for a proposed schedule.

### 10. Sources and relation to the supplied work

The mathematical input from the supplied corpus is the round-5 sparse construction and its entropy upper bound in `ErdosProblems/Erdos251/SparseRationalisation.md`, the compiled variable-alphabet core in `SparseRationalisationCore.lean`, and the existing mean-tail and circular-arc laboratories. The new work replaces the pair/buffer mechanism by residue feedback, attains the entropy constant, incorporates an arithmetic alphabet cost $\beta$, and proves the subcritical dimension lower bound. No new prime-distribution input is used.

Classical context and independently checked online sources:

1. Z. Nitecki, *Subsum sets: intervals, Cantor sets, and Cantorvals*, arXiv:1106.3779v2. Theorem 4, printed p. 9, gives the classical term-versus-tail interval criterion. It does not state the residue-feedback or sharp sparse-congruence theorem above. https://arxiv.org/abs/1106.3779
2. M. B. Nathanson, *Convergent series of integers with missing digits*, arXiv:2010.06719v3, provides related variable-radix and restricted-digit counting context, not the present cumulative-congruence result. https://arxiv.org/abs/2010.06719
3. V. Becher and S. Lew Deveali, *Normal numbers in sparse Cantor sets*, arXiv:2607.06773v1, studies binary digits supported on sparse sets and normality in other bases. Its bounded binary alphabets and normality conclusions differ from the polylogarithmic correction alphabets and rationalisation considered here. https://arxiv.org/abs/2607.06773
4. T. Tao, *On the importance of partial progress* and *Maximising the results-to-effort ratio*. These motivate the construction/obstruction pairing and the brief base-$b$ extension; they are not mathematical proof inputs. https://terrytao.wordpress.com/career-advice/on-the-importance-of-partial-progress/ ; https://terrytao.wordpress.com/advice-on-writing-papers/maximising-the-results-to-effort-ratio/

These checks establish antecedent mechanisms and distinctions, not a comprehensive priority search. All theorem numbers in this memorandum are local to it.
