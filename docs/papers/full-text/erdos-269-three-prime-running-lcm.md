<a id="erdos-269-three-prime-running-lcm"></a>

# Irrational distinct-height sums for finite prime sets

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We prove that the reciprocals of the distinct running least common multiples of the integers supported on a finite set of at least two primes have an irrational sum. Rationality would identify nearby normalised tails, whereas an isolated interchange of two prime-power jumps changes their values. An arrangement of closed geodesics on a torus supplies this interchange. For the corresponding sum counted with multiplicity, we give a tail recurrence and a residue criterion; its irrationality for three primes remains open here.

<a id="sec:problem"></a>

# Two sums from running least common multiples

Let $`P`$ be a finite set of primes, and let $`\mathcal S_P`$ be the positive integers supported on $`P`$, including $`1`$. For $`x\ge1`$, write
``` math
\operatorname{L}(x)=\operatorname{lcm}\{u\in\mathcal S_P:u\le x\},\qquad
 \operatorname{H}_P(x)=\prod_{p\in P}p^{\lfloor\log_p x\rfloor}.
```
Since each $`u\le x`$ divides $`\operatorname{H}_P(x)`$ and the maximal powers of the primes in $`P`$ occur among these $`u`$, the two functions are equal. The running LCM therefore changes only at a positive prime power, where it is multiplied by the corresponding prime. We consider the sum that counts each distinct value once:
``` math
\mathcal D_P=1+\sum_{\substack{t=p^n\\p\in P,\ n\ge1}}\frac1{\operatorname{H}_P(t)}.
```
The indexing is unambiguous because positive powers of distinct primes never coincide. We use $`\mathbb{N}=\{0,1,2,\ldots\}`$.

<div id="res:distinct-height-all" class="theorem">

**Theorem 1** (the distinct-height sums). *For every finite set $`P`$ of primes with $`|P|\ge2`$, the number $`\mathcal D_P`$ is irrational.*

</div>

In a letter dated 1 January 1973, Erdős asserted this result without printing a proof \[erdos1974letter\]. The argument below compares two normalised tails whose sequences of prime-power jumps agree for a long time. Under a rationality assumption the tails lie in a fixed lattice, and hence must be equal. We then find a later pair of jumps whose order is reversed and whose contribution changes. The construction works in the closure of the logarithmic flow; it requires no conjecture about linear independence of reciprocal logarithms.

Erdős also asked about the sum with multiplicity,
``` math
\mathcal R_P=\sum_{u\in\mathcal S_P}\frac1{\operatorname{L}(u)},
```
as recorded in \[erdosgraham1980, p. 65\] and \[erdos1988, p. 106\]. For example, $`\operatorname{L}(5)=\operatorname{L}(6)=60`$ for $`P=\{2,3,5\}`$, giving $`2/60`$ in $`\mathcal R_P`$ and $`1/60`$ in $`\mathcal D_P`$. The theorem concerns $`\mathcal D_P`$, a distinct target from Problem #269. The repeated sum $`\mathcal R_{\{2,3,5\}}`$ remains unresolved by the results in this paper. For a singleton $`P=\{p\}`$ both sums are $`p/(p-1)`$, which explains the restriction $`|P|\ge2`$.

The proof of the theorem occupies Section <a href="#sec:distinct" data-reference-type="ref" data-reference="sec:distinct">2</a>. The two-prime case has a stronger conclusion: Fan’s factorisation \[fan2026comment\] and a Hecke–Mahler value theorem make both sums transcendental (Section <a href="#sec:two-prime" data-reference-type="ref" data-reference="sec:two-prime">3</a>). Sections <a href="#sec:lcm" data-reference-type="ref" data-reference="sec:lcm">4</a> and <a href="#sec:escape" data-reference-type="ref" data-reference="sec:escape">5</a> derive the recurrence and residue criterion for the repeated three-prime sum. We give a second proof for $`\mathcal D_{\{2,3,5\}}`$ in Appendix <a href="#sec:distinct-235" data-reference-type="ref" data-reference="sec:distinct-235">6</a>, discuss finite separation of the three-prime kernel in Appendix <a href="#sec:rank" data-reference-type="ref" data-reference="sec:rank">7</a>, and list the proof sources in Appendix <a href="#app:sources" data-reference-type="ref" data-reference="app:sources">8</a>.

<a id="sec:distinct"></a>

# Proof for a finite set of primes

List the positive prime powers from $`P`$ as $`t_1<t_2<\cdots`$, let $`q_k`$ be the prime whose power is $`t_k`$, and put $`Q_k=q_1\cdots q_k=\operatorname{H}_P(t_k)`$. Then
``` math
\mathcal D_P=1+\sum_{k\ge1}Q_k^{-1}.
```
The estimate $`Q_k\ge2^k`$ proves convergence; for example, when $`P=\{2,3,5\}`$ the successive heights are $`1,2,6,12,60,120,360,720,\ldots`$.

<a id="sec:words"></a>

## Tails and finite words

For an infinite word $`u=u_1u_2\cdots`$ over $`P`$, define $`V(u)=\sum_{j\ge1}(u_1\cdots u_j)^{-1}`$. For a nonempty finite word $`\sigma=\sigma_1\cdots\sigma_n`$, put
``` math
\Pi(\sigma)=\sigma_1\cdots\sigma_n,\qquad
 f(\sigma)=\sum_{j=1}^{n}\sigma_{j+1}\cdots\sigma_n.
```
The empty product at the end of $`f`$ is $`1`$, so removing a prefix gives
``` math
\begin{equation}
\label{eq:word-shift}
 V(\sigma u)=\frac{f(\sigma)+V(u)}{\Pi(\sigma)}.
\end{equation}
```
We apply this identity to $`x_k=V(q_{k+1}q_{k+2}\cdots)=\sum_{j>k}Q_k/Q_j`$. Every suffix contains every prime of $`P`$, so $`0<x_k<1/(\min P-1)\le1`$.

<div id="res:dp-integral-tails" class="lemma">

**Lemma 2** (integral tails). *If $`\mathcal D_P=N/K`$ with integers $`N`$ and $`K\ge1`$, then $`Kx_k`$ is an integer for every $`k\ge1`$.*

</div>

<div class="proof">

*Proof.* Multiplying the defining series by $`Q_k`$ and using $`Q_i\mid Q_k`$ for $`i\le k`$, we obtain
``` math
Kx_k=Q_kN-K\left(Q_k+\sum_{i\le k}\frac{Q_k}{Q_i}\right)\in\mathbb Z.
```
 ◻

</div>

We shall compare words obtained by rearranging successive finite blocks. A long common prefix makes their values close, while equality of their values will force an integer identity on each rearranged block.

<div id="res:dp-blocks" class="lemma">

**Lemma 3** (rearranged blocks). *Let $`u=\sigma_1\sigma_2\cdots`$ and $`u'=\sigma'_1\sigma'_2\cdots`$ be infinite words, where each $`\sigma_i`$ is a nonempty finite word and $`\sigma'_i`$ is a rearrangement of it, and suppose that every suffix of $`u`$ or $`u'`$ starting at a block boundary has value in $`(0,1)`$.*

1.  *If $`V(u)=V(u')`$, then $`f(\sigma_i)=f(\sigma'_i)`$ for every $`i`$.*

2.  *If $`\sigma_i=\sigma'_i`$ for every $`i<i_0`$, then $`|V(u)-V(u')|<1/\Pi(\sigma_1\cdots\sigma_{i_0-1})`$.*

</div>

<div class="proof">

*Proof.* Write $`U_i`$ and $`U'_i`$ for the values starting at block $`i`$. Applying <a href="#eq:word-shift" data-reference-type="eqref" data-reference="eq:word-shift">[eq:word-shift]</a> to two blocks with the same product, we obtain
``` math
\Pi(\sigma_i)(U_i-U'_i)
 =f(\sigma_i)-f(\sigma'_i)+U_{i+1}-U'_{i+1}.
```
When $`U_i=U'_i`$, we have an integer equal to a number in $`(-1,1)`$, so both differences vanish and induction proves (i). For (ii), we remove the common prefix to get
``` math
V(u)-V(u')=\frac{U_{i_0}-U'_{i_0}}
 {\Pi(\sigma_1\cdots\sigma_{i_0-1})},
```
which proves (ii). ◻

</div>

<div id="res:dp-short" class="lemma">

**Lemma 4** (short rearrangements). *The map $`f`$ is injective on the orderings of any set of at most three distinct primes.*

</div>

<div class="proof">

*Proof.* For two letters we have $`f(ab)=1+b`$, and for three we have $`f(abc)=1+c(1+b)`$. Suppose that two orderings of $`\{a,b,c\}`$ have the same value. Equal last letters would force equal middle letters, so it suffices to consider $`a(1+s)=b(1+t)`$, with $`s\in\{b,c\}`$ and $`t\in\{a,c\}`$. The choices $`(s,t)=(b,a)`$ and $`(c,c)`$ imply $`a=b`$; the other two imply $`b\mid a`$ or $`a\mid b`$. Each is impossible for distinct primes. ◻

</div>

The collision $`f(5,7,3,2)=f(7,2,3,5)=51`$ shows why we cannot use this lemma for larger $`P`$. Instead, we shall find an isolated interchange of two letters, for which $`f(ab)-f(ba)=b-a\ne0`$.

<a id="sec:flow"></a>

## The logarithmic flow

Consider
``` math
\mathbb T=\prod_{q\in P}\mathbb R/(\log q)\mathbb Z,
 \qquad \Theta(s)=(s\bmod\log q)_{q\in P}.
```
For $`\theta\in\mathbb T`$, a $`q`$-crossing is a time $`t`$ at which $`\theta_q+t\in(\log q)\mathbb Z`$. At $`\theta_k=\Theta(\log t_k)`$ the positive crossings occur at $`\log(q^j/t_k)`$ with $`q^j>t_k`$, so their labels, read in time order, are $`q_{k+1}q_{k+2}\cdots`$. Crossings at this phase never coincide.

We work in the closure $`T_0`$ of $`\Theta(\mathbb R)`$, where every forward orbit is dense. To verify this last assertion, use the pigeonhole principle to find arbitrarily large $`d>0`$ with $`\Theta(d)`$ arbitrarily close to $`0`$. Negative times are then limits of positive ones, and translation gives density from every starting point, even after any prescribed waiting time.

In the normalised coordinates $`\varphi_q=\theta_q/\log q`$, Kronecker’s theorem identifies $`T_0`$ with the image of the smallest rational subspace $`L\subseteq\mathbb R^P`$ containing $`\omega=(1/\log q)_{q\in P}`$. Any two coordinate forms $`\varphi_a,\varphi_b`$ are linearly independent on $`L`$. To see this, their dependence would put a nonzero vector supported on $`\{a,b\}`$ in the rational annihilator of $`L`$. That intersection is rational, so it would contain a nonzero integer vector. Its pairing with $`\omega`$ would force $`\log a/\log b\in\mathbb Q`$, contrary to unique factorisation. In particular, $`(\log b)\varphi_b-(\log a)\varphi_a`$ is a nonzero form on $`L`$. We write it as $`\theta_b-\theta_a`$ when using real representatives.

<div id="res:dp-two-walls" class="lemma">

**Lemma 5** (two walls). *If $`|P|\ge4`$, there is $`x\in T_0`$ with $`\theta_q(x)=0`$ for exactly two primes $`q\in P`$.*

</div>

<div class="proof">

*Proof.* We first choose a rational plane in $`L`$ on which every pair of coordinate forms remains independent. This is possible because each corresponding determinant is a nonzero polynomial on $`L\times L`$, and a finite union of their zero sets cannot contain all rational pairs. An integer basis for the lattice in this plane identifies its image with a two-dimensional subtorus of $`T_0`$. On this subtorus each wall $`\theta_q=0`$ has the equation $`\langle\gamma_q,s\rangle\in\mathbb Z`$, where $`\gamma_q\in\mathbb Z^2\setminus\{0\}`$, and the vectors $`\gamma_q`$ are pairwise nonparallel. A wall may have several components if $`\gamma_q`$ is not primitive.

We count the vertices, edges and faces of this finite arrangement of closed geodesics. If $`k_v`$ is the number of wall families through a vertex $`v`$, the two incident half-edges contributed by each family give $`E=\sum_v k_v`$. Two families alone divide the torus into open parallelograms, since their integer linear forms define a finite covering of the standard torus. The remaining lines subdivide these parallelograms into convex polygons with at least three sides. Combining $`2E\ge3F`$ with Euler’s formula $`V-E+F=0`$, we obtain
``` math
\sum_v(k_v-3)=E-3V\le0.
```
Since the origin belongs to all $`|P|\ge4`$ families, this inequality forces at least one vertex to belong to exactly two families. ◻

</div>

<a id="sec:tail-comparison"></a>

## Comparison of two tails

<div class="proof">

*Proof of Theorem <a href="#res:distinct-height-all" data-reference-type="ref" data-reference="res:distinct-height-all">1</a>.* Suppose that $`\mathcal D_P=N/K`$, with $`K\ge1`$. Fix $`p\in P`$ and a jump $`t_k`$ which is a power of $`p`$. We shall compare the tails after $`t_k`$ and $`t_m=t_kp^n`$, choosing $`n`$ so that multiplication by $`p^n`$ moves all logarithmic phases very little.

Choose $`T>0`$ so that the number $`\nu`$ of crossings in $`(0,T]`$ satisfies $`2^\nu\ge K`$, and let $`g>0`$ be the minimum gap between distinct crossings in $`[0,T+1]`$. Put $`\beta=\min_{q\ne p}\operatorname{dist}(\theta_{k,q},0)>0`$. When $`|P|\ge4`$, also choose the point $`x`$ and primes $`a,b`$ from Lemma <a href="#res:dp-two-walls" data-reference-type="ref" data-reference="res:dp-two-walls">5</a>, and set
``` math
\eta=\min\left(\frac1{10},
       \min_{c\ne a,b}\operatorname{dist}(\theta_c(x),0)\right)>0.
```
Take $`\varepsilon<\min(\beta,g/2,\log2/(2|P|))`$, and in this latter case require also $`\varepsilon<\eta/8`$. Dirichlet’s simultaneous approximation theorem gives arbitrarily large $`n`$ and integers $`m_q\ge1`$ for $`q\ne p`$ such that
``` math
\delta_p=0,\qquad \delta_q=n\log p-m_q\log q,\qquad
 \max_q|\delta_q|<\varepsilon.
```
The numbers $`\delta_q`$ are pairwise distinct, since an equality would identify positive powers of distinct primes.

We compare crossings at $`\theta_k`$ with those at $`\theta_m=\theta_k+\Theta(n\log p)`$ by moving each $`q`$-crossing through $`-\delta_q`$. This preserves signs for $`q\ne p`$, because every such crossing is at distance at least $`\beta>\varepsilon`$ from $`0`$, and the $`p`$-crossings remain fixed. Thus positive crossings correspond bijectively.

We cut the crossings of $`\theta_k`$ whenever successive times are more than $`2\varepsilon`$ apart, calling each resulting block a chain. Since each crossing moves by less than $`\varepsilon`$, different chains keep their order. Moreover, each chain contains at most $`|P|`$ crossings, all of different primes: otherwise its first $`|P|+1`$ crossings would span less than $`2\varepsilon|P|<\log2`$, although some prime would have to occur twice. The same argument excludes a repeated prime in a shorter chain. Thus the two tail words are concatenations of the same chains, with the letters possibly rearranged inside each chain.

By our choice of $`g`$ and $`\varepsilon`$, every chain meeting $`(0,T]`$ is a singleton. We therefore have a common prefix of $`\nu`$ letters, and Lemma <a href="#res:dp-blocks" data-reference-type="ref" data-reference="res:dp-blocks">3</a>(ii) gives $`|x_k-x_m|<2^{-\nu}\le1/K`$. The integral-tail lemma forces $`x_k=x_m`$. By Lemma <a href="#res:dp-blocks" data-reference-type="ref" data-reference="res:dp-blocks">3</a>(i), every chain $`C`$ and its rearrangement $`C'`$ now satisfy $`f(C)=f(C')`$.

When $`|P|\le3`$, choose $`q\ne p`$. If $`\delta_q>0`$, density of $`j\log p-i\log q+\log t_k`$ for large positive $`i,j`$ supplies crossings $`s_p,s_q>0`$ with $`s_q-\delta_q<s_p<s_q`$. Their order reverses. The case $`\delta_q<0`$ is the same with the inequalities reversed. The two crossings belong to one chain, which has at most three distinct primes and changes its order. This contradicts Lemma <a href="#res:dp-short" data-reference-type="ref" data-reference="res:dp-short">4</a>.

For $`|P|\ge4`$, put $`D=\delta_a-\delta_b\ne0`$. Since the form $`\theta_b-\theta_a`$ is nonzero on $`L`$, choose a small $`y\in L`$ with $`|\theta_q(y)|<\eta/8`$ for all $`q`$ and $`\theta_b(y)-\theta_a(y)`$ strictly between $`0`$ and $`D`$. At the phase
``` math
z=x+y+\Theta(-\eta/2)
```
there is one $`a`$-crossing and one $`b`$-crossing in $`[-\eta/4,5\eta/4]`$. Their times $`\tau_a,\tau_b`$ lie in $`(\eta/4,3\eta/4)`$, and $`\tau_a-\tau_b`$ is strictly between $`0`$ and $`D`$. There are no other crossings in that interval: for $`c\ne a,b`$ the nearest one is at distance at least $`7\eta/8`$ from $`\eta/2`$.

Because the inequalities are strict, we may choose a neighbourhood $`U`$ of $`z`$ in $`T_0`$ on which these crossing and difference conditions persist. By density, $`\theta_k+\Theta(t^*)\in U`$ for some $`t^*>T+2`$. The two corresponding crossings of $`\theta_k`$ are less than $`|D|<2\varepsilon`$ apart, whereas every other crossing is more than $`\eta/2>4\varepsilon`$ away. They form a chain of length two. After shifting, their time difference becomes $`(\tau_a-\tau_b)-D`$, which has the opposite sign. Thus $`C=ab,C'=ba`$ or conversely, contradicting $`f(ab)-f(ba)=b-a\ne0`$. ◻

</div>

The [companion’s proof of the general theorem](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-distinct-proof) records further examples of colliding rearrangements. In particular, a return near the origin may reverse a whole chain whose two orders have equal $`f`$-values. The point on two walls avoids that difficulty even when $`T_0`$ is smaller than the ambient torus. Classical Cantor-series criteria of Erdős–Straus \[erdosstraus1974\] and Hančl–Tijdeman \[hancltijdeman2004\], and the criterion of Diananda–Oppenheim \[dianandaoppenheim1955\], do not by themselves decide this bounded-base series; the companion gives their precise hypotheses in its historical discussion.

<a id="sec:two-prime"></a>

# The two-prime case and prime-power subseries

For two primes the repeated sum factors into the two sums over pure powers. Fan gave this factorisation and its transcendence consequence in his post of 26 June 2026 \[fan2026comment\]. The distinct-height sum is affine in the same Hecke–Mahler value. We include the calculation because it explains both the stronger conclusion for two primes and the effect of counting multiplicities.

<div id="res:two-prime-transcendence" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-two-prime-transcendence">Lean†</a></p>

**Theorem 6** (both two-prime sums). *<span id="res:two-prime-repeated-transcendence" label="res:two-prime-repeated-transcendence"></span> Let $`p<q`$ be distinct primes. Put $`\theta=\log p/\log q`$ and $`A=\sum_{n\ge0}p^{-n}q^{-\lfloor n\theta\rfloor}`$. Let $`\mathcal R_{p,q}`$ sum the reciprocal running LCM at every positive $`\{p,q\}`$-smooth integer, and let $`\mathcal D_{p,q}`$ count each distinct running LCM once. Then
``` math
\begin{equation}
\label{eq:two-prime-affine}
 \mathcal D_{p,q}=\frac{(q-p)A+p}{q-1},\qquad
 \mathcal R_{p,q}=\frac{(p+q-1)A-(p-1)A^2}{q-1}.
\end{equation}
```
Both numbers are transcendental.*

</div>

The Lean proof assumes the transcendence theorem of Bugeaud and Laurent; the two identities in <a href="#eq:two-prime-affine" data-reference-type="eqref" data-reference="eq:two-prime-affine">[eq:two-prime-affine]</a> are proved in Lean without it.

The dagger on the formal-source mark refers to the assumed Bugeaud–Laurent transcendence theorem. The identities themselves do not use that assumption.

<div class="proof">

*Proof.* Write $`x=1/p`$, $`y=1/q`$, $`m_n=\lfloor n\theta\rfloor`$ and $`\delta_n=m_{n+1}-m_n`$. Unique factorisation makes $`\theta`$ irrational, and $`0<\theta<1`$ gives $`\delta_n\in\{0,1\}`$. The initial value and the positive powers of $`p`$ contribute $`A=\sum_{n\ge0}x^ny^{m_n}`$. There is one $`q`$-power strictly between $`p^n`$ and $`p^{n+1}`$ exactly when $`\delta_n=1`$, so the positive powers of $`q`$ contribute
``` math
B=\sum_{n\ge0}\delta_nx^ny^{m_n+1},\qquad \mathcal D_{p,q}=A+B.
```
Since $`0<x,y<1`$, these series converge absolutely. The identity $`y^{m_{n+1}}-y^{m_n}=\delta_ny^{m_n}(y-1)`$ and an index shift in $`A`$ give $`A-1-xA=x(y-1)B/y`$. Therefore
``` math
B=\frac{p-(p-1)A}{q-1}.
```
We compute the repeated sum from the height $`p^{i+\lfloor j/\theta\rfloor}q^{j+m_i}`$ at $`p^iq^j`$, obtaining
``` math
\mathcal R_{p,q}
 =A\sum_{j\ge0}y^jx^{\lfloor j/\theta\rfloor}=A(1+B).
```
For the last equality, each $`j\ge1`$ corresponds to $`n=\lfloor j/\theta\rfloor`$ with $`m_n=j-1`$ and $`\delta_n=1`$. Substitution proves <a href="#eq:two-prime-affine" data-reference-type="eqref" data-reference="eq:two-prime-affine">[eq:two-prime-affine]</a>.

To apply the transcendence theorem, we express $`A`$ in terms of the Hecke–Mahler series $`F_\theta(x,y)=\sum_{n\ge1}\sum_{k=1}^{m_n}x^ny^k`$. Geometric summation gives
``` math
\begin{equation}
\label{eq:hecke-mahler-boundary}
 A=\frac1{1-x}-\frac{1-y}{y}F_\theta(x,y).
\end{equation}
```
Bugeaud and Laurent’s theorem \[bugeaudlaurent2023, Theorem 1.1\] applies with intercept $`\rho=0`$, $`\beta=x`$ and $`\alpha=y`$: the slope $`\theta`$ is irrational and lies in $`(0,1)`$, $`x`$ and $`y`$ are nonzero algebraic numbers, $`|x|<1`$ and $`|xy^\theta|=p^{-2}<1`$. Thus $`F_\theta(x,y)`$ is transcendental; this case $`\rho=0`$ is due to Loxton and van der Poorten \[loxtonvdp1977, Theorem 8, p. 40\]. Thus $`A`$ is transcendental. The displayed affine and quadratic polynomials are nonconstant, so an algebraic value of either would force $`A`$ to be algebraic. ◻

</div>

The calculation also applies to the monoid generated by any coprime integers $`1<p<q`$, such as $`4`$ and $`9`$, although that monoid need not contain all integers supported on the prime divisors of $`pq`$. The [companion’s two-prime calculation](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-two-prime) gives the extension and explains why multiplicatively dependent generators such as $`4,8`$ behave differently.

For a general finite $`P`$ and $`p\in P`$, put
``` math
E_p=\sum_{\alpha\ge0}\frac1{\operatorname{L}(p^\alpha)}.
```
Then $`\mathcal D_P=\sum_{p\in P}E_p-(|P|-1)`$, since the term $`1`$ occurs in every $`E_p`$. With two primes, $`\mathcal R_{\{p,q\}}=E_pE_q`$. A version of the preceding tail comparison also treats each $`E_p`$.

<div id="res:single-prime-subsums" class="theorem">

**Theorem 7** (the single-prime sub-sums). *For every finite set $`P`$ of primes with $`|P|\ge2`$ and every $`p\in P`$, the number $`E_p`$ is irrational.*

</div>

We adapt the word argument by replacing $`V`$ and $`f`$ with
``` math
V_p(u)=\sum_{i:u_i=p}\frac1{u_1\cdots u_i},\qquad
 f_p(\sigma)=\sum_{j:\sigma_j=p}\sigma_{j+1}\cdots\sigma_n.
```
The identity <a href="#eq:word-shift" data-reference-type="eqref" data-reference="eq:word-shift">[eq:word-shift]</a> still holds, and actual suffixes have $`V_p`$-values in $`(0,1)`$. Rationality therefore again forces equal $`f_p`$-values on rearranged chains. On a chain of distinct primes containing $`p`$, $`f_p`$ is the product of the primes following $`p`$, so it changes whenever that follower set changes. A small displacement of a return near the origin changes this set for one of two opposite directions. The [companion’s proof for prime-power subseries](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-prime-subseries) constructs that displacement and verifies the required strict crossing inequalities. It uses no two-wall lemma. For $`|P|=2`$ both $`E_p`$ are transcendental by the calculation above; for $`|P|\ge3`$ no priority claim is made, and the source record contains no separate literature search for this subseries theorem.

For the full repeated sum, scaling by $`p^n`$ also brings in the early terms of rays $`p^\alpha w`$ with $`w`$ supported on $`P\setminus\{p\}`$. Those extra terms change the comparison. For $`P=\{2,3,5\}`$ the normalised tails are unbounded, as the next section and the companion’s lower bounds show.

<a id="sec:lcm"></a>

# The repeated three-prime sum

<span id="sec:cells" label="sec:cells"></span><span id="sec:fibre" label="sec:fibre"></span><span id="sec:shell" label="sec:shell"></span> <span id="sec:actual-orbit" label="sec:actual-orbit"></span> For three pairwise distinct primes $`p,q,r`$, abbreviate $`\operatorname{H}_{\{p,q,r\}}`$ to $`\operatorname{H}`$ and write $`\operatorname{K}(i,j,k)=\operatorname{H}(p^iq^jr^k)^{-1}`$. We first record the height and multiplicity identities used in the tail calculation.

<div id="res:lcm" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L49">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-lcm-comparator">Comparator</a></p>

**Proposition 8** (the running least common multiple). *Let $`p,q,r`$ be pairwise distinct primes and $`x\ge1`$. Then the running LCM equals the three-prime height: $`\operatorname{L}(x)=\operatorname{H}(x)`$.*

</div>

<div class="proof">

*Proof.* We have $`u\mid\operatorname{H}(x)`$ for every supported $`u\le x`$. For the reverse divisibility, take the maximal powers of $`p,q,r`$ below $`x`$: they belong to the prefix and are pairwise coprime, so their product divides its LCM. ◻

</div>

For each prime, $`x/p<p^{\lfloor\log_p x\rfloor}\le x`$. Multiplying gives
``` math
\begin{equation}
\label{res:cube}
 x^3/(pqr)<\operatorname{H}(x)\le x^3.
\end{equation}
```

<div id="res:cell" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-cell">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-cell-comparator">Comparator</a></p>

**Proposition 9** (cells and jumps). *The running LCM is constant when the three integer logarithms are constant. A jump in exactly one logarithm multiplies it by the corresponding prime. The first $`n`$ positive powers of each prime, together with $`1`$, form $`3n+1`$ distinct points.*

</div>

<div class="proof">

*Proof.* The height is a product of the three maximal pure powers, which proves the constancy and jump assertions. Unique factorisation separates the $`3n`$ positive pure powers from one another and from $`1`$. ◻

</div>

<div id="res:fibre-prop" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L407">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-fibre-prop-comparator">Comparator</a></p>

**Proposition 10** (grouping terms with the same height). *For a finite exponent box $`\mathcal B`$, set $`F(H)=\{(i,j,k)\in\mathcal B:\operatorname{H}(p^iq^jr^k)=H\}`$. Then
``` math
\begin{equation}
\label{res:fibre}
 \sum_{(i,j,k)\in\mathcal B}\operatorname{K}(i,j,k)=\sum_H\frac{\#F(H)}H.
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Partition the finite exponent box by the value of the height. The terms in the part $`F(H)`$ all equal $`1/H`$. ◻

</div>

Henceforth $`P=\{2,3,5\}`$ and $`S=\mathcal R_P`$. Group the smooth integers into half-open dyadic intervals and define
``` math
s_a=\sum_{\substack{x\in\mathcal S_P\\2^a\le x<2^{a+1}}}\frac1{\operatorname{H}(x)},
 \qquad T_a=\sum_{j\ge0}s_{a+j},\qquad
 h_a=\frac{\operatorname{H}(2^a)}2,\qquad X_a=h_aT_a.
```
The factor $`1/2`$ makes $`h_a`$ a common multiple of the heights strictly before $`2^a`$. Indeed, each such height has exponent of $`2`$ at most $`a-1`$. Here $`h_0=1/2`$, and $`h_a`$ is an integer for $`a\ge1`$. Put
``` math
\begin{equation}
\label{eq:actual-digit}
 b_a=\frac{\operatorname{H}(2^{a+1})}{\operatorname{H}(2^a)},\qquad
 m_a=\sum_{\substack{x\in\mathcal S_P\\2^a\le x<2^{a+1}}}
       \frac{\operatorname{H}(2^{a+1})}{2\operatorname{H}(x)}.
\end{equation}
```

<div id="res:dyadic-alphabet" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperCompleteR20/DyadicAlphabetWhole.lean#L19">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-dyadic-alphabet-comparator">Comparator</a></p>

**Lemma 11** (integer coefficients and four possible bases). *For every $`a\ge0`$, $`m_a`$ is a positive integer and $`b_a\in\{2,6,10,30\}`$. The word “numerator” does not impose the positional-digit restriction $`m_a<b_a`$; that restriction need not hold.*

</div>

<div class="proof">

*Proof.* For $`x<2^{a+1}`$ we have $`2\operatorname{H}(x)\mid\operatorname{H}(2^{a+1})`$, so every summand in $`m_a`$ is integral. The interval contains $`2^a`$, giving positivity. Between successive powers of $`2`$ there is at most one power of $`3`$ and at most one power of $`5`$. Along with the final factor $`2`$, these give $`b_a\in\{2,6,10,30\}`$. ◻

</div>

For example, $`[2,4)`$ contains $`2,3`$ and gives $`(b_1,m_1)=(6,4)`$. At $`[16,32)`$ we obtain $`(b_4,m_4)=(30,65)`$, so these coefficients cannot be treated as positional digits.

<div id="res:actual-orbit" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7SeriesIdentification.lean#L168">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-actual-orbit-comparator">Comparator</a></p>

**Proposition 12** (the tail recurrence and a quadratic bound). *The series defining $`S,T_a`$ converge. For every $`a\ge0`$,
``` math
X_{a+1}=b_aX_a-m_a,\qquad
 0<X_a\le\frac{8640}{343}(a+1)^2<90(a+1)^2.
```
For every integer $`B\ge1`$, either some $`BX_a`$ is integral and all later states are integral, or $`\operatorname{dist}(BX_a,\mathbb Z)\ge1/31`$ at arbitrarily large indices.*

</div>

<div class="proof">

*Proof.* We count at most $`(a+1)^2`$ smooth integers in $`[2^a,2^{a+1})`$: each pair of exponents of $`3,5`$, both at most $`a`$, allows at most one exponent of $`2`$. By <a href="#res:cube" data-reference-type="eqref" data-reference="res:cube">[res:cube]</a>, $`s_a\le30(a+1)^2/8^a`$. As $`h_a\le8^a/2`$ and $`a+j+1\le(a+1)(j+1)`$, we have
``` math
X_a\le15(a+1)^2\sum_{j\ge0}\frac{(j+1)^2}{8^j}
     =\frac{8640}{343}(a+1)^2.
```
This also proves convergence. Splitting off $`s_a`$ gives the recurrence, since $`h_{a+1}=b_ah_a`$ and $`m_a=h_{a+1}s_a`$.

For the final assertion, suppose that every sufficiently late distance is strictly less than $`1/31`$, and write $`BX_a=z_a+e_a`$, where $`z_a`$ is integral and $`|e_a|<1/31`$. The recurrence makes $`e_{a+1}-b_ae_a`$ an integer of absolute value less than $`(1+b_a)/31\le1`$. Thus $`e_{a+1}=b_ae_a`$. Since $`b_a\ge2`$, boundedness forces every such error to vanish. Once integral, the states remain integral by the recurrence. ◻

</div>

The repeated series is a Cantor series: $`S/2=\sum_{a\ge0}m_a/(b_0\cdots b_a)`$. The criteria in \[erdosstraus1974, Theorem 2.1\] and \[hancltijdeman2004, Theorem 3.1\] require a small-numerator hypothesis $`m_a/(b_{a-1}b_a)\to0`$. Here the $`b_a`$ are bounded and $`m_a`$ grows quadratically. The [companion’s tail estimates](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-repeated-bounds) prove this lower bound as well as sharper upper bounds. In particular, $`X_a>m_a/30`$ is unbounded, so the finite-state argument for distinct heights does not extend through a mere change of notation.

<div id="res:denominator-reduction" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7RationalBridge.lean#L80">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-denominator-reduction-comparator">Comparator</a></p>

**Theorem 13** (rationality gives positive integer tails). *If $`S=A/D`$ in lowest terms, where $`D=2^u3^v5^wB`$ and $`\gcd(B,30)=1`$, then for every $`a\ge a_0=u+1+2v+3w`$,
``` math
d_a=BX_a\in\mathbb Z_{>0},\qquad
 d_{a+1}=b_ad_a-Bm_a,\qquad d_a\le90B(a+1)^2.
```*

</div>

<div class="proof">

*Proof.* For $`a\ge1`$, clearing the finite prefix gives
``` math
\begin{equation}
\label{eq:prefix-lattice}
 X_a=h_aS-\sum_{\substack{x\in\mathcal S_P\\x<2^a}}
                 \frac{h_a}{\operatorname{H}(x)},\qquad
 \sum_{\substack{x\in\mathcal S_P\\x<2^a}}\frac{h_a}{\operatorname{H}(x)}\in\mathbb Z.
\end{equation}
```
If $`a\ge u+1+2v+3w`$, the exponent $`a-1`$ of $`2`$ in $`h_a`$ is at least $`u`$, and $`2^a\ge3^v,5^w`$. Therefore $`2^u3^v5^w\mid h_a`$, and $`BX_a`$ differs from $`h_aA/(2^u3^v5^w)`$ by an integer. Positivity, recurrence and the bound follow from Proposition <a href="#res:actual-orbit" data-reference-type="ref" data-reference="res:actual-orbit">12</a>. ◻

</div>

<div id="res:exact-onset" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-exact-onset">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-exact-onset-comparator">Comparator</a></p>

**Corollary 14** (the first index at which the denominator clears). *Under the same lowest-terms hypothesis, put $`M=2^u3^v5^w`$ and let $`\operatorname{den}`$ denote the positive reduced denominator. For $`a\ge1`$,
``` math
\operatorname{den}(BX_a)=\frac{M}{\gcd(M,h_a)}.
```
Consequently $`BX_a`$ is integral exactly when $`2^a\ge\max(2^{u+1},3^v,5^w)`$. The first such $`a`$ can be found by integer comparisons, without logarithmic rounding.*

</div>

<div class="proof">

*Proof.* Equation <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a> shows that $`BX_a`$ and $`h_aA/M`$ have the same reduced denominator. Since $`\gcd(A,M)=1`$, this denominator is $`M/\gcd(M,h_a)`$. Divisibility by each of $`2^u,3^v,5^w`$ gives the three stated inequalities. ◻

</div>

For a hypothetical reduced denominator $`2^3 3^2 5\cdot7`$, the first integral $`7X_a`$ would occur at $`a=4`$. The sufficient onset in the theorem is $`11`$. The [companion’s denominator calculation](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-denominator) also determines the reduced denominator of $`X_a`$ itself.

<a id="sec:escape"></a>

# A residue criterion

<span id="sec:open" label="sec:open"></span> Iterating the recurrence gives $`X_{\ell+2}=b_{\ell+1}b_\ell X_\ell-(b_{\ell+1}m_\ell+m_{\ell+1})`$. For a window of $`h`$ steps starting at $`\ell`$, define
``` math
W_{\ell,0}=1,\quad F_{\ell,0}=0,\qquad
 W_{\ell,h+1}=b_{\ell+h}W_{\ell,h},\quad
 F_{\ell,h+1}=b_{\ell+h}F_{\ell,h}+m_{\ell+h}.
```
Induction yields
``` math
\begin{equation}
\label{eq:actual-tail}
 X_{\ell+h}=W_{\ell,h}X_\ell-F_{\ell,h}.
\end{equation}
```
Under rationality, this determines the residue of a positive integer tail modulo $`W_{\ell,h}`$. We compare that residue with its quadratic bound. For integers $`W\ge1,t`$, let $`\operatorname{lpr}_W(t)=1+((t-1)\bmod W)`$, taking the remainder in $`\{0,\ldots,W-1\}`$. Thus $`\operatorname{lpr}_W(0)=W`$. Throughout this section set
``` math
\begin{equation}
\label{eq:actual-bound}
 K(B,a)=90B(a+1)^2.
\end{equation}
```

<div id="res:consumer" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L138">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-consumer-comparator">Comparator</a></p>

**Lemma 15** (least positive residues). *If $`d`$ is a positive integer with $`d\le K`$ and $`d\equiv -BF\pmod W`$, where $`W\ge1`$, then $`\operatorname{lpr}_W(-BF)\le K`$.*

</div>

<div class="proof">

*Proof.* The least positive representative is at most every positive representative of its class, and in particular at most $`d`$. ◻

</div>

For $`\ell=1,h=6`$, direct iteration gives $`W_{1,6}=648000`$ and $`F_{1,6}=524431`$. Hence $`\operatorname{lpr}_{W_{1,6}}(-F_{1,6})=123569>K(1,7)=5760`$. This excludes an integral $`X_1`$. A rational denominator might clear only later, so a criterion for irrationality must allow every late start and every denominator part coprime to $`30`$.

<div id="res:windowconsumer" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7WindowResults.lean#L51">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-windowconsumer-comparator">Comparator</a></p>

**Theorem 16** (a residue criterion for irrationality). *The number $`S`$ is irrational if and only if
``` math
\begin{equation}
\label{eq:escape}
 \begin{gathered}
 \text{for every }B\ge1\text{ with }\gcd(B,30)=1
 \text{ and every }a_0\ge1,\\
 \text{there are }\ell\ge a_0,\ h\ge1\text{ such that}
 \operatorname{lpr}_{W_{\ell,h}}(-BF_{\ell,h})>K(B,\ell+h).
 \end{gathered}
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Suppose that <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a> holds and $`S`$ is rational. By Theorem <a href="#res:denominator-reduction" data-reference-type="ref" data-reference="res:denominator-reduction">13</a>, $`d_a=BX_a`$ is a positive integer for every sufficiently large $`a`$. Choose a window beyond that onset. Equation <a href="#eq:actual-tail" data-reference-type="eqref" data-reference="eq:actual-tail">[eq:actual-tail]</a> gives $`d_{\ell+h}\equiv-BF_{\ell,h}\pmod{W_{\ell,h}}`$, contrary to Lemma <a href="#res:consumer" data-reference-type="ref" data-reference="res:consumer">15</a> and <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>.

Conversely, suppose that $`S`$ is irrational and fix $`B,\ell\ge1`$. By <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a>, $`BX_\ell`$ is nonintegral. Write $`\delta=\lceil BX_\ell\rceil-BX_\ell\in(0,1)`$. Since $`W_{\ell,h}\ge2^h`$ and $`X_{\ell+h}=O((\ell+h+1)^2)`$, $`\delta+BX_{\ell+h}/W_{\ell,h}`$ lies in $`(0,1)`$ for sufficiently large $`h`$. The window identity then shows that
``` math
\operatorname{lpr}_{W_{\ell,h}}(-BF_{\ell,h})
 =\lceil BX_\ell\rceil W_{\ell,h}-BF_{\ell,h}
 =\delta W_{\ell,h}+BX_{\ell+h}.
```
The first term eventually exceeds $`K(B,\ell+h)`$. This proves the required inequality from every fixed start. ◻

</div>

The upper-bound property of $`K`$ is essential: choosing the zero function would make every residue inequality automatic. The [companion’s residue analysis](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-residue) treats smaller bounds and identifies when more general bounds give the same criterion. Finite searches cover only finitely many multipliers and starts.

The repeated three-prime question can therefore be written in three equivalent forms.

<div class="problem">

**Problem 17** (the repeated three-prime target). Prove that $`S=\mathcal R_{\{2,3,5\}}`$ is irrational.

</div>

<div id="prob:tails269" class="problem">

**Problem 18** (no reduced tail is an integer). Prove that for every $`a\ge1`$ and every integer $`B\ge1`$ coprime to $`30`$,
``` math
\begin{equation}
\label{eq:tail-nonintegrality}
 BX_a\notin\mathbb Z.
\end{equation}
```

</div>

<div id="prob:producer" class="problem">

**Problem 19** (residue inequalities after every starting index). Prove <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>.

</div>

An integral $`BX_a`$ makes $`S`$ rational by <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a>; Theorem <a href="#res:denominator-reduction" data-reference-type="ref" data-reference="res:denominator-reduction">13</a> proves the converse implication. Theorem <a href="#res:windowconsumer" data-reference-type="ref" data-reference="res:windowconsumer">16</a> gives the third form. All three remain unproved for $`S`$. The [companion’s discussion of the repeated sum](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-open) records the finite calculations and the hypotheses missing from proposed finite-difference and function-theoretic arguments.

<a id="sec:distinct-235"></a>

# Five affine maps for $`\{2,3,5\}`$

The distinct-height sum for three small primes also admits a direct finite-state proof. It uses dyadic blocks $`(2^a,2^{a+1}]`$, whose right endpoint is included, in contrast to the half-open blocks for the repeated sum in Section <a href="#sec:lcm" data-reference-type="ref" data-reference="sec:lcm">4</a>.

<div id="res:distinct-height-235" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L689">Lean</a></p>

**Theorem 20** (the distinct-height sum for $`\{2,3,5\}`$). *The number $`\mathcal D_{\{2,3,5\}}`$ is irrational.*

</div>

<div class="proof">

*Proof.* Put $`P_a=\operatorname{H}(2^a)`$ and $`Y_a=P_a\sum_{t>2^a}\operatorname{H}(t)^{-1}`$, where $`t`$ runs over pure prime powers. The internal jumps of a dyadic block have one of the five types $`\varnothing,3,5,35,53`$, with the order recording the order of the actual powers. Splitting off these jumps and the terminal factor $`2`$ gives $`Y_a=G_{\tau_a}(Y_{a+1})`$, where
``` math
G_\tau(y)=\frac{\mu_\tau+y}{b_\tau},\qquad
 \begin{array}{c|ccccc}
 \tau&\varnothing&3&5&35&53\\\hline
 b_\tau&2&6&10&30&30\\
 \mu_\tau&1&3&3&13&9
 \end{array}
```
Every tail lies in $`(0,1)`$, and the least $`\mu_\tau/b_\tau`$ is $`3/10`$. Every three consecutive blocks contain a power of $`5`$, since $`2<\log_2 5<3`$. At such a block the tail is at most $`7/15`$. Before it, at most two applications of $`G_\varnothing(y)=(1+y)/2`$ majorise all the intervening maps. Thus
``` math
Y_a\in I=[3/10,13/15],\qquad
 G_\varnothing^2(7/15)=13/15.
```
The images of $`I`$, in their order on the line, are
``` math
\begin{array}{c|c}
 \tau&G_\tau(I)\\\hline
 53&[31/100,74/225]\\
 5&[33/100,29/75]\\
 35&[133/300,104/225]\\
 3&[11/20,29/45]\\
 \varnothing&[13/20,14/15]
 \end{array}
```
Their consecutive gaps are $`1/900,17/300,79/900,1/180`$, all positive. Therefore $`Y_a`$ determines $`\tau_a`$, and then determines $`Y_{a+1}=b_{\tau_a}Y_a-\mu_{\tau_a}`$ and every later block.

If $`\mathcal D_{\{2,3,5\}}=N/K`$, clearing the prefix makes every $`KY_a`$ an integer in the fixed interval $`[3K/10,13K/15]`$. Two tails repeat, so the block word is eventually periodic. However, if $`\alpha=\log2/\log3`$, the number of powers of $`3`$ in block $`a`$ is $`\lfloor(a+1)\alpha\rfloor-\lfloor a\alpha\rfloor`$. A period $`\ell`$ would give, for all sufficiently large $`a`$, $`\lfloor(a+n\ell)\alpha\rfloor=\lfloor a\alpha\rfloor+nc`$ with an integer $`c`$. Division by $`n`$ and passage to the limit imply $`\ell\alpha=c`$, contradicting unique factorisation. ◻

</div>

The [companion’s affine-map argument](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-five-maps) includes the general finite-state criterion and its exact computations. It succeeds for every set of three primes at most $`31`$, and for $`292`$ of the $`330`$ sets of four primes in that range. For $`\{2,3,5,7\}`$ the automaton has two admissible words with the same affine map at every subsequent refinement. This prevents that automaton from decoding its first block. It does not establish equal tails for two different words occurring in the actual prime-power sequence.

<a id="sec:rank"></a>

# The three-prime kernel

The factorisation in Section <a href="#sec:two-prime" data-reference-type="ref" data-reference="sec:two-prime">3</a> has no finite separated analogue for three primes. After rescaling rows and columns, the entries reduce to a threshold matrix. Its row and column indices can be selected independently, which avoids a simultaneous approximation hypothesis.

<div id="res:infinite-rank" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L22">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-infinite-rank-comparator">Comparator</a></p>

**Theorem 21** (no finite separation of the kernel). *Let $`p,q,r`$ be primes with $`p\ne q`$, $`p\ne r`$ and $`q\ne r`$. For every $`n\ge0`$ there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$ such that, for every $`k\ge0`$,
``` math
\det\bigl(\operatorname{K}(I(a),J(b),k)\bigr)_{0\le a,b<n}\ne0.
```
Consequently, for no finite $`d`$ do there exist rational-valued functions $`f_\ell(i)`$ and $`G_\ell(j,k)`$, $`0\le\ell<d`$, satisfying
``` math
\operatorname{K}(i,j,k)=\sum_{\ell<d}f_\ell(i)G_\ell(j,k)
 \qquad\hbox{for all }i,j,k.
```*

</div>

<div class="proof">

*Proof.* For fixed $`k`$, we rescale rows and columns to obtain a matrix independent of $`k`$. Put $`c=r^{-1}`$, $`x_i=\{i\log_r p\}`$ and $`y_j=\{j\log_r q\}`$, where braces denote fractional parts. Splitting the floor exponents gives
``` math
\operatorname{K}(i,j,k)=U_i(k)^{-1}C_{ij}V_j(k)^{-1},\qquad
 C_{ij}=c^{\mathbf1_{\{x_i+y_j\ge1\}}},
```
where
``` math
\begin{aligned}
 U_i(k)&=p^i q^{\lfloor\log_q(p^ir^k)\rfloor}
            r^{k+\lfloor\log_r p^i\rfloor},\\
 V_j(k)&=q^j p^{\lfloor\log_p(q^jr^k)\rfloor}
            r^{\lfloor\log_r q^j\rfloor}.
\end{aligned}
```
These positive factors preserve nonvanishing of minors. The remaining entry records whether $`x_i+y_j\ge1`$. Distinct primes make $`\log_r p`$ and $`\log_r q`$ irrational, so each fractional-part orbit is dense in $`[0,1]`$. We choose row and column indices independently, using only these two one-dimensional density statements. For $`n\ge1`$, choose distinct rows with $`0<x_{I(0)}<\cdots<x_{I(n-1)}<1`$. We choose each column so that its entries change from $`1`$ to $`c`$ at a different selected row. Writing $`s_b=1-y_{J(b)}`$, density of $`(y_j)`$ lets us choose

``` math
s_0\in(0,x_{I(0)}),\qquad
 s_b\in(x_{I(b-1)},x_{I(b)})\quad(1\le b<n).
```

The intervals for the $`s_b`$ are disjoint, so the column indices are distinct. The strict inequalities also avoid the threshold itself, and give $`x_{I(a)}+y_{J(b)}\ge1`$ exactly when $`b\le a`$. Thus multiplying row $`a`$ by $`U_{I(a)}(k)`$ and column $`b`$ by $`V_{J(b)}(k)`$ reduces the selected kernel minor to
``` math
T_n(c)=\begin{pmatrix}
 c&1&\cdots&1\\
 c&c&\cdots&1\\
 \vdots&\vdots&\ddots&\vdots\\
 c&c&\cdots&c
 \end{pmatrix},\qquad
 \det T_n(c)=c(c-1)^{n-1}.
```
Indeed, subtracting each preceding row from the next, working upwards from the last row, leaves diagonal entries $`c,c-1,\ldots,c-1`$. The original determinant is therefore
``` math
c(c-1)^{n-1}
 \prod_{a<n}U_{I(a)}(k)^{-1}\prod_{b<n}V_{J(b)}(k)^{-1}\ne0.
```
The indices were chosen from $`C`$, independently of $`k`$. For $`n=0`$ the empty determinant equals $`1`$.

For the final assertion, suppose a separation with $`d`$ summands existed and fix any $`k`$. On the rows $`I(0),\ldots,I(d)`$ and columns $`J(0),\ldots,J(d)`$ its matrix would be the product of the $`(d+1)\times d`$ matrix $`(f_\ell(I(a)))_{a,\ell}`$ and the $`d\times(d+1)`$ matrix $`(G_\ell(J(b),k))_{\ell,b}`$. Its rank would be at most $`d`$, so its determinant would vanish, contrary to the minor just constructed. ◻

</div>

No continuity or boundedness is assumed for the separated factors.

<div id="res:admissible-modular-minors" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7ModularMinors.lean#L133">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-admissible-modular-minors-comparator">Comparator</a></p>

**Corollary 22** (the same minors modulo integers coprime to $`30`$). *For $`(p,q,r)=(2,3,5)`$ and every $`n\ge1`$, there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$, chosen independently of $`B`$ and $`k`$, such that for every $`B\ge2`$ coprime to $`30`$ and every $`k\ge0`$, the selected $`n\times n`$ kernel matrix has unit determinant over $`\mathbb Z/B\mathbb Z`$, with each reciprocal prime power interpreted by its modular inverse.*

</div>

<div class="proof">

*Proof.* Choose the maps from Theorem <a href="#res:infinite-rank" data-reference-type="ref" data-reference="res:infinite-rank">21</a>. Every row and column factor is a unit modulo $`B`$. The normalised determinant is $`5^{-1}(-4/5)^{n-1}`$, also a unit. ◻

</div>

The modulus may be composite, for example $`49`$ or $`77`$. Coprimality with $`30`$ makes both the reciprocal entries and the determinant units: the latter introduces only a power of $`4`$ in its numerator.

<div id="res:rank" class="example">

**Example 23**. For $`(p,q,r)=(2,3,5)`$, the leading two-by-two determinant is $`-1/15`$: its four entries are $`1,1/6,1/2,1/60`$, so it equals $`1/60-1/12`$.

</div>

<a id="leading-minors."></a>

#### Leading minors.

The leading $`4\times4`$ block at $`\{2,3,5\}`$ is singular:
``` math
\operatorname{K}(3,j,0)=\frac1{120}\operatorname{K}(0,j,0)\qquad(0\le j<4).
```
These equalities follow by evaluating the height at $`3^j`$ and $`8\cdot3^j`$. But at $`j=4`$, $`\operatorname{K}(3,4,0)-\operatorname{K}(0,4,0)/120=-1/19440000`$. Thus the leading minors do not supply the arbitrary-order theorem.

<div id="res:finite-cut-rank" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/PaperR7FiniteCutRank.lean#L182">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md#res-finite-cut-rank-comparator">Comparator</a></p>

**Proposition 24** (rank of a matrix of threshold columns). *Let $`m\ge1`$ and let $`c`$ lie in a field with $`c\ne 0,1`$. For $`0\le k\le m`$ write $`v_k`$ for the length-$`m`$ column with a $`1`$ in each of the first $`k`$ coordinates and $`c`$ thereafter. A matrix whose distinct columns are $`v_k`$ for $`k`$ in a nonempty set $`E`$ has rank $`|E|-\mathbf 1_{\{0,m\}\subseteq E}`$.*

</div>

The correction accounts for the two constant columns: $`v_0=c v_m`$. There is no other dependence among distinct threshold columns.

<div class="proof">

*Proof.* List $`E=\{k_1<\cdots<k_t\}`$. The $`t-1`$ differences $`v_{k_{j+1}}-v_{k_j}=(1-c)\mathbf 1_{\{k_j,\ldots,k_{j+1}-1\}}`$ have disjoint nonempty supports, hence are linearly independent. If $`k_1>0`$ or $`k_t<m`$, their union misses a coordinate where $`v_{k_1}`$ is nonzero, so the rank is $`t`$. If $`k_1=0`$ and $`k_t=m`$, then $`v_0=c\,\mathbf 1`$ lies in the span of the differences (their sum is $`(1-c)\mathbf 1`$), so the rank is $`t-1`$. ◻

</div>

The restrictions $`c\ne0,1`$ exclude a zero column or identical columns; they hold for $`c=1/r`$ over $`\mathbb Q`$. In one fixed layer $`k`$, ordering the sampled row phases puts every column in the stated form. The formula therefore determines the rank of each nonempty rectangular sample. For fixed row and column indices this rank is independent of $`k`$. The [companion’s kernel analysis](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-rank) gives the exact rational comparisons.

<a id="approximation."></a>

#### Approximation.

Truncating the original kernel to $`i<N`$ gives a sum of $`N`$ separated terms. The bound $`\operatorname{H}(x)>x^3/(pqr)`$ makes the truncation error tend to zero both uniformly and in $`\ell^1(\mathbb N^3)`$. The rescaled matrix in the rank proof has uniform distance $`(1-1/r)/2`$ from the matrices of finite rank. Rescaling preserves exact rank but removes the decay responsible for the first approximation. The [companion’s approximation theorem](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-approximation) proves both assertions for their stated norms. Neither the rank theorem nor the approximation bound implies irrationality of the scalar sum.

<a id="app:sources"></a>

# Proof sources and further comparisons

The margin marks link to Lean declarations and any associated Comparator comparison; they describe earlier checks, not a fresh run for this revision. The dagger on Theorem <a href="#res:two-prime-transcendence" data-reference-type="ref" data-reference="res:two-prime-transcendence">6</a> marks its assumed Bugeaud–Laurent theorem. Its identities are proved in Lean without that assumption. The five-map theorem has a Lean proof and no Comparator comparison. We prove the general distinct-height theorem, its four lemmas and the prime-power subseries theorem by ordinary arguments. A second AI agent checked those arguments on 26 September 2026, and the reported corrections were incorporated; no human mathematical review is reported. Individual declarations and revisions are listed in the [evidence record](https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-269-three-prime-running-lcm.md) and the [companion’s source inventory](../../../paper/269/erdos269-running-lcm-reasoning-surface.pdf#nameddest=r3-source-inventory). The public links retain their original revisions and may precede this manuscript’s local source cut.

The [distinct-height programs](https://github.com/wcook04/plectis-erdos/tree/10178c4df40cb27d83b5ebb1ec337dd588b82998/research/experiments/erdos269/distinct_height) recompute the five-map constants and the finite-state calculations in exact arithmetic. Their illustrations of the general proof are unnecessary for its validity. The proof of Theorem <a href="#res:windowconsumer" data-reference-type="ref" data-reference="res:windowconsumer">16</a> establishes an equivalence; it does not establish its residue inequalities for the actual repeated sum.

The companion also compares the bounded-ratio argument with Erdős–Taylor \[erdostaylor1957, Theorem 1, p. 600\] and Fan \[fan2026strongly, Lemma 3.1, p. 7\], and the carry restrictions with the polynomial Cantor-series results of Hančl–Tijdeman \[hancltijdeman2008, Theorems 2.2, 3.1 and 4.2\]. Koutsoukou-Argyraki and Li’s Isabelle development \[afperdosstraus2020\] formalises classical irrationality criteria. It does not treat the present repeated series.

For transcendence, the relevant comparisons are the finite-difference conditions of Luca–Ouaknine–Worrell \[lucaouaknineworrell2025\], the echoing conditions in \[kebis2024echoing\], the fixed-base complexity theorem of Adamczewski–Bugeaud \[adamczewskibugeaud2007\], and multivariate Mahler theory \[adamczewskifaverjon2026\]. Quadratic growth of $`m_a`$ supplies none of the missing cancellation or recurrence hypotheses. The companion exhibits nonzero boundary terms in a proposed third-difference calculation and distinguishes variable-base digits from fixed-base expansions. Work on fixed-prime semigroups \[tijdemanmeijer1974; languasco2025\] and other Ahmes-series problems \[kovactao2024\] provides context; no estimate from those papers enters our dyadic counting argument.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="authorship-and-availability."></a>

#### Authorship and availability.

AI agents carried out most of the research and drafting. The companion contains the longer proofs and exact computations, together with the hypotheses and limitations of the unsuccessful approaches.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem number and its status as of 28 July 2026 are taken from Thomas Bloom’s Erdős Problems catalogue \[erdosproblems\]. We thank Wouter van Doorn for advice on exposition, particularly on unexplained terminology, unnecessary notation and restrictive hypotheses. His advice concerned a note on Problem #243; he has not reviewed this paper’s mathematics.

<div class="thebibliography">

99 Paul Erdős and Ronald L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L’Enseignement Mathématique **28**, L’Enseignement Mathématique (1980), [source](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Paul Erdős, *On the irrationality of certain series: problems and results*, in *New Advances in Transcendence Theory*, Cambridge University Press (1988), 102–109, [doi:`10.1017/CBO9780511897184.009`](https://doi.org/10.1017/CBO9780511897184.009). Paul Erdős, *Letter to the Editor*, Fibonacci Quarterly **12**, no. 4 (1974), 335, [source](https://www.fq.math.ca/Scanned/12-4/letter.pdf). Thomas F. Bloom, *Erdős Problem \#269* (2026), [source](https://www.erdosproblems.com/269). Accessed 28 July 2026. Yann Bugeaud and Michel Laurent, *Transcendence and continued fraction expansion of values of Hecke–Mahler series*, Acta Arithmetica **209** (2023), 59–90, [doi:`10.4064/aa220323-18-1`](https://doi.org/10.4064/aa220323-18-1); arXiv:[2203.12901](https://arxiv.org/abs/2203.12901). John H. Loxton and Alfred J. van der Poorten, *Arithmetic properties of certain functions in several variables III*, Bulletin of the Australian Mathematical Society **16** (1977), 15–47, [doi:`10.1017/S0004972700022978`](https://doi.org/10.1017/S0004972700022978). Steve Fan, *Comment on Erdős Problem \#269, thread 269, post 7218* (2026), [source](https://www.erdosproblems.com/forum/thread/269#post-7218). Public forum post, 26 June 2026, thread 269, post 7218. P. H. Diananda and A. Oppenheim, *Criteria for irrationality of certain classes of numbers II*, American Mathematical Monthly **62**, no. 4 (1955), 222–225. Cited in the form stated by Serbenyuk, arXiv:[1706.03124](https://arxiv.org/abs/1706.03124), Theorem 1. Paul Erdős and Ernst G. Straus, *On the irrationality of certain series*, Pacific Journal of Mathematics **55**, no. 1 (1974), 85–92, [doi:`10.2140/pjm.1974.55.85`](https://doi.org/10.2140/pjm.1974.55.85). Jaroslav Hančl and Robert Tijdeman, *On the irrationality of Cantor and Ahmes series*, Publicationes Mathematicae Debrecen **65**, no. 3–4 (2004), 371–380, [doi:`10.5486/PMD.2004.3254`](https://doi.org/10.5486/PMD.2004.3254). Paul Erdős and S. James Taylor, *On the set of points of convergence of a lacunary trigonometric series and the equidistribution properties of related sequences*, Proceedings of the London Mathematical Society **s3-7**, no. 1 (1957), 598–615, [doi:`10.1112/plms/s3-7.1.598`](https://doi.org/10.1112/plms/s3-7.1.598). Steve Fan, *Strongly complete sets and a conjecture of Erdős* (2026), [source](https://arxiv.org/abs/2607.14071v1); arXiv:[2607.14071](https://arxiv.org/abs/2607.14071). The cited Lemma 3.1 is in arXiv v1, 15 July 2026. Jaroslav Hančl and Robert Tijdeman, *On the irrationality of polynomial Cantor series*, Acta Arithmetica **133**, no. 1 (2008), 37–52, [doi:`10.4064/aa133-1-3`](https://doi.org/10.4064/aa133-1-3). Florian Luca, Joël Ouaknine and James Worrell, *Transcendence of Hecke–Mahler Series*, Bulletin of the London Mathematical Society **57**, no. 5 (2025), 1360–1368, [doi:`10.1112/blms.70033`](https://doi.org/10.1112/blms.70033); arXiv:[2412.07908](https://arxiv.org/abs/2412.07908). Numbered references use the published article. Pavol Kebis, Florian Luca, Joël Ouaknine, Andrew Scoones and James Worrell, *On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words*, in *51st International Colloquium on Automata, Languages, and Programming (ICALP 2024)*, Leibniz International Proceedings in Informatics **297**, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2024), 144:1–144:15, [doi:`10.4230/LIPIcs.ICALP.2024.144`](https://doi.org/10.4230/LIPIcs.ICALP.2024.144). Robert Tijdeman and H. G. Meijer, *On integers generated by a finite number of fixed primes*, Compositio Mathematica **29**, no. 3 (1974), 273–286, [source](https://www.numdam.org/article/CM_1974__29_3_273_0.pdf). Alessandro Languasco, Florian Luca, Pieter Moree and Alain Togbé, *Sequences of integers generated by two fixed primes*, Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg **95** (2025), 123–148, [doi:`10.1007/s12188-025-00293-9`](https://doi.org/10.1007/s12188-025-00293-9); arXiv:[2309.12806](https://arxiv.org/abs/2309.12806). Vjekoslav Kovač and Terence Tao, *On several irrationality problems for Ahmes series*, Acta Mathematica Hungarica **175** (2025), 572–608, [doi:`10.1007/s10474-025-01528-0`](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593](https://arxiv.org/abs/2406.17593). Angeliki Koutsoukou-Argyraki and Wenda Li, *Irrationality Criteria for Series by Erdős and Straus*, Archive of Formal Proofs (2020), [source](https://isa-afp.org/entries/Irrational_Series_Erdos_Straus.html). Entry dated 12 May 2020; proof-document version consulted: 6 February 2026. Boris Adamczewski and Yann Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer bases*, Annals of Mathematics **165**, no. 2 (2007), 547–565, [doi:`10.4007/annals.2007.165.547`](https://doi.org/10.4007/annals.2007.165.547). Boris Adamczewski and Colin Faverjon, *Mahler’s method in several variables and finite automata*, Annals of Mathematics **204**, no. 2 (2026), 455–533, [doi:`10.4007/annals.2026.204.2.1`](https://doi.org/10.4007/annals.2026.204.2.1). Online 13 September 2026; locators here refer to the [68-page author manuscript](https://faverjon.perso.math.cnrs.fr/AdamczewskiFaverjon_MahlerFiniteAutomata.pdf).

</div>
