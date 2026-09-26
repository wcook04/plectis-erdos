<a id="erdos-269-three-prime-running-lcm"></a>

# No Finite Separable Representation at Three Prime Generators

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

For every finite set $`P`$ of at least two primes, the sum of the reciprocals of the distinct running least common multiples of the $`P`$-smooth integers is irrational. Erdős asserted this in a 1973 letter that gives no proof. For two primes it follows from a Hecke–Mahler transcendence theorem; the new case is three or more primes. A rational value would make the scaled tails of the sum integers, so two tails that are close would be equal. The tails after a prime power $`t`$ and after $`tp^n`$, for a good return $`n`$, are close, and their words of primes differ by rearranging short runs; a point of a torus lying on exactly two coordinate walls produces a run of two primes whose rearrangement changes the tail. The proof is an ordinary one, refereed by a second reader. For $`\{2,3,5\}`$ a different proof, by five affine maps with disjoint images on dyadic blocks, is checked in Lean. The companion extends this finite-state method to every set of three primes at most $`31`$ by exact computation; it fails for $`\{2,3,5,7\}`$, where two different words of blocks have the same affine map. The same comparison of two tails proves that the sub-sum of the catalogue series over the powers of one prime is irrational. For three distinct primes the reciprocal running-LCM kernel has nonsingular minors of every order, so no finite sum of products separates one exponent from the other two. For the repeated $`\{2,3,5\}`$ series, which counts a running LCM once for every integer at which it occurs, we prove a tail recurrence and a residue criterion equivalent to irrationality. Its tails grow quadratically, the finite-state argument has no counterpart there, and the criterion’s inequalities for every multiplier coprime to $`30`$ after arbitrarily late starts are unproved.

<a id="sec:problem"></a>

# Introduction

For a finite prime set $`P`$, let $`\mathcal S_P`$ consist of the positive integers whose prime factors lie in $`P`$, including $`1`$. We use $`\mathbb{N}=\{0,1,2,\ldots\}`$ for exponent indices. For $`x\ge1`$, put
``` math
\operatorname{L}(x)=\operatorname{lcm}\{u\in\mathcal S_P:u\le x\},\qquad
 \mathcal R_P=\sum_{u\in\mathcal S_P}\operatorname{L}(u)^{-1}.
```
Erdős asked whether $`\mathcal R_P`$ is irrational when $`|P|\ge2`$ \[erdosgraham1980, p. 65\]\[erdos1988, p. 106\]. For $`P=\{p,q,r\}`$, write
``` math
\operatorname{H}(x)=p^{\lfloor\log_p x\rfloor}q^{\lfloor\log_q x\rfloor}
 r^{\lfloor\log_r x\rfloor},\qquad
 \operatorname{K}(i,j,k)=\operatorname{H}(p^iq^jr^k)^{-1}.
```
Prime-power divisibility gives $`\operatorname{L}=\operatorname{H}`$ (Proposition <a href="#res:lcm" data-reference-type="ref" data-reference="res:lcm">12</a>). The running LCM is therefore constant between consecutive prime powers $`p^n,q^n,r^n`$ ($`n\ge1`$), and at each of them it is multiplied by the corresponding prime (Proposition <a href="#res:cell" data-reference-type="ref" data-reference="res:cell">13</a>). Counting each of its values once gives the *distinct-height sum*
``` math
\mathcal D_P=1+\sum_{t}\operatorname{H}(t)^{-1},
```
where $`t`$ runs over the prime powers $`p^n,q^n,r^n`$ with $`n\ge1`$. The two sums differ because the running LCM repeats: $`5`$ and $`6`$ both have running LCM $`60`$, which contributes $`2/60`$ to $`\mathcal R_{\{2,3,5\}}`$ and $`1/60`$ to $`\mathcal D_{\{2,3,5\}}`$. In a letter dated 1 January 1973, Erdős called the irrationality of $`\mathcal R_P`$ a conjecture he could not prove and wrote that he could show the distinct-height sum to be irrational; the letter prints no argument \[erdos1974letter\]. Erdős and Graham state only the question for $`\mathcal R_P`$ \[erdosgraham1980, p. 65\], and we have not found a proof in print (the companion’s Section 11.1 lists the sources searched). Section <a href="#sec:distinct" data-reference-type="ref" data-reference="sec:distinct">2</a> proves the irrationality of $`\mathcal D_P`$ for every finite $`P`$ with $`|P|\ge2`$.

Fan used the identity $`\operatorname{L}=\operatorname{H}`$ to separate the two-prime kernel \[fan2026comment\]. With three primes, even a finite sum of separated products is impossible (Section <a href="#sec:rank" data-reference-type="ref" data-reference="sec:rank">3</a>). That theorem is about the kernel and says nothing about the arithmetic of its sum. Sections <a href="#sec:lcm" data-reference-type="ref" data-reference="sec:lcm">5</a> and <a href="#sec:escape" data-reference-type="ref" data-reference="sec:escape">6</a> turn to the repeated $`\{2,3,5\}`$ sum and state exactly what its irrationality still requires.

*Formal proofs.* A result with a kernel-checked Lean proof carries a mark in the margin. *Lean* opens the proof: the declaration itself when one declaration states the whole result, otherwise the list of declarations that together state it. *Comparator* opens the record of an independent check, in which the same statement, written again from Mathlib alone in a separate repository, was compared with our proof by Lean’s Comparator tool, allowing only the three standard axioms. A dagger on the Lean mark means that the Lean proof assumes an input named just below the result. A result without a mark has no Lean proof of its whole statement; what is checked is said below it. The [evidence record](https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md) gives every declaration, version and check. These checks show that the stated propositions are proved; whether they are the right propositions is a question the reader can settle by comparing them with the text.

<a id="sec:distinct"></a>

# The distinct-height sums

Let $`P`$ be a finite set of primes with $`|P|\ge2`$ and put $`\operatorname{H}_P(t)=\prod_{r\in P}r^{\lfloor\log_rt\rfloor}`$. The proof of Proposition <a href="#res:lcm" data-reference-type="ref" data-reference="res:lcm">12</a> applies to any finite set of primes: the running LCM of the $`P`$-smooth integers up to $`t`$ is $`\operatorname{H}_P(t)`$, and it changes only at the prime powers $`r^n`$ ($`r\in P`$, $`n\ge1`$), where it is multiplied by $`r`$. List these prime powers as $`t_1<t_2<\cdots`$, let $`q_k`$ be the prime of $`t_k`$, and put $`Q_k=q_1\cdots q_k=\operatorname{H}_P(t_k)`$. Then
``` math
\mathcal D_P=1+\sum_{k\ge1}\frac1{Q_k}.
```
For $`P=\{2,3,5\}`$ the prime powers $`2,3,4,5,8,9,16,25,27,32,\ldots`$ carry the heights $`2,6,12,60,120,360,720,3600,10800,21600,\ldots`$, so $`\mathcal D_{\{2,3,5\}}=1.7796169832947490504\ldots`$.

<div id="res:distinct-height-all" class="theorem">

**Theorem 1** (the distinct-height sums). *For every finite set $`P`$ of primes with $`|P|\ge2`$, the number $`\mathcal D_P`$ is irrational.*

</div>

Ordinary proof, given below. It was found within this project on 26 September 2026 and independently refereed by a second reader, whose five small corrections are incorporated. It has no Lean proof, so Comparator does not apply. The case $`P=\{2,3,5\}`$ is Theorem <a href="#res:distinct-height-235" data-reference-type="ref" data-reference="res:distinct-height-235">6</a>, which is checked in Lean.

For $`|P|=2`$ the theorem is contained in Theorem <a href="#res:two-prime-transcendence" data-reference-type="ref" data-reference="res:two-prime-transcendence">11</a>: $`\mathcal D_{\{p,q\}}`$ is an affine function of one Hecke–Mahler value, which is transcendental by Loxton and van der Poorten \[loxtonvdp1977, Theorem 8, p. 40\] and Bugeaud and Laurent \[bugeaudlaurent2023, Theorem 1.1\]. The new case is $`|P|\ge3`$, where every Hecke–Mahler theorem we found has a single slope.

The proof compares two tails of the series. A rational value makes every scaled tail an integer, so two tails closer than the scale are equal. The tails after $`t_k`$ and after $`t_kp^n`$, for a suitable $`n`$, are that close. Their words of primes differ only by rearranging short runs, and equality of the tails forces an integer invariant $`f`$ to agree on each run and its rearrangement. A run of two primes violates this, and a point of a torus on exactly two coordinate walls produces one.

<a id="words."></a>

#### Words.

For an infinite word $`u=u_1u_2\cdots`$ over $`P`$ put $`V(u)=\sum_{i\ge1}(u_1\cdots u_i)^{-1}`$. For a finite word $`\sigma=\sigma_1\cdots\sigma_n`$ put $`\Pi(\sigma)=\sigma_1\cdots\sigma_n`$ and
``` math
f(\sigma)=\sum_{t=1}^{n}\sigma_{t+1}\cdots\sigma_n ,
```
the term $`t=n`$ being $`1`$. Then $`f(\sigma)`$ is a positive integer and
``` math
\begin{equation}
\label{eq:word-shift}
 V(\sigma u)=\frac{f(\sigma)+V(u)}{\Pi(\sigma)}.
\end{equation}
```
Put $`x_k=V(q_{k+1}q_{k+2}\cdots)=\sum_{j>k}Q_k/Q_j`$. Every suffix of $`q_1q_2\cdots`$ contains every prime of $`P`$, in particular one larger than $`\min P`$, so its value lies in $`(0,1/(\min P-1))\subseteq(0,1)`$.

<div id="res:dp-integral-tails" class="lemma">

**Lemma 2** (integral tails). *If $`\mathcal D_P=N/K`$ with integers $`N`$ and $`K\ge1`$, then $`Kx_k`$ is an integer for every $`k\ge1`$.*

</div>

<div class="proof">

*Proof.* $`Q_k\mathcal D_P=Q_k+\sum_{i\le k}Q_k/Q_i+x_k`$, and $`Q_i`$ divides $`Q_k`$ for $`i\le k`$. So $`Kx_k=Q_kN-K\bigl(Q_k+\sum_{i\le k}Q_k/Q_i\bigr)`$. ◻

</div>

<div id="res:dp-blocks" class="lemma">

**Lemma 3** (rearranged blocks). *Let $`u=\sigma_1\sigma_2\cdots`$ and $`u'=\sigma'_1\sigma'_2\cdots`$ be infinite words, where each $`\sigma_i`$ is a nonempty finite word and $`\sigma'_i`$ is a rearrangement of it, and suppose that every suffix of $`u`$ or $`u'`$ starting at a block boundary has value in $`(0,1)`$.*

1.  *If $`V(u)=V(u')`$, then $`f(\sigma_i)=f(\sigma'_i)`$ for every $`i`$.*

2.  *If $`\sigma_i=\sigma'_i`$ for every $`i<i_0`$, then $`|V(u)-V(u')|<1/\Pi(\sigma_1\cdots\sigma_{i_0-1})`$.*

</div>

<div class="proof">

*Proof.* Let $`U_i`$ and $`U'_i`$ be the values of the suffixes starting at block $`i`$. Since $`\Pi(\sigma_i)=\Pi(\sigma'_i)`$, <a href="#eq:word-shift" data-reference-type="eqref" data-reference="eq:word-shift">[eq:word-shift]</a> gives $`\Pi(\sigma_i)(U_i-U'_i)=f(\sigma_i)-f(\sigma'_i)+U_{i+1}-U'_{i+1}`$. If $`U_i=U'_i`$, the integer $`f(\sigma_i)-f(\sigma'_i)`$ equals $`U'_{i+1}-U_{i+1}\in(-1,1)`$, so both vanish. Induction from $`U_1=V(u)=V(u')`$ proves (i). For (ii), $`V(u)-V(u')=(U_{i_0}-U'_{i_0})/\Pi(\sigma_1\cdots\sigma_{i_0-1})`$. ◻

</div>

<div id="res:dp-short" class="lemma">

**Lemma 4** (short rearrangements). *The map $`f`$ is injective on the orderings of any set of at most three distinct primes.*

</div>

<div class="proof">

*Proof.* For two primes, $`f(ab)=1+b`$. For three, $`f(\sigma_1\sigma_2\sigma_3)=1+\sigma_3(1+\sigma_2)`$. Let $`\sigma,\sigma'`$ be orderings of $`\{a,b,c\}`$ with $`f(\sigma)=f(\sigma')`$. If $`\sigma_3=\sigma'_3`$, then $`\sigma_2=\sigma'_2`$ and $`\sigma=\sigma'`$. Otherwise say $`\sigma_3=a`$ and $`\sigma'_3=b`$, so $`a(1+\sigma_2)=b(1+\sigma'_2)`$ with $`\sigma_2\in\{b,c\}`$ and $`\sigma'_2\in\{a,c\}`$. The pairs $`(b,a)`$ and $`(c,c)`$ give $`a=b`$, the pair $`(b,c)`$ gives $`b\mid a`$, and $`(c,a)`$ gives $`a\mid b`$. ◻

</div>

For four primes injectivity fails: $`f(5,7,3,2)=f(7,2,3,5)=51`$. The proof therefore looks for a run of two primes, for which $`f(ab)-f(ba)=b-a\ne0`$.

<a id="the-torus."></a>

#### The torus.

Let $`\mathbb T=\prod_{q\in P}\mathbb{R}/(\log q)\mathbb{Z}`$ and $`\Theta(s)=(s\bmod\log q)_{q\in P}`$ for $`s\in\mathbb{R}`$. For $`\theta\in\mathbb T`$ a *$`q`$-crossing* is a real $`t`$ with $`\theta_q+t\in(\log q)\mathbb{Z}`$, and $`W(\theta)`$ is the word of the primes of the positive crossings in increasing order of time. For $`\theta_k=\Theta(\log t_k)`$ the positive $`q`$-crossings are the times $`\log(q^j/t_k)`$ with $`q^j>t_k`$, so $`W(\theta_k)=q_{k+1}q_{k+2}\cdots`$, and crossings of different primes never coincide.

Let $`T_0`$ be the closure of $`\Theta(\mathbb{R})`$, a subtorus containing every $`\theta_k`$. Every forward orbit $`\{\theta+\Theta(t):t\ge t_0\}`$ with $`\theta\in T_0`$ is dense in $`T_0`$, by Kronecker’s theorem or a one-line pigeonhole argument (the companion’s Section 4.1).

In the coordinates $`\varphi_q=\theta_q/\log q`$ the torus is $`\mathbb{R}^P/\mathbb{Z}^P`$, and by Kronecker’s theorem $`T_0`$ is the image of the smallest rational subspace $`L\subseteq\mathbb{R}^P`$ containing $`\omega=(1/\log q)_{q\in P}`$. The annihilator of $`L`$ is a rational subspace spanned by the integer vectors $`c`$ with $`\sum_qc_q/\log q=0`$. If it contained a nonzero vector supported on at most two primes $`a,b`$, it would contain an integer one, and $`\log a/\log b`$ would be rational, which is false because no power of $`a`$ is a power of $`b`$. So each $`\varphi_q`$ is nonzero on $`L`$ and any two are linearly independent on $`L`$. In particular the linear form $`\theta_b-\theta_a=(\log b)\varphi_b-(\log a)\varphi_a`$ is nonzero on $`L`$, although it vanishes on the flow direction $`\omega`$.

<div id="res:dp-two-walls" class="lemma">

**Lemma 5** (two walls). *If $`|P|\ge4`$, there is $`x\in T_0`$ with $`\theta_q(x)=0`$ for exactly two primes $`q\in P`$.*

</div>

<div class="proof">

*Proof.* For $`q\ne q'`$ the function $`(u_1,u_2)\mapsto\varphi_q(u_1)\varphi_{q'}(u_2)-\varphi_q(u_2)\varphi_{q'}(u_1)`$ is a nonzero polynomial on $`L\times L`$, since $`\varphi_q`$ and $`\varphi_{q'}`$ are independent on $`L`$. Rational points are dense in $`L\times L`$, so there are rational $`u_1,u_2\in L`$ at which all these determinants are nonzero, and a change of basis of their span multiplies every determinant by the same nonzero constant. Their span is a rational plane; with a $`\mathbb{Z}`$-basis $`e_1,e_2`$ of its integer points, $`s\mapsto s_1e_1+s_2e_2`$ identifies $`\mathbb{R}^2/\mathbb{Z}^2`$ with a subtorus $`S\subseteq T_0`$. On $`S`$ the condition $`\theta_q=0`$ reads $`\langle\gamma_q,s\rangle\in\mathbb{Z}`$ with $`\gamma_q=(\varphi_q(e_1),\varphi_q(e_2))\in\mathbb{Z}^2`$, and these vectors are nonzero and pairwise non-parallel. Each set $`\{\theta_q=0\}\cap S`$ is therefore a family of finitely many disjoint parallel closed geodesics.

Two non-parallel closed geodesics of the flat torus meet. So the union of the families is a graph whose vertices are the points on at least two families, and every geodesic contains a vertex. Let $`k_v`$ be the number of families through a vertex $`v`$. A geodesic with $`r`$ vertices is cut into $`r`$ edges, and geodesics of one family are disjoint, so $`E=\sum_vk_v`$. For $`q\ne q'`$ the map $`s\mapsto(\langle\gamma_q,s\rangle,\langle\gamma_{q'},s\rangle)`$ is a covering of $`\mathbb{R}^2/\mathbb{Z}^2`$ of degree $`|\det(\gamma_q,\gamma_{q'})|`$, so each component of the complement of these two families is an open parallelogram. Each face of the arrangement lies in such a parallelogram, where the other families are straight chords, so it is an open convex polygon with at least three sides. Euler’s formula $`V-E+F=0`$ for the torus and $`2E\ge3F`$ give $`\sum_v(k_v-3)\le0`$. The origin lies on all $`|P|\ge4`$ families, so some vertex has $`k_v=2`$, and it is the required $`x`$. ◻

</div>

<div class="proof">

*Proof of Theorem <a href="#res:distinct-height-all" data-reference-type="ref" data-reference="res:distinct-height-all">1</a>.* Suppose $`\mathcal D_P=N/K`$. Fix $`p\in P`$ and an index $`k`$ with $`q_k=p`$. If $`|P|\ge4`$, fix $`a`$, $`b`$ and $`x`$ as in Lemma <a href="#res:dp-two-walls" data-reference-type="ref" data-reference="res:dp-two-walls">5</a>, and put $`\eta=\min(1/10,\ \min_{c\ne a,b}\operatorname{dist}(\theta_c(x),0))>0`$, distances being taken in $`\mathbb{R}/(\log c)\mathbb{Z}`$. Let $`\beta=\min_{q\ne p}\operatorname{dist}(\theta_{k,q},0)`$, which is positive because $`t_k`$ is a power of $`p`$. Choose $`T>0`$ such that $`2^\nu\ge K`$, where $`\nu`$ is the number of crossings of $`\theta_k`$ in $`(0,T]`$, and let $`g>0`$ be the least distance between two crossings of $`\theta_k`$ in $`[0,T+1]`$.

For $`n\ge1`$ let $`t_m=t_kp^n`$, so that $`\theta_m=\theta_k+\Theta(n\log p)`$. Write $`\delta_p=0`$ and $`\delta_q=n\log p-m_q\log q`$ for $`q\ne p`$, with $`m_q`$ the nearest integer to $`n\log p/\log q`$; then $`\Theta(n\log p)`$ has coordinates $`\delta_q\bmod\log q`$. By Dirichlet’s simultaneous approximation theorem we may choose $`n`$ with
``` math
\varepsilon=\max_q|\delta_q|
 <\min\Bigl(\beta,\ \frac g2,\ \frac{\log2}{2|P|},\ \frac\eta8\Bigr),
```
the last term only when $`|P|\ge4`$. Then every $`m_q\ge1`$, and the numbers $`\delta_q`$ are pairwise distinct because $`p^n`$ and the $`q^{m_q}`$ are pairwise distinct.

*Chains.* The $`q`$-crossings of $`\theta_m`$ are those of $`\theta_k`$ shifted by $`-\delta_q`$. Every $`q`$-crossing $`s`$ of $`\theta_k`$ with $`q\ne p`$ has $`|s|\ge\beta>|\delta_q|`$, so the shift preserves signs and matches the positive $`q`$-crossings of $`\theta_k`$ and $`\theta_m`$ in order. Cut the positive crossings of $`\theta_k`$ wherever two consecutive ones are more than $`2\varepsilon`$ apart, and call the pieces *chains*. Crossings in different chains are more than $`2\varepsilon`$ apart and their shifts differ by less than $`2\varepsilon`$, so they keep their order. Hence $`W(\theta_m)`$ is the concatenation of the chains of $`W(\theta_k)`$ in the same order, each rearranged. Two crossings of one prime are at least $`\log2`$ apart, and any $`|P|+1`$ consecutive crossings of one chain lie within $`2\varepsilon|P|<\log2`$; they would belong to $`|P|+1`$ distinct primes, which is impossible. So a chain has at most $`|P|`$ crossings, and they belong to distinct primes.

*Equal tails.* A chain meeting $`(0,T]`$ is a single crossing, since the crossings in $`[0,T+1]`$ are at least $`g>2\varepsilon`$ apart and a crossing beyond $`T+1`$ is more than $`1`$ away. So the first $`\nu`$ blocks of the two chain decompositions agree, and Lemma <a href="#res:dp-blocks" data-reference-type="ref" data-reference="res:dp-blocks">3</a>(ii) gives $`|x_k-x_m|<2^{-\nu}\le1/K`$. By Lemma <a href="#res:dp-integral-tails" data-reference-type="ref" data-reference="res:dp-integral-tails">2</a>, $`Kx_k`$ and $`Kx_m`$ are integers less than $`1`$ apart, so $`x_k=x_m`$. Lemma <a href="#res:dp-blocks" data-reference-type="ref" data-reference="res:dp-blocks">3</a>(i) then gives $`f(C)=f(C')`$ for every chain $`C`$ of $`W(\theta_k)`$ and its rearrangement $`C'`$ in $`W(\theta_m)`$.

*Case $`|P|\le3`$.* Take $`q\ne p`$, and suppose $`\delta_q>0`$; the other sign is symmetric. The positive $`p`$-crossings of $`\theta_k`$ are the numbers $`j\log p`$ with $`j\ge1`$, and its positive $`q`$-crossings are the numbers $`i\log q-\log t_k`$ with $`i`$ large. Since $`\log p/\log q`$ is irrational, the differences $`j\log p-i\log q+\log t_k`$ with $`i,j`$ large are dense in $`\mathbb{R}`$. So some $`p`$-crossing $`j\log p`$ and $`q`$-crossing $`s`$ of $`\theta_k`$ satisfy $`s-\delta_q<j\log p<s`$. Their shifts reverse their order, so they lie in one chain, which is genuinely rearranged in $`W(\theta_m)`$. It consists of at most three distinct primes, and Lemma <a href="#res:dp-short" data-reference-type="ref" data-reference="res:dp-short">4</a> gives $`f(C)\ne f(C')`$, a contradiction.

*Case $`|P|\ge4`$.* Put $`D=\delta_a-\delta_b`$, so $`0<|D|<2\varepsilon`$. Since $`\theta_b-\theta_a`$ is a nonzero linear form on $`L`$, there is $`y\in L`$ with $`|\theta_q(y)|<\eta/8`$ for every $`q`$ and $`\theta_b(y)-\theta_a(y)`$ strictly between $`0`$ and $`D`$. Let $`z`$ be the point $`x+y+\Theta(-\eta/2)`$ of $`T_0`$, with $`y`$ read in the torus. The $`a`$-crossings of $`z`$ are the times $`\eta/2-\theta_a(y)+j\log a`$, so exactly one of them, $`\tau_a`$, lies in $`[-\eta/4,5\eta/4]`$, and it lies in $`(\eta/4,3\eta/4)`$; the same holds for $`b`$, and $`\tau_a-\tau_b`$ lies strictly between $`0`$ and $`D`$. Every $`c`$-crossing of $`z`$ with $`c\ne a,b`$ is at distance at least $`7\eta/8`$ from $`\eta/2`$, so it lies outside $`[-\eta/4,5\eta/4]`$. Let $`U`$ be the set of $`\theta\in T_0`$ with exactly one $`a`$-crossing and one $`b`$-crossing in $`[-\eta/4,5\eta/4]`$, both in $`(\eta/4,3\eta/4)`$, with their difference $`\tau_a-\tau_b`$ strictly between $`0`$ and $`D`$, and with no other crossing in $`[-\eta/4,5\eta/4]`$. Each condition is open, so $`U`$ is an open subset of $`T_0`$ containing $`z`$, and by density $`\theta_k+\Theta(t^*)\in U`$ for some $`t^*>T+2`$.

Then $`\theta_k`$ has an $`a`$-crossing $`t^*+\tau_a`$ and a $`b`$-crossing $`t^*+\tau_b`$ less than $`|D|<2\varepsilon`$ apart, and every other crossing of $`\theta_k`$ is more than $`\eta/2>4\varepsilon`$ away from both. So these two crossings form a chain $`C`$. Their shifts differ by $`(\tau_a-\tau_b)-D`$, whose sign is opposite to that of $`\tau_a-\tau_b`$, so $`C'`$ is $`C`$ reversed. But $`f(ab)-f(ba)=b-a\ne0`$, a contradiction. ◻

</div>

The companion’s Section 11.1 compares $`\mathcal D_P`$, written as a Cantor series, with the criteria of Erdős–Straus \[erdosstraus1974\], Hančl–Tijdeman \[hancltijdeman2004\] and Diananda and Oppenheim \[dianandaoppenheim1955\], none of which decides it.

<a id="sec:distinct-235"></a>

## The case $`\{2,3,5\}`$, checked in Lean

<div id="res:distinct-height-235" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L689">Lean</a></p>

**Theorem 6** (the distinct-height sum for $`\{2,3,5\}`$). *The number $`\mathcal D_{\{2,3,5\}}`$ is irrational.*

</div>

Checked in Lean for the sum exactly as defined in the introduction ([Lean proof](https://github.com/wcook04/plectis-erdos/blob/5154f4c46fa5d5ab2cff8df857a0b10f310cbeeb/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L689)); Comparator has not yet been run on it. The constants of its proof, the five affine maps, their bounds and the gaps between their images, are also recomputed in exact arithmetic by the [distinct-height programs](https://github.com/wcook04/plectis-erdos/tree/10178c4df40cb27d83b5ebb1ec337dd588b82998/research/experiments/erdos269/distinct_height).

The Lean proof takes a different route (companion, Sections 4.2 and 4.3): each dyadic block acts on the normalised tail by one of five affine maps with disjoint images, so a tail determines every later block, and a rational value would make the blocks eventually periodic, which the powers of $`3`$ prevent. With an automaton recording how recently each prime appeared, the same method proves every set of three primes at most $`31`$ by exact computation, and it fails for $`\{2,3,5,7\}`$, where two words of blocks have the same affine map (companion, Sections 4.4 and 4.5).

<a id="sec:rank"></a>

# Nonsingular minors of every order

<div id="res:infinite-rank" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L22">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-infinite-rank-comparator">Comparator</a></p>

**Theorem 7** (no finite separation of the kernel). *Let $`p,q,r`$ be primes with $`p\ne q`$, $`p\ne r`$ and $`q\ne r`$. For every $`n\ge0`$ there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$ such that, for every $`k\ge0`$,
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
The positive factors do not affect whether a minor vanishes; $`C`$ records only whether $`x_i+y_j\ge1`$. Distinct primes make $`\log_r p`$ and $`\log_r q`$ irrational, so each fractional-part orbit is dense in $`[0,1]`$. The row and column indices are independent choices; no density of a single orbit of pairs is required. For $`n\ge1`$, choose distinct rows with $`0<x_{I(0)}<\cdots<x_{I(n-1)}<1`$. We choose each column so that its entries change from $`1`$ to $`c`$ at a different selected row. Writing $`s_b=1-y_{J(b)}`$, density of $`(y_j)`$ lets us choose

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
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/PaperR7ModularMinors.lean#L133">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-admissible-modular-minors-comparator">Comparator</a></p>

**Corollary 8** (the same minors modulo integers coprime to $`30`$). *For $`(p,q,r)=(2,3,5)`$ and every $`n\ge1`$, there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$, chosen independently of $`B`$ and $`k`$, such that for every $`B\ge2`$ coprime to $`30`$ and every $`k\ge0`$, the selected $`n\times n`$ kernel matrix has unit determinant over $`\mathbb Z/B\mathbb Z`$, with each reciprocal prime power interpreted by its modular inverse.*

</div>

<div class="proof">

*Proof.* Choose the maps from Theorem <a href="#res:infinite-rank" data-reference-type="ref" data-reference="res:infinite-rank">7</a>. Every row and column factor is a unit modulo $`B`$. The normalised determinant is $`5^{-1}(-4/5)^{n-1}`$, also a unit. ◻

</div>

The modulus may be composite, for example $`49`$ or $`77`$. Coprimality with $`30`$ makes both the reciprocal entries and the determinant units: the latter introduces only a power of $`4`$ in its numerator.

<div id="res:rank" class="example">

**Example 9**. For $`(p,q,r)=(2,3,5)`$, the leading two-by-two determinant is $`-1/15`$: its four entries are $`1,1/6,1/2,1/60`$, so it equals $`1/60-1/12`$.

</div>

<a id="the-indices-must-be-selected."></a>

#### The indices must be selected.

The leading $`4\times4`$ block at $`\{2,3,5\}`$ is singular:
``` math
\operatorname{K}(3,j,0)=\frac1{120}\operatorname{K}(0,j,0)\qquad(0\le j<4).
```
These equalities follow by evaluating the height at $`3^j`$ and $`8\cdot3^j`$. But at $`j=4`$, $`\operatorname{K}(3,4,0)-\operatorname{K}(0,4,0)/120=-1/19440000`$. Thus the leading minors do not supply the arbitrary-order theorem.

<div id="res:finite-cut-rank" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/PaperR7FiniteCutRank.lean#L182">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-finite-cut-rank-comparator">Comparator</a></p>

**Proposition 10** (rank of a matrix of threshold columns). *Let $`m\ge1`$ and let $`c`$ lie in a field with $`c\ne 0,1`$. For $`0\le k\le m`$ write $`v_k`$ for the length-$`m`$ column with a $`1`$ in each of the first $`k`$ coordinates and $`c`$ thereafter. A matrix whose distinct columns are $`v_k`$ for $`k`$ in a nonempty set $`E`$ has rank $`|E|-\mathbf 1_{\{0,m\}\subseteq E}`$.*

</div>

The correction accounts for the two constant columns: $`v_0=c v_m`$. There is no other dependence among distinct threshold columns.

<div class="proof">

*Proof.* List $`E=\{k_1<\cdots<k_t\}`$. The $`t-1`$ differences $`v_{k_{j+1}}-v_{k_j}=(1-c)\mathbf 1_{\{k_j,\ldots,k_{j+1}-1\}}`$ have disjoint nonempty supports, hence are linearly independent. If $`k_1>0`$ or $`k_t<m`$, their union misses a coordinate where $`v_{k_1}`$ is nonzero, so the rank is $`t`$. If $`k_1=0`$ and $`k_t=m`$, then $`v_0=c\,\mathbf 1`$ lies in the span of the differences (their sum is $`(1-c)\mathbf 1`$), so the rank is $`t-1`$. ◻

</div>

The restrictions $`c\ne0,1`$ exclude a zero column or identical columns; they hold for $`c=1/r`$ over $`\mathbb Q`$. In one fixed layer $`k`$, ordering the sampled row phases puts every column in the stated form. The formula therefore determines the rank of each nonempty rectangular sample. For fixed row and column indices this rank is independent of $`k`$. Section 5 of the companion paper, *The Three-Prime Running LCM: Kernel Rank and Tail Arithmetic*, gives the exact rational comparisons.

<a id="exact-rank-is-not-an-approximation-obstruction."></a>

#### Exact rank is not an approximation obstruction.

Truncating the original kernel to $`i<N`$ gives a sum of $`N`$ separated terms. The bound $`\operatorname{H}(x)>x^3/(pqr)`$ makes the truncation error tend to zero both uniformly and in $`\ell^1(\mathbb N^3)`$. By contrast, the rescaled matrix in the rank proof has uniform distance $`(1-1/r)/2`$ from the matrices of finite rank. Rescaling preserves exact rank but removes the decay responsible for the first approximation. The companion proves both assertions, including the distinction between finite restrictions and the full infinite matrix, in Section 5.1.

<a id="sec:two-prime"></a>

# The two-prime comparison

Fan’s post of 26 June 2026 gives the repeated two-prime factorisation, its quadratic expression in one Hecke–Mahler value and its transcendence conclusion \[fan2026comment\]. Counting the contributions at powers of each prime also gives the affine formula for the distinct-height sum below. The calculation fixes the normalisations and distinguishes the two sums.

<div id="res:two-prime-transcendence" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-two-prime-transcendence">Lean†</a></p>

**Theorem 11** (both two-prime sums). *<span id="res:two-prime-repeated-transcendence" label="res:two-prime-repeated-transcendence"></span> Let $`p<q`$ be distinct primes. Put $`\theta=\log p/\log q`$ and $`A=\sum_{n\ge0}p^{-n}q^{-\lfloor n\theta\rfloor}`$. Let $`\mathcal R_{p,q}`$ sum the reciprocal running LCM at every positive $`\{p,q\}`$-smooth integer, and let $`\mathcal D_{p,q}`$ count each distinct running LCM once. Then
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

<div class="proof">

*Proof.* Set $`x=1/p`$, $`y=1/q`$, $`m_n=\lfloor n\theta\rfloor`$ and $`\delta_n=m_{n+1}-m_n`$. Unique factorisation makes $`\theta`$ irrational, and $`0<\theta<1`$ gives $`\delta_n\in\{0,1\}`$. The initial value and the positive powers of $`p`$ contribute $`A=\sum_{n\ge0}x^ny^{m_n}`$. There is one $`q`$-power strictly between $`p^n`$ and $`p^{n+1}`$ exactly when $`\delta_n=1`$, so the positive powers of $`q`$ contribute
``` math
B=\sum_{n\ge0}\delta_nx^ny^{m_n+1},\qquad \mathcal D_{p,q}=A+B.
```
Since $`0<x,y<1`$, these series converge absolutely. The identity $`y^{m_{n+1}}-y^{m_n}=\delta_ny^{m_n}(y-1)`$ and an index shift in $`A`$ give $`A-1-xA=x(y-1)B/y`$. Therefore
``` math
B=\frac{p-(p-1)A}{q-1}.
```
At $`p^iq^j`$ the height is $`p^{i+\lfloor j/\theta\rfloor}q^{j+m_i}`$, hence
``` math
\mathcal R_{p,q}
 =A\sum_{j\ge0}y^jx^{\lfloor j/\theta\rfloor}=A(1+B).
```
For the last equality, each $`j\ge1`$ corresponds to $`n=\lfloor j/\theta\rfloor`$ with $`m_n=j-1`$ and $`\delta_n=1`$. These identities prove <a href="#eq:two-prime-affine" data-reference-type="eqref" data-reference="eq:two-prime-affine">[eq:two-prime-affine]</a>.

For the Hecke–Mahler series $`F_\theta(x,y)=\sum_{n\ge1}\sum_{k=1}^{m_n}x^ny^k`$, geometric summation gives
``` math
\begin{equation}
\label{eq:hecke-mahler-boundary}
 A=\frac1{1-x}-\frac{1-y}{y}F_\theta(x,y).
\end{equation}
```
Bugeaud and Laurent’s theorem \[bugeaudlaurent2023, Theorem 1.1\] applies with intercept $`\rho=0`$, $`\beta=x`$ and $`\alpha=y`$: the slope $`\theta`$ is irrational and lies in $`(0,1)`$, $`x`$ and $`y`$ are nonzero algebraic numbers, $`|x|<1`$ and $`|xy^\theta|=p^{-2}<1`$. Hence $`F_\theta(x,y)`$ is transcendental; this case $`\rho=0`$ is due to Loxton and van der Poorten \[loxtonvdp1977, Theorem 8, p. 40\]. Thus $`A`$ is transcendental. The displayed affine and quadratic polynomials are nonconstant, so an algebraic value of either would force $`A`$ to be algebraic. ◻

</div>

The same calculation applies to the monoid generated by any coprime integers $`1<p<q`$, such as $`4,9`$, but need not describe all integers supported on their prime factors. The companion’s Section 3 gives this extension and the failure for $`4,8`$.

The distinct-height sums for every finite set of primes were treated in Section <a href="#sec:distinct" data-reference-type="ref" data-reference="sec:distinct">2</a>. The tail argument of the next two sections starts again from the running LCM and retains every multiplicity; it does not use the rank theorem.

<a id="sec:lcm"></a>

# The recurrence for the repeated sum

<span id="sec:cells" label="sec:cells"></span><span id="sec:fibre" label="sec:fibre"></span><span id="sec:shell" label="sec:shell"></span> <span id="sec:actual-orbit" label="sec:actual-orbit"></span>

<div id="res:lcm" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L49">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-lcm-comparator">Comparator</a></p>

**Proposition 12** (the running least common multiple). *Let $`p,q,r`$ be pairwise distinct primes and $`x\ge1`$. Then the running LCM equals the three-prime height: $`\operatorname{L}(x)=\operatorname{H}(x)`$.*

</div>

<div class="proof">

*Proof.* Every smooth $`n\le x`$ has prime exponents bounded by the corresponding integer logarithms, so $`n\mid\operatorname{H}(x)`$. Conversely the three maximal pure powers occur among those smooth numbers; their product divides the running LCM because they are pairwise coprime. ◻

</div>

The inequalities $`x/p<p^{\lfloor\log_p x\rfloor}\le x`$ for each of the three primes also give
``` math
\begin{equation}
\label{res:cube}
 x^3/(pqr)<\operatorname{H}(x)\le x^3.
\end{equation}
```

<div id="res:cell" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-cell">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-cell-comparator">Comparator</a></p>

**Proposition 13** (cells and jumps). *The running LCM is constant when the three integer logarithms are constant. A jump in exactly one logarithm multiplies it by the corresponding prime. The first $`n`$ positive powers of each prime, together with $`1`$, form $`3n+1`$ distinct points.*

</div>

<div class="proof">

*Proof.* The first two claims follow from the height formula. Positive powers of different primes cannot coincide, by unique factorisation, and none is $`1`$. ◻

</div>

For $`(p,q,r)=(2,3,5)`$ the smooth numbers $`5`$ and $`6`$ share the height $`60`$, as noted in the introduction. The next identity retains such multiplicities when equal heights are grouped.

<div id="res:fibre-prop" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L407">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-fibre-prop-comparator">Comparator</a></p>

**Proposition 14** (grouping terms with the same height). *For a finite exponent box $`\mathcal B`$, set $`F(H)=\{(i,j,k)\in\mathcal B:\operatorname{H}(p^iq^jr^k)=H\}`$. Then
``` math
\begin{equation}
\label{res:fibre}
 \sum_{(i,j,k)\in\mathcal B}\operatorname{K}(i,j,k)=\sum_H\frac{\#F(H)}H.
\end{equation}
```*

</div>

<div class="proof">

*Proof.* Each term in $`F(H)`$ equals $`1/H`$. The multiplicities remain present in every subsequent infinite sum. ◻

</div>

From now on let $`P=\{2,3,5\}`$ and $`S=\mathcal R_P`$. For $`a\ge0`$ define
``` math
s_a=\sum_{\substack{x\text{ smooth}\\2^a\le x<2^{a+1}}}\frac1{\operatorname{H}(x)},
 \quad T_a=\sum_{j\ge0}s_{a+j},\quad
 h_a=\frac{\operatorname{H}(2^a)}2,\quad X_a=h_aT_a.
```
The half-height $`h_a`$ clears the finite prefix: for $`a\ge1`$ and smooth $`x<2^a`$, the exponent of $`2`$ in $`\operatorname{H}(x)`$ is at most $`a-1`$, so $`\operatorname{H}(x)\mid\operatorname{H}(2^a)/2`$. This is why we omit the final factor $`2`$. Here $`h_0=1/2`$; only for $`a\ge1`$ is $`h_a`$ an integer. Define
``` math
\begin{equation}
\label{eq:actual-digit}
 b_a=\frac{\operatorname{H}(2^{a+1})}{\operatorname{H}(2^a)},\qquad
 m_a=\sum_{\substack{x\text{ smooth}\\2^a\le x<2^{a+1}}}
       \frac{\operatorname{H}(2^{a+1})}{2\operatorname{H}(x)}.
\end{equation}
```

<div id="res:dyadic-alphabet" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/PaperCompleteR20/DyadicAlphabetWhole.lean#L19">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-dyadic-alphabet-comparator">Comparator</a></p>

**Lemma 15** (integer coefficients and four possible bases). *For every $`a\ge0`$, $`m_a`$ is a positive integer and $`b_a\in\{2,6,10,30\}`$. The word “numerator” does not impose the positional-digit restriction $`m_a<b_a`$; that restriction need not hold.*

</div>

<div class="proof">

*Proof.* If $`x<2^{a+1}`$, the exponent of $`2`$ in $`\operatorname{H}(x)`$ is at most $`a`$, while the other exponents are bounded by those of $`\operatorname{H}(2^{a+1})`$. Hence $`2\operatorname{H}(x)\mid\operatorname{H}(2^{a+1})`$. Each summand is an integer, and the shell contains $`2^a`$. Between consecutive powers of $`2`$ there is at most one power of $`3`$ and at most one power of $`5`$: successive powers of either odd prime have ratio greater than two. These factors, when present, and the factor $`2`$ at the right endpoint give the four possible bases. ◻

</div>

In the shell $`[2,4)`$ the terms $`1/2`$ and $`1/6`$, with $`h_2=b_1=6`$, give $`m_1=4`$ and the recurrence $`X_2=6X_1-4`$. The shell $`[16,32)`$ shows why these numerators are not positional digits: $`m_4=65>b_4=30`$. The companion computes the carried digits separately.

<div id="res:actual-orbit" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/PaperR7SeriesIdentification.lean#L168">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-actual-orbit-comparator">Comparator</a></p>

**Proposition 16** (the tail recurrence and a quadratic bound). *The series defining $`S,T_a`$ converge. For every $`a\ge0`$,
``` math
X_{a+1}=b_aX_a-m_a,\qquad
 0<X_a\le\frac{8640}{343}(a+1)^2<90(a+1)^2.
```
For every integer $`B\ge1`$, either some $`BX_a`$ is integral and all later states are integral, or $`\operatorname{dist}(BX_a,\mathbb Z)\ge1/31`$ at arbitrarily large indices.*

</div>

<div class="proof">

*Proof.* For each pair of exponents of $`3`$ and $`5`$, at most one exponent of $`2`$ places the smooth integer in $`[2^a,2^{a+1})`$. The two odd-prime exponents lie between $`0`$ and $`a`$, giving at most $`(a+1)^2`$ terms. By <a href="#res:cube" data-reference-type="eqref" data-reference="res:cube">[res:cube]</a>, $`s_a\le30(a+1)^2/8^a`$. Since $`h_a\le8^a/2`$ and $`a+j+1\le(a+1)(j+1)`$ for $`a,j\ge0`$, summing the later shells gives
``` math
X_a\le15(a+1)^2\sum_{j\ge0}\frac{(j+1)^2}{8^j}
      =\frac{8640}{343}(a+1)^2.
```
This proves convergence and the bound. Splitting the first shell gives the recurrence because $`m_a=h_{a+1}s_a`$ and $`h_{a+1}=b_ah_a`$. If all sufficiently late distances are strictly below $`1/31`$, write $`BX_a=z_a+e_a`$ with $`z_a\in\mathbb Z`$ and $`|e_a|<1/31`$. Since $`Bm_a`$ is integral, $`e_{a+1}-b_ae_a`$ is an integer of absolute value less than $`(1+b_a)/31\le1`$, so $`e_{a+1}=b_ae_a`$. The lower bound $`b_a\ge2`$ forces this bounded error to vanish; integrality then propagates by the recurrence. ◻

</div>

The identity $`S/2=\sum_{a\ge0}m_a/(b_0\cdots b_a)`$ places the recurrence in the setting of Cantor series. The classical criteria of Erdős–Straus \[erdosstraus1974, Theorem 2.1\] and Hančl–Tijdeman \[hancltijdeman2004, Theorem 3.1\] require $`m_a/(b_{a-1}b_a)\to0`$. That hypothesis fails here: the numerators grow quadratically while the bases are bounded. The companion’s Section 7 proves the growth assertion and gives the precise carry conditions. The argument below instead uses the recurrence and the proved bound $`90B(a+1)^2`$ directly.

<div id="res:denominator-reduction" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/PaperR7RationalBridge.lean#L80">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-denominator-reduction-comparator">Comparator</a></p>

**Theorem 17** (rationality gives positive integer tails). *If $`S=A/D`$ in lowest terms, where $`D=2^u3^v5^wB`$ and $`\gcd(B,30)=1`$, then for every $`a\ge a_0=u+1+2v+3w`$,
``` math
d_a=BX_a\in\mathbb Z_{>0},\qquad
 d_{a+1}=b_ad_a-Bm_a,\qquad d_a\le90B(a+1)^2.
```*

</div>

<div class="proof">

*Proof.* For $`a\ge1`$, every $`\operatorname{H}(x)`$ with $`x<2^a`$ divides $`h_a`$. Subtracting the finite prefix therefore gives
``` math
\begin{equation}
\label{eq:prefix-lattice}
 X_a=h_aS-\sum_{\substack{x\text{ smooth}\\x<2^a}}
                  \frac{h_a}{\operatorname{H}(x)},
 \qquad
 \sum_{\substack{x\text{ smooth}\\x<2^a}}
                  \frac{h_a}{\operatorname{H}(x)}\in\mathbb Z.
\end{equation}
```
The exponent of $`2`$ in $`h_a`$ is $`a-1`$. Moreover $`a\ge2v`$ gives $`2^a\ge3^v`$, and $`a\ge3w`$ gives $`2^a\ge5^w`$. Thus $`2^u3^v5^w\mid h_a`$ after the stated onset, and $`BX_a`$ differs from $`h_aA/(2^u3^v5^w)`$ by an integer and is therefore integral. Positivity, the recurrence and the bound follow from Proposition <a href="#res:actual-orbit" data-reference-type="ref" data-reference="res:actual-orbit">16</a>. ◻

</div>

Every positive denominator splits in the required way: $`B`$ is what remains after removing all factors $`2`$, $`3`$ and $`5`$. For example, a hypothetical reduced denominator $`2^3 3^2 5\cdot7`$ would give $`B=7`$; the next result gives the first integral $`7X_a`$ at $`a=4`$, whereas the sufficient bound above gives $`a_0=11`$.

<div id="res:exact-onset" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-exact-onset">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-exact-onset-comparator">Comparator</a></p>

**Corollary 18** (the first index at which the denominator clears). *Under the same lowest-terms hypothesis, put $`M=2^u3^v5^w`$ and let $`\operatorname{den}`$ denote the positive reduced denominator. For $`a\ge1`$,
``` math
\operatorname{den}(BX_a)=\frac{M}{\gcd(M,h_a)}.
```
Consequently $`BX_a`$ is integral exactly when $`2^a\ge\max(2^{u+1},3^v,5^w)`$. The first such $`a`$ can be found by integer comparisons, without logarithmic rounding.*

</div>

<div class="proof">

*Proof.* By <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a>, $`BX_a`$ differs from $`h_aA/M`$ by an integer. Since $`\gcd(A,M)=1`$, reducing that fraction gives the displayed denominator. The three divisibility conditions for $`h_a`$ are precisely the three inequalities stated above. ◻

</div>

The companion’s Section 4.6 shows where the dyadic and two-tail arguments stop for the repeated sum, whose scaled tails are unbounded.

The comparison does close on part of the catalogue series. For $`p\in P`$ let $`E_p=\sum_{\alpha\ge0}\operatorname{L}(p^\alpha)^{-1}`$ be the sub-sum of $`\mathcal R_P`$ over the powers of $`p`$. Then $`\mathcal D_P=\sum_{q\in P}E_q-(|P|-1)`$, and for two primes $`\mathcal R_{\{p,q\}}=E_pE_q`$, which is the factorisation in the proof of Theorem <a href="#res:two-prime-transcendence" data-reference-type="ref" data-reference="res:two-prime-transcendence">11</a>.

<div id="res:single-prime-subsums" class="theorem">

**Theorem 19** (the single-prime sub-sums). *For every finite set $`P`$ of primes with $`|P|\ge2`$ and every $`p\in P`$, the number $`E_p`$ is irrational.*

</div>

Ordinary proof in the companion, Section 4.6. It was found within this project on 26 September 2026 and independently refereed by a second reader; it has no Lean proof, so Comparator does not apply. For $`|P|=2`$, $`E_p`$ is an affine function of the Hecke–Mahler value in the proof of Theorem <a href="#res:two-prime-transcendence" data-reference-type="ref" data-reference="res:two-prime-transcendence">11</a> and is transcendental; the new case is $`|P|\ge3`$, for which we have not searched the literature.

The proof compares the tails after $`p^\alpha`$ and $`p^{\alpha+n}`$ as in Section <a href="#sec:distinct" data-reference-type="ref" data-reference="sec:distinct">2</a>, with the invariant replaced by the product of the primes that follow $`p`$ in a run, and takes the run at a passage of the flow near the origin of the torus; no two-wall lemma is needed. For $`\mathcal R_P`$ itself the comparison fails at its first step: between the two scales the tail of $`\mathcal R_P`$ gains the early terms of every ray $`p^\alpha w`$, with $`w`$ a $`(P\smallsetminus\{p\})`$-smooth integer, that enters there, and $`E_p`$ is the case $`w=1`$, where nothing enters.

<a id="sec:escape"></a>

# A window test and the remaining arithmetic

<span id="sec:open" label="sec:open"></span> Two steps of the recurrence already show the finite data we need:
``` math
X_{\ell+2}=b_{\ell+1}b_\ell X_\ell
             -(b_{\ell+1}m_\ell+m_{\ell+1}).
```
If $`BX_\ell`$ is an integer, this identity determines the residue of $`BX_{\ell+2}`$ modulo the product of the two bases. We will compare the least positive representative of that residue with the upper bound for the endpoint tail.

For a window starting at $`\ell\ge0`$ and having $`h\ge0`$ steps, define its product of bases and accumulated numerator from <a href="#eq:actual-digit" data-reference-type="eqref" data-reference="eq:actual-digit">[eq:actual-digit]</a> by
``` math
W_{\ell,0}=1,\quad F_{\ell,0}=0,\qquad
 W_{\ell,h+1}=b_{\ell+h}W_{\ell,h},\quad
 F_{\ell,h+1}=b_{\ell+h}F_{\ell,h}+m_{\ell+h}.
```
Induction on $`h`$ gives
``` math
\begin{equation}
\label{eq:actual-tail}
 X_{\ell+h}=W_{\ell,h}X_\ell-F_{\ell,h}.
\end{equation}
```
For integers $`W\ge1`$ and $`t`$, define $`\operatorname{lpr}_W(t)=1+((t-1)\bmod W)`$, using a remainder in $`\{0,\ldots,W-1\}`$. Thus a zero residue is represented by $`W`$, not $`0`$. Throughout this section use the upper bound
``` math
\begin{equation}
\label{eq:actual-bound}
 K(B,a)=90B(a+1)^2.
\end{equation}
```

<div id="res:consumer" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L138">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-consumer-comparator">Comparator</a></p>

**Lemma 20** (least positive residues). *If $`d`$ is a positive integer with $`d\le K`$ and $`d\equiv -BF\pmod W`$, where $`W\ge1`$, then $`\operatorname{lpr}_W(-BF)\le K`$.*

</div>

<div class="proof">

*Proof.* Every positive representative of the residue is at least its least positive representative, so $`\operatorname{lpr}_W(-BF)\le d\le K`$. ◻

</div>

For example, the window starting at $`\ell=1`$ with length $`6`$ has $`W_{1,6}=648000`$ and $`F_{1,6}=524431`$. At $`B=1`$ its least positive residue is $`123569`$, exceeding $`K(1,7)=5760`$. This rules out an integral $`X_1`$, but not a rational denominator that would clear only at a later index. The theorem therefore asks for windows beyond every prescribed starting index, as well as for every eligible denominator.

<div id="res:windowconsumer" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos269/PaperR7WindowResults.lean#L51">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/f3f86ba3c00e3dc0345ce7cb605c8d10b2d42a74/evidence/erdos-269-three-prime-running-lcm.md#res-windowconsumer-comparator">Comparator</a></p>

**Theorem 21** (a residue criterion for irrationality). *The number $`S`$ is irrational if and only if
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

*Proof.* Assume <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a> and suppose $`S`$ is rational. Theorem <a href="#res:denominator-reduction" data-reference-type="ref" data-reference="res:denominator-reduction">17</a> supplies a positive integral carry $`d_a=BX_a`$ after its onset. Choose a window in <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a> beyond that onset. Equation <a href="#eq:actual-tail" data-reference-type="eqref" data-reference="eq:actual-tail">[eq:actual-tail]</a> gives $`d_{\ell+h}\equiv-BF_{\ell,h}\pmod{W_{\ell,h}}`$, contradicting Lemma <a href="#res:consumer" data-reference-type="ref" data-reference="res:consumer">20</a> and the upper bound.

Conversely, let $`S`$ be irrational and fix $`B,\ell\ge1`$. Equation <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a> makes $`BX_\ell`$ nonintegral. Put $`\delta=\lceil BX_\ell\rceil-BX_\ell\in(0,1)`$. Since $`W_{\ell,h}\ge2^h`$ and $`X_{\ell+h}=O((\ell+h+1)^2)`$, for all sufficiently large $`h`$ the number $`\delta+BX_{\ell+h}/W_{\ell,h}`$ lies in $`(0,1)`$. The window identity shows that the integer $`\lceil BX_\ell\rceil W_{\ell,h}-BF_{\ell,h}`$ lies strictly between $`0`$ and $`W_{\ell,h}`$ and is congruent to $`-BF_{\ell,h}`$. Hence
``` math
\operatorname{lpr}_{W_{\ell,h}}(-BF_{\ell,h})
 =\delta W_{\ell,h}+BX_{\ell+h}.
```
Its exponentially growing first term eventually exceeds $`K(B,\ell+h)`$. This proves <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>, in fact from each fixed start. ◻

</div>

The proved bound $`90B(a+1)^2`$ controls every positive integral $`BX_a`$ that rationality would force. Polynomial growth alone does not suffice: the zero bound would make the residue inequality automatic. The companion, Section 8, treats smaller and more general bounds. No finite search establishes the unbounded quantifiers in <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>.

The remaining task has the following three equivalent formulations.

<div class="problem">

**Problem 22** (the repeated three-prime target). Prove that $`S=\mathcal R_{\{2,3,5\}}`$ is irrational.

</div>

<div id="prob:tails269" class="problem">

**Problem 23** (no reduced tail is an integer). Prove that for every $`a\ge1`$ and every integer $`B\ge1`$ coprime to $`30`$,
``` math
\begin{equation}
\label{eq:tail-nonintegrality}
 BX_a\notin\mathbb Z.
\end{equation}
```

</div>

<div id="prob:producer" class="problem">

**Problem 24** (residue inequalities after every starting index). Prove <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>.

</div>

Indeed, one integral scaled tail makes $`S`$ rational by <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a>, whereas denominator clearing gives such tails from a rational $`S`$. Theorem <a href="#res:windowconsumer" data-reference-type="ref" data-reference="res:windowconsumer">21</a> supplies the third equivalence. These arithmetic assertions remain unproved. The companion’s finite certificates (Section 9) and its comparisons with other approaches (Section 10) are supplementary; the argument here does not rely on them.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="proof-sources."></a>

#### Proof sources.

Theorem <a href="#res:two-prime-transcendence" data-reference-type="ref" data-reference="res:two-prime-transcendence">11</a> uses the transcendence theorem of Bugeaud and Laurent, which its Lean proof assumes. Fan’s post of 26 June 2026 on the erdosproblems.com forum has priority for the two-prime deduction \[fan2026comment\]. Theorem <a href="#res:distinct-height-all" data-reference-type="ref" data-reference="res:distinct-height-all">1</a> and Lemmas <a href="#res:dp-integral-tails" data-reference-type="ref" data-reference="res:dp-integral-tails">2</a>–<a href="#res:dp-two-walls" data-reference-type="ref" data-reference="res:dp-two-walls">5</a> have the ordinary proofs given in Section <a href="#sec:distinct" data-reference-type="ref" data-reference="sec:distinct">2</a> and no Lean proofs; a formal proof would need Kronecker’s theorem on the closure of a line in a torus and the Euler characteristic count of Lemma <a href="#res:dp-two-walls" data-reference-type="ref" data-reference="res:dp-two-walls">5</a>. The proof of Theorem <a href="#res:distinct-height-all" data-reference-type="ref" data-reference="res:distinct-height-all">1</a> was found by an AI agent on 26 September 2026 and refereed by a second AI agent working independently, who re-derived every step and closed five small gaps; it has had no human review. Theorem <a href="#res:single-prime-subsums" data-reference-type="ref" data-reference="res:single-prime-subsums">19</a> has the ordinary proof in the companion, refereed in the same way, and no Lean proof. Theorem <a href="#res:distinct-height-235" data-reference-type="ref" data-reference="res:distinct-height-235">6</a> is checked in Lean, as the remark below it states; Comparator has not yet compared it. Every other theorem, proposition, lemma and corollary has a Lean proof of its whole statement, marked in the margin; Appendix <a href="#app:sources" data-reference-type="ref" data-reference="app:sources">7</a> describes the formal sources. Neither these proofs nor the finite calculations supply the required windows for every eligible denominator and arbitrarily late starts.

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

The companion contains the detailed bounds and supplementary arguments; its source inventory explains the normalisation conventions of the Lean sources. The [distinct-height programs](https://github.com/wcook04/plectis-erdos/tree/10178c4df40cb27d83b5ebb1ec337dd588b82998/research/experiments/erdos269/distinct_height) recompute the constants of Theorem <a href="#res:distinct-height-235" data-reference-type="ref" data-reference="res:distinct-height-235">6</a> and the companion’s three- and four-prime certificates in exact rational arithmetic, and store their outputs; the same directory holds exact illustrations of the proof of Theorem <a href="#res:distinct-height-all" data-reference-type="ref" data-reference="res:distinct-height-all">1</a>, which the proof does not use. AI agents carried out most of the research and drafting. The work has not had independent human mathematical review.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering and its status as of 28 July 2026 are taken from the Erdős Problems catalogue maintained by Thomas Bloom \[erdosproblems\]. Earlier mathematical inputs are credited at their points of use. We thank Wouter van Doorn for advice on exposition, especially on unexplained terminology, unnecessary notation and the need to explain restrictive hypotheses. His advice concerned a note on Problem #243; he has not reviewed the mathematics of this paper.

<a id="app:sources"></a>

# Guide to the formal sources

There are four separate arguments. The proof of Theorem <a href="#res:distinct-height-all" data-reference-type="ref" data-reference="res:distinct-height-all">1</a> uses integral tails, rearranged blocks, a closed subtorus and an Euler characteristic count, and has no Lean proof. The proof of Theorem <a href="#res:distinct-height-235" data-reference-type="ref" data-reference="res:distinct-height-235">6</a> uses dyadic blocks, the disjoint images of five affine maps and the irrationality of $`\log2/\log3`$; its Lean proof follows the same route. The rank proof uses the height formula, row and column rescaling, and a threshold determinant. The arithmetic argument uses the shell coefficients, the tail recurrence, denominator clearing and least positive residues. The Lean proof of Theorem <a href="#res:windowconsumer" data-reference-type="ref" data-reference="res:windowconsumer">21</a> establishes the equivalence of the residue condition with irrationality; it does not establish the residue condition itself.

<a id="library-declarations."></a>

#### Library declarations.

The margin marks link each result to its Lean proof. The main steps rest on the following library declarations, each opened at a fixed revision. Distinct heights: [the height is the running LCM](https://github.com/wcook04/plectis-erdos/blob/5154f4c46fa5d5ab2cff8df857a0b10f310cbeeb/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L60); [the sum counts each distinct value once](https://github.com/wcook04/plectis-erdos/blob/5154f4c46fa5d5ab2cff8df857a0b10f310cbeeb/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L698); [a power of $`5`$ in every three consecutive blocks](https://github.com/wcook04/plectis-erdos/blob/5154f4c46fa5d5ab2cff8df857a0b10f310cbeeb/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L437); [the blocks containing a power of $`3`$ are not eventually periodic](https://github.com/wcook04/plectis-erdos/blob/5154f4c46fa5d5ab2cff8df857a0b10f310cbeeb/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L494); [the criterion for the five block letters](https://github.com/wcook04/plectis-erdos/blob/5154f4c46fa5d5ab2cff8df857a0b10f310cbeeb/lean/ErdosProblems/Erdos269/DistinctHeightBlockRadix.lean#L340); [the irrationality of $`\mathcal D_{\{2,3,5\}}`$](https://github.com/wcook04/plectis-erdos/blob/5154f4c46fa5d5ab2cff8df857a0b10f310cbeeb/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L689). Running LCM: [the exact height formula](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L123); [constancy on each logarithmic cell](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L179); the jumps by [$`p`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L326), [$`q`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L339) and [$`r`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L352); [exactly $`3\,\mathrm{count}+1`$ jump values](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L278); [the quadratic bound on exponent shells](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L646). Dyadic blocks: [at most one internal pure-power jump per channel](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L668); [the radix is $`2`$, $`6`$, $`10`$ or $`30`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L699); [the radix lies in $`[2,30]`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L711). Kernel rank: [the kernel is not of rank one](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L479); [the smallest $`2\times 2`$ minor equals $`-1/15`$](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L721); [the tail-state recurrence](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L490). Residues and carries: [no bounded positive state represents an escaping residue](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L76) ([integer form](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L110)); [the local-window escape condition](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L629) and [its exclusion of a positive reduced carry](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L645); [a bounded-radix orbit is integral or cofinally far from the integers](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/BoundedRadixTailEscape.lean#L89); [no uniformly bounded nonzero carry lift](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/CarryLiftExtinction.lean#L238); [block-null words are channel coboundaries](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreeChannelBlockRigidity.lean#L59); [the carry as a residue digit plus a coboundary](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/WeightedPhaseCarry.lean#L109); [a finite-dimensional factorisation gives a finite realised span](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/WeightedPhaseCarry.lean#L334).

<a id="scope-of-the-supplementary-literature."></a>

#### Scope of the supplementary literature.

The companion develops the comparisons omitted from the main argument. Its Section 6 relates the bounded-ratio argument to Erdős–Taylor \[erdostaylor1957, Theorem 1, p. 600\] and Fan \[fan2026strongly, Lemma 3.1, p. 7\]; Section 7 compares the exact carry restrictions and polynomial-radix assumptions of Hančl–Tijdeman \[hancltijdeman2008, Theorems 2.2, 3.1 and 4.2\]. The Isabelle development of Koutsoukou-Argyraki and Li \[afperdosstraus2020\] verifies classical criteria, not the present series.

Section 10 of the companion separates the finite-difference hypotheses of Luca–Ouaknine–Worrell \[lucaouaknineworrell2025, Definition 5, Theorems 6 and 8, Claim 10\] from quadratic growth alone, and checks the obstacles to using the echoing \[kebis2024echoing\], digit-complexity \[adamczewskibugeaud2007, Theorem 1\] and multivariate Mahler \[adamczewskifaverjon2026\] results. These comparisons do not establish the missing hypotheses for $`S`$.

For broader background, the companion distinguishes work on fixed-prime semigroups \[tijdemanmeijer1974; languasco2025\] from other unit-fraction irrationality problems \[kovactao2024\]. No estimate from those papers is used in this note’s counting argument.

<div class="thebibliography">

99 Paul Erdős and Ronald L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L’Enseignement Mathématique **28**, L’Enseignement Mathématique (1980), [source](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Paul Erdős, *On the irrationality of certain series: problems and results*, in *New Advances in Transcendence Theory*, Cambridge University Press (1988), 102–109, [doi:`10.1017/CBO9780511897184.009`](https://doi.org/10.1017/CBO9780511897184.009). Paul Erdős, *Letter to the Editor*, Fibonacci Quarterly **12**, no. 4 (1974), 335, [source](https://www.fq.math.ca/Scanned/12-4/letter.pdf). Thomas F. Bloom, *Erdős Problem \#269* (2026), [source](https://www.erdosproblems.com/269). Accessed 28 July 2026. Yann Bugeaud and Michel Laurent, *Transcendence and continued fraction expansion of values of Hecke–Mahler series*, Acta Arithmetica **209** (2023), 59–90, [doi:`10.4064/aa220323-18-1`](https://doi.org/10.4064/aa220323-18-1); arXiv:[2203.12901](https://arxiv.org/abs/2203.12901). John H. Loxton and Alfred J. van der Poorten, *Arithmetic properties of certain functions in several variables III*, Bulletin of the Australian Mathematical Society **16** (1977), 15–47, [doi:`10.1017/S0004972700022978`](https://doi.org/10.1017/S0004972700022978). Steve Fan, *Comment on Erdős Problem \#269, thread 269, post 7218* (2026), [source](https://www.erdosproblems.com/forum/thread/269#post-7218). Public forum post, 26 June 2026, thread 269, post 7218. P. H. Diananda and A. Oppenheim, *Criteria for irrationality of certain classes of numbers II*, American Mathematical Monthly **62**, no. 4 (1955), 222–225. Cited in the form stated by Serbenyuk, arXiv:[1706.03124](https://arxiv.org/abs/1706.03124), Theorem 1. Paul Erdős and Ernst G. Straus, *On the irrationality of certain series*, Pacific Journal of Mathematics **55**, no. 1 (1974), 85–92, [doi:`10.2140/pjm.1974.55.85`](https://doi.org/10.2140/pjm.1974.55.85). Jaroslav Hančl and Robert Tijdeman, *On the irrationality of Cantor and Ahmes series*, Publicationes Mathematicae Debrecen **65**, no. 3–4 (2004), 371–380, [doi:`10.5486/PMD.2004.3254`](https://doi.org/10.5486/PMD.2004.3254). Paul Erdős and S. James Taylor, *On the set of points of convergence of a lacunary trigonometric series and the equidistribution properties of related sequences*, Proceedings of the London Mathematical Society **s3-7**, no. 1 (1957), 598–615, [doi:`10.1112/plms/s3-7.1.598`](https://doi.org/10.1112/plms/s3-7.1.598). Steve Fan, *Strongly complete sets and a conjecture of Erdős* (2026), [source](https://arxiv.org/abs/2607.14071v1); arXiv:[2607.14071](https://arxiv.org/abs/2607.14071). The cited Lemma 3.1 is in arXiv v1, 15 July 2026. Jaroslav Hančl and Robert Tijdeman, *On the irrationality of polynomial Cantor series*, Acta Arithmetica **133**, no. 1 (2008), 37–52, [doi:`10.4064/aa133-1-3`](https://doi.org/10.4064/aa133-1-3). Florian Luca, Joël Ouaknine and James Worrell, *Transcendence of Hecke–Mahler Series*, Bulletin of the London Mathematical Society **57**, no. 5 (2025), 1360–1368, [doi:`10.1112/blms.70033`](https://doi.org/10.1112/blms.70033); arXiv:[2412.07908](https://arxiv.org/abs/2412.07908). Numbered references use the published article. Pavol Kebis, Florian Luca, Joël Ouaknine, Andrew Scoones and James Worrell, *On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words*, in *51st International Colloquium on Automata, Languages, and Programming (ICALP 2024)*, Leibniz International Proceedings in Informatics **297**, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2024), 144:1–144:15, [doi:`10.4230/LIPIcs.ICALP.2024.144`](https://doi.org/10.4230/LIPIcs.ICALP.2024.144). Robert Tijdeman and H. G. Meijer, *On integers generated by a finite number of fixed primes*, Compositio Mathematica **29**, no. 3 (1974), 273–286, [source](https://www.numdam.org/article/CM_1974__29_3_273_0.pdf). Alessandro Languasco, Florian Luca, Pieter Moree and Alain Togbé, *Sequences of integers generated by two fixed primes*, Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg **95** (2025), 123–148, [doi:`10.1007/s12188-025-00293-9`](https://doi.org/10.1007/s12188-025-00293-9); arXiv:[2309.12806](https://arxiv.org/abs/2309.12806). Vjekoslav Kovač and Terence Tao, *On several irrationality problems for Ahmes series*, Acta Mathematica Hungarica **175** (2025), 572–608, [doi:`10.1007/s10474-025-01528-0`](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593](https://arxiv.org/abs/2406.17593). Angeliki Koutsoukou-Argyraki and Wenda Li, *Irrationality Criteria for Series by Erdős and Straus*, Archive of Formal Proofs (2020), [source](https://isa-afp.org/entries/Irrational_Series_Erdos_Straus.html). Entry dated 12 May 2020; proof-document version consulted: 6 February 2026. Boris Adamczewski and Yann Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer bases*, Annals of Mathematics **165**, no. 2 (2007), 547–565, [doi:`10.4007/annals.2007.165.547`](https://doi.org/10.4007/annals.2007.165.547). Boris Adamczewski and Colin Faverjon, *Mahler’s method in several variables and finite automata*, Annals of Mathematics **204**, no. 2 (2026), 455–533, [doi:`10.4007/annals.2026.204.2.1`](https://doi.org/10.4007/annals.2026.204.2.1). Online 13 September 2026; locators here refer to the [68-page author manuscript](https://faverjon.perso.math.cnrs.fr/AdamczewskiFaverjon_MahlerFiniteAutomata.pdf).

</div>
