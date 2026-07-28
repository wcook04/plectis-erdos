<a id="erdos-269-three-prime-running-lcm"></a>

# The Three-Prime Running Least Common Multiple

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Let $`p,q,r`$ be pairwise distinct primes and let $`\operatorname{L}(x)`$ denote the least common multiple of all $`\{p,q,r\}`$-smooth numbers not exceeding $`x`$. We prove two exact statements in the smallest case $`\{2,3,5\}`$. First, group the jumps of $`\operatorname{L}`$ into the blocks cut out by consecutive powers of two. Each open block $`(2^{a},2^{a+1})`$ contains at most one pure $`3`$-power and at most one pure $`5`$-power, so the block radix $`\beta_a`$, the product of the terminal factor $`2`$ with a factor $`3`$ when the block contains an internal $`3`$-power and a factor $`5`$ when it contains an internal $`5`$-power, belongs to the exact four-element alphabet $`\{2,6,10,30\}`$, rather than merely lying in a coarse bounded interval. Second, the reciprocal of the running least common multiple at a smooth point is not a product of functions of the three exponents separately: on the smallest nontrivial two-by-two exponent rectangle its determinant is exactly $`-1/15`$. Thus that matrix has rank two, which excludes every argument that first separates the three coordinates and then treats them one at a time.

The structural spine of the note is the identification
``` math
\operatorname{L}(x)=p^{\lfloor\log_p x\rfloor}q^{\lfloor\log_q x\rfloor}
 r^{\lfloor\log_r x\rfloor}
 \qquad(x\ge1),
```
so the running least common multiple is the product of the three maximal pure prime powers below the cutoff. This is the $`P`$-restricted form of the classical prime-power decomposition of $`\operatorname{lcm}(1,\ldots,N)`$; we record it because every later statement in the formal development is derived from it. It gives $`\operatorname{L}(x)\le x^{3}`$; constancy on each cell where the three integer logarithms are constant; multiplication by exactly the corresponding prime when exactly one logarithm advances by one; and exactly $`3n+1`$ distinct jump values from the first $`n`$ positive powers of each of the three primes together with the common origin $`1`$. We also prove an exact finite normal form in which a rectangular lattice sum of reciprocal running values is grouped by its genuine height, with each coefficient the cardinality of the corresponding fibre, and a uniform bound $`9\,\#\mathcal S\le(j+3)^{2}`$ on the cardinality of a smooth exponent shell whose sorted height coordinates sum to $`j`$.

Problem #269 is open and nothing here decides it. We prove no irrationality or transcendence statement in any three-prime case. What we prove towards it is conditional: after cancellation of the $`\{2,3,5\}`$-smooth part of a hypothetical denominator, the remaining denominator $`B`$ is coprime to $`30`$, and a denominator-dependent cofinal local-window residue escape rules out every positive reduced integral carry obeying the matching bound. Lean checks the absorption-and-cancellation core and the resulting implication. An integer-only checker constructs the corresponding block digits, reproduces three small certificates, and finds an escaping window of length at most $`18`$ for each of $`106{,}666`$ tested denominator/start pairs. This is finite experimental evidence, not a cofinal theorem. Two problem-specific statements are not proved here: the rationality-to-carry identification, including the divisibility needed to perform that cancellation, and the cofinal escape property itself.

<a id="sec:problem"></a>

# Introduction

Let $`P`$ be a finite set of primes with $`|P|\ge2`$, and let $`a_1<a_2<\cdots`$ enumerate the positive integers all of whose prime factors lie in $`P`$. Erdős Problem #269 asks whether
``` math
\sum_{n\ge1}\frac{1}{[a_1,\ldots,a_n]}
```
is irrational, where $`[a_1,\ldots,a_n]`$ is the least common multiple \[erdosgraham1980, p. 65\]\[erdos1988, p. 106\]. Numbering and status follow Bloom’s catalogue \[erdosproblems\]. The problem is open for every finite $`P`$ with $`|P|\ge2`$. In the primary 1988 source, Erdős proves the infinite-$`P`$ assertion and presents persistence for a finite number of primes greater than one as a probable extension, not as a theorem; the current open status is supplied by the catalogue rather than inferred from that conjectural wording.

Three things are known and fix the shape of the question. The restriction $`|P|\ge2`$ is necessary: for $`P=\{p\}`$ the enumeration is $`a_n=p^{\,n-1}`$, so $`[a_1,\ldots,a_n]=p^{\,n-1}`$ and the sum is $`p/(p-1)`$, which is rational. For infinite $`P`$ the sum is always irrational, which Erdős calls a simple exercise \[erdos1988, p. 106\]. And in a letter of 1 January 1973 he recorded that he could prove irrationality once duplicate summands are removed \[erdos1974letter\].

That last remark is the one this note is closest to. The running least common multiple is not injective in $`n`$: it is constant along stretches of the enumeration and changes only at certain points. Removing duplicate summands means summing over the distinct values rather than over $`n`$. Sections <a href="#sec:cells" data-reference-type="ref" data-reference="sec:cells">3</a> and <a href="#sec:fibre" data-reference-type="ref" data-reference="sec:fibre">4</a> make that reindexing exact, in the case $`|P|=3`$: they identify where the value is constant, by exactly what factor it changes when it changes, and what multiplicity each distinct value carries. They do not recover the irrationality proof Erdős reported for the de-duplicated sum, and they say nothing about the original sum. We do not know of a published account of that proof.

Throughout, $`p,q,r`$ are pairwise distinct primes. Call $`n`$ *smooth* when $`n=p^{i}q^{j}r^{k}`$ for some $`i,j,k\ge0`$; this is the [smooth lattice value](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L31). For $`x\ge1`$ write
``` math
\operatorname{L}(x)=\operatorname{lcm}\{\,n\le x:\ n\ \text{smooth}\,\},
 \qquad
 \operatorname{H}(x)=p^{\lfloor\log_p x\rfloor}\,q^{\lfloor\log_q x\rfloor}\,
 r^{\lfloor\log_r x\rfloor},
```
the [running least common multiple](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L53) and the [pure-power height](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L36), where $`\lfloor\log_b x\rfloor`$ is the integer logarithm, the largest $`e`$ with $`b^{e}\le x`$. Since $`a_1,\ldots,a_n`$ are exactly the smooth numbers up to $`a_n`$, we have $`[a_1,\ldots,a_n]=\operatorname{L}(a_n)`$, and the summands of the problem are the reciprocals of $`\operatorname{L}`$ along the enumeration. The reciprocal of the height at a smooth point is the [lattice kernel](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L40)
``` math
\operatorname{K}(i,j,k)=\frac{1}{\operatorname{H}(p^{i}q^{j}r^{k})} .
```
For $`b\in\{p,q,r\}`$ we call the set of positive powers of $`b`$ the *$`b`$-channel*.

We treat $`|P|=3`$ throughout, writing $`P=\{p,q,r\}`$, and the smallest instance is $`\{2,3,5\}`$. Two of the statements proved here are unconditional and exact rather than approximate. Theorem <a href="#res:dyadic-alphabet" data-reference-type="ref" data-reference="res:dyadic-alphabet">11</a> determines the alphabet of the dyadic compression of the jump word exactly: the radix $`\beta_a`$ of the block between $`2^{a}`$ and $`2^{a+1}`$ takes one of the four values $`2`$, $`6`$, $`10`$, $`30`$ and no others. Theorem <a href="#res:rank" data-reference-type="ref" data-reference="res:rank">10</a> shows that the smallest two-by-two restriction of the kernel at $`\{2,3,5\}`$ has determinant $`-1/15`$ and hence rank two. In particular, it is not a product $`f(i)g(j)h(k)`$, so every argument that first separates the three coordinates and then treats them one at a time is excluded. The mechanism is a small computation: $`\operatorname{H}(6)=4\cdot3\cdot5=60`$ and not $`6`$, because the running least common multiple at a smooth cutoff already sees powers of the other primes that the cutoff itself does not contain. We do not determine whether the coordinates separate when $`|P|=2`$.

The identification $`\operatorname{L}(x)=\operatorname{H}(x)`$ of Theorem <a href="#res:lcm" data-reference-type="ref" data-reference="res:lcm">1</a> is what makes every statement about $`\operatorname{L}`$ below computable from three integer logarithms. In the unrestricted case that identification is classical: $`\operatorname{lcm}(1,\ldots,N)=\prod_{t\le N}t^{\lfloor\log_t N\rfloor}`$, the product being over the primes $`t\le N`$, equivalently $`\log\operatorname{lcm}(1,\ldots,N)=\psi(N)`$ for Chebyshev’s function $`\psi`$ \[apostol1976, Ch. 4\]. We record the $`P`$-restricted form because every later statement in the formal development is derived from it, and we claim nothing new for it.

The line of argument developed below has four stages. First, identify $`\operatorname{L}`$ exactly as a product of three pure powers, so that every later statement is a statement about three integer logarithms. Second, compress its jump word into dyadic blocks, whose radix takes only the four values of Theorem <a href="#res:dyadic-alphabet" data-reference-type="ref" data-reference="res:dyadic-alphabet">11</a>. Third, assume the sum rational with reduced denominator $`D`$, factor $`D=D_{\mathrm{sm}}B`$ where every prime divisor of $`D_{\mathrm{sm}}`$ lies in $`\{2,3,5\}`$ and $`\gcd(B,30)=1`$, prove that the integral carry states share the factor $`D_{\mathrm{sm}}`$, cancel it, and obtain a positive reduced carry $`d_n`$ bounded by $`K(B,n)`$ and satisfying $`d_{n+1}=b_nd_n-Bm_n`$. Fourth, find a window over which the accumulated base and forcing put the residue of that carry above the bound, which is impossible. The first two stages and the finite core of the fourth are proved and formalised here. The algebraic absorption-and-cancellation core of the third stage is also checked, but the problem-specific claim that the actual carry shares $`D_{\mathrm{sm}}`$ is not. That rationality-to-carry instantiation and the cofinal existence of windows in the fourth stage are the two obligations of Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">8</a>. The third and fourth stages follow a pattern standard in irrationality proofs; what is specific here is that the radix word driving the carry is the block alphabet of Theorem <a href="#res:dyadic-alphabet" data-reference-type="ref" data-reference="res:dyadic-alphabet">11</a>.

The statement of Problem #269 has been formalised before, as a conjecture with an unfilled proof, in the *Formal Conjectures* collection \[formalconjectures269\]. That is a formal statement of the question. The declarations described below are propositions about the objects the question is posed over. No claim of priority is made for any of these declarations. Kovač and Tao \[kovactao2024\] treat several irrationality problems of Erdős for series of unit fractions by elementary means; nothing from that work is used here. We offer no numerical evidence about the value of the sum itself.

*Status.* The problem treated here is open, and this note does not close it. Every statement below marked as checked is a proposition that the pinned Lean kernel accepts from the sources this note links to, with no `sorry`, no added axiom, and no unchecked evaluation. That is a claim about the formal statement, not about its mathematical interest, its novelty, or the original problem. The unresolved obligations are named exactly, in their own section, and none of the finite computations, reductions, or no-go results here removes one of them.

| Statement | Status | Treatment here |
|:---|:---|:---|
| Irrationality in any three-prime case | Open | Not proved. |
| $`\operatorname{L}(x)=\operatorname{H}(x)`$ | Proved here | Theorem <a href="#res:lcm" data-reference-type="ref" data-reference="res:lcm">1</a>; needs the primes distinct; classical in the unrestricted case. |
| $`\operatorname{H}(x)\le x^{3}`$ | Proved here | Proposition <a href="#res:cube" data-reference-type="ref" data-reference="res:cube">2</a>. |
| Constancy on logarithmic cells | Proved here | Theorem <a href="#res:cell" data-reference-type="ref" data-reference="res:cell">3</a>. |
| Single-coordinate jump ratios | Proved here | Theorem <a href="#res:jump" data-reference-type="ref" data-reference="res:jump">4</a>. |
| Exactly $`3n+1`$ jump values | Proved here | Theorem <a href="#res:count" data-reference-type="ref" data-reference="res:count">5</a>. |
| Height-fibre normal form | Proved here; finite | Theorem <a href="#res:fibre" data-reference-type="ref" data-reference="res:fibre">6</a>. |
| Infinite limit of that expansion | Not proved | Section <a href="#sec:fibre" data-reference-type="ref" data-reference="sec:fibre">4</a>. |
| Shell multiplicity $`9\,\#\mathcal S\le(j+3)^{2}`$ | Proved here | Theorem <a href="#res:shell" data-reference-type="ref" data-reference="res:shell">9</a>. |
| $`2\times2`$ kernel restriction has rank two at $`\{2,3,5\}`$ | Proved here | Determinant $`-1/15`$; Theorem <a href="#res:rank" data-reference-type="ref" data-reference="res:rank">10</a>. |
| Dyadic block radix lies in $`\{2,6,10,30\}`$ | Proved here | Theorem <a href="#res:dyadic-alphabet" data-reference-type="ref" data-reference="res:dyadic-alphabet">11</a>. |
| Canonical least-positive-residue arithmetic | Proved here | Theorem <a href="#res:consumer" data-reference-type="ref" data-reference="res:consumer">13</a>. |
| Carry contradiction assuming <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a> | Proved here | Theorem <a href="#res:windowconsumer" data-reference-type="ref" data-reference="res:windowconsumer">14</a>; the implication only. |
| Smooth-factor absorption and carry cancellation | Proved here; conditional core | Theorem <a href="#res:denominator-reduction" data-reference-type="ref" data-reference="res:denominator-reduction">12</a>; divisibility of the actual carry remains unproved. |
| Dyadic-window scan for $`B\le1000`$ | Exact finite computation | $`106{,}666`$ pairs; no failures; not a theorem. |
| Bridge from the actual summands to $`(b_n,m_n,K)`$ | Not proved | Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">8</a>. |
| Local-window escape for the actual $`\{2,3,5\}`$ word | Open | Problem <a href="#prob:producer" data-reference-type="ref" data-reference="prob:producer">15</a>. |

Status of the statements discussed in this note.

<a id="structure"></a>

## Structure

Section <a href="#sec:lcm" data-reference-type="ref" data-reference="sec:lcm">2</a> identifies the running value. Sections <a href="#sec:cells" data-reference-type="ref" data-reference="sec:cells">3</a> and <a href="#sec:fibre" data-reference-type="ref" data-reference="sec:fibre">4</a> develop its jump structure and the finite normal form, Section <a href="#sec:shell" data-reference-type="ref" data-reference="sec:shell">5</a> bounds fibre multiplicity, and Section <a href="#sec:rank" data-reference-type="ref" data-reference="sec:rank">6</a> records the obstruction to separating the kernel. Section <a href="#sec:escape" data-reference-type="ref" data-reference="sec:escape">7</a> determines the block alphabet, proves the conditional contradiction, and states the remaining unproved hypothesis. Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">8</a> collects the questions that remain. Linked phrases open the corresponding Lean declaration at the pinned source revision 234ced3455a7.

**Keywords.** irrationality; least common multiple; smooth numbers; lattice sums; Lean 4. **MSC 2020.** 11J72 (primary); 11A05, 11N25, 68V20 (secondary).

<a id="sec:lcm"></a>

# The running least common multiple as a product of pure powers

The smooth numbers up to $`x`$ are indexed by the exponent triples $`(i,j,k)`$ with $`i\le\lfloor\log_p x\rfloor`$, $`j\le\lfloor\log_q x\rfloor`$, $`k\le\lfloor\log_r x\rfloor`$ and $`p^{i}q^{j}r^{k}\le x`$: the coordinate bounds make the index set finite, and the last condition is the actual constraint. This is the [smooth prefix index set](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L46). Both conditions matter: the coordinate box is strictly larger than the prefix, since a product of three large pure powers can exceed $`x`$ while each factor does not.

The identification below is routine, and its unrestricted analogue is classical, as recalled in the introduction; the short proof is given because every later statement is derived from it in the formal development.

<div id="res:lcm" class="theorem">

**Theorem 1** (the running least common multiple). *Let $`p,q,r`$ be pairwise distinct primes and $`x\ge1`$. Then $`\operatorname{L}(x)=\operatorname{H}(x)`$.*

</div>

<div class="proof">

*Proof.* For divisibility in one direction, every smooth $`n\le x`$ has exponents bounded by the corresponding integer logarithms, so $`n\mid\operatorname{H}(x)`$, and hence $`\operatorname{L}(x)\mid\operatorname{H}(x)`$. For the other, the three pure powers $`p^{\lfloor\log_p x\rfloor}`$, $`q^{\lfloor\log_q x\rfloor}`$ and $`r^{\lfloor\log_r x\rfloor}`$ are themselves smooth numbers not exceeding $`x`$, so each divides $`\operatorname{L}(x)`$. Distinct primes have coprime powers, so their product divides $`\operatorname{L}(x)`$ as well. The two divisibilities give equality. ◻

</div>

Formalised as the [running-lcm identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L123), from the [divisibility into the height](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L77) and the three membership statements for the pure powers, namely the [first](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L84), [second](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L97), and [third](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L110) pure-power memberships.

The hypothesis that the primes are pairwise distinct is used exactly once, in the coprimality step, and it is not decorative: without it the three pure powers need not have coprime orders and their product need not divide the least common multiple. The identity is what makes every later statement about $`\operatorname{L}`$ computable from three integer logarithms.

<div id="res:cube" class="proposition">

**Proposition 2**. *For every $`x\ge1`$, $`\operatorname{H}(x)\le x^{3}`$.*

</div>

<div class="proof">

*Proof.* Each of the three factors is a power of its base not exceeding $`x`$. ◻

</div>

Formalised as the [cubic majorant](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L430), which needs no primality. The exponent $`3`$ is the number of generating primes, and the bound is the reason the reciprocal kernel is comparable to $`x^{-3}`$ rather than to $`x^{-1}`$.

<a id="sec:cells"></a>

# Constancy on logarithmic cells and the jump values

Say that $`x`$ and $`y`$ lie in the same *logarithmic cell* when $`\lfloor\log_b x\rfloor=\lfloor\log_b y\rfloor`$ for each of $`b=p,q,r`$: the [cell relation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L163).

<div id="res:cell" class="theorem">

**Theorem 3** (constancy on cells). *If $`x,y\ge1`$ lie in the same logarithmic cell, then $`\operatorname{L}(x)=\operatorname{L}(y)`$. The same holds for the kernel at two smooth points whose values lie in one cell.*

</div>

<div class="proof">

*Proof.* Immediate from Theorem <a href="#res:lcm" data-reference-type="ref" data-reference="res:lcm">1</a>, since $`\operatorname{H}`$ depends on $`x`$ only through the three integer logarithms. ◻

</div>

Formalised as the [cell constancy of the running value](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L179), the [cell constancy of the height](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L169), and the [cell constancy of the kernel](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L191). The running value therefore changes only when one of the three logarithms changes, and the next theorem says by exactly how much.

<div id="res:jump" class="theorem">

**Theorem 4** (single-coordinate jump ratios). *Let $`x,y\ge1`$. If $`\lfloor\log_p y\rfloor=\lfloor\log_p x\rfloor+1`$ while the other two logarithms agree, then $`\operatorname{L}(y)=p\,\operatorname{L}(x)`$; and similarly with $`q`$ or $`r`$ in place of $`p`$.*

</div>

<div class="proof">

*Proof.* By Theorem <a href="#res:lcm" data-reference-type="ref" data-reference="res:lcm">1</a> both sides are heights, and one factor of the height gains one in its exponent while the others are unchanged. ◻

</div>

Formalised as the [first](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L326), [second](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L339), and [third](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L352) coordinate steps, over the corresponding statements for the height alone, which need no primality: the [first height step](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L294), the [second](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L305), and the [third](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L316).

The jump values are therefore the pure prime powers, and they do not collide across channels.

<div id="res:count" class="theorem">

**Theorem 5** (jump count). *Let $`n\ge0`$. The set of the first $`n`$ positive powers of $`p`$, of $`q`$, and of $`r`$ has exactly $`3n`$ elements, and adjoining the common origin $`1`$ gives exactly $`3n+1`$.*

</div>

<div class="proof">

*Proof.* The count is routine. Within one channel the powers $`b,b^{2},\ldots,b^{n}`$ are distinct because $`b\ge2`$. Across two channels a common value would be a positive power of two distinct primes, which unique factorisation forbids. Finally $`1`$ is not a positive power of any prime. ◻

</div>

Formalised as the [positive jump count](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L249) and the [jump count with the origin](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L278), over the [channel cardinality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L208), the [channel disjointness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L229), and the [exclusion of the origin](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L219); the channels themselves are the [positive power sets](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L204). The exponent $`0`$ is omitted from each channel because it is the shared initial value, which is why the origin is counted once rather than three times.

<a id="sec:fibre"></a>

# The height-fibre normal form

Grouping a lattice sum by the value of the running least common multiple turns it into a sum over heights whose coefficients are multiplicities. We prove this exactly, on a finite rectangular box.

Write $`B(h_p,h_q,h_r)`$ for the box of exponent triples with $`i\le h_p`$, $`j\le h_q`$, $`k\le h_r`$, the [exponent box](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L368), and for a height $`H`$ write $`F(H)`$ for the set of points of the box whose running height equals $`H`$, the [height fibre](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L377).

<div id="res:fibre" class="theorem">

**Theorem 6** (finite normal form). *For every box,
``` math
\sum_{(i,j,k)\in B}\operatorname{K}(i,j,k)
 =\sum_{H}\frac{\#F(H)}{H},
```
the outer sum ranging over the heights actually attained on $`B`$.*

</div>

<div class="proof">

*Proof.* The identity is a regrouping. Partition $`B`$ into the fibres of the height map. On $`F(H)`$ every summand is $`1/H`$ by definition of the kernel, so the fibre contributes $`\#F(H)/H`$. ◻

</div>

Formalised as the [height-fibre normal form](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L406), over the [fibre sum](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L384), with the height of a lattice point given by the [point height](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L373).

Together with Theorem <a href="#res:cell" data-reference-type="ref" data-reference="res:cell">3</a> this is the finite core of the ordered prime-power jump expansion: the value is constant on cells, the cells are indexed by heights, and the coefficient of a height is the number of lattice points it collects. The passage to the infinite sum, and the explicit ordering of the pure powers that would make the expansion a series in the jumps, are not proved here. Theorem <a href="#res:fibre" data-reference-type="ref" data-reference="res:fibre">6</a> is an identity between two finite sums, and it is stated over the full box rather than the smooth prefix, so it is not a statement about $`\operatorname{L}`$ at a cutoff.

The same module records a one-step map $`\tau(b,d,s)=b(s-d)`$, the [variable-base tail step](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L487), with the rewriting [that names its expanded form](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L490). No orbit of this map is analysed.

<a id="sec:shell"></a>

# A quadratic bound for smooth exponent shells

A tail estimate needs to know how many lattice points can share a short multiplicative interval. Write $`\mathcal S`$ for the set of exponent triples in a box $`B(h_p,h_q,h_r)`$ whose smooth value lies in $`[\lambda,\eta)`$, the [smooth exponent shell](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L500).

<div id="res:short" class="lemma">

**Lemma 7** (uniqueness in a short interval). *Let $`b\ge1`$ and suppose $`\eta\le b\,\lambda`$. If $`b^{a}w`$ and $`b^{a'}w`$ both lie in $`[\lambda,\eta)`$, then $`a=a'`$.*

</div>

<div class="proof">

*Proof.* If $`a<a'`$ then $`\eta\le b\,\lambda\le b\cdot b^{a}w=b^{a+1}w\le b^{a'}w<\eta`$, which is impossible; the case $`a>a'`$ is symmetric. ◻

</div>

Formalised as the [short-interval uniqueness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L509). The hypothesis is that the interval has multiplicative width at most $`b`$.

<div id="res:drop" class="proposition">

**Proposition 8**. *If $`\eta\le r\,\lambda`$ then $`\#\mathcal S\le(h_p+1)(h_q+1)`$; if $`\eta\le p\,\lambda`$ then $`\#\mathcal S\le(h_q+1)(h_r+1)`$.*

</div>

<div class="proof">

*Proof.* Suppose $`\eta\le r\,\lambda`$. If two triples of $`\mathcal S`$ agree in their first two coordinates, Lemma <a href="#res:short" data-reference-type="ref" data-reference="res:short">7</a> applied with $`b=r`$ and $`w=p^{i}q^{j}`$ forces their third coordinates to agree as well. So the projection forgetting the third coordinate is injective on $`\mathcal S`$, and its image lies in a rectangle with $`(h_p+1)(h_q+1)`$ points. The case $`\eta\le p\,\lambda`$ is the same with the first coordinate projected away. ◻

</div>

Formalised as the [third-coordinate projection](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L585) and the [first-coordinate projection](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L543).

<div id="res:shell" class="theorem">

**Theorem 9** (quadratic multiplicity bound). *Suppose $`\eta\le r\,\lambda`$ and $`h_p\le h_q\le h_r`$ with $`h_p+h_q+h_r=j`$. Then
``` math
9\,\#\mathcal S\le(j+3)^{2}.
```*

</div>

<div class="proof">

*Proof.* By Proposition <a href="#res:drop" data-reference-type="ref" data-reference="res:drop">8</a>, $`\#\mathcal S\le(h_p+1)(h_q+1)`$; under the sorting hypothesis the two surviving coordinates are the two smallest. It therefore suffices to prove that $`a\le b\le c`$ with $`a+b+c=j`$ gives $`9(a+1)(b+1)\le(j+3)^{2}`$. From $`a\le b\le c`$ we get $`a+2b\le j`$, so it is enough that $`9(a+1)(b+1)\le(a+2b+3)^{2}`$; writing $`b=a+d`$ with $`d\ge0`$, the difference of the two sides is $`d(3a+4d+3)\ge0`$. ◻

</div>

Formalised as the [quadratic shell bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L646), over the [sorted quadratic estimate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L629). The constant $`9`$ is the square of the number of generating primes and appears because the bound is the arithmetic–geometric comparison for a sum of three sorted coordinates; sorting is a hypothesis, not a normalisation, since the shell itself is not symmetric in the three bases.

The bound is uniform in $`\lambda`$ and $`\eta`$ subject to the width condition, and it is stated for the actual filtered shell rather than for a lattice model of it. It is an input to a tail estimate and is not itself one: no series is bounded here. The estimate is elementary and uses no analytic input on the distribution of smooth numbers, only the projection of Proposition <a href="#res:drop" data-reference-type="ref" data-reference="res:drop">8</a>.

<a id="sec:rank"></a>

# Non-separability of the three-prime kernel

One might hope to write the three-prime kernel as $`f(i)g(j)h(k)`$ and so reduce the problem to one-dimensional criteria. Theorem <a href="#res:rank" data-reference-type="ref" data-reference="res:rank">10</a> shows that this already fails at $`\{2,3,5\}`$, and that the failure is exact.

<div id="res:rank" class="theorem">

**Theorem 10** (non-separability at $`\{2,3,5\}`$). *With $`(p,q,r)=(2,3,5)`$,
``` math
\operatorname{K}(0,0,0)\,\operatorname{K}(1,1,0)
 -\operatorname{K}(1,0,0)\,\operatorname{K}(0,1,0)
 =-\tfrac1{15}\ne0.
```
Consequently this two-by-two kernel restriction has rank two over $`\mathbb Q`$.*

</div>

<div class="proof">

*Proof.* The four values are $`\operatorname{K}(0,0,0)=1`$, $`\operatorname{K}(1,0,0)=1/2`$, $`\operatorname{K}(0,1,0)=1/6`$ and $`\operatorname{K}(1,1,0)=1/60`$, computed from $`\operatorname{H}(1)=1`$, $`\operatorname{H}(2)=2`$, $`\operatorname{H}(3)=2\cdot3=6`$ and $`\operatorname{H}(6)=4\cdot3\cdot5=60`$. Hence the determinant is $`1/60-1/12=-1/15`$, and a two-by-two matrix with nonzero determinant has rank two. ◻

</div>

Formalised as the [non-separation witness](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L479), over the four exact values, the [origin](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L443), [value at two](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L450), [value at three](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L458), and [value at six](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L467). The exact determinant calculation is the [rank-two certificate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L721). The height at $`6`$ is $`60`$ rather than $`6`$ because the maximal pure powers below $`6`$ are $`4`$, $`3`$ and $`5`$: the running least common multiple at a smooth cutoff sees powers of the other primes that the cutoff itself does not contain. That is the mechanism behind the non-separation.

A nonzero two-by-two minor rules out writing the kernel as $`f(i)g(j)h(k)`$ on this box, and hence rules out any argument that first separates the coordinates and then treats them one at a time. It gives no rank lower bound beyond two, and it is not an independence or irrationality statement.

<a id="sec:escape"></a>

# Dyadic blocks and a conditional carry contradiction

<a id="the-four-element-block-alphabet"></a>

## The four-element block alphabet

Compress the jump word between consecutive powers of two: a block starts just after $`2^a`$, includes every pure $`3`$- or $`5`$-power strictly between $`2^a`$ and $`2^{a+1}`$, and ends with the jump at $`2^{a+1}`$. A channel cannot occur twice inside one block. Indeed, if
``` math
2^a<p^e,p^f<2^{a+1}\qquad(p\ge2),
```
then the ratio between the interval endpoints is $`2\le p`$, so strict monotonicity of the powers forces $`e=f`$. This is the [checked internal-power uniqueness lemma](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L668).

Let $`\beta_a`$ be the product of the terminal dyadic factor $`2`$, a factor $`3`$ when the block contains an internal $`3`$-power, and a factor $`5`$ when it contains an internal $`5`$-power.

<div id="res:dyadic-alphabet" class="theorem">

**Theorem 11** (the dyadic block alphabet). *For every $`a`$,
``` math
\beta_a\in\{2,6,10,30\};
  \qquad\text{in particular}\qquad 2\le\beta_a\le30.
```*

</div>

<div class="proof">

*Proof.* Internal-power uniqueness leaves two independent yes/no choices, one for the $`3`$-channel and one for the $`5`$-channel. Multiplying the terminal factor $`2`$ by the selected channel factors gives exactly the displayed four cases. ◻

</div>

The definition is the [dyadic block base](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L688); Lean checks both the [exact four-case alphabet](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L699) and the [bounded-radix consequence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L711). The radix word is therefore constrained to four values, and no growth hypothesis on it is needed. What is not yet checked in Lean is the identification of the corresponding block digit with the multiplicity forcing in the original series.

<a id="the-denominator-reduction-and-its-boundary"></a>

## The denominator reduction and its boundary

Let $`D`$ be the reduced denominator of a hypothetical rational value, and write
``` math
D=D_{\mathrm{sm}}B,\qquad
  D_{\mathrm{sm}}=2^{u}3^{v}5^{w},\qquad \gcd(B,30)=1.
```
The coprimality condition below is therefore intended as the endpoint of a reduction from an arbitrary $`D`$, not as a restriction on which rational values are being considered. Every fixed $`\{2,3,5\}`$-smooth factor divides the running height once the cutoff reaches that factor ([checked absorption](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L513)). If the denominator-cleared carry states $`c_n`$ share the absorbed factor, so that $`c_n=D_{\mathrm{sm}}d_n`$, Lean cancels it from
``` math
c_{n+1}=b_nc_n-D_{\mathrm{sm}}B\,m_n
```
and obtains
``` math
d_{n+1}=b_nd_n-Bm_n
```
([checked cancellation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L546)). Positivity and the sharp denominator-dependent upper bound descend through the same positive factor ([checked bound transfer](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L566)), and the reduced carry inherits the exact window identity ([checked window transfer](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L577)).

<div id="res:denominator-reduction" class="theorem">

**Theorem 12** (conditional denominator reduction). *If the actual denominator-cleared carry for $`D=D_{\mathrm{sm}}B`$ has the common-factor form $`c_n=D_{\mathrm{sm}}d_n`$ with $`D_{\mathrm{sm}}>0`$, then its recurrence, positivity, bound, and window identity reduce to the same statements with multiplier $`B`$, where $`\gcd(B,30)=1`$.*

</div>

The theorem is conditional at exactly one point: height absorption does not by itself prove that the *carry state* is divisible by $`D_{\mathrm{sm}}`$. That divisibility must come from the still-unproved rationality-to-carry identification for the actual series. The phrase “$`B`$ coprime to $`30`$” below is valid only downstream of this bridge.

<a id="the-window-recurrence-and-the-residue-contradiction"></a>

## The window recurrence and the residue contradiction

The statements of this subsection are about integer sequences: they do not refer to $`\operatorname{L}`$ or to the smooth numbers, and the identification of those sequences with the block data of the preceding subsection is the obligation just recorded. For an integer radix word $`b_n`$ and forcing word $`m_n`$, define
``` math
\begin{aligned}
 W_{\ell,0}&=1,
&W_{\ell,h+1}&=b_{\ell+h}W_{\ell,h},\\
 F_{\ell,0}&=0,
&F_{\ell,h+1}&=b_{\ell+h}F_{\ell,h}+m_{\ell+h}.
\end{aligned}
```
These are the [window base](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L417) and [window forcing](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L422). If an integral carry satisfies
``` math
d_{n+1}=b_n d_n-Bm_n ,
```
then induction gives the exact division-free identity
``` math
d_{\ell+h}=W_{\ell,h}d_\ell-BF_{\ell,h};
```
this is the [checked window identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L480).

For $`C>0`$, let $`\operatorname{lpr}_C(x)\in\{1,\ldots,C\}`$ be the least positive representative of $`x\bmod C`$, with a zero residue represented by $`C`$. This is the [canonical representative](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ResidueEscape.lean#L19). Lean checks both its [positive range](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ResidueEscape.lean#L24) and its [congruence to the source integer](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ResidueEscape.lean#L45). This convention matters: replacing $`\operatorname{lpr}_C(x)`$ by $`|x|`$ would not be a modular statement.

Let $`K(B,n)`$ be the bound on the reduced carry at denominator $`B`$. Define *cofinal local-window escape* to mean that for every $`B>0`$ coprime to $`30`$ and every $`\ell_0`$, there are $`\ell\ge\ell_0`$ and $`h>0`$ such that
``` math
C_{\ell,h}:=|W_{\ell,h}|>0
 \quad\text{and}\quad
 K(B,\ell+h)<
 \operatorname{lpr}_{C_{\ell,h}}(-BF_{\ell,h}).
\tag{E}\label{eq:escape}
```
Both the quantifier over $`B`$ and the dependence of $`K`$ on $`B`$ are part of the statement. The exact unproved proposition is the [cofinal local-window escape condition](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L594).

The next statement is the finite core of the argument. The key point is the convention just fixed: because $`\operatorname{lpr}_C`$ represents a vanishing residue by $`C`$ and not by $`0`$, the proof has to treat that case separately, and the two branches conclude for different reasons.

<div id="res:consumer" class="theorem">

**Theorem 13** (the finite residue contradiction). *Let $`C>0`$, $`c>0`$, and $`|c|\le K`$. If $`c\equiv x\pmod C`$ and $`K<\operatorname{lpr}_C(x)`$, then the hypotheses are contradictory.*

</div>

<div class="proof">

*Proof.* The canonical representative lies in $`\{1,\ldots,C\}`$. The inequalities put $`c`$ strictly between $`0`$ and $`C`$. If $`x\equiv0\pmod C`$, its positive representative is $`C`$ while $`c\bmod C=c\ne0`$. Otherwise both $`c`$ and $`\operatorname{lpr}_C(x)`$ are their own residues and congruence makes them equal, contradicting $`|c|\le K<\operatorname{lpr}_C(x)`$. ◻

</div>

The natural-state version is the [finite contradiction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ResidueEscape.lean#L71); the integer carry version is the [integer form of the contradiction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/ResidueEscape.lean#L104).

<div id="res:windowconsumer" class="theorem">

**Theorem 14** (a conditional contradiction for bounded carries). *Assume the cofinal escape property <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>. Fix $`B>0`$ coprime to $`30`$. There is no integral sequence $`d_n`$ satisfying simultaneously
``` math
d_{n+1}=b_nd_n-Bm_n,\qquad d_n>0,\qquad
 |d_n|\le K(B,n)\quad(n\ge0).
```*

</div>

<div class="proof">

*Proof.* Choose one window supplied by <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>. The checked window identity gives
``` math
d_{\ell+h}\equiv -BF_{\ell,h}\pmod{|W_{\ell,h}|}.
```
The endpoint state is positive and at most $`K(B,\ell+h)`$, whereas the canonical positive residue of the right-hand side is larger than this bound. Theorem <a href="#res:consumer" data-reference-type="ref" data-reference="res:consumer">13</a> is the contradiction. ◻

</div>

This is formalised as the [reduced-carry extinction theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/234ced3455a73357c33113e8a285e1a3b3d411fb/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L610). Coprimality with $`30`$ is used by <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a> to select a window; once a window has been chosen, the finite contradiction does not use it. The formalisation carries the edge cases: $`|W_{\ell,h}|=0`$ is excluded, a zero residue is represented by the full modulus, and positivity prevents the endpoint carry from being zero.

<a id="a-finite-check-of-the-escape-condition"></a>

## A finite check of the escape condition

The integer-only [dyadic-window checker](https://github.com/wcook04/plectis-lean-erdos249-257/tree/234ced3455a73357c33113e8a285e1a3b3d411fb/scripts/check_erdos269_dyadic_windows.py) constructs the ordered pure-power jumps, the block bases, and the block digits from exact multiplicity counts. It reproduces the following certificates; the columns are denominator $`B`$, dyadic start $`a`$, window length $`h`$, endpoint jump index $`n`$, window base $`W`$, forcing $`F`$, least positive residue $`R=\operatorname{lpr}_{W}(-BF)`$, and short bound $`K`$.
``` math
\begin{array}{c|c|c|c|r|r|r|r}
B&a&h&n&W&F&R&K\\ \hline
1&1&2&4&60&47&13&9\\
7&1&3&6&360&289&137&95\\
16&1&4&9&10800&8735&640&352
\end{array}
```
A fresh scan over every $`B\le1000`$ coprime to $`30`$ and every $`100\le a\le500`$ tested $`106{,}666`$ pairs. In every case a window of length at most $`18`$ made both $`W>K`$ and $`\operatorname{lpr}_{W}(-BF)>K`$; the largest first successful length was $`14`$. The computation uses integers only and is reproducible from the pinned checker. Neither the scan nor the three displayed certificates proves escape for unbounded $`B`$ or for cofinally many starts.

<a id="sec:open"></a>

# Complements and further questions

Two statements would be needed to turn Section <a href="#sec:escape" data-reference-type="ref" data-reference="sec:escape">7</a> into an irrationality proof at $`\{2,3,5\}`$, and they are of different kinds. The first is the complete problem-specific carry identification. Starting with an arbitrary reduced denominator $`D=D_{\mathrm{sm}}B`$, it must identify the ordered jump word and its block digits $`m_a`$, derive the bound $`K(B,a)`$, and prove that the denominator-cleared carry is divisible by $`D_{\mathrm{sm}}`$. Theorem <a href="#res:denominator-reduction" data-reference-type="ref" data-reference="res:denominator-reduction">12</a> then produces $`d_{n+1}=b_nd_n-Bm_n`$ with $`\gcd(B,30)=1`$ and the radix $`b_a=\beta_a`$ of Theorem <a href="#res:dyadic-alphabet" data-reference-type="ref" data-reference="res:dyadic-alphabet">11</a>. The second obligation is the Diophantine existence statement of Problem <a href="#prob:producer" data-reference-type="ref" data-reference="prob:producer">15</a>. No Lean theorem yet supplies that problem-specific carry identification or proves <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>.

<div id="prob:producer" class="problem">

**Problem 15** (cofinal local-window escape). With $`b_a=\beta_a\in\{2,6,10,30\}`$ the block radix of Theorem <a href="#res:dyadic-alphabet" data-reference-type="ref" data-reference="res:dyadic-alphabet">11</a>, and with $`m_a`$ and $`K(B,a)`$ as in the identification above, prove <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>: for every $`B>0`$ coprime to $`30`$ and every starting index there are a later $`\ell`$ and an $`h>0`$ with $`|W_{\ell,h}|>0`$ and
``` math
\operatorname{lpr}_{|W_{\ell,h}|}(-BF_{\ell,h})>K(B,\ell+h).
```

</div>

By Theorem <a href="#res:windowconsumer" data-reference-type="ref" data-reference="res:windowconsumer">14</a> a proof of Problem <a href="#prob:producer" data-reference-type="ref" data-reference="prob:producer">15</a> rules out the corresponding positive reduced carry; together with the identification above it supplies the missing contradiction for the three-prime case. Until both pieces are present, Problem #269 remains open.

For each $`B`$, condition <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a> asks only for a cofinal family of windows. The radix word is constrained to $`\{2,6,10,30\}`$, so the remaining arithmetic is in the block digit and its carry into the residue class, and one seeks blocks for which the modulus $`|W_{\ell,h}|`$ grows faster than the carry window and the weighted forcing $`-BF_{\ell,h}`$ does not remain trapped in the two short arcs adjacent to $`0`$ modulo that modulus. A theorem for one cofinal family is enough; no equidistribution of all windows is required.

None of the following weaker statements suffices, and each removes a false version of <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>. Merely proving $`2\le b_a\le30`$ loses the exact channel alphabet. A fixed finite list of denominator certificates does not address the universal $`B`$-quantifier. A bound independent of $`B`$ is not the bound delivered by denominator clearing. Large absolute forcing is irrelevant unless its *least positive residue* is large. In the other direction, a construction of infinitely many $`(B,\ell_0)`$ for which every such window family fails would show that no argument of this shape can succeed.

<div class="problem">

**Problem 16** (direct nonintegral tails). As an alternative to local windows, prove directly that for every positive $`B`$ coprime to $`30`$ the denominator-cleared tail of the actual $`\{2,3,5\}`$ expansion is nonintegral cofinally. Such a theorem would bypass <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>, but it would still have to be joined to the denominator-clearing step in the same way.

</div>

An analytic treatment of the three logarithmic coordinates would have to be genuinely three-dimensional: by Theorem <a href="#res:rank" data-reference-type="ref" data-reference="res:rank">10</a>, a preliminary separation into one-dimensional factors is unavailable even at $`\{2,3,5\}`$.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

The [pinned formal-source revision](https://github.com/wcook04/plectis-lean-erdos249-257/tree/234ced3455a73357c33113e8a285e1a3b3d411fb) contains the Lean sources, the fixed toolchain, the library manifest, and the exact dyadic-window checker used in the finite experiment. This manuscript provides navigation rather than proof authority.

<a id="declaration-of-generative-ai-use."></a>

#### Declaration of generative AI use.

Large-language-model agents were used throughout development to draft and revise prose, formal proofs, and software. The author set the objectives and acceptance criteria, selected and reviewed the claims, and approved the published version. The author assumes responsibility for the accuracy, interpretation, and presentation of the work. Generative systems are production tools; they are not authors and supply no independent authority. Lean checks each proof term against the fixed library version, and the sources linked here contain no proof placeholders and no project-defined axioms; Lean does not authorise the exposition, the citation choices, or the interpretation, for which the author remains responsible.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering and status follow the Erdős Problems catalogue maintained by Thomas Bloom \[erdosproblems\].

<a id="app:index"></a>

# Guide to the formal sources

Each linked phrase opens its Lean declaration at the pinned source revision 234ced3455a7. The running-LCM structure, residue arithmetic, and local-window bridge occupy three separate modules. Four distinctions are worth carrying into the source. The height statements hold for arbitrary bases, while the statements about $`\operatorname{L}`$ need the three primes to be distinct. The normal form of Section <a href="#sec:fibre" data-reference-type="ref" data-reference="sec:fibre">4</a> is a finite identity over a rectangular box, not a convergence theorem. The smooth part of a hypothetical denominator can be cancelled only after divisibility of the actual carry states by that factor is proved. And the formal cofinal-escape predicate is an unproved hypothesis of Theorem <a href="#res:windowconsumer" data-reference-type="ref" data-reference="res:windowconsumer">14</a>; its application to the actual $`\{2,3,5\}`$ word is not asserted.

<div class="thebibliography">

9

P. Erdős and R. L. Graham, [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf), Monogr. Enseign. Math. 28, Geneva, 1980, p. 65. P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. Erdős, letter to the editor (written 1 January 1973), Fibonacci Quart. **12** (1974), p. 335. T. F. Bloom, [*Erdős Problem \#269*](https://www.erdosproblems.com/269), `erdosproblems.com/269`, accessed 22 July 2026. The Formal Conjectures Authors, [*FormalConjectures.ErdosProblems.`269`*](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/269.lean), Lean source, 2025, accessed 27 July 2026. T. M. Apostol, *Introduction to Analytic Number Theory*, Springer, New York, 1976, Ch. 4. V. Kovač and T. Tao, *On several irrationality problems for Ahmes series*, [arXiv:2406.17593](https://arxiv.org/abs/2406.17593), 2024.

</div>
