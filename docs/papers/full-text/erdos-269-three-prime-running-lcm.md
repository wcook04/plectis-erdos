<a id="erdos-269-three-prime-running-lcm"></a>

# No Finite Separable Representation at Three Prime Generators

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

For three distinct primes, the reciprocal running-LCM kernel has nonsingular minors of every order, with the same indices in every third-coordinate layer. Diagonal rescaling leaves a binary floor carry whose threshold columns determine every finite sampled rank. This rules out finite exact separation of the kernel, not rationality of its sum. For the repeated $`\{2,3,5\}`$ series, we give the literal integral tail recurrence, a quadratic bound, exact denominator clearing and a residue criterion equivalent to irrationality. We do not prove the required cofinal escape. The two-prime comparison reproduces the earlier Hecke–Mahler reduction attributed to Steve Fan and distinguishes the repeated and distinct-height values. A concrete moving-boundary example explains why quadratic coefficient growth does not by itself yield finite-difference cancellation.

<a id="sec:problem"></a>

# Introduction

Let $`P`$ be a finite set of at least two primes and let $`\mathcal S_P`$ be the positive integers supported on $`P`$, including $`1`$. All sums below retain multiplicity unless explicitly marked distinct-height. Put
``` math
\operatorname{L}(x)=\operatorname{lcm}\{u\in\mathcal S_P:u\le x\},\qquad
 \mathcal R_P=\sum_{u\in\mathcal S_P}\operatorname{L}(u)^{-1}.
```
The historical question is whether $`\mathcal R_P`$ is irrational \[erdosgraham1980, p. 65\]\[erdos1988, p. 106\]. We address the repeated series, not the distinct-height assertion recorded by Erdős in his earlier letter \[erdos1974letter\]. For $`P=\{p,q,r\}`$, define
``` math
\operatorname{H}(x)=p^{\lfloor\log_p x\rfloor}
 q^{\lfloor\log_q x\rfloor}r^{\lfloor\log_r x\rfloor},\qquad
 \operatorname{K}(i,j,k)=\operatorname{H}(p^iq^jr^k)^{-1}.
```
Prime-power divisibility gives $`\operatorname{L}=\operatorname{H}`$ (Proposition <a href="#res:lcm" data-reference-type="ref" data-reference="res:lcm">6</a>). The supplied forum record credits Steve Fan’s post of 26 June 2026 with this identity for every finite prime set and the two-prime factorisation, reduction and transcendence conclusion \[fan2026comment\]. We retain that attribution; the live thread was not accessible during this revision.

With two primes, the corresponding kernel factors into a function of each exponent separately, reducing the double sum to a product. The first question at three primes is whether finitely many such products still suffice. Theorem <a href="#res:infinite-rank" data-reference-type="ref" data-reference="res:infinite-rank">1</a> rules this out: one floor carry survives after all row and column factors have been removed. The proof uses only this rescaling, the density of the rotations by $`\log_r p`$ and $`\log_r q`$ taken separately, and a staircase determinant, and one choice of indices serves every third-coordinate layer. We first explain that obstruction, then recover the two-prime comparison, and finally identify the arithmetic of the actual three-prime tails. The last step is necessary because the rank of a kernel does not determine the irrationality of its sum.

<a id="literature-and-scope."></a>

#### Literature and scope.

Fixed-prime semigroups and their neighbouring elements are classical objects; see Tijdeman–Meijer \[tijdemanmeijer1974\] and the recent two-prime study of Languasco, Luca, Moree and Togbé \[languasco2025\]. No asymptotic counting theorem from those works is needed for our elementary shell bounds. Kovač–Tao \[kovactao2024\] concerns neighbouring irrationality problems for distinct unit fractions, not this repeated-height sum. The rank theorem below concerns equality of kernels with arbitrary rational-valued separated factors. It does not exclude a different analytic representation of the scalar value.

<a id="reading-guide."></a>

#### Reading guide.

Section <a href="#sec:rank" data-reference-type="ref" data-reference="sec:rank">2</a> proves the representation theorem. The two-prime comparison in Section <a href="#sec:two-prime" data-reference-type="ref" data-reference="sec:two-prime">3</a> uses an external value theorem. Sections <a href="#sec:actual-orbit" data-reference-type="ref" data-reference="sec:actual-orbit">[sec:actual-orbit]</a> and <a href="#sec:escape" data-reference-type="ref" data-reference="sec:escape">5</a> define the actual arithmetic quantities and one open target, in equivalent tail and window forms. Source coordinates are collected in Appendix <a href="#app:sources" data-reference-type="ref" data-reference="app:sources">6</a> and the accompanying concordance, not used as substitutes for proofs.

<a id="sec:rank"></a>

# The binary carry and arbitrary-order rank

<div id="res:infinite-rank" class="theorem">

**Theorem 1** (arbitrary-order non-separability). *Let $`p,q,r`$ be primes with $`p\ne q`$, $`p\ne r`$ and $`q\ne r`$. For every $`n\ge0`$ there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$ such that, for every $`k\ge0`$,
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

*Proof.* Put $`c=r^{-1}`$, $`x_i=\{i\log_r p\}`$ and $`y_j=\{j\log_r q\}`$. Splitting the floor exponents gives
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
Both factors are positive. Distinct primes make $`\log_r p`$ and $`\log_r q`$ irrational, so each individual rotation is dense. No joint density of $`(x_i,y_j)`$ is needed. For $`n\ge1`$, use density of $`(x_i)`$ to choose distinct row indices with $`0<x_{I(0)}<\cdots<x_{I(n-1)}<1`$. Now put $`s_b=1-y_{J(b)}`$. Density of $`(y_j)`$ lets us choose

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
Indeed, subtracting each preceding row from the next, working upwards from the last row, leaves diagonal entries $`c,c-1,\ldots,c-1`$. Before normalisation, the determinant is this nonzero number times
``` math
\prod_{a<n}U_{I(a)}(k)^{-1}\prod_{b<n}V_{J(b)}(k)^{-1}.
```
The factors are nonzero, and the same $`I,J`$ work for every $`k`$. The empty minor for $`n=0`$ equals $`1`$.

For the final assertion, suppose a separation with $`d`$ summands existed and fix any $`k`$. On the rows $`I(0),\ldots,I(d)`$ and columns $`J(0),\ldots,J(d)`$ its matrix would be the product of the $`(d+1)\times d`$ matrix $`(f_\ell(I(a)))_{a,\ell}`$ and the $`d\times(d+1)`$ matrix $`(G_\ell(J(b),k))_{\ell,b}`$. Its rank would be at most $`d`$, so its determinant would vanish, contrary to the minor just constructed. ◻

</div>

<a id="scope-of-the-rank-obstruction."></a>

#### Scope of the rank obstruction.

The proof works over $`\mathbb R`$ or $`\mathbb C`$ as well as $`\mathbb Q`$: a factorisation through a $`d`$-dimensional space still has rank at most $`d`$. The displayed theorem retains the rational-valued scope of the supplied formal statement. Also $`p\ne q`$ is not used by the carry argument itself; it is retained because the running-LCM application has three distinct prime generators.

<div id="res:admissible-modular-minors" class="corollary">

**Corollary 2** (the same minors modulo every admissible denominator). *For $`(p,q,r)=(2,3,5)`$ and every $`n\ge1`$, there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$, chosen independently of $`B`$ and $`k`$, such that for every $`B\ge2`$ coprime to $`30`$ and every $`k\ge0`$, the selected $`n\times n`$ kernel matrix has unit determinant over $`\mathbb Z/B\mathbb Z`$, with each reciprocal prime power interpreted by its modular inverse.*

</div>

<div class="proof">

*Proof.* Choose the maps from Theorem <a href="#res:infinite-rank" data-reference-type="ref" data-reference="res:infinite-rank">1</a>. Every row and column factor is a unit modulo $`B`$. The normalised determinant is $`5^{-1}(-4/5)^{n-1}`$, also a unit. ◻

</div>

<div id="res:rank" class="example">

**Example 3**. For $`(p,q,r)=(2,3,5)`$, the leading two-by-two determinant is $`-1/15`$: its four entries are $`1,1/6,1/2,1/60`$, so it equals $`1/60-1/12`$.

</div>

<a id="the-indices-must-be-selected."></a>

#### The indices must be selected.

The leading $`4\times4`$ block at $`\{2,3,5\}`$ is singular:
``` math
\operatorname{K}(3,j,0)=\frac1{120}\operatorname{K}(0,j,0)\qquad(0\le j<4).
```
These equalities follow by evaluating the height at $`3^j`$ and $`8\cdot3^j`$. At $`j=4`$ the difference is $`-1/19440000`$. Thus the leading minors do not supply the arbitrary-order theorem.

<div id="res:finite-cut-rank" class="proposition">

**Proposition 4** (finite sampled cut rank). *Let $`m\ge1`$ and let $`c`$ lie in a field with $`c\ne 0,1`$. For $`0\le k\le m`$ write $`v_k`$ for the length-$`m`$ column with a $`1`$ in each of the first $`k`$ coordinates and $`c`$ thereafter. A matrix whose distinct columns are $`v_k`$ for $`k`$ in a nonempty set $`E`$ has rank $`|E|-\mathbf 1_{\{0,m\}\subseteq E}`$.*

</div>

<div class="proof">

*Proof.* List $`E=\{k_1<\cdots<k_t\}`$. The $`t-1`$ differences $`v_{k_{j+1}}-v_{k_j}=(1-c)\mathbf 1_{\{k_j,\ldots,k_{j+1}-1\}}`$ have disjoint nonempty supports, hence are linearly independent. If $`k_1>0`$ or $`k_t<m`$, their union misses a coordinate where $`v_{k_1}`$ is nonzero, so the rank is $`t`$. If $`k_1=0`$ and $`k_t=m`$, then $`v_0=c\,\mathbf 1`$ lies in the span of the differences (their sum is $`(1-c)\mathbf 1`$), so the rank is $`t-1`$. ◻

</div>

After ordering the sampled row phases, the columns have exactly the forms $`v_k`$ above; repeated rows or columns add no rank. Thus the formula classifies every nonempty finite sample after diagonal rescaling, uniformly in the third coordinate. It also gives an exact algorithm: order the rationals $`p^i/r^{\lfloor\log_r p^i\rfloor}`$, count those strictly below $`r^{\lfloor\log_r q^j\rfloor+1}/q^j`$, and apply the endpoint correction. Integer comparisons suffice; no floating-point decision at a threshold is needed.

<a id="the-norm-matters."></a>

#### The norm matters.

For the infinite normalised carry matrix,
``` math
\inf_{F\text{ of finite separated rank}}\|C-F\|_\infty=(1-c)/2.
```
For $`c=1/r`$, distinct columns are exactly $`1-c`$ apart in the supremum norm. An error $`\varepsilon<(1-c)/2`$ would place the approximating columns in a bounded subset of their finite-dimensional span, with pairwise distance at least $`1-c-2\varepsilon>0`$. Such a subset is totally bounded, a contradiction. This argument uses bounded columns, not bounded individual factors in a separated expression. The constant $`(1+c)/2`$ attains the bound.

Finite restrictions have a different behaviour. At $`c=1/5`$,
``` math
T=\begin{pmatrix}1/5&1\\1/5&1/5\end{pmatrix},\qquad
 A=\begin{pmatrix}3/10&9/10\\1/10&3/10\end{pmatrix}
```
satisfy $`\det A=0`$ and $`\|T-A\|_{\max}=1/10<2/5`$. For the original three-index kernel, put $`K^{(N)}(i,j,k)=\mathbf1_{\{i<N\}}K(i,j,k)`$. This has separated rank at most $`N`$ across $`i\mid(j,k)`$, and the $`\ell^1(\mathbb N^3)`$ error satisfies
``` math
\|K-K^{(N)}\|_{\ell^1}
 \le\frac{pqr\,p^{-3N}}{(1-p^{-3})(1-q^{-3})(1-r^{-3})}.
```
This follows from $`\operatorname{H}(x)>x^3/(pqr)`$. Thus the infinite uniform obstruction coexists with geometric approximation in the summation norm. The scalar irrationality question requires arithmetic information about the actual multiplicities.

<a id="sec:two-prime"></a>

# The two-prime comparison

For distinct primes $`p<q`$, write $`L_{p,q}(t)=p^{\lfloor\log_p t\rfloor}q^{\lfloor\log_q t\rfloor}`$. Prime-power divisibility identifies this product with the running LCM. Let $`\mathcal R_{p,q}`$ retain every smooth-number multiplicity, and let $`\mathcal D_{p,q}`$ retain the initial value and one reciprocal at each positive pure-power jump. Fan’s forum post gives the repeated two-prime factorisation and its quadratic reduction to a single Hecke–Mahler value, and the same boundary-channel calculation yields the de-duplicated affine formula displayed below \[fan2026comment\]. We give the calculation to fix normalisations and to distinguish repeated from distinct-height sums.

<div id="res:two-prime-transcendence" class="theorem">

**Theorem 5** (both two-prime sums). *<span id="res:two-prime-repeated-transcendence" label="res:two-prime-repeated-transcendence"></span> Let $`p<q`$ be distinct primes. Put $`\theta=\log p/\log q`$ and $`A=\sum_{n\ge0}p^{-n}q^{-\lfloor n\theta\rfloor}`$. Let $`\mathcal R_{p,q}`$ sum the reciprocal running LCM at every positive $`\{p,q\}`$-smooth integer, and let $`\mathcal D_{p,q}`$ count each distinct running LCM once. Then
``` math
\begin{equation}
\label{eq:two-prime-affine}
 \mathcal D_{p,q}=\frac{(q-p)A+p}{q-1},\qquad
 \mathcal R_{p,q}=\frac{(p+q-1)A-(p-1)A^2}{q-1}.
\end{equation}
```
Both numbers are transcendental.*

</div>

<div class="proof">

*Proof.* Set $`x=1/p`$, $`y=1/q`$, $`m_n=\lfloor n\theta\rfloor`$ and $`\delta_n=m_{n+1}-m_n`$. Unique factorisation makes $`\theta`$ irrational, and $`0<\theta<1`$ gives $`\delta_n\in\{0,1\}`$. The initial value and the $`p`$-channel contribute $`A=\sum_{n\ge0}x^ny^{m_n}`$. There is one $`q`$-power between $`p^n`$ and $`p^{n+1}`$ precisely when $`\delta_n=1`$, so the other channel contributes
``` math
B=\sum_{n\ge0}\delta_nx^ny^{m_n+1},\qquad \mathcal D_{p,q}=A+B.
```
All these series converge absolutely. Since $`y^{m_{n+1}}-y^{m_n}=\delta_ny^{m_n}(y-1)`$, shifting the series for $`A`$ gives $`A-1-xA=x(y-1)B/y`$. Therefore
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

The two-prime reduction expresses both sums through one value. The third prime leaves the binary carry of Section <a href="#sec:rank" data-reference-type="ref" data-reference="sec:rank">2</a>. Its rank theorem concerns that function; the scalar arithmetic depends on the multiplicities introduced next. The de-duplicated irrationality assertion is historical \[erdos1974letter\].

<a id="sec:lcm"></a>

# Exact multiplicities and normalised tails

<span id="sec:cells" label="sec:cells"></span><span id="sec:fibre" label="sec:fibre"></span><span id="sec:shell" label="sec:shell"></span> <span id="sec:actual-orbit" label="sec:actual-orbit"></span>

<div id="res:lcm" class="proposition">

**Proposition 6** (the running least common multiple). *Let $`p,q,r`$ be pairwise distinct primes and $`x\ge1`$. Then the running LCM equals the three-prime height: $`\operatorname{L}(x)=\operatorname{H}(x)`$.*

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

**Proposition 7** (cells and jumps). *The running LCM is constant when the three integer logarithms are constant. A jump in exactly one logarithm multiplies it by the corresponding prime. The first $`n`$ positive powers in each channel, together with $`1`$, form $`3n+1`$ distinct points.*

</div>

<div class="proof">

*Proof.* The first two claims follow from the height formula. Positive powers from different prime channels cannot coincide, by unique factorisation, and none is $`1`$. ◻

</div>

<div id="res:fibre-prop" class="proposition">

**Proposition 8** (height-fibre regrouping). *For a finite exponent box $`\mathcal B`$, set $`F(H)=\{(i,j,k)\in\mathcal B:\operatorname{H}(p^iq^jr^k)=H\}`$. Then
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
Thus $`T_a`$ is the raw tail, $`X_a`$ its normalised state, and $`P_a:=\operatorname{H}(2^a)=2h_a`$. In particular $`h_0=1/2`$, while $`h_a`$ is a positive integer for $`a\ge1`$. The literal radix and forcing numerator are
``` math
\begin{equation}
\label{eq:actual-digit}
 b_a=\frac{\operatorname{H}(2^{a+1})}{\operatorname{H}(2^a)},\qquad
 m_a=\sum_{\substack{x\text{ smooth}\\2^a\le x<2^{a+1}}}
       \frac{\operatorname{H}(2^{a+1})}{2\operatorname{H}(x)}.
\end{equation}
```

<div id="res:dyadic-alphabet" class="lemma">

**Lemma 9** (integer forcing and the four radices). *For every $`a\ge0`$, $`m_a`$ is a positive integer and $`b_a\in\{2,6,10,30\}`$. The word “numerator” does not impose the positional-digit restriction $`m_a<b_a`$; that restriction need not hold.*

</div>

<div class="proof">

*Proof.* If $`x<2^{a+1}`$, the two-exponent of $`\operatorname{H}(x)`$ is at most $`a`$, while the other exponents are bounded by those of $`\operatorname{H}(2^{a+1})`$. Hence $`2\operatorname{H}(x)\mid\operatorname{H}(2^{a+1})`$. Each forcing summand is an integer, and the shell contains $`2^a`$. Between consecutive two-powers there is at most one three-power and at most one five-power: two successive powers in either channel have ratio strictly greater than two. Their optional factors, together with the terminal factor two, give the four radices. ◻

</div>

Since $`h_{a+1}=b_0b_1\cdots b_a/2`$, the value $`S/2=\sum_{a\ge0}m_a/(b_0b_1\cdots b_a)`$ is a Cantor series and $`X_a=\sum_{j\ge a}m_j/(b_a\cdots b_j)`$ is its normalised tail. Such tails, with their integer carry recurrence, are the classical tool for the rationality of Cantor series. Erdős and Straus characterise rationality by integer carries \[erdosstraus1974, Theorem 2.1 and (2.4), pp. 85–86\], and Hančl and Tijdeman give a practical form of that criterion through the tails \[hancltijdeman2004, §§2–3 and Theorem 3.1, pp. 372–375\]. Both criteria assume that the $`n`$th numerator is $`o(a_{n-1}a_n)`$, where $`a_n`$ is the $`n`$th base. Here $`m_a\ge1`$ and $`b_{a-1}b_a\le900`$, so the recurrence, the bound and the denominator clearing below are proved directly for this series. The polynomial criterion of Hančl–Tijdeman \[hancltijdeman2008, Theorems 2.2 and 3.1\] assumes a nonconstant polynomial radix and does not cover this bounded sequence. Their Theorem 4.2 is a separate, more general telescoping principle: it requires an exact finite-product decomposition and a small transformed numerator. Neither a quadratic bound nor a polynomial carry ansatz supplies those hypotheses. The prior Isabelle/HOL formalisation of the classical Erdős–Straus criteria is due to Koutsoukou-Argyraki and Li \[afperdosstraus2020\]; it is not a verification of the present series.

<div id="res:actual-orbit" class="proposition">

**Proposition 10** (the actual recurrence and a polynomial bound). *The series defining $`S,T_a`$ converge. For every $`a\ge0`$,
``` math
X_{a+1}=b_aX_a-m_a,\qquad
 0<X_a\le\frac{8640}{343}(a+1)^2<90(a+1)^2.
```
For every integer $`B\ge1`$, either some $`BX_a`$ is integral and all later states are integral, or $`\operatorname{dist}(BX_a,\mathbb Z)\ge1/31`$ at arbitrarily large indices.*

</div>

<div class="proof">

*Proof.* A dyadic shell contains at most one two-exponent for each pair of three- and five-exponents. Each of the latter lies between $`0`$ and $`a`$, so there are at most $`(a+1)^2`$ terms. By <a href="#res:cube" data-reference-type="eqref" data-reference="res:cube">[res:cube]</a>, $`s_a\le30(a+1)^2/8^a`$. Therefore
``` math
X_a\le15(a+1)^2\sum_{j\ge0}\frac{(j+1)^2}{8^j}
      =\frac{8640}{343}(a+1)^2.
```
This proves convergence and the bound. Splitting the first shell gives the recurrence because $`m_a=h_{a+1}s_a`$ and $`h_{a+1}=b_ah_a`$. Put $`Y_a=BX_a`$. If all sufficiently late distances are strictly below $`1/31`$, write $`Y_a=z_a+e_a`$ with $`z_a\in\mathbb Z`$ and $`|e_a|<1/31`$. Then $`e_{a+1}-b_ae_a`$ is an integer of absolute value less than one, so $`e_{a+1}=b_ae_a`$. The factors $`b_a\ge2`$ force a bounded such error to be zero. An integral state propagates by the integer recurrence. ◻

</div>

The window criterion needs only a valid carry cap; $`90B(a+1)^2`$ suffices. The long record proves $`X_a\le Q(n_a)`$ and the smaller bound $`X_a\le\widetilde Q(n_a)`$, where $`n_a=a+\lfloor\log_3 2^a\rfloor+\lfloor\log_5 2^a\rfloor`$. It keeps these sharper caps separate from the coarse cap used here.

<div id="res:denominator-reduction" class="theorem">

**Theorem 11** (actual rationality-to-reduced-carry bridge). *If $`S=A/D`$ in lowest terms, where $`D=2^u3^v5^wB`$ and $`\gcd(B,30)=1`$, then for every $`a\ge a_0=u+1+2v+3w`$,
``` math
d_a=BX_a\in\mathbb Z_{>0},\qquad
 d_{a+1}=b_ad_a-Bm_a,\qquad d_a\le90B(a+1)^2.
```*

</div>

<div class="proof">

*Proof.* For $`a\ge1`$, strict boundary clearing gives
``` math
\begin{equation}
\label{eq:prefix-lattice}
 X_a=h_aS-Z_a,\qquad
 Z_a=\sum_{\substack{x\text{ smooth}\\x<2^a}}\frac{h_a}{\operatorname{H}(x)}\in\mathbb Z.
\end{equation}
```
The two-exponent of $`h_a`$ is $`a-1`$. Moreover $`a\ge2v`$ gives $`2^a\ge3^v`$, and $`a\ge3w`$ gives $`2^a\ge5^w`$. Thus $`2^u3^v5^w\mid h_a`$ after the stated onset, and $`BX_a=h_aA/(2^u3^v5^w)-BZ_a`$ is integral. Positivity, the recurrence and the bound follow from Proposition <a href="#res:actual-orbit" data-reference-type="ref" data-reference="res:actual-orbit">10</a>. ◻

</div>

<div id="res:exact-onset" class="corollary">

**Corollary 12** (the exact clearing onset). *Under the same lowest-terms hypothesis, put $`M=2^u3^v5^w`$ and let $`\operatorname{den}`$ denote the positive reduced denominator. For $`a\ge1`$,
``` math
\operatorname{den}(BX_a)=\frac{M}{\gcd(M,h_a)}.
```
Consequently $`BX_a`$ is integral exactly when $`2^a\ge\max(2^{u+1},3^v,5^w)`$. The first such $`a`$ can be found by integer comparisons, without logarithmic rounding.*

</div>

<div class="proof">

*Proof.* Equation <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a> gives $`BX_a=h_aA/M-BZ_a`$. Since $`\gcd(A,M)=1`$, reducing that fraction gives the displayed denominator. The three divisibility conditions for $`h_a`$ are precisely the three inequalities stated above. ◻

</div>

<a id="sec:escape"></a>

# A window test and the remaining arithmetic

<span id="sec:open" label="sec:open"></span> The actual digits in <a href="#eq:actual-digit" data-reference-type="eqref" data-reference="eq:actual-digit">[eq:actual-digit]</a> define
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
For integers $`W\ge1`$ and $`t`$, define $`\operatorname{lpr}_W(t)=1+((t-1)\bmod W)`$, using a remainder in $`\{0,\ldots,W-1\}`$. Thus a zero residue is represented by $`W`$, not $`0`$. Throughout this section use the valid cap
``` math
\begin{equation}
\label{eq:actual-bound}
 K(B,a)=90B(a+1)^2.
\end{equation}
```

<div id="res:consumer" class="lemma">

**Lemma 13** (finite endpoint obstruction). *If $`d`$ is a positive integer with $`d\le K`$ and $`d\equiv -BF\pmod W`$, where $`W\ge1`$, then $`\operatorname{lpr}_W(-BF)\le K`$.*

</div>

<div class="proof">

*Proof.* Every positive representative of the residue is at least its least positive representative, so $`\operatorname{lpr}_W(-BF)\le d\le K`$. ◻

</div>

<div id="res:windowconsumer" class="theorem">

**Theorem 14** (the actual window criterion). *The number $`S`$ is irrational if and only if
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

*Proof.* If $`S`$ is rational, Theorem <a href="#res:denominator-reduction" data-reference-type="ref" data-reference="res:denominator-reduction">11</a> supplies a positive integral carry $`d_a=BX_a`$ after its onset. Choose a window in <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a> beyond that onset. Equation <a href="#eq:actual-tail" data-reference-type="eqref" data-reference="eq:actual-tail">[eq:actual-tail]</a> gives $`d_{\ell+h}\equiv-BF_{\ell,h}\pmod{W_{\ell,h}}`$, contradicting Lemma <a href="#res:consumer" data-reference-type="ref" data-reference="res:consumer">13</a> and the valid cap.

Conversely, let $`S`$ be irrational and fix $`B,\ell\ge1`$. Equation <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a> makes $`BX_\ell`$ nonintegral. Put $`\delta=\lceil BX_\ell\rceil-BX_\ell\in(0,1)`$. Since $`W_{\ell,h}\ge2^h`$ and $`X_{\ell+h}=O((\ell+h+1)^2)`$, for all sufficiently large $`h`$ the number $`\delta+BX_{\ell+h}/W_{\ell,h}`$ lies in $`(0,1)`$. The window identity then gives the exact equality
``` math
\operatorname{lpr}_{W_{\ell,h}}(-BF_{\ell,h})
 =\delta W_{\ell,h}+BX_{\ell+h}.
```
Its exponentially growing first term eventually exceeds $`K(B,\ell+h)`$. This proves <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>, in fact from each fixed start. ◻

</div>

The validity of the cap is needed in the rational direction; an upper polynomial growth condition by itself would not suffice. The zero cap, for example, makes positive-residue escape automatic. The criterion identifies the target in window coordinates. The unresolved point is the source-specific exclusion below.

<div class="problem">

**Problem 15** (the repeated three-prime target). Prove that $`S=\mathcal R_{\{2,3,5\}}`$ is irrational.

</div>

<div id="prob:tails269" class="problem">

**Problem 16** (exact nonintegrality of every reduced tail). Prove that for every $`a\ge1`$ and every integer $`B\ge1`$ coprime to $`30`$,
``` math
\begin{equation}
\label{eq:tail-nonintegrality}
 BX_a\notin\mathbb Z.
\end{equation}
```

</div>

<div id="prob:producer" class="problem">

**Problem 17** (actual cofinal local-window escape). Prove the cofinal window condition <a href="#eq:escape" data-reference-type="eqref" data-reference="eq:escape">[eq:escape]</a>.

</div>

Indeed, one integral scaled tail makes $`S`$ rational by <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a>; conversely, a rational $`S`$ has such tails after denominator clearing. These are equivalent formulations of one target, not two independent missing hypotheses.

<a id="a-coefficient-obstruction-not-a-transferred-theorem."></a>

#### A coefficient obstruction, not a transferred theorem.

Luca, Ouaknine and Worrell \[lucaouaknineworrell2025, Definition 5, Theorems 6 and 8, Claim 10\] use finite-difference cancellation away from floor crossings, followed by expanding-gap and relative-variation estimates. For our literal numerators, put $`\gamma_{a,t}=P_tP_{a+1}/P_{a+t+1}`$ and $`D_{r,a}=15\sum_{j=0}^3(-1)^j\binom3j\gamma_{a,jr}m_{a+jr}`$. At $`a=0,r=35`$, exact comparisons give $`\lfloor\log_3 2^{35\nu}\rfloor=22\nu`$, $`\lfloor\log_5 2^{35\nu}\rfloor=15\nu`$ and $`b_{35\nu}=2`$ for $`0\le\nu\le3`$. These facts together eliminate the relevant floor-addition crossings and make all four corrections $`1`$. Nevertheless
``` math
D_{35,0}=15(1-3\cdot195+3\cdot723-1582)=45\ne0.
```
The long record proves this by exact lattice counts and isolates the uncancelled boundary strips. It refutes automatic cubic cancellation, not every possible operator or an eventual sparse-defect construction.

A fixed-base expansion is not impossible: the direct base-$`30`$ recoding has coefficients $`e_a=m_a30^{a+1}/P_{a+1}\in\mathbb Z_{>0}`$, but $`e_a\ge(15/4)^{a+1}`$, so it fails the polynomial-growth hypothesis of the cited criterion. The finite-alphabet echoing criterion \[kebis2024echoing\] and the base-expansion complexity theorem \[adamczewskibugeaud2007, Theorem 1\] likewise require properties of a value-preserving coefficient or digit sequence, not merely of $`(b_a)`$.

<a id="a-separate-distinct-height-programme."></a>

#### A separate distinct-height programme.

For $`\mathcal D_{2,3,5}`$, recovering a proof of the historical irrationality assertion or establishing transcendence is a different task. An analytic approach must first construct a specified function and an exact value identity, then verify a published value theorem’s hypotheses. In particular, the multivariate Mahler theory of Adamczewski and Faverjon \[adamczewskifaverjon2026\] requires a functional system and suitable evaluation data; having a two-dimensional lattice count is not enough. No such system is established here.

<a id="the-information-the-remaining-argument-must-use."></a>

#### The information the remaining argument must use.

The bounded-radix alternative permits the integral branch. If $`(g_a)`$ is an unbounded sequence of positive integers with bounded successive ratios, the real $`\xi`$ with $`\operatorname{dist}(g_a\xi,\mathbb Z)\to0`$ form a countable set. For increasing sequences this is due to Erdős and Taylor \[erdostaylor1957, Theorem 1, p. 600\], who obtain it by modifying Eggleston’s proof of his Theorem 16, and Fan proves the form stated here \[fan2026strongly, Lemma 3.1, p. 7\]. For $`g_a=Bh_a`$ $`(a\ge1)`$ the ratios are the integers $`b_a\in\{2,6,10,30\}`$, and the argument of Proposition <a href="#res:actual-orbit" data-reference-type="ref" data-reference="res:actual-orbit">10</a> identifies the set: it consists of the $`\xi`$ for which $`Bh_a\xi`$ is eventually an integer. By <a href="#eq:prefix-lattice" data-reference-type="eqref" data-reference="eq:prefix-lattice">[eq:prefix-lattice]</a> and Theorem <a href="#res:denominator-reduction" data-reference-type="ref" data-reference="res:denominator-reduction">11</a> it contains $`S`$ for some $`B`$ exactly when $`S`$ is rational. Infinite rank and the modular minors of Corollary <a href="#res:admissible-modular-minors" data-reference-type="ref" data-reference="res:admissible-modular-minors">2</a> constrain the kernel, while a scalar argument must also use its exact multiplicities. The long record gives further conditional rigidity statements, but an argument for $`S`$ must verify their block identities for the actual weighted multiplicities. Neither a finite-dimensional ansatz nor a countability statement does that.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="proof-sources."></a>

#### Proof sources.

The two-prime deduction uses an external transcendence theorem and is not formalised here. The arbitrary-order rank theorem and literal tail bridge have the named Lean sources recorded in the concordance. Two verification tracks must be kept separate: the public repository and the selected Palomar release. The supplied 16 September 2026 inventory records a successful public CI build at commit `99f4bf47422abbd8757cbb22b50ba079d764d3a7`. The separate Palomar release at `52f29ad1` selects the arbitrary-order uniform-minor and non-separation theorems themselves, not merely the $`2\times2`$ fixture. Its recorded Comparator replay therefore has that broader scope. These are attached verification receipts, not a fresh build performed for this editorial revision, and do not certify every sentence of either paper or the irrationality of $`S`$. The elementary modular-minor corollary is proved above. Its older linked module is not among the attached source files, so its current build status is not inferred from the inventory. The exact-denominator corollary and the boundary example added in this revision have ordinary proofs and exact checks, but no new formalisation claim. The required cofinal escape remains unproved.

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

Each source link is pinned to its own immutable revision. The exact-reference inventory records those revisions and their bytewise comparison with the public source commit recorded in the supplied inventory. The extended reasoning record and the accompanying source retain the detailed shell bounds, finite experiments and alternative representations with their exact hypotheses. Supplied later-source labels and public links remain separate source coordinates.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering and the historical status snapshot are taken from the Erdős Problems catalogue maintained by Thomas Bloom \[erdosproblems\]. Earlier mathematical inputs are credited at their points of use.

<a id="app:sources"></a>

# Guide to the formal sources

The mathematical dependency chain is: height identity, kernel rescaling, threshold determinant; and, independently, literal shell forcing, tail recurrence, denominator clearing and residue contradiction. The historical declaration inventory is retained in the long record and the machine-readable source index. The package also includes an exact concordance of the links removed from the main narrative. Moving a link changes its location, not its immutable revision or evidence status.

<div class="center">

| Statement family | Source and scope |
|:---|:---|
| Kernel rank | `KernelCarryRank`: arbitrary-order uniform minors and no finite rational separation; also selected in the Palomar release. |
| Literal series | `DyadicShellSummability`, `RationalityCarryBridge`: actual summable tails and denominator clearing, not merely an abstract recurrence. |
| Quadratic bounds | `PaperR8RankMajorant` and `ActualSharpTailMajorantR10`: the actual $`Q`$ bound and the smaller jump-constrained bound recorded in the long paper. |
| Residue equivalence | `CofinalWindowEscapeEquivalence` and `R12/OcticWindowBand`: conditional consumer and exact equivalence, not an unconditional cofinal producer. |
| External input | Bugeaud–Laurent and Loxton–van der Poorten for the two-prime theorem; no Lean value theorem claimed. |

</div>

The public inventory supplied for this revision pins commit `99f4bf47422abbd8757cbb22b50ba079d764d3a7`; historical hyperlinks in the text retain their own revisions. A source location, a CI build, a selected Comparator statement and an axiom audit are different evidence items. None may stand in for the others without its own receipt.

<a id="sec:pinned-lean-sources"></a>

# Pinned Lean sources

The following declarations are this note’s pin-faithful source inventory. Line numbers are those of the commit named by `\commit`.

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L123)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L179)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L326)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L339)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L352)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L278)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L406)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L699)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L668)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L646)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L31)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L36)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L40)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L46)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L53)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L59)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L77)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L84)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L97)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L110)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L163)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L169)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L191)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L204)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L208)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L219)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L229)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L243)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L249)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L273)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L294)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L305)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L316)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L368)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L373)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L377)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L384)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L430)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L443)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L450)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L458)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L467)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L479)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L487)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L490)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L500)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L509)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L543)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L585)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L629)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L662)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L711)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L26)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L31)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L52)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L71)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L76)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L96)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L110)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L417)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L422)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L455)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L469)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L480)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L548)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L581)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L601)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L612)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L629)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L645)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L721)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ResidueEscape.lean#L138)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/BoundedRadixTailEscape.lean#L89)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L497)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/WeightedPhaseCarry.lean#L109)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/WeightedPhaseCarry.lean#L293)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/WeightedPhaseCarry.lean#L334)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/WeightedPhaseCarry.lean#L150)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/WeightedPhaseCarry.lean#L157)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/ThreeChannelBlockRigidity.lean#L59)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/CarryLiftExtinction.lean#L178)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/CarryLiftExtinction.lean#L238)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/CarryLiftExtinction.lean#L289)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos269/CarryLiftExtinction.lean#L308)

<div class="thebibliography">

99 Paul Erdős and Ronald L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L’Enseignement Mathématique **28**, L’Enseignement Mathématique (1980), [source](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). Paul Erdős, *On the irrationality of certain series: problems and results*, in *New Advances in Transcendence Theory*, Cambridge University Press (1988), 102–109, [doi:`10.1017/CBO9780511897184.009`](https://doi.org/10.1017/CBO9780511897184.009). Paul Erdős, *Letter to the Editor*, Fibonacci Quarterly **12**, no. 4 (1974), 335, [source](https://www.fq.math.ca/Scanned/12-4/letter.pdf). Thomas F. Bloom, *Erdős Problem \#269* (2026), [source](https://www.erdosproblems.com/269). Catalogue snapshot cited in the supplied manuscript: 28 July 2026. Yann Bugeaud and Michel Laurent, *Transcendence and continued fraction expansion of values of Hecke–Mahler series*, Acta Arithmetica **209** (2023), 59–90, [doi:`10.4064/aa220323-18-1`](https://doi.org/10.4064/aa220323-18-1); arXiv:[2203.12901](https://arxiv.org/abs/2203.12901). John H. Loxton and Alfred J. van der Poorten, *Arithmetic properties of certain functions in several variables III*, Bulletin of the Australian Mathematical Society **16** (1977), 15–47, [doi:`10.1017/S0004972700022978`](https://doi.org/10.1017/S0004972700022978). Steve Fan, *Comment on Erdős Problem \#269, thread 269, post 7218* (2026), [source](https://www.erdosproblems.com/forum/thread/269#post-7218). 26 June 2026, thread 269, post 7218; priority retained from the supplied record. Paul Erdős and Ernst G. Straus, *On the irrationality of certain series*, Pacific Journal of Mathematics **55**, no. 1 (1974), 85–92, [doi:`10.2140/pjm.1974.55.85`](https://doi.org/10.2140/pjm.1974.55.85). Jaroslav Hančl and Robert Tijdeman, *On the irrationality of Cantor and Ahmes series*, Publicationes Mathematicae Debrecen **65**, no. 3–4 (2004), 371–380, [doi:`10.5486/PMD.2004.3254`](https://doi.org/10.5486/PMD.2004.3254). Paul Erdős and S. James Taylor, *On the set of points of convergence of a lacunary trigonometric series and the equidistribution properties of related sequences*, Proceedings of the London Mathematical Society **s3-7**, no. 1 (1957), 598–615, [doi:`10.1112/plms/s3-7.1.598`](https://doi.org/10.1112/plms/s3-7.1.598). Steve Fan, *Strongly complete sets and a conjecture of Erdős* (2026), [source](https://arxiv.org/abs/2607.14071v1); arXiv:[2607.14071](https://arxiv.org/abs/2607.14071). The cited Lemma 3.1 is in arXiv v1, 15 July 2026. Jaroslav Hančl and Robert Tijdeman, *On the irrationality of polynomial Cantor series*, Acta Arithmetica **133**, no. 1 (2008), 37–52, [doi:`10.4064/aa133-1-3`](https://doi.org/10.4064/aa133-1-3). Florian Luca, Joël Ouaknine and James Worrell, *Transcendence of Hecke–Mahler Series*, Bulletin of the London Mathematical Society **57**, no. 5 (2025), 1360–1368, [doi:`10.1112/blms.70033`](https://doi.org/10.1112/blms.70033); arXiv:[2412.07908](https://arxiv.org/abs/2412.07908). Numbered references use the published article. Pavol Kebis, Florian Luca, Joël Ouaknine, Andrew Scoones and James Worrell, *On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words*, in *51st International Colloquium on Automata, Languages, and Programming (ICALP 2024)*, Leibniz International Proceedings in Informatics **297**, Schloss Dagstuhl – Leibniz-Zentrum für Informatik (2024), 144:1–144:15, [doi:`10.4230/LIPIcs.ICALP.2024.144`](https://doi.org/10.4230/LIPIcs.ICALP.2024.144). Robert Tijdeman and H. G. Meijer, *On integers generated by a finite number of fixed primes*, Compositio Mathematica **29**, no. 3 (1974), 273–286, [source](https://www.numdam.org/article/CM_1974__29_3_273_0.pdf). Alessandro Languasco, Florian Luca, Pieter Moree and Alain Togbé, *Sequences of integers generated by two fixed primes*, Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg **95** (2025), 123–148, [doi:`10.1007/s12188-025-00293-9`](https://doi.org/10.1007/s12188-025-00293-9); arXiv:[2309.12806](https://arxiv.org/abs/2309.12806). Vjekoslav Kovač and Terence Tao, *On several irrationality problems for Ahmes series*, Acta Mathematica Hungarica **175** (2025), 572–608, [doi:`10.1007/s10474-025-01528-0`](https://doi.org/10.1007/s10474-025-01528-0); arXiv:[2406.17593](https://arxiv.org/abs/2406.17593). Angeliki Koutsoukou-Argyraki and Wenda Li, *Irrationality Criteria for Series by Erdős and Straus*, Archive of Formal Proofs (2020), [source](https://isa-afp.org/entries/Irrational_Series_Erdos_Straus.html). Entry dated 12 May 2020; proof-document version consulted: 6 February 2026. Boris Adamczewski and Yann Bugeaud, *On the complexity of algebraic numbers I. Expansions in integer bases*, Annals of Mathematics **165**, no. 2 (2007), 547–565, [doi:`10.4007/annals.2007.165.547`](https://doi.org/10.4007/annals.2007.165.547). Boris Adamczewski and Colin Faverjon, *Mahler’s method in several variables and finite automata*, Annals of Mathematics **204**, no. 2 (2026), 455–533, [doi:`10.4007/annals.2026.204.2.1`](https://doi.org/10.4007/annals.2026.204.2.1). Online 13 September 2026; locators here refer to the [68-page author manuscript](https://faverjon.perso.math.cnrs.fr/AdamczewskiFaverjon_MahlerFiniteAutomata.pdf).

</div>

*Companion system context.* The [claim and trust boundary](../../../paper/systems/claim-faithful-publication-systems-paper.pdf#nameddest=systems-trust), [cold-clone route to proof authority](../../../paper/systems/cold-clone-to-proof-receipt.pdf#nameddest=cold-clone-authority), and [public contribution protocol](../../../paper/systems/open-source-mathematics-strategy.pdf#nameddest=strategy-protocol) are described in sibling papers. Those descriptions do not change the mathematical status of this note.
