<a id="erdos-1049-rational-base-lambert"></a>

# Zudilin’s Forms at Rational Bases and the Exact Normalised Hankel Order

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

We specialise Zudilin’s 2004 $`q`$-harmonic linear forms to prove that $`F(a/b)=\sum_{n\ge1}((a/b)^n-1)^{-1}`$ is irrational for coprime integers $`a>b\ge1`$ whenever $`\log b/\log a<\theta^*`$, where $`\theta^*=0.4056830213840605\ldots`$. In particular, $`F((31/4)^r)`$ is irrational for every integer $`r\ge1`$, with the same upper bound $`301`$ for the irrationality exponent at every $`r`$. The forms, their permutation-group integrality, the direction $`(14,12,14;27)`$ and the constants are Zudilin’s. The proof here uses his polynomial integrality statement before integer specialisation, cancels cyclotomic factors before homogenisation, and establishes the cancelled degree and positive-remainder estimates. It does not reach $`3/2`$. For the different normalised Hankel family in Zudilin’s 2016 construction, we sharpen the lower bound for the formal order to
``` math
\operatorname{ord}_q V_N^*=\frac{N(N-1)(2N-1)}6,
 \qquad [q^{\operatorname{ord}_q V_N^*}]V_N^*
       =\frac{(N!)^2(N+1)!}{2^N}.
```
The proof identifies a unique least-order tuple in the classical moment–Vandermonde expansion. We also state the precise limits of a base-uniform rank-two degree estimate and of local residue collisions: neither supplies the small nonzero integral forms still required at $`3/2`$. The principal irrationality and formal-order results have source-applied Lean declarations; the mathematical proofs are given in the text.

<a id="sec:problem"></a>

# Introduction

For $`t>1`$, expansion of each geometric series gives
``` math
F(t)=\sum_{n\ge1}\frac1{t^n-1}
     =\sum_{n\ge1}\frac{\tau(n)}{t^n},
```
where $`\tau(n)`$ is the number of positive divisors of $`n`$. The rearrangement is justified by nonnegativity, and the resulting series converges since $`\tau(n)\le n`$ and $`\sum_{n\ge1}nt^{-n}<\infty`$.

Chowla conjectured that $`F(t)`$ is irrational for every rational $`t>1`$, as Erdős records \[erdos1988, p. 102\]; this is Erdős Problem #1049. Specialising Zudilin’s 2004 construction to rational bases, Theorem <a href="#res:rational-base-threshold" data-reference-type="ref" data-reference="res:rational-base-threshold">1</a> proves irrationality on an explicit region that contains the power family in Corollary <a href="#res:thirtyone-four" data-reference-type="ref" data-reference="res:thirtyone-four">2</a>.

Cyclotomic cancellation in the linear forms of Zudilin’s 2004 construction \[zudilin2004\] produces positive forms $`\Lambda_n=U_nF-V_n`$ with integral coefficient polynomials of degree at most $`W_n`$, and
``` math
\log\!\bigl(b^{W_n}\Lambda_n(a/b)\bigr)
 =\bigl(C_1\log b-C_0\log a\bigr)n^2+o(n^2).
```
A negative exponent yields positive linear forms with integer coefficients tending to zero; the values need not themselves be integers.

The order of these operations explains the region. At a rational base $`a/b`$, each remaining polynomial degree costs a power of $`b`$ when denominators are cleared. Cancelling a common cyclotomic factor first reduces that degree. The proof must then compare the actual cancelled degree with the decay of the positive remainder; divisibility alone gives neither estimate.

The Hankel argument concerns a different family: the 2016 normalised remainders, not the 2004 coefficient pair. Section <a href="#sec:hankel-order" data-reference-type="ref" data-reference="sec:hankel-order">3</a> identifies one increasing moment-index tuple responsible for the first coefficient. Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">4</a> separates local divisibility at $`3/2`$ from nonvanishing and a real size estimate. The long record supplies the positive-measure proof, source comparisons and excluded constructions.

<a id="related-methods-and-notation."></a>

#### Related methods and notation.

The integer-base digit argument and its repair for signed coefficients are represented by Vandehey \[vandehey2013, Thms. 1.1–1.2, p. 2\]; Duverney and Tachiya obtain integer-base linear-independence refinements \[duverneytachiya2019, Thms. 1.1–1.2 and Cor. 1.1, pp. 2–3\]. These are not rational-base denominator estimates. Van Assche’s little $`q`$-Legendre approximants provide the orthogonal-polynomial comparison \[vanassche2001, (4), (9), (16), pp. 3–4\]. Throughout, $`F`$ denotes the Lambert value. The function parameter is $`q=p^{-1}`$ when $`p>1`$; the Gaussian polynomial $`{m\brack k}_p`$ uses base $`p`$, not $`q`$. The indices $`n`$ and $`N`$ denote, respectively, approximation scale and Hankel rank. A formal order as $`q\to0`$ is not an asymptotic estimate as $`N\to\infty`$ at fixed $`q`$. We use $`(z;q)_m=\prod_{j=0}^{m-1}(1-zq^j)`$, with empty products and empty determinants equal to $`1`$. The local symbol $`N=15n`$ in the next proof is a cyclotomic cutoff, not a Hankel rank. All logarithms are natural; constants in $`O_x(\cdot)`$ may depend on the fixed base $`x`$.

<a id="sec:rational-base-irrationality"></a>

# A rational base at which $`F`$ is irrational

The direction $`(14,12,14;27)`$, the thirteen intervals and the constants $`C_1,C_0`$ below are those of Zudilin’s construction \[zudilin2004, §5, pp. 161–162\]; there $`C_1/C_0=2.46497868\ldots`$ is his bound for the irrationality exponent at integer bases \[zudilin2004, Thm. 1, p. 154\]. Write $`\psi_1(u)=\sum_{k\ge0}(k+u)^{-2}`$. Let $`\mathcal I`$ be the thirteen intervals listed in the proof and put
``` math
C_1=\frac{1091}{2},\qquad
 J=\sum_{[u,v)\in\mathcal I}\bigl(\psi_1(u)-\psi_1(v)\bigr),\qquad
 C_0=266-\frac3{\pi^2}(225-J).
```
Thus $`\theta^*=C_0/C_1`$ and $`\mu=C_1/C_0`$ are defined exactly. Here $`\mu`$ is the reciprocal cutoff; it is not the notation $`\mu_{\rm irr}(\xi)`$ for the irrationality exponent of an individual value. The cutoff is sufficient for this construction, not asserted optimal.

<div id="res:rational-base-threshold" class="theorem">

**Theorem 1** (rational-base region for Zudilin’s forms). *Let $`a>b\ge1`$ be coprime integers with
``` math
\begin{gathered}
 b^{\mu}<a,\qquad\text{equivalently}\qquad
 \frac{\log b}{\log a}<\theta^*,\\
 \theta^*=\frac{C_0}{C_1}=0.4056830213840605\ldots,\\
 \mu=\frac{C_1}{C_0}=2.4649786835749750\ldots.
\end{gathered}
```
Then $`F(a/b)`$ is irrational.*

</div>

The cancellation is performed before homogenisation, so the clearing degree is the degree of the cancelled pair. The value $`3/2`$ is outside this sufficient region: $`J\le\psi_1(1/14)-\psi_1(1)<196`$ gives $`\theta^*<266/(1091/2)<1/2<\log2/\log3`$. At equality $`\log b/\log a=\theta^*`$ the leading quadratic exponent vanishes, so this argument gives no conclusion from its displayed estimates.

<div class="proof">

*Proof of Theorem <a href="#res:rational-base-threshold" data-reference-type="ref" data-reference="res:rational-base-threshold">1</a>.* Set
``` math
a_0=14n+1,\quad a_1=12n+1,\quad a_2=14n+1,\quad\beta=27n+2,
 \qquad N=15n.
```
Use the coefficient pair $`A_n,B_n`$ of the source identities \[zudilin2004, (8)–(11), pp. 156–157\], with $`H_n=A_nF-B_n`$. Put $`D_N(X)=\prod_{\ell=1}^{N}\Phi_\ell(X)`$, $`M_n=266n^2+34n+1`$, and
``` math
\Omega_n(X)=\prod_{\ell=2}^{N}\Phi_\ell(X)^{\nu_\ell},
 \qquad \nu_\ell=\omega(n/\ell),
```
where the periodic function
``` math
\begin{split}
\omega(x)=\max\{0,&\ \lfloor14x\rfloor+\lfloor13x\rfloor
                  -\lfloor12x\rfloor-\lfloor15x\rfloor,\\
                &\ 2\lfloor14x\rfloor-\lfloor13x\rfloor
                  -\lfloor15x\rfloor\}
\end{split}
```
is zero or one. Its support in $`[0,1)`$ consists of
``` math
\begin{gathered}
\,[1/14,1/12),\ [1/7,1/6),\ [3/14,1/4),\ [2/7,1/3),\\
[5/14,2/5),\ [3/7,7/15),\ [1/2,8/15),\ [4/7,3/5),\\
[9/14,2/3),\ [5/7,11/15),\ [11/14,4/5),\\
[6/7,13/15),\ [13/14,14/15).
\end{gathered}
```
These are the intervals $`\mathcal I`$ used to define $`J`$. The function $`\omega`$, these thirteen intervals and the exponents $`\nu_\ell=\omega(n/\ell)`$ of the source’s (22) are printed at \[zudilin2004, pp. 161–162\]. The zero-one values and this thirteen-interval support are [omega indicator](https://github.com/wcook04/plectis-erdos/blob/f36a98bf3d3e6f65f1074e3b800e3293d5b8a51a/ErdosProblems/Erdos1049/PaperOmegaIndicatorR7.lean#L1297).

#### Integral polynomials and their degrees.

The source’s polynomial inclusion is Lemma 7, display (23) \[zudilin2004, p. 161\]. Its parameter vector is $`n(13,14,12,14,15,13)`$, its maximum is $`15n`$, and $`\beta-a_1-a_2=n>0`$, which is the positivity condition $`s>0`$ of the lemma. The conditions (14) of \[zudilin2004, p. 157\], $`a_1\le a_2`$ and $`a_1+a_2\le\beta\le a_0+a_2`$, hold as well, so the exponent in (23) is the integer (16), which equals $`M_n`$. The lemma’s hypotheses therefore hold for every $`n\ge1`$. It gives
``` math
\Lambda_n(X)=X^{-M_n}\frac{D_N(X)}{\Omega_n(X)}H_n(X)
            =U_n(X)F(X)-V_n(X),\qquad U_n,V_n\in\mathbb Z[X].
```
This is the polynomial conclusion before the source’s subsequent integer-specialisation step in display (24) on p. 162. The coefficientwise interpretation also follows by comparing the source rational coefficients: $`F`$ is not a rational function, since $`F(e^h)=h^{-1}\log(1/h)+O(h^{-1})`$ as $`h\downarrow0`$. For this estimate split the original sum at $`n=1/h`$; the remaining geometric tail is $`O(h^{-1})`$.

In the source expression (10) for $`A_n`$, with coefficients (8) on p. 156, the degree of the $`k`$th summand is
``` math
d_k=a_0k+E_k+(a_1-1)(k-a_1)+(\beta-k-1)(k-a_2),
```
where
``` math
E_k=\frac{a_1(a_1-1)-(\beta-a_2)(\beta-a_2-1)
                   +(\beta-k)(\beta-k-1)}2.
```
For $`a_2\le k\le\beta-2`$, one has $`d_{k+1}-d_k=40n+1-k>0`$. There is therefore a unique highest-degree summand, and
``` math
K_n:=\deg A_n=\frac{1091n^2+81n+2}{2},\qquad
 W_n:=\deg U_n=K_n-M_n+\sum_{\ell\le15n}(1-\nu_\ell)\varphi(\ell).
```
For fixed $`n`$, the positive representation below gives $`H_n(x)=O(1)`$ as $`x\to\infty`$. Hence $`\Lambda_n(x)=O(x^{W_n-K_n})`$. Since $`F(x)=O(x^{-1})`$ and $`K_n\ge1`$, the identity $`V_n=U_nF-\Lambda_n`$ gives $`\deg V_n\le W_n-1`$. Thus $`W_n`$ clears both coordinates. The degree argument holds with $`n`$ fixed while $`x\to\infty`$; the remainder estimate below instead holds with $`x`$ fixed while $`n\to\infty`$. These are different limiting operations. The zero polynomial causes no difficulty in the assertion about the second coordinate.

#### The limiting degree cost.

The limits below are the cyclotomic limits of \[zudilin2004, Lemmas 1–2, p. 155\]. The proof uses the argument through reciprocal intervals, the summatory totient estimate and the trigamma function from the proof of \[zudilin2002, Lemma 1, p. 466\], with an explicit truncation of the block sum. The elementary summatory estimate $`\sum_{\ell\le y}\varphi(\ell)=3y^2/\pi^2+O(y\log y)`$ gives
``` math
\frac1{n^2}\sum_{\ell\le15n}\varphi(\ell)\longrightarrow\frac{675}{\pi^2}.
```
For $`[u,v)\in\mathcal I`$, the condition $`\{n/\ell\}\in[u,v)`$ is the disjoint union of intervals $`n/(k+v)<\ell\le n/(k+u)`$ for $`k\ge0`$. For finitely many $`k`$ the same summatory estimate applies term by term. The remaining terms have total normalised mass $`O(1/K^2)`$ after truncation at $`k=K`$, since they involve only $`\ell\le n/(K+u)`$. Letting first $`n`$ and then $`K`$ tend to infinity proves
``` math
\frac1{n^2}\sum_{\ell\le15n}\nu_\ell\varphi(\ell)
 \longrightarrow\frac3{\pi^2}
 \sum_{[u,v)\in\mathcal I}\sum_{k\ge0}
 \left(\frac1{(k+u)^2}-\frac1{(k+v)^2}\right)=\frac{3J}{\pi^2}.
```
Here no contributing index exceeds $`14n`$, since $`u\ge1/14`$. Consequently
``` math
K_n/n^2\longrightarrow C_1,\qquad
 (K_n-W_n)/n^2\longrightarrow C_0.
```

#### A positive remainder at every fixed real base.

For $`x>1`$ and $`q=1/x`$, the source identity (9) on p. 156 has the positive representation
``` math
H_n(x)=\sum_{t\ge0}q^{a_0t}
 \frac{(q^{t+1};q)_{a_1-1}}{(q;q)_{a_1-1}}
 \frac{(q;q)_{\beta-a_2-1}}{(q^{a_2+t};q)_{\beta-a_2}}.
```
The last denominator has length $`\beta-a_2`$, the length given by the gamma expression (7) and the residues (8) of \[zudilin2004, p. 156\]. The unnumbered display of $`R(T)`$ on that page prints the length $`\beta-a_2-1`$; the numbered identities fix the normalisation used here. Every finite product lies between $`P=(q;q)_\infty>0`$ and $`1`$, so
``` math
P^2\le H_n(x)\le\frac{P^{-2}}{1-q^{a_0}}.
```
In particular $`\log H_n(x)=O_x(1)`$ and $`\Lambda_n(x)>0`$.

For fixed $`x>1`$, the cyclotomic identity
``` math
\log\Phi_\ell(x)-\varphi(\ell)\log x
 =\sum_{d\mid\ell}\mu_{\rm Mob}(d)\log(1-x^{-\ell/d})
```
has total absolute error $`O_x(n)`$ over $`\ell\le15n`$, where $`\mu_{\rm Mob}`$ is the Möbius function. Indeed, it is at most $`15n B(x)`$, where
``` math
B(x)=\sum_{d\ge1}\frac{-\log(1-x^{-d})}{d}<\infty.
```
Since $`0\le1-\nu_\ell\le1`$, it follows that
``` math
\log\Lambda_n(x)=-(K_n-W_n)\log x+O_x(n).
```

#### Homogenisation.

Because $`U_n,V_n`$ are integral polynomials of degree at most $`W_n`$, $`b^{W_n}U_n(a/b)`$ and $`b^{W_n}V_n(a/b)`$ are integers. That integrality and the cleared linear-form identity it produces are [cleared linear form identity](https://github.com/wcook04/plectis-erdos/blob/f36a98bf3d3e6f65f1074e3b800e3293d5b8a51a/ErdosProblems/Erdos1049/PaperHomogenisationR7.lean#L61). Moreover
``` math
\begin{split}
 \log\bigl(b^{W_n}\Lambda_n(a/b)\bigr)
 &=K_n\log b-(K_n-W_n)\log a+O_{a/b}(n)\\
 &=\bigl(C_1\log b-C_0\log a\bigr)n^2+o(n^2).
\end{split}
```
The coefficient is negative under the theorem’s hypothesis. Thus positive linear forms in $`F(a/b)`$ with integer coefficients tend to zero. If $`F(a/b)=r/s`$ were rational, every such form would have absolute value at least $`1/|s|`$, a contradiction. The separation bound for a nonzero integral form at a rational target is [rational integer linear form gap](https://github.com/wcook04/plectis-erdos/blob/f36a98bf3d3e6f65f1074e3b800e3293d5b8a51a/ErdosProblems/Erdos1049/TwoSelectorRemainderEscape.lean#L128). ◻

</div>

<div id="res:thirtyone-four" class="corollary">

**Corollary 2**. *$`F\bigl((31/4)^r\bigr)`$ is irrational for every integer $`r\ge1`$.*

</div>

<div class="proof">

*Proof.* The exact inequalities $`31^2<4^5`$ and $`4^{200}<31^{81}`$ give $`2/5<\log4/\log31<81/200`$. The first term of each trigamma difference yields
``` math
J\ge J_0:=\sum_{[u,v)\in\mathcal I}(u^{-2}-v^{-2})
   =\frac{2015640690251}{25971865920}.
```
Using $`\pi>157/50`$ gives the rational lower bound
``` math
\theta^*>\frac{2359630009523263}{5820307922172744}
           >\frac{81}{200}.
```
Finally, the logarithmic ratio and coprimality are preserved by a common positive integer power. ◻

</div>

Lean checks Theorem <a href="#res:rational-base-threshold" data-reference-type="ref" data-reference="res:rational-base-threshold">1</a> as [the rational-base region](https://github.com/wcook04/plectis-erdos/blob/f4e61ed8a6941571310049e22dc239baa1b04e12/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L113), and Corollary <a href="#res:thirtyone-four" data-reference-type="ref" data-reference="res:thirtyone-four">2</a> as [the powers of $`31/4`$](https://github.com/wcook04/plectis-erdos/blob/f4e61ed8a6941571310049e22dc239baa1b04e12/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L117), with [the base $`31/4`$](https://github.com/wcook04/plectis-erdos/blob/f4e61ed8a6941571310049e22dc239baa1b04e12/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L121) as the case $`r=1`$. Both declarations apply the source supply rather than assuming it. The construction of the approximations is Zudilin’s \[zudilin2004; zudilin2016\]. What is checked here is the Lean formalisation of that construction’s consequence.

<div id="cor:rational-base-measure" class="corollary">

**Corollary 3** (an irrationality measure uniform over powers). *For coprime $`a>b\ge1`$ with $`\theta=\log b/\log a<\theta^*`$ and every integer $`r\ge1`$,
``` math
\mu_{\rm irr}\!\left(F((a/b)^r)\right)
 \le\frac{1-\theta}{\theta^*-\theta}.
```
Here $`\mu_{\rm irr}(\xi)`$ is the supremum of the exponents $`\nu`$ for which $`|\xi-p/q|<q^{-\nu}`$ has infinitely many reduced rational solutions. In particular, $`\mu_{\rm irr}(F((31/4)^r))<301`$ for every $`r\ge1`$.*

</div>

<div class="proof">

*Proof.* The passage from the forms to an exponent bound is the standard one that Zudilin uses at integer bases \[zudilin2004, p. 162\]; the estimates below give an exponent bound independent of $`r`$, although the estimates are applied separately at each fixed base $`(a/b)^r`$. The raw source coefficient is a sum of $`O(n)`$ Laurent monomials times two Gaussian polynomials, each of coefficient sum at most $`2^{27n+2}`$. Its coefficient norm is $`\exp(O(n))`$, and every exponent is at most $`K_n`$. The same normalising multiplier used above therefore gives
``` math
|U_n(x)|\le x^{W_n}\exp(O_x(n))\qquad(x>1\text{ fixed}).
```
Set $`\xi=F(a/b)`$, $`Q_n=b^{W_n}U_n(a/b)`$ and $`P_n=b^{W_n}V_n(a/b)`$. With
``` math
\alpha=(C_1-C_0)\log a,\qquad
 \tau=C_0\log a-C_1\log b>0,
```
we have $`\log(Q_n\xi-P_n)=-\tau n^2+o(n^2)`$ and $`|Q_n|\le\exp(\alpha n^2+o(n^2))`$.

For integers $`A,B,p,q`$ with $`q>0`$, if $`L=A\xi-B`$ and $`2q|L|\le1`$, then
``` math
|L|\le |A|\,|\xi-p/q|.
```
When $`Ap-Bq=0`$ this is equality. Otherwise the nonzero integer $`Ap-Bq`$ gives $`1/q\le |L|+|A|\,|\xi-p/q|`$, which proves the inequality. For a fixed $`\eta\in(0,\tau)`$ choose $`n=\lceil\sqrt{\log(2q)/(\tau-\eta)}\rceil`$ and apply it to $`(Q_n,P_n)`$. The two-sided remainder estimate yields
``` math
|\xi-p/q|\ge
 q^{-(\alpha+\tau+2\eta)/(\tau-\eta)-o(1)}.
```
Let $`\eta\downarrow0`$. The resulting bound is $`1+\alpha/\tau=(1-\theta)/(\theta^*-\theta)`$. Taking a common power multiplies $`\alpha,\tau`$ by $`r`$, leaving this quotient unchanged; the constants in the approximation inequality may depend on $`r`$. For $`31/4`$, rational interval arithmetic gives
``` math
0.40568302137302<\theta^*<0.40568302139506,
 \qquad \log4/\log31<0.4036982.
```
For completeness, if $`f_{u,v}(x)=(x+u)^{-2}-(x+v)^{-2}`$ and $`u<v`$, its positive decreasing tail satisfies
``` math
\int_M^\infty f_{u,v}(x)\,dx
 \le\sum_{k=M}^\infty f_{u,v}(k)
 \le f_{u,v}(M)+\int_M^\infty f_{u,v}(x)\,dx.
```
The integral is $`(M+u)^{-1}-(M+v)^{-1}`$. The accompanying certificate uses $`M=256`$, Machin’s identity for $`\pi`$ with alternating-series bounds, and the positive $`\operatorname{arctanh}`$ series for logarithms. All endpoints are rational. They enclose the exponent bound between $`300.4269130`$ and $`300.4269164`$, in particular below $`301`$. These numerical enclosures are exact-arithmetic certificates, not additional Lean declarations. ◻

</div>

<a id="comparison-and-scope."></a>

#### Comparison and scope.

Bundschuh and Väänänen’s Theorem 2 at $`\alpha=-1`$ \[bv1994, p. 177\] gives irrationality for $`\log b/\log a<\theta_{\rm BV}:=1/2-1/\pi^2`$. Since $`\pi^2<10`$, one has $`\theta_{\rm BV}<2/5<\log4/\log31`$, so $`31/4`$ lies outside that sufficient region. The two sufficient regions differ on $`[\theta_{\rm BV},\theta^*)`$. For the generalized $`q`$-logarithm, Zudilin remarks that his results extend to non-integer rational bases $`p=r/s`$ under an assumption $`\log|r|>c\log|s|`$ for a computable constant $`c>0`$, without computing $`c`$ \[zudilin2016, Sec. 2, p. 4\]. For $`F`$, the specialisation above shows that $`c=\mu`$, the exponent bound of \[zudilin2004, p. 162\], is admissible.

<div id="res:sevenhalves" class="theorem">

**Theorem 4** (the $`7/2`$ height condition). *The [integer power certificate](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L32) $`2^{18}<7^7`$ yields the [Archimedean height condition](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L83)
``` math
\frac{\log 7}{\log(7/2)}
 <
 \left(\frac12+\frac1{\pi^2}\right)^{-1}.
```*

</div>

This is the elementary parameter check at $`q=7/2`$ in Bundschuh and Väänänen’s Theorem 2 ($`\alpha=-1`$). Their analytic irrationality theorem is not a Lean result here.

Negative bases are not treated: the positive-remainder estimates used here assume $`x>1`$. The boundary $`x=1`$ is excluded because the Lambert series diverges there.

<a id="the-base-uniform-degree-restriction"></a>

## The base-uniform degree restriction

The preceding construction uses degree and decay estimates valid at every fixed real base greater than one, with common quadratic degree and decay parameters. It is this common-parameter hypothesis, not fixed-base asymptotics alone, that imposes the following restriction.

<div id="res:archimedean-cap" class="theorem">

**Theorem 5** (Archimedean cap on base-uniform rank-two families). *Let $`(U_n,V_n)`$ be pairs in $`\mathbb Z[X]^2`$ satisfying $`\Lambda_n(x)=U_n(x)F(x)-V_n(x)\ne0`$, $`\deg U_n,\deg V_n\le\delta n^2(1+o(1))`$, $`\log\max(H(U_n),H(V_n))\le h n^2(1+o(1))`$ with $`H`$ the $`\ell^1`$ coefficient norm, and $`\log|\Lambda_n(x)|=-\sigma n^2\log x\,(1+o(1))`$ for every real $`x>1`$, with $`\sigma,\delta>0`$ and $`h\ge0`$ independent of $`x`$. Then with $`d_n=\max(\deg U_n,\deg V_n)`$, the homogenised forms $`b^{d_n}\Lambda_n(a/b)`$ tend to zero whenever $`\log b/\log a<\sigma/(\sigma+\delta)`$, and $`\sigma/(\sigma+\delta)\le1/2`$.*

</div>

<div class="proof">

*Proof.* Write $`H_n=\max(H(U_n),H(V_n))`$. Then $`|U_n(x)|,|V_n(x)|\le H_n x^{d_n}`$ for real $`x>1`$. Suppose $`\sigma>\delta`$ and choose an integer $`p\ge2`$ with $`(\sigma-\delta)\log p>h`$. Set $`a_n=U_n(p)`$, $`b_n=V_n(p)`$ and $`L_n=a_n F(p)-b_n`$. Hypotheses on height and degree give $`|a_n|\le\exp((h+\delta\log p)n^2+o(n^2))`$, while $`|L_n|=\exp(-\sigma\log p\,n^2+o(n^2))`$. The adjacent integer
``` math
a_nb_{n+1}-a_{n+1}b_n=a_{n+1}L_n-a_n L_{n+1}
```
is then $`o(1)`$, hence eventually zero. Also $`a_n\ne0`$ for large $`n`$: otherwise the nonzero integer $`L_n=-b_n`$ would have absolute value less than $`1`$. Thus $`b_n/a_n`$ is eventually a fixed rational $`r`$. If $`F(p)\ne r`$ then $`|L_n|\ge|F(p)-r|`$; if $`F(p)=r`$ then $`L_n=0`$. Both contradict the hypotheses, so $`\sigma\le\delta`$. The integer argument of this paragraph, from the two cross-product limits to the contradiction, is [no small forms of cross product limits](https://github.com/wcook04/plectis-erdos/blob/f36a98bf3d3e6f65f1074e3b800e3293d5b8a51a/ErdosProblems/Erdos1049/PaperRankTwoCapR7.lean#L123). The homogenised logarithm satisfies
``` math
\limsup_{n\to\infty} n^{-2}\log\bigl|b^{d_n}\Lambda_n(a/b)\bigr|
 \le \delta\log b-\sigma\log(a/b),
```
which is negative on the stated sufficient region. The arithmetic form of that region is [logarithmic region iff negative balance](https://github.com/wcook04/plectis-erdos/blob/f36a98bf3d3e6f65f1074e3b800e3293d5b8a51a/ErdosProblems/Erdos1049/PaperRankTwoCapR7.lean#L144), and the final numerical clause is [half cap iff](https://github.com/wcook04/plectis-erdos/blob/f36a98bf3d3e6f65f1074e3b800e3293d5b8a51a/ErdosProblems/Erdos1049/PaperRankTwoCapR7.lean#L155). The conclusion bounds the sufficient cutoff furnished by the displayed degree estimate. An exclusion for a particular family requires its actual degree and remainder asymptotics. ◻

</div>

The hypotheses are essential: this is a restriction on the stated base-uniform rank-two estimates, not on all Padé or Hermite–Padé constructions. For a distinct simultaneous construction, Postelmans and Van Assche prove the $`\mathbb{Q}`$-linear independence of $`1,\zeta_q(1),\zeta_q(2)`$ when $`q=1/p`$ with integer $`p\ge2`$ \[postelmansvanassche2007, Thm. 1.3, p. 3; Sec. 6\]. Their integer inverse-base hypothesis is not removed here.

<a id="sec:hankel-order"></a>

# Exact normalised-Hankel order in Zudilin’s construction

Here the problem is cancellation inside a determinant. Entrywise orders give only a lower bound because terms of that order may cancel. The moment expansion below resolves this by finding one uniquely least-order index tuple, whose coefficient is nonzero. This is a formal-power-series argument; fixed-base estimates are a separate question addressed after the proof.

At $`x=z=1`$, Zudilin’s normalised moments \[zudilin2016, (6), pp. 6–7\] are
``` math
v_m^*=\sum_{t\ge0}q^{(m+1)t}
 \frac{(q;q)_m^3(q^{t+1};q)_m}{(q^{m+1+t};q)_{m+1}},
 \qquad
 V_N^*=\det_{0\le i,j<N}(v_{i+j}^*).
```
His row transformation proves
``` math
\operatorname{ord}_q V_N^*\ge
 \frac{N(N-1)(2N-1)}6
```
for every $`N\ge1`$ \[zudilin2016, Sec. 4, Lemma 1, pp. 6–7\]. A formal moment expansion identifies the unique least-order term and shows that this estimate is always sharp.

<div id="res:zudilin-sharp-qorder" class="theorem">

**Theorem 6** (sharp normalized Hankel order). *For every $`N\ge1`$,
``` math
\operatorname{ord}_q V_N^*=\frac{N(N-1)(2N-1)}6,
```
and the coefficient of the first nonzero monomial is
``` math
[q^{N(N-1)(2N-1)/6}]V_N^*
   =\frac{(N!)^2(N+1)!}{2^N}.
```*

</div>

<div class="proof">

*Proof.* Write $`P=(q;q)_\infty`$ and introduce the coefficientwise formal series
``` math
G_q(w)=\frac1{(w;q)_\infty^3}
 \sum_{t\ge0}\frac{w^t}{(q;q)_t}
       \frac{(q^tw^2;q)_\infty}{(q^tw;q)_\infty^2},
 \qquad a_k(q)=[w^k]P^4G_q(w).
```
For fixed $`w`$-degree, all operations define power series in $`q`$. The product identities $`(q;q)_m=P/(q^{m+1};q)_\infty`$ and $`(q^a;q)_m=(q^a;q)_\infty/(q^{a+m};q)_\infty`$ give the exact formal identity
``` math
v_m^*=P^4G_q(q^{m+1})
      =\sum_{k\ge0}a_k(q)q^{(m+1)k}.
```
At $`q=0`$, the term $`t=0`$ in $`G_q`$ is $`(1-w^2)/(1-w)^5`$ and the terms $`t\ge1`$ sum to $`w/(1-w)^4`$. Consequently
``` math
G_0(w)=\frac{1+2w}{(1-w)^4},\qquad
 a_k(0)=\frac{(k+1)^2(k+2)}2=:c_k>0.
```

The expansion below is Heine’s formula for a Hankel determinant of moments as a sum of squared Vandermonde products; Zudilin uses its integral form and reproduces its proof in \[zudilin2017det, Sec. 2, (2)–(5), pp. 2–3\]. Apply Cauchy–Binet to a finite truncation of the moment sum and then pass coefficientwise to the limit. This is legitimate because only finitely many increasing index tuples contribute to any fixed $`q`$-degree. It gives
``` math
V_N^*=\sum_{k_0<\cdots<k_{N-1}}
 \left(\prod_{i=0}^{N-1}a_{k_i}(q)q^{k_i}\right)
 \prod_{0\le i<j<N}(q^{k_i}-q^{k_j})^2.
```
The summand indexed by $`(k_i)`$ has order
``` math
\sum_{i=0}^{N-1}(2N-1-2i)k_i.
```
Each $`a_k(q)`$ has $`q`$-order zero with positive initial coefficient $`c_k`$, and $`k_i\ge i`$. Equality with the least possible order occurs uniquely when $`k_i=i`$ for every $`i`$. That tuple contributes
``` math
\sum_{i=0}^{N-1}(2N-1-2i)i=\frac{N(N-1)(2N-1)}6
```
and leading coefficient
``` math
\prod_{i=0}^{N-1}c_i=\frac{(N!)^2(N+1)!}{2^N}.
```
No other tuple can cancel this coefficient. ◻

</div>

Lean checks both identities at every rank as [the exact order](https://github.com/wcook04/plectis-erdos/blob/0b500c7cf8e8bb7ae343484378df02f277fb8194/lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L173) and [the leading coefficient](https://github.com/wcook04/plectis-erdos/blob/0b500c7cf8e8bb7ae343484378df02f277fb8194/lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L199).

<a id="formal-order-real-size-and-arithmetic-content."></a>

#### Formal order, real size and arithmetic content.

Formal order alone does not control a fixed-$`q`$ residual: multiplying by $`(1-q)^{N^3}`$ preserves the first term and changes its logarithm by a cubic quantity for fixed $`0<q<1`$. A separate positive-measure proof in the long record gives $`V_N^*(q)>0`$ and $`\log(V_N^*(q)/(C_Nq^{B_N}))=O_q(N)`$, where $`B_N=N(N-1)(2N-1)/6`$ and $`C_N=(N!)^2(N+1)!/2^N`$. Neither conclusion supplies arithmetic divisibility. The cyclotomic Hankel factors in Krattenthaler–Rochev–Väänänen–Zudilin \[krvz2009, Prop. 4, pp. 14–15\] are proved for a different tail recurrence; that recurrence has not been established for this family. Likewise, positivity of these remainders does not prove that their coefficient sequence is a Stieltjes moment sequence. The latter requires positivity of both its Hankel matrices and their once-shifted companions \[wangzhu2016, Lemma 2.1, p. 4\], at all ranks. The long record states this coefficient question separately and records exact finite-rank tests. No divisor from the 2004 forms is transferred to the 2016 family.

The long record now certifies both leading coefficient-Hankel families through rank eight, for every real $`p\ge1`$. At $`p>1`$ this suffices to make the coefficient matrix positive definite through that rank, and hence to obtain real pencil roots below $`F(p)`$, without an all-rank moment conjecture. The endpoint coefficient sequence $`(m!)^3`$ has a Stieltjes measure but is indeterminate: a measure need not be unique \[berg2007, Thm. 5.1\]. Positive continued-fraction coefficients and finite Gaussian quadrature are useful finite reformulations \[sw2024; golubwelsch1969\]; neither constructs a single measure for the entire moving-degree sequence.

<a id="sec:open"></a>

# Local cancellation and the remaining real estimate

The tools of this section are elementary: congruences at the endpoints, the pigeonhole principle and Bézout’s identity for unimodular rows. The hypotheses on minors, multiplicities and real remainders are stated explicitly where they enter.

For natural $`a,b,N,K,Q,D`$, a *coordinatewise corridor* means
``` math
a,Q,D>0,\quad D\le N+K,\quad a^K\mid QD,
 \quad Qb^{N+K+1}<a^{K+1}.
```
The divisibility and the last inequality imply $`b^{N+K+1}<a(N+K)`$. At $`(a,b)=(3,2)`$ this contradicts $`3x<2^{x+1}`$ for $`x=N+K\ge2`$.

<div id="res:nocorridor" class="theorem">

**Theorem 7** (no corridor at base $`3/2`$). *For all $`N\ge1`$ and $`K\ge1`$ and all natural $`Q,D`$, the tuple $`(3,2,N,K,Q,D)`$ is not a [coordinatewise corridor](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L155).*

</div>

For $`r,s,B,F\in\mathbb{Q}`$ with $`r\ne0`$ and $`c:\mathbb{N}\to\mathbb{Q}`$, put
``` math
P_N=\sum_{m=0}^{N-1}c(m+1)\frac{s^{m+1}}{r^{m+1}},
 \qquad U_N=Br^N(F-P_N).
```
Here $`F`$ in the recurrence is an arbitrary rational parameter; it is not an assumption that the Lambert value is rational.

<div id="res:tailrec" class="theorem">

**Theorem 8** (cleared-tail recurrence). *Let $`r,s,B,F\in\mathbb{Q}`$ with $`r\ne0`$, let $`c:\mathbb{N}\to\mathbb{Q}`$, and let $`P_N`$ and $`U_N`$ be the cleared tail state. Then for every $`N`$ the [cleared-tail recurrence](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L187) is
``` math
U_{N+1}=r\,U_N-B\,c(N+1)\,s^{\,N+1}.
```*

</div>

Here $`P_N`$ is the prefix and $`U_N`$ the cleared tail state in the definitions immediately above; the phrase “cleared tail state” in the statement refers to this declared pair of objects.

<div id="res:forcing" class="theorem">

**Theorem 9** (the forcing term). *Let $`s,B`$ be natural numbers and $`c:\mathbb{N}\to\mathbb{N}`$, and put $`G_N=B\,c(N+1)\,s^{\,N+1}`$.*

1.  *If $`s\ge2`$, $`B\ge1`$ and $`c(N+1)\ge1`$, then $`2^{\,N+1}\le G_N`$.*

2.  *If $`s=1`$, then $`G_N=B\,c(N+1)`$.*

</div>

Fix a common width $`W`$. For $`P\in\mathbb{Z}[X]`$ of degree at most $`W`$, write
``` math
H_W(P)=2^WP(3/2)=\sum_{i=0}^W[P]_i3^i2^{W-i}.
```
A specialised row is primitive when its two integer coordinates have gcd one. This normalisation is different from removing the common polynomial coefficient content, and must precede the local count. For depths $`R,S\ge0`$, define
``` math
J_{3,R}(P)=H_W(P)\pmod{3^R},\qquad
 J_{2,S}(P)=H_W(P)\pmod{2^S}.
```

<div id="res:bottomjet" class="lemma">

**Lemma 10** (bottom-jet divisibility). *Vanishing of the [bottom jet](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L191) is exactly divisibility by the corresponding power of three: $`J_{3,R}(P)=0`$ if and only if $`3^R\mid H_W(P)`$.*

</div>

All four jets of $`(U,V)`$ vanish precisely when $`D=3^R2^S`$ divides both specialised coordinates. The dependence on the declared width remains fixed when rows are added. The width is part of $`H_W`$: replacing it by $`W+1`$ doubles both evaluated coordinates and changes their $`2`$-adic divisibility. One must not lower a row’s width to its own degree while forming a common-width selector sum.

<div id="res:jetkernel" class="theorem">

**Theorem 11** (binary four-jet collision). *Fix a width $`W`$ and depths $`R,S`$, and let $`(U_j,V_j)_{j<M}`$ be any $`M`$ pairs of integral polynomials. Call a subset of $`\{0,\dots,M-1\}`$, equivalently a vector of $`\{0,1\}^M`$, a *binary selector*. If the $`2^M`$ binary selectors outnumber the finite four-jet target
``` math
(\mathbb{Z}/3^R\mathbb{Z})^2\times(\mathbb{Z}/2^S\mathbb{Z})^2,
```
then two distinct subsets have the same four-jet sum. Subtracting their indicator vectors gives a nonzero coefficient vector in $`\{-1,0,1\}^M`$ cancelling all four jets. The target has exact cardinality
``` math
(3^R)^2(2^S)^2.
```
In particular, if $`R>0`$ and $`4R+2S\le M`$, such a collision exists.*

</div>

<div class="proof">

*Proof.* Send each binary selector to the sum of the four-jet signatures it selects. The claimed cardinal inequality and the pigeonhole principle give two distinct selectors in the same fibre. The cardinality formula is the product of the four cyclic-modulus cardinalities. For $`R>0`$,
``` math
(3^R)^2(2^S)^2<(4^R)^2(2^S)^2=2^{4R+2S}\le2^M,
```
which proves the stated sufficient threshold. The cardinality formula, the collision, the signed $`\{-1,0,1\}`$ vector and the sufficient width are together [four jet paper statement](https://github.com/wcook04/plectis-erdos/blob/f36a98bf3d3e6f65f1074e3b800e3293d5b8a51a/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L248). ◻

</div>

The ambient count does not use relations between the two residue coordinates. Vanishing minors can reduce that cost to one coordinate.

<div id="res:plucker-collapse" class="theorem">

**Theorem 12** (Bézout–Plücker tail collapse). *Let $`R_0`$ be a commutative ring and let $`w_n=(A_n,B_n)\in R_0^2`$. Suppose that every row is unimodular ($`u_n A_n+v_n B_n=1`$ for some $`u_n,v_n`$) and every adjacent minor vanishes:
``` math
A_nB_{n+1}-B_nA_{n+1}=0\qquad(n\ge0).
```
Then every pairwise minor $`A_iB_j-B_iA_j`$ vanishes. In particular, take $`R_0=\mathbb{Z}/(2^S3^R)\mathbb{Z}`$ with $`R>0`$. If $`S+2R\le k`$, there are two distinct binary selectors $`s,t\in\{0,1\}^{k}`$ such that
``` math
\sum_{i<k}s_iw_i=\sum_{i<k}t_iw_i.
```
Thus the sufficient width is $`S+2R`$, rather than the ambient two-coordinate width $`2S+4R`$.*

</div>

<div class="proof">

*Proof.* A Bézout identity makes each row a unimodular anchor; a unit coordinate is the special case already recorded. Vanishing of the next minor therefore writes the next row as a scalar multiple of the current one; induction places the entire tail on the line through $`w_0`$ and proves the pairwise-minor assertion. A determinant-one Bézout shear sends $`w_0`$ to $`(1,0)`$, so all selector sums have only one free residue coordinate and occupy at most $`2^S3^R`$ values. Finally
``` math
2^S3^R<2^S4^R=2^{S+2R}\le2^k,
```
and pigeonhole gives the two selectors. The unit-second-coordinate special cases of the minor collapse and modular selector collision are recorded together as [plucker paper statement](https://github.com/wcook04/plectis-erdos/blob/f36a98bf3d3e6f65f1074e3b800e3293d5b8a51a/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L269). ◻

</div>

Primitive integer rows are unimodular modulo every modulus. A particular coordinate need not be a unit: $`(2,3)`$ modulo $`6`$ is an example. Explicitly, if $`uA+vB=1`$ and $`AB'-BA'=0`$, then $`(A',B')=(uA'+vB')(A,B)`$; this identity is valid even when the ring has zero divisors. Unimodularity of the next row makes the scalar a unit, although the scalar-multiple conclusion already suffices here. The minor-vanishing hypothesis remains a separate condition on the source rows.

<a id="an-exponent-model-and-row-normalisation"></a>

## An exponent model and row normalisation

The next proposition compares two explicit exponent polynomials of a Padé-type denominator model. No coefficient formula producing them is derived here, so the proposition by itself gives no integrality, nonvanishing or approximation estimate.

<div id="res:pade" class="proposition">

**Proposition 13** (exponent model: summand bound and exact gap). *Let $`\widetilde{E}_n=3n^{2}-n`$ and put
``` math
\widetilde{P}(n,k)=2\bigl(k(n-k)+nk\bigr)+k(k-1),
```
``` math
\widetilde{Q}(n,m)=2(n^{2}-n)+j^{2}+2jm+j-m^{2}+3m,
 \qquad j=n-m-1 .
```
Then, for integers $`n,k,m`$:*

1.  *if $`0\le k\le n`$, the [summand exponent bound](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L30) is $`\widetilde{P}(n,k)\le\widetilde{E}_n`$, and the gap factors as $`\widetilde{E}_n-\widetilde{P}(n,k)=(n-k)(3n-k-1)`$;*

2.  *the [exact gap identity](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L52) is $`\widetilde{E}_n-\widetilde{Q}(n,m)=2\bigl(n+m(m-1)\bigr)`$.*

</div>

For the first exponent inequality, $`n=0`$ forces $`k=0`$ and the gap is zero. For $`n\ge1`$ both $`n-k`$ and $`3n-k-1`$ are nonnegative. The second identity is a direct polynomial identity after substituting $`j=n-m-1`$; it makes no unstated restriction on $`m`$.

<div id="res:content" class="proposition">

**Proposition 14** (row-content determinant scaling). *Rowwise integer contents scale the [exterior determinant](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L124) by the same factors: the [content factorisation](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L94) and the [absolute determinant scaling](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L104) identify the local divisor with the Archimedean height cost.*

</div>

For nonzero row contents $`c_1,c_2`$, write $`r_i=c_ir_i^{\rm prim}`$. Then $`\det(r_1,r_2)=c_1c_2\det(r_1^{\rm prim},r_2^{\rm prim})`$ and $`r_i\cdot(\xi,-1)=c_i r_i^{\rm prim}\cdot(\xi,-1)`$. These identities concern multiplication or division of whole integer rows, not cancellation of a polynomial factor before specialisation.

<a id="one-minor-gcd-controls-two-different-costs"></a>

## One minor gcd controls two different costs

Let a rank-two lattice $`\Lambda\subset\mathbb{Z}^2`$ be generated by primitive rows, and let $`g>0`$ be the gcd of their $`2\times2`$ minors. By the description of Smith invariants through gcds of minors \[stanley2016, Thms. 2.3–2.4, p. 3\], its Smith invariants are $`1,g`$. For $`D\ge1`$, therefore
``` math
\bigl|\operatorname{im}(\Lambda\bmod D)\bigr|
       =\frac{D^2}{\gcd(g,D)},\qquad
 \left[\mathbb{Z}^2:\frac{\Lambda\cap D\mathbb{Z}^2}{D}\right]
       =\frac{g}{\gcd(g,D)}.
```
To verify the formulas, make a unimodular change of coordinates sending $`\Lambda`$ to $`\mathbb{Z}\oplus g\mathbb{Z}`$; that change preserves $`D\mathbb{Z}^2`$. The first quotient counts the modular signatures. The second is the index remaining after dividing a successful collision by $`D`$. Once $`D\mid g`$, the modular count is $`D`$, while the remaining index is $`g/D`$. Without primitive generators, use both Smith invariants $`d_1\mid d_2`$:
``` math
|\operatorname{im}(\Lambda\bmod D)|=
 \frac{D^2}{\gcd(d_1,D)\gcd(d_2,D)},\qquad
 \left[\mathbb{Z}^2:\frac{\Lambda\cap D\mathbb{Z}^2}{D}\right]=
 \frac{d_1d_2}{\gcd(d_1,D)\gcd(d_2,D)}.
```
This follows coordinatewise from $`\Lambda\simeq d_1\mathbb{Z}\oplus d_2\mathbb{Z}`$; omitting the first invariant without primitivity would change both counts.

If two independent divided rows $`(A_i,B_i)`$ have $`|A_i|\le H`$ and $`|A_i\xi-B_i|\le\varepsilon`$, their determinant gives
``` math
2H\varepsilon\ge \frac{g}{\gcd(g,D)}.
```
This is a restriction on two independent forms in the divided lattice. For one nonzero integral form tending to zero, no additional product $`H\varepsilon\to0`$ is required.

<a id="a-collision-must-have-a-small-nonzero-real-remainder"></a>

## A collision must have a small nonzero real remainder

A real bin records the analytic requirement alongside the modular signature. The multiplicity to control is the number of equal real values within one modular fibre.

<div id="res:boundedfibre" class="theorem">

**Theorem 15** (quantitative bounded-fibre escape). *Let $`A,B,J`$ be finite sets and let $`f:A\to B`$, $`g:A\to\mathbb R`$ and $`\iota:A\to J`$. Suppose that each simultaneous fibre of $`(f,g)`$ has at most $`k`$ elements and that, for some $`\delta>0`$,
``` math
\iota(x)=\iota(y)\quad\Longrightarrow\quad |g(x)-g(y)|<\delta.
```
If $`|B||J|k<|A|`$, then some distinct $`x,y\in A`$ satisfy
``` math
f(x)=f(y),\qquad 0<|g(x)-g(y)|<\delta.
```*

</div>

<div class="proof">

*Proof.* Partition $`A`$ by $`(f,\iota)`$. Some cell has more than $`k`$ elements, so its $`g`$-values cannot all agree. Two unequal values in that cell have the same modular signature and differ by less than $`\delta`$. ◻

</div>

For primitive integer rows $`(A_j,B_j)`$, put $`e_j=A_jF(3/2)-B_j`$ and apply the theorem to binary selectors, with
``` math
f(\varepsilon)=\sum_j\varepsilon_j(A_j,B_j)\pmod D,
 \qquad g(\varepsilon)=\sum_j\varepsilon_j e_j.
```
Let $`Q`$ be the number of attained modular signatures and let $`k`$ bound the simultaneous $`(f,g)`$ fibres. Here $`Q`$ counts attained signatures, not the whole ambient residue space; one may use $`Q\le D^2/\gcd(g_0,D)`$ when $`g_0`$ is the minor gcd of the primitive row lattice. The letter $`g_0`$ avoids confusion with the real-value map $`g`$ in the theorem. A useful bound for $`k`$ is an additional obligation, not a consequence of the modular count. All selector remainders lie in an interval of length $`T=\sum_j|e_j|`$. Dividing that interval into half-open bins of width $`D/n`$ gives the sufficient inequality
``` math
\begin{equation}
\label{eq:quantitative-selector-budget}
 2^M>Qk\left(\left\lfloor\frac{nT}{D}\right\rfloor+1\right).
\end{equation}
```
Its conclusion is a signed row sum divisible coordinatewise by $`D`$, with a nonzero divided real remainder of absolute value less than $`1/n`$. At a right endpoint use the final bin as a singleton if necessary; the bound $`\lfloor nT/D\rfloor+1`$ still applies and two distinct values in one bin differ strictly by less than $`D/n`$. The count is for attained signatures and actual equal-value multiplicities, not for all points of the ambient residue module.

More precisely, if modular fibre $`b`$ has its own real span $`T_b`$ and exact value multiplicity $`k_b`$, it suffices that
``` math
2^M>\sum_b k_b\left(\left\lfloor\frac{nT_b}{D}\right\rfloor+1\right).
```
These are estimates for the primitive real remainders of the declared source family. Bounded unnormalised hypergeometric remainders cannot replace them. A nonzero function need not be nonzero at $`3/2`$, as the factor $`2X-3`$ shows; positive individual remainders need not remain positive after subtraction. Primitivity of the input rows does not eliminate repeated subset sums. Exact value multiplicity must be bounded in the same family and after the same normalisation as the analytic span.

<a id="the-source-specific-endpoint-question"></a>

## The source-specific endpoint question

The following sufficient construction keeps source membership, primitive scaling, local cancellation and the real estimate together. Without source and height restrictions, arbitrary polynomial lifts of small rational approximations would simply restate irrationality.

<div id="prob:kernel" class="problem">

**Problem 16** (common-width simultaneous endpoint-jet construction). Exhibit an integer constant $`C\ge1`$ and, for every sufficiently large positive integer $`n`$, positive integers $`W_n,R_n,S_n,M_n`$ such that
``` math
n^2\le W_n,R_n,S_n\le Cn^2,
 \qquad 4R_n+2S_n\le M_n\le Cn^2,
```
together with polynomial pairs coming from a named source family with an explicit coefficient-height bound after primitive normalisation, $`(U_{n,j},V_{n,j})\in\mathbb{Z}[X]^2`$ for $`0\le j<M_n`$, each of degree at most the common declared width $`W_n`$, whose specialised integer rows are primitive:
``` math
\gcd\!\bigl(H_{W_n}(U_{n,j}),H_{W_n}(V_{n,j})\bigr)=1.
```
Find a nonzero vector $`\lambda^{(n)}\in\{-1,0,1\}^{M_n}`$ for which, on putting
``` math
U_n=\sum_{j<M_n}\lambda^{(n)}_jU_{n,j},
 \qquad V_n=\sum_{j<M_n}\lambda^{(n)}_jV_{n,j},
```
the pair $`(U_n,V_n)`$ is not $`(0,0)`$, all four common-width jets vanish,
``` math
J_{3,R_n}(U_n)=J_{3,R_n}(V_n)=0,
 \qquad J_{2,S_n}(U_n)=J_{2,S_n}(V_n)=0,
```
where every jet in this display is formed using the declared width $`W_n`$, and the resulting divided integer linear form
``` math
A_n=\frac{H_{W_n}(U_n)}{3^{R_n}2^{S_n}},
 \qquad
 B_n=\frac{H_{W_n}(V_n)}{3^{R_n}2^{S_n}},
 \qquad
 \rho_n=A_nF(3/2)-B_n
```
satisfies the explicit analytic condition
``` math
0<|\rho_n|<\frac1n.
```

</div>

The jet equations make $`A_n,B_n`$ integers. If $`F(3/2)=a/b`$ were rational, a nonzero $`\rho_n`$ would have absolute value at least $`1/|b|`$, contradicting $`|\rho_n|<1/n`$ for large $`n`$. The required analytic inequality is exactly the displayed scalar condition. For irrationality it suffices to obtain such forms along any unbounded sequence of $`n`$; the all-sufficiently-large-$`n`$ formulation is a stronger construction requirement. Height estimates become relevant when a specific construction uses them to obtain this scalar inequality, or when an independent-row determinant is invoked.

For the literal two-parameter source deformations, the long record keeps the rowwise primitive normalisation, the two local minor valuations and the remaining real-error minimum together. The narrow regular-scale family has an ordinary determinant obstruction to bounded divided errors; that obstruction does not exclude sparse scales or the wider deformation. Thus the next estimate must concern the real remainders of the chosen family. Increasing the number of modular collisions alone does not establish it. An efficient test order is therefore: fix the source and width, compute primitive rows and the minor gcd, bound the attained signatures, and only then estimate real spans and exact-value multiplicities. A failed real bound is not repaired merely by finding more congruence solutions.

<a id="functional-equations."></a>

#### Functional equations.

Bell and Smertnig’s classification of Mahler series with multiplicative coefficients shows that $`L(z)=\sum_{n\ge1}\tau(n)z^n`$ is not $`k`$-Mahler for any $`k\ge2`$ \[bellsmertnig2026, Thm. 1.3 and the consequences on p. 3\]. The earlier simultaneous-$`2`$/$`3`$ obstruction is consequently subsumed by this known single-base result. A construction using additional functions or functional relations must specify those functions and its closure conditions; the single-base statement is not an obstruction to every approximation method.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

The [pinned formal-source revision](https://github.com/wcook04/plectis-erdos/tree/99f4bf47422abbd8757cbb22b50ba079d764d3a7) contains the Lean sources, the fixed toolchain, and the library manifest used in the verification. The ordinary proofs used here are printed with their hypotheses.

<a id="funding-and-competing-interests."></a>

#### Funding and competing interests.

This work received no external funding. The author declares no competing interests.

<a id="acknowledgements."></a>

#### Acknowledgements.

The problem numbering and status follow the Erdős Problems catalogue maintained by Thomas Bloom \[erdosproblems\].

<a id="app:index"></a>

# Guide to the formal sources

The supplied public snapshot is `3d6d938d696fed0fb71dd55115a18a73738ff223`. Its `PaperR17/SourceConsumers.lean` constructs the actual cancelled source supply and applies it in `rational_base_region`, `thirtyone_four_powers` and the measure declarations. The `AllRow/Producer.lean` file proves the actual source-row initial monomials and applies the all-rank determinant consumer. These endpoints are not merely conditional interfaces.

The accompanying audit distinguishes the public CI evidence in the packet from release-only and outside-build material; it is not a fresh kernel run. The ordinary unimodular-row Bézout–Plücker proof is stronger than the linked unit-second-coordinate Lean version. The finite coefficient-moment and cyclotomic-content calculations in the long record are exact computer algebra, not Lean theorems. Historical links elsewhere in the text retain their own revisions; the audit supplies a declaration-name map for careful repinning, rather than claiming that every old line coordinate has been revalidated.

<a id="sec:pinned-lean-sources"></a>

# Pinned Lean sources

The following declarations are this note’s pin-faithful source inventory. Line numbers are those of the commit named by `\commit`.

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L33)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L67)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L94)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L113)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L121)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L142)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L168)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L173)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L181)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L198)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L204)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L218)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L36)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L19)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L24)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L46)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L60)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L84)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L116)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L98)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L131)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L142)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L161)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L197)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L203)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L221)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L226)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L238)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L254)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L270)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L286)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L302)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L320)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L338)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L356)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L398)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L416)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L428)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean#L45)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean#L59)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean#L91)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean#L105)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean#L122)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/HermitePadeNoGo.lean#L103)

- [](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos1049/HermitePadeNoGo.lean#L126)

<div class="thebibliography">

99

P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. Bundschuh and K. Väänänen, [*Arithmetical investigations of a certain infinite product*](https://numdam.org/item/CM_1994__91_2_175_0.pdf), Compositio Math. **91** (1994), no. 2, 175–199. W. Zudilin, *Remarks on irrationality of $`q`$-harmonic series*, Manuscripta Math. **107** (2002), no. 4, 463–477, doi:[10.1007/s002290200249](https://doi.org/10.1007/s002290200249). W. Zudilin, [*Heine’s basic transform and a permutation group for $`q`$-harmonic series*](https://geodesic.mathdoc.fr/articles/10.4064/aa111-2-4/), Acta Arith. **111** (2004), no. 2, 153–164, doi:[10.4064/aa111-2-4](https://doi.org/10.4064/aa111-2-4). Page references are to the printed journal pages. W. Zudilin, [*On the irrationality of generalized $`q`$-logarithm*](https://arxiv.org/abs/1601.02688v2), arXiv:1601.02688; Res. Number Theory **2** (2016), Art. 15, doi:[10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x). Page references are to arXiv:1601.02688v2. The remark that the results extend to non-integer $`p=r/s`$, $`|p|>1`$, under an assumption $`\log|r|>c\log|s|`$ for a computable $`c>0`$, is in Section 2, p. 4, in the paragraph beginning “Finally, we remark”; no value of $`c`$ is computed there, and the remark is made for the generalized $`q`$-logarithm of that paper. R. P. Stanley, *Smith normal form in combinatorics*, J. Combin. Theory Ser. A **144** (2016), 476–495, doi:[10.1016/j.jcta.2016.06.013](https://doi.org/10.1016/j.jcta.2016.06.013); arXiv:[1602.00166v1](https://arxiv.org/abs/1602.00166v1). Page references are to arXiv:1602.00166v1. W. Zudilin, *A determinantal approach to irrationality*, Constr. Approx. **45** (2017), no. 2, 301–310, doi:[10.1007/s00365-016-9333-7](https://doi.org/10.1007/s00365-016-9333-7); arXiv:[1507.05697v1](https://arxiv.org/abs/1507.05697v1). Page and equation references are to arXiv:1507.05697v1. T. F. Bloom, [*Erdős Problem \#1049*](https://www.erdosproblems.com/1049), `erdosproblems.com/1049`. Historical snapshot cited in the supplied manuscript: accessed 28 July 2026, displaying “last edited 28 September 2025”. J. Bell and D. Smertnig, [*Mahler series with multiplicative coefficient sequences*](https://arxiv.org/abs/2603.23456v1), arXiv:2603.23456v1, 24 March 2026. Theorem 1.3 is on pp. 2–3; its stated consequences on p. 3 include that the divisor and totient generating series are not $`k`$-Mahler for any $`k\ge2`$. J. Vandehey, [*On an incomplete argument of Erdős on the irrationality of Lambert series*](https://arxiv.org/abs/1206.0340v1), Integers **13** (2013), Paper A58. Page references are to arXiv:1206.0340v1 (2012). D. Duverney and Y. Tachiya, *Refinement of the Chowla–Erdős method and linear independence of certain Lambert series*, Forum Math. **31** (2019), no. 6, 1557–1566, doi:[10.1515/forum-2018-0299](https://doi.org/10.1515/forum-2018-0299). Page references are to the [authors’ version](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf). W. Van Assche, [*Little $`q`$-Legendre polynomials and irrationality of certain Lambert series*](https://arxiv.org/abs/math/0101187v1), Ramanujan J. **5** (2001), no. 3, 295–310, doi:[10.1023/A:1012930828917](https://doi.org/10.1023/A:1012930828917). Page references are to arXiv:math/0101187v1. K. Postelmans and W. Van Assche, [*Irrationality of $`\zeta_q(1)`$ and $`\zeta_q(2)`$*](https://arxiv.org/abs/math/0604312v1), J. Number Theory **126** (2007), no. 1, 119–154, doi:[10.1016/j.jnt.2006.11.011](https://doi.org/10.1016/j.jnt.2006.11.011). Page references are to arXiv:math/0604312v1 (2006). C. Krattenthaler, I. Rochev, K. Väänänen and W. Zudilin, *On the non-quadraticity of values of the $`q`$-exponential function and related $`q`$-series*, Acta Arith. **136** (2009), no. 3, 243–269, doi:[10.4064/aa136-3-4](https://doi.org/10.4064/aa136-3-4); arXiv:[0812.2921v1](https://arxiv.org/abs/0812.2921v1). Page references are to arXiv:0812.2921v1. Y. Wang and B.-X. Zhu, [*Log-convex and Stieltjes moment sequences*](https://arxiv.org/abs/1612.04114v1), Adv. Appl. Math. **81** (2016), 115–127, doi:[10.1016/j.aam.2016.06.008](https://doi.org/10.1016/j.aam.2016.06.008). Page references are to arXiv:1612.04114v1. C. Berg, *On powers of Stieltjes moment sequences, II*, J. Comput. Appl. Math. **199** (2007), 23–38; arXiv:[math/0412340v1](https://arxiv.org/abs/math/0412340v1). Theorem references use the preprint; Theorem 5.1 treats factorial powers. A. D. Sokal and J. Walrad, *Continued-fraction characterization of Stieltjes moment sequences with support in $`[\xi,\infty)`$*, [arXiv:2404.12131v1](https://arxiv.org/abs/2404.12131v1), 2024. The classical Stieltjes criterion is recalled on pp. 1–2. G. H. Golub and J. H. Welsch, *Calculation of Gauss Quadrature Rules*, Math. Comp. **23** (1969), no. 106, 221–230, doi:[10.1090/S0025-5718-69-99647-1](https://doi.org/10.1090/S0025-5718-69-99647-1).

</div>

*Companion system context.* The [claim and trust boundary](../../../paper/systems/claim-faithful-publication-systems-paper.pdf#nameddest=systems-trust), [cold-clone route to proof authority](../../../paper/systems/cold-clone-to-proof-receipt.pdf#nameddest=cold-clone-authority), and [public contribution protocol](../../../paper/systems/open-source-mathematics-strategy.pdf#nameddest=strategy-protocol) are described in sibling papers. Those descriptions do not change the mathematical status of this note.
