<a id="erdos-1041-lemniscate-newton-flow"></a>

# Paths in Polynomial Lemniscates: A Degree-Seven Counterexample and Radial Connections

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

A monic polynomial of degree seven can have all its zeros in the open unit disc while every connected subset of $`\{|f|<1\}`$ containing two zeros has Hausdorff measure greater than $`2`$. We give the polynomial constructed by `ani`. The proof confines the slit preimage within the two-root component to a small disc about a critical point; radial projection on each of its two inverse sheets then gives the measure bound. For monic trinomials whose zeros lie in the open unit disc, the root equation keeps every root-to-origin segment inside the lemniscate.

<a id="sec:problem"></a>

# Introduction

Two points in the open unit disc are less than $`2`$ apart. The extra condition in the following question is that the whole connecting curve stay where a given polynomial has modulus less than $`1`$. For a monic polynomial $`f`$, write
``` math
\Omega_f=\{z:|f(z)|<1\},\qquad K_t(f)=\{z:|f(z)|\le t\}.
```
Erdős, Herzog and Piranian \[ehp1958, Problem 5, p. 139\] asked whether two zeros in the open unit disc could always be connected by a short curve in $`\Omega_f`$. Their question is listed as Problem 1041 in Bloom’s catalogue \[bloom\].

<div id="res:problem" class="problem">

**Problem 1** (Erdős \#1041). Let $`f(z)=\prod_{i=1}^{n}(z-z_i)`$ be monic with $`n\ge2`$ and all $`z_i`$ in the open unit disc. Must two root occurrences be joined by a curve of length less than $`2`$ inside $`\{|f|<1\}`$?

</div>

A repeated root allows a constant curve between two occurrences, so we consider distinct zeros. Pendyala \[june2026, Theorem 1 and Lemma 1\] proved the degree-four case using a close-pair chord or radial segments through the centre of a smallest enclosing disc. In degree seven the answer is negative. The example was constructed by the erdosproblems.com contributor [`ani`](https://www.erdosproblems.com/forum/thread/1041#post-8861).

<div id="counterexample-statement">

</div>

<div id="res:ani-degree-seven-counterexample" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1041-lemniscate-newton-flow.md#res-ani-degree-seven-counterexample">Lean</a></p>

**Theorem 2** (`ani`’s degree-seven example). *The monic polynomial $`f`$ in <a href="#eq:ani-f" data-reference-type="eqref" data-reference="eq:ani-f">[eq:ani-f]</a> has seven distinct zeros in the open unit disc. Every connected set $`K\subset\Omega_f`$ containing two of its zeros satisfies $`\mathcal H^1(K)>2`$.*

</div>

Here $`\mathcal H^1`$ is one-dimensional Hausdorff measure. Applied to a path image, the theorem also rules out a rectifiable path of total variation less than $`2`$.

Five components of $`\Omega_f`$ contain one zero each, and the sixth contains two. Thus only the last component can contain a connected set joining two zeros. On this component, $`f`$ is a double cover of the value disc, and the sum of the distances from its critical point to its two zeros is slightly greater than $`2`$. Distance estimates alone do not identify a component containing the selected roots; the double-cover argument uses the component established for this particular polynomial.

We cut the value disc from the critical value to the unit circle and confine the *whole* preimage of the slit to a small disc about the critical point. A connected set joining the zeros must approach this disc on both inverse sheets. Radial projection then gives a lower bound for its measure on each sheet. Adding these bounds subtracts twice the radius of the small disc from the sum of the two root distances; the remaining quantity is greater than $`2`$.

We begin with a quadratic example in which the slit preimage is small but the two zeros can still be joined by a segment of length less than $`2`$. The double-cover estimate identifies the additional inequality needed for the degree-seven example. In Section <a href="#sec:trinomial" data-reference-type="ref" data-reference="sec:trinomial">3</a>, the root equation for $`z^n+az^m+b`$ bounds the polynomial on every segment from the origin to a zero. A polynomial with four nonzero terms shows that this conclusion need not persist. The [long record](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=scope-further-estimates) gives the separate analytic criteria involving small or isolated critical values, together with the component and flow estimates used in those arguments.

<a id="sec:counterexample"></a>

# A component with a narrow bottleneck

<a id="a-quadratic-model"></a>

## A quadratic model

Consider $`p(z)=z^2-r^2`$ with $`0<r<1`$. Its critical point is $`0`$, its critical value is $`-r^2`$, and the outward slit in the value disc is $`J=(-1,-r^2]`$. We can compute its preimage without choosing a branch:
``` math
p^{-1}(J)=\{iy:|y|<\sqrt{1-r^2}\}.
```
This vertical interval separates the two inverse sheets containing $`r`$ and $`-r`$. It shrinks to the critical point as $`r\uparrow1`$. Yet the horizontal segment $`[-r,r]`$ stays in $`\{|p|<1\}`$ and has length $`2r<2`$. A narrow neck alone therefore does not give the desired counterexample. For the radial-distance estimate below to exceed $`2`$, the two root distances from the critical point must themselves have sum greater than $`2`$.

<a id="a-length-estimate-for-a-double-cover"></a>

## A length estimate for a double cover

Near a simple critical point $`c`$, write $`p(c+z)-p(c)=z^2A(z)`$. The quadratic model suggests the spatial scale $`\sqrt{\delta/M}`$, where $`\delta=1-|p(c)|`$ is the length of the remaining value slit and $`M=|A(0)|=|p''(c)|/2`$. The next lemma makes that comparison uniform on a disc of radius $`h`$. Its degree-two hypothesis has a separate role: the two local inverse images found near $`c`$ must account for *every* inverse image in the chosen component. Otherwise a local estimate would leave a possible connection elsewhere in the component.

<div id="lem:two-sheet-bottleneck" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L187">Lean</a></p>

**Lemma 3**. *Let $`p`$ be a polynomial and $`U`$ a component of $`\{|p|<1\}`$ on which $`p`$ has degree two, with one simple critical point $`c`$ and $`v=p(c)\ne0`$. Write $`p(c+z)-v=z^2A(z)`$ and put $`M=|A(0)|`$, $`\delta=1-|v|`$. Let $`h>0`$. If $`|A(z)/A(0)-1|\le1/4`$ for $`|z|\le h`$ and $`\delta<Mh^2/4`$, then every connected subset $`K`$ of $`U`$ containing its two roots $`a,b`$ satisfies
``` math
\mathcal H^1(K)\ge |a-c|+|b-c|-\frac83\sqrt{\delta/M}.
```*

</div>

<div class="proof">

*Proof.* Cut the value disc along $`J=\{tv:1\le t<1/|v|\}`$. The slit avoids $`0`$ and removes the only critical value of $`p|_U`$. Over its simply connected complement, the double cover splits into two inverse sheets $`U_1,U_2`$, containing $`a,b`$ respectively.

We next confine their common boundary inside $`U`$. Put $`r_0=(4/3)\sqrt{\delta/M}<2h/3`$. On $`|z|=r_0`$, the quadratic estimate gives
``` math
|p(c+z)-v|\ge\tfrac34Mr_0^2=\tfrac43\delta>\delta.
```
Every value on $`J`$ is less than $`\delta`$ from $`v`$. Rouché’s theorem therefore gives exactly two preimages in $`B(c,r_0)`$, counted with multiplicity. Continue them from the double zero at $`c`$ as the value moves outward along $`J`$. They cannot cross the circle just estimated; their values remain in the unit disc, so they stay in $`U`$. The degree-two hypothesis now identifies these local preimages with the entire fibre in $`U`$. Thus
``` math
p^{-1}(J)\cap U\subset B(c,r_0).
```

It remains to count how much of $`K`$ lies on each sheet. For $`r_0<t<|a-c|`$, suppose $`K\cap U_1`$ missed the circle $`|z-c|=t`$. Then $`K\cap U_1\cap\{|z-c|>t\}`$ would be both open and closed in $`K`$: the boundary of $`U_1`$ inside $`U`$ lies in $`B(c,r_0)`$, and the remaining boundary is on the missing circle. This set contains $`a`$ and excludes $`b`$, contradicting connectedness. Hence the radial image of $`K\cap U_1`$ contains $`(r_0,|a-c|)`$ whenever this interval is nonempty. The map $`z\mapsto|z-c|`$ is $`1`$-Lipschitz, and therefore
``` math
\mathcal H^1(K\cap U_1)\ge(|a-c|-r_0)_+.
```
The same argument on $`U_2`$ gives the contribution from $`b`$. The radial intervals may overlap on the real line; it is the disjointness of the *sheets in the plane* that permits addition. Hausdorff outer measure adds across disjoint open sets, without a measurability assumption on $`K`$, so
``` math
\begin{align*}
 \mathcal H^1(K)
 &\ge (|a-c|-r_0)_+ + (|b-c|-r_0)_+\\
 &\ge |a-c|+|b-c|-2r_0.
\end{align*}
```
This is the required bound. No parametrisation of $`K`$ has been used. ◻

</div>

<figure id="fig:two-sheet-bottleneck" data-latex-placement="!htbp">
<div id="bottleneck-geometry">

</div>
<figcaption>The slit and its preimage in Lemma <a href="#lem:two-sheet-bottleneck" data-reference-type="ref" data-reference="lem:two-sheet-bottleneck">3</a>. The component and radii are schematic, with both zeros outside the small disc. Connectedness forces the radial image on each sheet to contain the dotted interval. These intervals are displayed separately, although they may overlap as subsets of the real line. The two measure contributions add because <span class="math inline"><em>U</em><sub>1</sub></span> and <span class="math inline"><em>U</em><sub>2</sub></span> are disjoint in the plane, giving <span class="math inline">|<em>a</em> − <em>c</em>|+|<em>b</em> − <em>c</em>|−2<em>r</em><sub>0</sub></span>. The dotted intervals are not paths in <span class="math inline"><em>U</em></span>.</figcaption>
</figure>

<a id="the-polynomial"></a>

## The polynomial

The construction must satisfy three requirements: all roots lie in the unit disc, the only component containing more than one root has degree two, and the lower bound in Lemma <a href="#lem:two-sheet-bottleneck" data-reference-type="ref" data-reference="lem:two-sheet-bottleneck">3</a> exceeds $`2`$ for its two roots. We start near $`z^7-1`$, whose roots lie on the unit circle, and perturb its multiple critical point at the origin. The powers of $`\varepsilon`$ below are chosen so that the linear, quadratic and cubic perturbations all have order $`\varepsilon^7`$ at $`z=\varepsilon w`$. Thus coefficients that are small at the root circle can change the geometry at the critical-point scale. The following fixed coefficients are those of `ani`’s construction. Put $`s=10^{-6}`$, $`\varepsilon=s^2=10^{-12}`$ and $`\rho=1-s^{16}`$, and let
``` math
\begin{gather*}
 A=-\frac{329507}{1600},\qquad B=\frac{551827}{800},\qquad
 C=-\frac{23013813}{32000},\\
 a=A-is,\qquad b=iB+\frac95s,\qquad c_0=-C-\frac{162}{25}is.
\end{gather*}
```
Define
``` math
\begin{align}
 F(z)&=z^7-1+\varepsilon^4(az^3-\bar a z^4)
      +\varepsilon^5(bz^2-\bar b z^5)
      +\varepsilon^6(c_0z-\bar c_0z^6),\label{eq:ani-F}\\
 f(z)&=\rho^7F(z/\rho).\label{eq:ani-f}
\end{align}
```
The identity $`F(z)=-z^7\overline{F(1/\bar z)}`$ reduces the Cayley substitution $`z=(1+ix)/(1-ix)`$ to a real polynomial. It does not by itself put the roots on the circle: we check signs at fourteen rational endpoints. The seven resulting intervals account for all zeros $`\zeta_j`$ of $`F`$, which are therefore distinct and have modulus one. Thus $`b_j=\rho\zeta_j`$ lies strictly inside the disc, as required. At the chosen parameter, $`1-\rho=\varepsilon^8`$; the finite estimates below show that this contraction does not erase the excess in the selected root distances.

To resolve the critical points near the origin, we pass to the scale $`z=\rho\varepsilon w`$. Write
``` math
F(\varepsilon w)=-1+\varepsilon^7Q(w),\qquad
 Q(w)=c_0w+bw^2+aw^3-\varepsilon\bar a w^4
                  -\varepsilon^3\bar b w^5-\varepsilon^5\bar c_0w^6+w^7.
```
Rouché estimates on six disjoint rational discs locate the six zeros of $`Q'`$. Exactly one, $`w_s`$, corresponds to a critical value of modulus less than one. It satisfies
``` math
|w_s-(0.0000000039+0.8232474662i)|<10^{-6}.
```
Let $`c_s=\rho\varepsilon w_s`$, $`v=f(c_s)`$, $`\delta=1-|v|`$, and write $`f(c_s+z)-v=z^2A_s(z)`$. Since $`|\zeta_j|=1`$,
``` math
|b_j-c_s|^2=\rho^2\bigl(1-2\varepsilon\operatorname{Re}
 (w_s\bar\zeta_j)+\varepsilon^2|w_s|^2\bigr).
```
The term proportional to $`\varepsilon`$ measures the effect of moving the critical point, while $`1-\rho=\varepsilon^8`$ measures the contraction of the zeros. The following finite estimates give the sign and size of their combined effect for the chosen pair:
``` math
\begin{align}
 M:=|A_s(0)|&>180\rho^5\varepsilon^5,&
 \delta&<\frac{36}{5\cdot10^6}\rho^7\varepsilon^7,
       \label{eq:ani-estimates}\\
 \left|A_s(z)/A_s(0)-1\right|&<\frac14
       \quad\left(|z|\le\frac{\rho\varepsilon}{10}\right),&
 |b_3-c_s|+|b_6-c_s|&>
       \rho\left(2+\frac{143}{1000}\varepsilon\right).
       \label{eq:ani-distances}
\end{align}
```
The subscripts $`3,6`$ refer to Cayley roots in the intervals $`(43812,43813)/10^4`$ and $`(-4816,-4815)/10^4`$. The Taylor estimate gives the uniform quadratic control required by Lemma <a href="#lem:two-sheet-bottleneck" data-reference-type="ref" data-reference="lem:two-sheet-bottleneck">3</a>. The first two inequalities give $`\sqrt{\delta/M}<\rho\varepsilon/5000`$, which bounds the term subtracted there. The last inequality supplies the sum of root distances from $`c_s`$; the final comparison below shows that its excess over $`2`$ survives this subtraction.

We must also place these two roots in the same component; distance estimates alone do not identify that pair. We join a small disc about $`w_s`$ to points close to $`8\zeta_3`$ and $`8\zeta_6`$ by polygonal arcs in the $`w`$-plane. For the four inner segments we use
``` math
1-|f(\rho\varepsilon w)|^2\ge
 2\rho^{14}\varepsilon^7
 \left(7\varepsilon+\operatorname{Re}Q(w)
                       -\tfrac12\varepsilon^7|Q(w)|^2\right).
```
This follows by expanding the square and using $`1-\rho^{14}\ge14\rho^{14}\varepsilon^8`$. On each segment, the expression in parentheses is a polynomial of degree at most fourteen in the segment parameter. All fifteen coefficients in its degree-fourteen Bernstein basis are positive. The basis polynomials are nonnegative and sum to one, so the expression is positive along the whole segment, which therefore stays inside $`\{|f|<1\}`$ after scaling. For the remaining radial portions we use the root identity
``` math
F(t\zeta)=t^7-1+
       \sum_{k=1}^6\varepsilon^{7-k}q_k\zeta^k(t^k-t^7),
 \qquad Q(w)=\sum_{k=1}^7q_kw^k,
```
which gives $`|F(t\zeta)|<1`$ for $`8\varepsilon\le t\le1`$. All rational intervals, vertices and coefficient tests are specified in [the companion’s finite verification](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=counterexample-certificate). At the regular level $`|f|=1`$, Riemann–Hurwitz gives $`k-1`$ critical points in a component with $`k`$ zeros, counted with multiplicity. Thus the component containing $`c_s`$ has exactly two roots, while every other component contains one.

<div class="proof">

*Proof of Theorem <a href="#res:ani-degree-seven-counterexample" data-reference-type="ref" data-reference="res:ani-degree-seven-counterexample">2</a>.* Apply Lemma <a href="#lem:two-sheet-bottleneck" data-reference-type="ref" data-reference="lem:two-sheet-bottleneck">3</a> to the component containing $`b_3,b_6`$, with $`h=\rho\varepsilon/10>0`$. The finite estimates give $`\sqrt{\delta/M}<\rho\varepsilon/5000`$ and $`\delta<Mh^2/4`$. Every connected set in that component containing the two zeros therefore has measure greater than
``` math
\rho\left(2+\left(\frac{143}{1000}-\frac8{15000}\right)
                        \varepsilon\right)>2.
```
All other components contain one zero. A connected set containing two zeros must lie in the component just considered, which proves the theorem. ◻

</div>

The choice $`s=10^{-6}`$ is fixed throughout. Extending these estimates to the small-parameter family reported by `ani` remains unproved here. The argument estimates the measure of the connected set itself; a bound for the total variation of a chosen parametrisation would not suffice.

<a id="sec:trinomial"></a>

# Trinomials and radial segments

If $`f(z)=z^n+b`$ has a zero $`\zeta`$ in the open unit disc, then $`|b|=|\zeta|^n<1`$. The identity $`f(t\zeta)=b(1-t^n)`$, $`0\le t\le1`$, keeps the whole segment $`[0,\zeta]`$ in the lemniscate. A middle monomial does not destroy this argument: the equation $`f(\zeta)=0`$ lets us eliminate its contribution before taking absolute values. Only $`b`$ and $`-\zeta^n`$ remain, both of modulus less than one.

<div id="res:trinomial-all-degree" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperTrinomialWholeR21.lean#L23">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1041-lemniscate-newton-flow.md#res-trinomial-all-degree-comparator">Comparator</a></p>

**Theorem 4** (all-degree monic trinomials). *Let $`1\le m<n`$ and
``` math
f(z)=z^n+az^m+b,
```
with every zero in the open unit disc. For any zero $`\zeta`$, the entire segment $`[0,\zeta]`$ lies in $`\{|f|<1\}`$. Distinct zeros $`\zeta_1,\zeta_2`$ are therefore joined by the broken line $`\zeta_1\to0\to\zeta_2`$ of length $`\|\zeta_1\|+\|\zeta_2\|<2`$ inside the open unit lemniscate.*

</div>

<div class="proof">

*Proof.* Fix a zero $`\zeta`$. Eliminating $`a\zeta^m`$ with the root equation gives
``` math
f(t\zeta)=b(1-t^m)+\zeta^n(t^n-t^m).
```
Vieta’s formula gives $`|b|<1`$. For $`0\le t<1`$, both $`1-t^m`$ and $`t^m-t^n`$ are nonnegative, and hence
``` math
|f(t\zeta)|\le |b|(1-t^m)+|\zeta|^n(t^m-t^n)<1-t^n\le1.
```
At $`t=1`$ the value is zero. We join any two distinct zeros by concatenating their segments through the origin. ◻

</div>

The same calculation has a useful partial-sum form. Write $`f(z)=\sum_{k=0}^n a_kz^k`$, take a zero $`\zeta`$, and put $`S_j=\sum_{k=0}^j a_k\zeta^k`$. Abel summation gives
``` math
f(t\zeta)=\sum_{j=0}^{n-1}(t^j-t^{j+1})S_j.
```
For $`0\le t<1`$, the weights are nonnegative and sum to $`1-t^n`$. Thus $`f(t\zeta)/(1-t^n)`$ is a convex combination of the $`S_j`$. In the trinomial case these are $`b`$ and $`-\zeta^n`$. Additional coefficients introduce further partial sums, whose moduli need not be controlled by the root locations. The theorem controls segments ending at zeros; it makes no assertion that the whole lemniscate is star-shaped. The next polynomial shows where the partial-sum argument can fail after a further term is added.

<div id="res:sextic-spoke" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/SexticSpokeWhole.lean#L9">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1041-lemniscate-newton-flow.md#res-sextic-spoke-comparator">Comparator</a></p>

**Proposition 5** (failure of a prescribed radial segment). *There exist $`r\in(0,1)`$ for which every zero of
``` math
f_r(z)=z^6+\tfrac15 r^2 z^4-\tfrac15 r^4 z^2-r^6
```
lies in the open unit disc, yet the radial segment from the origin to the zero $`r`$ leaves $`\{|f_r|<1\}`$.*

</div>

<div class="proof">

*Proof.* We substitute $`z=rw`$ and factor the polynomial as $`r^6(w^2-1)(w^4+\tfrac65w^2+1)`$, whose six zeros have modulus $`r`$. At the midpoint of that segment, $`f_r(r/2)=-(327/320)r^6`$; choosing $`320/327<r^6<1`$ proves the assertion. ◻

</div>

This failure concerns the prescribed segment only. In the long record we use the partial-sum identity again, first for power substitutions in a cubic and then for a quintic whose two missing coefficients select a suitable pair of segments.

<a id="scope-and-verification"></a>

# Scope and verification

The counterexample concerns the fixed degree-seven polynomial. The trinomial criterion is a separate positive result and does not extend to all sparse polynomials, as the prescribed-segment example shows. The [long record](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=scope-further-estimates) develops the additional short-path criteria and their limits.

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/5783e729f82dc8079b3b2e174dc02c8b1e56ea88/evidence/erdos-1041-lemniscate-newton-flow.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

The [verification notes](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=verification-notes) distinguish the formal counterexample and trinomial proof from the additional analytic arguments, and locate the exact rational replay. Independent human review of correspondence with the 1958 wording is not recorded.

<a id="acknowledgements"></a>

# Acknowledgements

I thank Wouter van Doorn for advice on explaining restrictive hypotheses, avoiding private terminology and introducing notation only when useful.

<div class="thebibliography">

99 T. F. Bloom, *Erdős Problems*, problem 1041. <https://www.erdosproblems.com/1041> P. Erdős, F. Herzog, and G. Piranian, *Metric properties of polynomials*, J. Analyse Math. **6** (1958), 125–148, doi:[10.1007/BF02790232](https://doi.org/10.1007/BF02790232). V. S. Pendyala, *A Degree-Four Lemniscate Path Theorem*, arXiv:[2606.24875v1](https://arxiv.org/abs/2606.24875v1) (2026), doi:[10.48550/arXiv.2606.24875](https://doi.org/10.48550/arXiv.2606.24875).

</div>
