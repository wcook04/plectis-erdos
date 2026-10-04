<a id="erdos-1041-lemniscate-newton-flow"></a>

# Paths in Polynomial Lemniscates: A Degree-Seven Counterexample and Radial Connections

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

A monic polynomial of degree seven can have all its zeros in the open unit disc while every connected subset of $`\{|f|<1\}`$ containing two zeros has Hausdorff measure greater than $`2`$. We give the polynomial constructed by `ani`. The proof confines the slit preimage within the two-root component to a small disc about a critical point; radial projection on each of its two inverse sheets then gives the measure bound. For monic trinomials whose zeros lie in the open unit disc, the root equation keeps every root-to-origin segment inside the lemniscate. Further remarks record analytic short-path criteria whose formal proofs still require additional inputs.

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
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1041-lemniscate-newton-flow.md#res-ani-degree-seven-counterexample">Lean</a></p>

**Theorem 2** (`ani`’s degree-seven example). *The monic polynomial $`f`$ in <a href="#eq:ani-f" data-reference-type="eqref" data-reference="eq:ani-f">[eq:ani-f]</a> has seven distinct zeros in the open unit disc. Every connected set $`K\subset\Omega_f`$ containing two of its zeros satisfies $`\mathcal H^1(K)>2`$.*

</div>

Here $`\mathcal H^1`$ is one-dimensional Hausdorff measure. Applied to a path image, the theorem also rules out a rectifiable path of total variation less than $`2`$.

Five components of $`\Omega_f`$ contain one zero each, and the sixth contains two. Thus only the last component can contain a connected set joining two zeros. On this component, $`f`$ is a double cover of the value disc, and the sum of the distances from its critical point to its two zeros is slightly greater than $`2`$. Distance estimates alone do not show that the roots nearest to that critical point lie in a common component; Section <a href="#sec:critical-proximity" data-reference-type="ref" data-reference="sec:critical-proximity">6.1</a> supplies no such component-selection argument.

We cut the value disc from the critical value to the unit circle and confine the *whole* preimage of the slit to a small disc about the critical point. A connected set joining the zeros must approach this disc on both inverse sheets. Radial projection then gives a lower bound for its measure on each sheet. Adding these bounds subtracts twice the radius of the small disc from the sum of the two root distances; the remaining quantity is greater than $`2`$.

We begin with a quadratic example in which the slit preimage is small but the two zeros can still be joined by a segment of length less than $`2`$. The double-cover estimate identifies the additional inequality needed for the degree-seven example. In Section <a href="#sec:trinomial" data-reference-type="ref" data-reference="sec:trinomial">3</a>, the root equation for $`z^n+az^m+b`$ bounds the polynomial on every segment from the origin to a zero. A polynomial with four nonzero terms shows that this conclusion need not persist. Sections <a href="#sec:constant-factor" data-reference-type="ref" data-reference="sec:constant-factor">4</a> and <a href="#sec:separation" data-reference-type="ref" data-reference="sec:separation">5</a> concern small or isolated critical values. These analytic arguments are independent of the counterexample and the trinomial theorem, and remain unformalised. Full proofs are given in the companion.

For the analytic arguments we use the component-wise Riemann–Hurwitz calculation of Ebenfelt, Khavinson and Shapiro \[eks2010, proof of Proposition 2.1\] together with Pólya’s area inequality in the forms given by Crane \[crane, Theorems 1 and 6\]. Inverse branches, slit domains and capacity also occur in Crane’s work on Smale’s mean-value conjecture \[crane2007smale, Lemma 2.1 and §§2–4\], whose derivative normalisation differs from the monic normalisation here. The [companion paper](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf) gives the rational tests for the degree-seven polynomial and the full arguments underlying Sections <a href="#sec:other-results" data-reference-type="ref" data-reference="sec:other-results">6</a>–<a href="#sec:open" data-reference-type="ref" data-reference="sec:open">7</a>.

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
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperTrinomialWholeR21.lean#L23">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1041-lemniscate-newton-flow.md#res-trinomial-all-degree-comparator">Comparator</a></p>

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
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/SexticSpokeWhole.lean#L9">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1041-lemniscate-newton-flow.md#res-sextic-spoke-comparator">Comparator</a></p>

**Proposition 5** (failure of a prescribed radial segment). *There exist $`r\in(0,1)`$ for which every zero of
``` math
f_r(z)=z^6+\tfrac15 r^2 z^4-\tfrac15 r^4 z^2-r^6
```
lies in the open unit disc, yet the radial segment from the origin to the zero $`r`$ leaves $`\{|f_r|<1\}`$.*

</div>

<div class="proof">

*Proof.* We substitute $`z=rw`$ and factor the polynomial as $`r^6(w^2-1)(w^4+\tfrac65w^2+1)`$, whose six zeros have modulus $`r`$. At the midpoint of that segment, $`f_r(r/2)=-(327/320)r^6`$; choosing $`320/327<r^6<1`$ proves the assertion. ◻

</div>

This failure concerns the prescribed segment only. In Section <a href="#sec:solved-families" data-reference-type="ref" data-reference="sec:solved-families">6.2</a> we use the partial-sum identity again, first for power substitutions in a cubic and then for a quintic whose two missing coefficients select a suitable pair of segments.

<a id="sec:constant-factor"></a>

# A small least critical value

<div id="low-critical-short">

</div>

For a squarefree polynomial, put $`\mu=\min_{f'(c)=0}|f(c)|>0`$. We follow a component from its first merger at level $`\mu`$ up to level $`1`$. Suppose that no two distinct zeros can be joined by a curve of length less than $`2`$. Conformal length estimates then give a lower bound for the hyperbolic distances between the zeros. A packing inequality bounds their number from below, and a boundary-length estimate converts this bound into a lower bound for the growth of the component’s area. When the interval of logarithmic levels, of length $`\log(1/\mu)`$, is sufficiently large, this contradicts Pólya’s area bound.

The companion gives the ordinary analytic argument and its rational comparison. They yield the following unformalised criterion, with no restriction on the locations of the zeros.

<span id="res:low-critical-thirteen-twentyfifths" label="res:low-critical-thirteen-twentyfifths"></span> Let $`f`$ be squarefree and monic of degree $`n\ge2`$, and let $`\mu`$ be its least critical-value modulus. If $`\mu\le13/25`$, then two distinct roots are joined inside $`\{|f|<1\}`$ by a rectifiable curve of length strictly less than $`2`$.

This assertion has an ordinary analytic argument and an exact rational comparison, but no Lean proof. The argument is recorded at [the small-critical-value proof](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=low-critical-proof).

<span id="res:scaled-low-critical" label="res:scaled-low-critical"></span> Every squarefree monic polynomial of degree $`n\ge2`$ has two distinct roots joined in $`\{|f|<(25/13)\mu\}`$ by a curve of length less than
``` math
2\bigl((25/13)\mu\bigr)^{1/n}.
```
In every degree the length can be chosen less than $`(5/2)\mu^{1/n}`$.

<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1041-lemniscate-newton-flow.md#res-scaled-low-critical">Lean†</a></p>

Lean checks this scaling implication under the named input `LowCriticalThirteenTwentyFifths`, the unformalised assertion in Remark <a href="#res:low-critical-thirteen-twentyfifths" data-reference-type="ref" data-reference="res:low-critical-thirteen-twentyfifths">[res:low-critical-thirteen-twentyfifths]</a>.

<div class="proof">

*Scaling implication.* For $`n\ge3`$, apply the preceding assertion to $`g(z)=s^{-n}f(sz)`$, where $`s=((25/13)\mu)^{1/n}`$. Its least critical-value modulus is $`13/25`$, and rescaling its connection gives the first bound. The estimate $`2(25/13)^{1/n}<5/2`$ holds for $`n\ge3`$. For $`n=2`$, write $`f(z)=(z-h)^2-d^2`$ and use the root segment, of length $`2|d|=2\sqrt\mu`$, contained in $`K_\mu(f)`$. ◻

</div>

<a id="the-analytic-argument"></a>

## The analytic argument

Suppose that no pair can be connected with length less than $`2`$ in $`\Omega_f`$. At a regular level $`t\in(\mu,1)`$ we take the component $`C_t`$ containing a chosen first merger. Let $`k\ge2`$ be its number of roots, and put $`a=\operatorname{Area}(C_t)/\pi\le1`$ and $`x=\log(t/\mu)`$. In the disc uniformisation, hyperbolic distance is normalised by $`d(0,s)=2\operatorname{artanh}s`$ for $`0\le s<1`$. The Bergman segment estimate bounds the length between roots at hyperbolic distance $`d`$ by $`\sqrt{2a\log\cosh(d/2)}`$. The assumption on connecting curves therefore forces pairwise distance at least $`D`$, where $`\cosh(D/2)=e^{2/a}`$.

Intrinsic distance in $`C_t`$ means the infimum of Euclidean lengths of curves in $`C_t`$. Choose the centre $`h`$ of the uniformisation on a connected set through the first pair in $`K_\mu(f)`$, outside every intrinsic open unit ball centred at a root. Such a point exists: those balls are pairwise disjoint under that assumption and cannot cover a connected set containing two roots. If $`d_j`$ are the hyperbolic distances of the roots from this centre, we obtain
``` math
\lambda(d_j)\le\tfrac12\delta(a),\qquad
 \sum_j\lambda(d_j)\ge x,\qquad
 \lambda(d)=-\log\tanh(d/2),\quad
 \delta(a)=-\log(1-e^{-1/a}).
```
The one-root Bergman estimate gives the first bound because every root has intrinsic distance at least $`1`$ from $`h`$. For the second, $`h`$ is not a root and lies in $`K_\mu(f)`$, so evaluating the finite Blaschke product for $`f/t`$ at the centre gives $`\sum_j\lambda(d_j)=\log(t/|f(h)|)\ge x`$. Thus the total contribution is at least $`x`$, while each root contributes at most $`\delta(a)/2`$, giving $`k\ge2x/\delta(a)`$. The pairwise separation gives additional information, which the following packing estimate uses to improve this lower bound. The passage through a first merger, including simultaneous mergers, is part of the analytic input still to be formalised.

<div id="circle-packing-inputs">

</div>

We intersect the disjoint hyperbolic balls of radius $`D/2`$ with a single circle of radius $`r`$. Their angular half-widths satisfy
``` math
w(d,r)=\arccos\!\left(\operatorname{clamp}_{[-1,1]}
 \frac{\cosh d\cosh r-\cosh(D/2)}{\sinh d\sinh r}\right),
 \qquad \sum_jw(d_j,r)\le\pi.
```
This circle-slice inequality is formalised separately. If nonnegative weights $`\sigma_i`$ at radii $`r_i>0`$ give $`\lambda(d)\le U+\sum_i\sigma_iw(d,r_i)`$ for every $`d>0`$ satisfying $`\lambda(d)\le\delta(a)/2`$, where $`U>0`$, summing at the $`k`$ roots gives
``` math
\begin{equation}
\label{eq:short-packing}
 k\ge\frac{x-\pi\sum_i\sigma_i}{U}.
\end{equation}
```
The circle must be fixed before taking these intersections: angular projections of disjoint balls at different distances can overlap.

To obtain area growth, lift one common value radius from all $`k`$ roots to $`\partial C_t`$, and join successive endpoints by boundary arcs. These arcs remain in $`\Omega_f`$ because $`t<1`$. Splitting the lift integral at level $`\mu`$ gives mean total length at most $`\sqrt{ka(x+2)/2}`$. The sum of the $`k`$ adjacent-root connections counts each lift twice and the boundary once, so $`2k\le\sqrt{2ka(x+2)}+\mathcal H^1(\partial C_t)`$. Combining this with $`\mathcal H^1(\partial C_t)^2\le2\pi k t\,(d/dt)\operatorname{Area}(C_t)`$ yields the ordinary differential inequality
``` math
\begin{equation}
\label{eq:short-area-growth}
 a'(x)\ge\frac1{2\pi^2}
       \bigl[2\sqrt k-\sqrt{2a(x)(x+2)}\bigr]_+^2.
\end{equation}
```
The companion proves the lift estimate and accounts for the nonnegative area jumps at merger levels.

<a id="the-recorded-rational-comparison"></a>

## The recorded rational comparison

<div id="certificate-stopping-time">

</div>

Equation <a href="#eq:short-packing" data-reference-type="eqref" data-reference="eq:short-packing">[eq:short-packing]</a>, the bound $`k\ge2x/\delta(a)`$ and the companion’s two further packing estimates give an integer lower bound for $`k`$. Starting from $`a(3/10^5)>10^{-6}`$, the recorded rational calculation reaches $`a>1`$ by
``` math
X=\frac{635762889599}{10^{12}}.
```
It used $`18`$ area levels, $`126`$ certified weighted inequalities and a maximum step $`1/400`$. To certify $`U`$ on an interval $`[u,v]`$, it bounds the expression by $`\lambda(u)-\sum_i\sigma_i\min(w(u,r_i),w(v,r_i))`$; the tail is bounded directly by $`\lambda`$. Numerical optimisation proposes the weights, while rational inequalities bound the whole half-line. Since $`t=\mu e^x`$, the contradiction $`a>1`$ occurs before level $`1`$ provided that $`\mu e^X<1`$. The recorded comparison gives $`(13/25)e^X<0.982000386<1`$. It also gives $`(529/1000)e^X<0.998996547`$, so the ordinary argument supports that sharper threshold as well. Neither threshold is claimed optimal, and this arithmetic does not formalise the analytic reduction.

<span id="res:constant-factor-path" label="res:constant-factor-path"></span> A related ordinary averaging argument, also unformalised in its analytic construction, gives the following bounds. For a monic polynomial of degree $`n\ge2`$, two zero occurrences can be joined in $`K_{2\mu}(f)`$ with length at most $`(71/10)\mu^{1/n}`$; they are distinct in the squarefree case, and a repeated root gives a constant path. When $`\mu\le1/2`$, the argument gives a path of length at most $`5.7`$ in $`\Omega_f`$. The proof, together with refinements that retain the number of zeros in the component or its logarithmic capacity, is given in the [inverse-ray averaging argument](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=constant-factor-proof).

<a id="sec:separation"></a>

# An isolated simple critical value

The next ordinary construction continues the two branches meeting at a simple critical point over a disc free of other critical values. It leads to a different sufficient condition from small $`\mu`$. Its square-root map, Bergman estimate and component-area bound are combined in the unformalised input `DiscSepBergmanArea`; the formal algebraic consequences are conditional on that construction.

After dividing values by $`v`$, the chosen critical value is $`1`$ and the roots still lie over $`0`$. We need a disc containing both $`0`$ and $`1`$ but no other critical value. Its centre $`w_0\in[0,1]`$ and radius $`S`$ therefore satisfy $`S>\max(w_0,1-w_0)`$. These are the parameters in the following statement.

<span id="res:critical-value-separation" label="res:critical-value-separation"></span> Let $`f`$ be monic of degree $`n\ge3`$, let $`c`$ be a simple critical point, and put $`v=f(c)\ne0`$. Fix $`w_0\in[0,1]`$ and $`S>\max(w_0,1-w_0)`$. Suppose every other critical point $`d`$ satisfies
``` math
\left|\frac{f(d)}v-w_0\right|\ge S .
```
Put $`p=w_0(1-w_0)`$. Then two distinct roots are joined inside $`\{|f|\le|v|\}`$ by a curve $`\Gamma`$ satisfying
``` math
\begin{equation}
\label{eq:disk-family-length}
 \operatorname{length}(\Gamma)^2
 \le 2|v|^{2/n}\Bigl(\frac{S}{n-1}\Bigr)^{2/n}
 \log\!\frac{S^2+S+p}{S^2-S+p}.
\end{equation}
```

<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1041-lemniscate-newton-flow.md#res-critical-value-separation">Lean†</a></p>

Lean assumes `DiscSepBergmanArea`: existence of the square-root connector, its Bergman length bound and the area bound for the two-sheeted component. The complete ordinary argument is in the [companion’s separation proof](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=critical-value-separation-proof).

For example, $`f(z)=z^3-3a^2z`$ with $`0<a<1/\sqrt3`$ has zeros $`0,\pm\sqrt3a`$. At $`c=a`$ its critical value is $`v=-2a^3`$ and the other normalised critical value is $`-1`$. Thus the disc with centre $`w_0=1`$ and radius $`4/3`$ satisfies the separation hypothesis.

<span id="res:critical-value-thresholds" label="res:critical-value-thresholds"></span> Let $`f`$ be monic of degree $`n\ge3`$ with all roots in the open unit disc. If $`c`$ is a simple critical point with $`0<|f(c)|<1`$ and, for some $`w_0\in[0,1]`$, every other critical point $`d`$ satisfies
``` math
\left|\frac{f(d)}{f(c)}-w_0\right|\ge\frac43,
```
then two roots are joined inside $`\{|f|<1\}`$ by a curve of length strictly below $`2`$. In degree three the branch-centred choice $`w_0=1`$ already works with $`4/3`$ replaced by $`6/5`$.

<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1041-lemniscate-newton-flow.md#res-critical-value-thresholds">Lean†</a></p>

The geometric conclusion assumes the construction in Remark <a href="#res:critical-value-separation" data-reference-type="ref" data-reference="res:critical-value-separation">[res:critical-value-separation]</a>. Lean checks the numerical inequalities for $`4/3`$ and $`6/5`$ without that input.

<a id="square-roots-and-component-area"></a>

## Square roots and component area

Here is the ordinary argument behind the two remarks. Choose $`\alpha^n=v`$ and normalise to $`P(z)=v^{-1}f(c+\alpha z)`$. The component $`U`$ above $`D(w_0,S)`$ containing $`0`$ has degree two, as follows by exhausting with regular discs and applying Riemann–Hurwitz. Since $`U`$ is simply connected and $`1-P`$ has only a double zero at $`0`$ there, it has a single-valued analytic square root $`\xi`$. The resulting map is a proper local biholomorphism onto $`V=\{\xi:|\xi^2-(1-w_0)|<S\}`$, which is star-shaped and hence simply connected. It is therefore biholomorphic, and its inverse maps $`[-1,1]`$ to the proposed connection. Along this interval $`P=1-\xi^2\in[0,1]`$, which gives the required containment.

Put $`a=1-w_0`$ and $`p=w_0(1-w_0)`$. We map $`V`$ to the unit disc by
``` math
\zeta=\xi\sqrt{\frac{S}{S^2+a\xi^2-a^2}}.
```
The endpoints $`\xi=\pm1`$ map to $`\zeta=\pm q`$, where $`q^2=S/(S^2+p)`$. The Bergman estimate is consequently
``` math
L^2\le\frac2\pi\log\frac{S^2+S+p}{S^2-S+p}\,
                    \operatorname{Area}(U).
```
The remaining estimate uses the fact that $`U`$ contains only two of the $`n`$ roots. An area bound for the whole lemniscate would lose this information. The companion therefore first treats a regular component $`W`$ containing $`k<n`$ roots, using an exterior map. Reflecting the $`n-k`$ exterior-root factors into the disc gives a Blaschke product $`B`$ with $`|B(0)|=\operatorname{cap}(\overline W)^n/t`$ and $`|B'|<n`$ on the boundary. Summing reciprocal derivatives over the fibre opposite $`B(0)`$ gives $`(n-k)/n<(1-|B(0)|)/(1+|B(0)|)`$, or equivalently $`\operatorname{cap}(\overline W)^n/t<k/(2n-k)`$. For $`k=2`$, this inequality and Pólya’s area–capacity inequality \[polya1928, printed pp. 280–282\], \[crane, Theorem 6\], followed by exhaustion, give $`\operatorname{Area}(U)\le\pi(S/(n-1))^{2/n}`$. We restore the length scale $`|v|^{1/n}`$ to obtain <a href="#eq:disk-family-length" data-reference-type="eqref" data-reference="eq:disk-family-length">[eq:disk-family-length]</a>. Dubinin’s relative area inequality \[dubinin, Theorem 1\] has a different full-covering hypothesis; the absolute component estimate is needed here.

<span id="res:separation-parent" label="res:separation-parent"></span> For the conditional threshold, decrease $`S`$ to $`4/3`$. Since $`p\ge0`$ and $`n\ge3`$, the logarithm is at most $`\log7<2`$ and $`(S/(n-1))^{2/n}\le1`$, giving $`L<2|v|^{1/n}<2`$. For $`n=3,w_0=1,S=6/5`$, use $`(3/5)^{2/3}\log11<2`$. The chosen critical value must be nonzero and have modulus less than one. Root locations by themselves do not isolate it from the others. <span id="bdry:critical-value-separation" label="bdry:critical-value-separation"></span>

<a id="sec:other-results"></a>

# Further estimates

<div id="supplementary-results">

</div>

<a id="sec:critical-proximity"></a>

## Root distances and component geometry

<span id="sec:exact-obstructions" label="sec:exact-obstructions"></span> <span id="res:critical-proximity" label="res:critical-proximity"></span> At a non-root critical point, the balance $`\sum_j(c-z_j)^{-1}=0`$ bounds the ratio of the two smallest root distances by $`n-1`$. Comparing their sum with the geometric mean of all $`n`$ distances then gives a bound of $`2r`$, where $`r^n=\prod_j|c-z_j|`$.

<span id="res:two-nearest-roots" label="res:two-nearest-roots"></span> When all zeros lie in the open unit disc, a different estimate holds: at every non-root critical point the sum of the distances to the two nearest zeros is strictly less than $`2`$. Both arguments and their precise statements are in the companion’s [root-distance estimates](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=root-distance-proofs). The nearest pair is chosen among all roots of $`f`$. It need not be the pair in the two-root component of the degree-seven example, where containment restricts which pair can be joined.

<span id="res:straight-no-go" label="res:straight-no-go"></span> These distance estimates alone do not imply containment. For the quintic
``` math
(z-a)(z^2+p^2)\left(z^2+\frac{902}{901}pz+p^2\right),
 \qquad p=\frac{999}{1000},\quad a=\frac{901}{902}p,
```
all roots lie in the disc and $`0`$ is a non-root critical point, but its unique nearest-root segment leaves the unit lemniscate. Moreover, every root-pair midpoint of $`z^3-(99/100)^3`$ lies outside it. This cubic still admits the two-segment connections of Theorem <a href="#res:trinomial-all-degree" data-reference-type="ref" data-reference="res:trinomial-all-degree">4</a>; it is the straight chords that fail. The [exact counterexamples](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=straight-path-counterexamples) include the escape calculations.

<span id="res:sep-or-false" label="res:sep-or-false"></span> The cubic $`z^3+3z/100-3/4`$ illustrates the restrictions in our sufficient conditions: its least critical-value modulus exceeds $`13/25`$, while its two normalised critical values are too close for the isolation criterion.

<span id="res:arity-not-capacity" label="res:arity-not-capacity"></span> A further cubic has two roots at its first merger but normalised component capacity one at level $`2\mu`$. By that level, all three roots lie in one component. Its capacity is therefore that of the whole filled lemniscate, whose normalisation uses the standard identity $`\operatorname{cap}(K_t(f))=t^{1/n}`$ \[ransford1995, Theorem 5.2.5 and p. 153\].

<span id="res:one-root-gamma-false" label="res:one-root-gamma-false"></span> Finally, $`z^8-(3/2)z`$ has a one-root unit-level component with perimeter larger than the proposed constant $`\Gamma(1/4)^2/(2\sqrt\pi)`$. These examples, with full calculations, appear in [the companion’s component examples](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=component-counterexamples). The last example imposes no restriction on root locations and disproves that specific perimeter constant. The existence of a uniform perimeter constant remains a separate question. Although \[revision2026, Proposition 2\] reports a Runge construction of unbounded one-root perimeters, its proof is unavailable and we do not use it.

<a id="sec:solved-families"></a>

## Sparse families and binomial chords

<span id="sec:binomial" label="sec:binomial"></span> <span id="res:cubic-fibres" label="res:cubic-fibres"></span> Suppose that all zeros lie in the open unit disc. The radial argument extends to $`P((z-h)^q)`$ when $`q\ge2`$ and $`P`$ is a monic cubic: if there are two distinct zeros, some such pair can be joined by a path consisting of two segments. The companion selects a nonzero root $`r`$ of $`P`$ for which $`[0,r]\subset\{|P|<1\}`$. Writing $`f(z)=P((z-h)^q)`$ and $`y^q=r`$, we have $`f(h+ty\zeta)=P(t^qr)`$ for $`0\le t\le1`$ and every $`q`$th root of unity $`\zeta`$. Thus one quotient segment gives $`q`$ contained segments through $`h`$. Averaging $`|h+y\zeta|^2`$ over the full fibre gives $`|h|^2+|y|^2<1`$, so two distinct fibre points are joined with length $`2|y|<2`$.

<span id="res:primitive-quintic" label="res:primitive-quintic"></span> For $`z^5+az^4+bz+c`$, a harmonic-moment identity selects two root indices with $`|bz_j+c|<1`$, after which Abel summation controls the whole segments. The companion gives the [cubic-fibre proof](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=cubic-fibre-proof) and the [quintic selection argument](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=quintic-proof), including repeated root occurrences.

<span id="res:complementary-binomial-chords" label="res:complementary-binomial-chords"></span> For $`z^n-r^n`$, $`0<r<1`$, the maximum modulus on a chord between adjacent points of radius $`s\le r`$ is $`r^n+(s\cos(\pi/n))^n`$. Thus the outer root chord works below $`r_*=(1+\cos^n(\pi/n))^{-1/n}`$. At and above this value, radial legs and a slightly contracted inner chord give open containment and length less than $`2r`$. The [chord calculation](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=binomial-chord-calculation) proves the maximum on the entire segment; it makes no assertion of geodesic optimality. For $`n=2`$, use the diameter.

<a id="sec:collinear"></a>

## Collinear roots

<span id="bdry:solved-polynomial-families" label="bdry:solved-polynomial-families"></span> <span id="res:sharp-collinear-root-diameter" label="res:sharp-collinear-root-diameter"></span> For collinear roots of diameter $`D`$, a Chebyshev alternation argument gives two adjacent root occurrences whose segment satisfies
``` math
|f|\le\frac{(D/2)^n}{2^{n-1}\cos^n(\pi/(2n))}.
```
The constant is sharp, with equality for the appropriately scaled zeros of $`T_n`$. Qualitative existence of a contained root segment was already proved in \[ehp1958, Theorem 1\]. We compare with the monic minimax polynomial (see Eremenko and Yuditskii \[eremenko-yuditskii, §1 and Theorem 1\] for the critical-sequence viewpoint). The companion contains the [alternation proof and equality case](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=collinear-proof).

<a id="sec:freepoint"></a>

## Critical-value means

<span id="res:fp-weighted-all-degree" label="res:fp-weighted-all-degree"></span> For $`c_j\in\overline{\mathbb D}`$ and positive weights of sum one, set $`G(z)=\prod_j|1-\bar c_jz|^{w_j}`$. Then $`\sum_jw_jG(c_j)^2\le1`$, with equality only when all $`c_j=0`$. For interior points, we form the analytic product $`g(z)=1+\sum_{\nu\ge1}a_\nu z^\nu`$ with $`|g|=G`$. The weighted Poisson kernel is $`P=1-2\operatorname{Re}(\zeta g'/g)`$, and
``` math
\sum_jw_jG(c_j)^2\le\int |g|^2P\,dm
          =1-\sum_{\nu\ge1}(2\nu-1)|a_\nu|^2.
```
Radial contraction gives the boundary case.

<span id="res:fp-to-s" label="res:fp-to-s"></span> To apply this inequality to a monic polynomial $`f`$ of degree $`n\ge2`$ with zeros in the closed unit disc, take its $`m=n-1`$ critical points, counted with multiplicity, and give them equal weights $`1/m`$. The reflected-derivative comparison gives the pointwise bound
``` math
|f(c_j)|^{2/m}\le
 \left(\prod_{k=1}^m|1-\bar c_kc_j|\right)^{2/m}=G(c_j)^2.
```
Summing and using the weighted inequality gives $`\sum_j|f(c_j)|^{2/m}\le m`$. For zeros in a closed disc with centre $`h`$ and radius $`R>0`$, apply this to $`R^{-n}f(h+Rz)`$ and scale back to obtain $`\sum_{j=1}^{n-1}|f(c_j)|^{2/(n-1)}\le(n-1)R^{2n/(n-1)}`$. If $`R=0`$, all critical values vanish. An unformalised refinement, recorded as an ordinary argument, uses $`g^2`$ in the same Poisson integral and gives the proposed fourth-power bound
``` math
\sum_{j=1}^{n-1}|f(c_j)|^{4/(n-1)}
       \le(n-1)R^{4n/(n-1)}
```
for the same enclosing disc. Equality is attained by $`(z-h)^n-\lambda`$ with $`|\lambda|=R^n`$. The companion supplies the [weighted identity, reflected-derivative comparison and equality analysis](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=weighted-poisson-proof).

Applying AM–GM to the quadratic specialisation gives Dubinin’s sharp critical-value product bound \[dubinin2006critical, Theorem 2\]. With a zero prescribed at the disc centre, his Theorem 3 gives a different, sharper product estimate and credits earlier work of Tischler \[tischler1989, p. 444, as discussed by Dubinin\]. The corresponding marked-zero positive-moment question in \[revision2026\] remains unresolved here. To turn any of these mean bounds into a short-path theorem, one would still have to select a pair of roots and control a curve joining them inside the lemniscate.

<a id="sec:orlicz"></a>

## Successive merger scales

<span id="res:orlicz-currency" label="res:orlicz-currency"></span> For a component with $`k`$ roots and a ratio $`r`$ of successive merger levels, an integral arising in length estimates is
``` math
I_k(r)=\int_r^1
 \frac{dq}{q\log((1+q^{2/k})/(1-q^{2/k}))}
       =k\Phi\left(\frac1k\log\frac1r\right),
 \qquad \Phi(x)=\int_0^x\frac{dt}{\log\coth t}.
```
Substituting $`q=e^{-kt}`$ gives the identity. Since the integrand increases from zero, $`\Phi`$ is strictly convex and $`\Phi(x)/x\to0`$ at zero. Even for fixed $`k`$, no positive multiple of $`k^{-1}\log(1/r)`$ is a uniform lower bound for $`I_k(r)`$. The precise endpoint statement and its proof are retained in the companion’s [merger-scale calculation](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=merger-integral-proof).

<a id="sec:open"></a>

# Flow constructions and remaining questions

<a id="sec:newton"></a>

## Inverse rays and perturbation

<span id="sec:arguments" label="sec:arguments"></span><span id="sec:reciprocal" label="sec:reciprocal"></span> <span id="res:value" label="res:value"></span> Along a Newton trajectory $`\dot z=-f(z)/f'(z)`$ on a real interval, with $`f'(z(t))\ne0`$, the chain rule gives $`(f\circ z)'=-f\circ z`$. Integrating this scalar equation yields $`f(z(t))=e^{-(t-t_0)}f(z(t_0))`$ for times in that interval. Thus the image in the value plane follows a fixed ray. This identity and the Newtonian graph of Shub, Tischler and Williams are used in the form given by Kozen and Stefánsson \[kozen-stefansson1997, Lemmas 2.1–2.2 and §2\]. The companion also records local complex-parameter identities for $`(f\circ z)'`$ and $`(e^t f(z(t)))'`$. These are pointwise derivative statements; the integration above concerns an existing real-interval trajectory. The companion retains the [value and finite-endpoint theorems](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=newton-value-proof).

<span id="res:ray" label="res:ray"></span> For a finite interval $`[a,b]`$, assume the Newton equation only for $`a<t<b`$ and continuity of $`f(z(t))`$ up to both endpoints. The interior identity then extends to $`f(z(b))=e^{a-b}f(z(a))`$, without evaluating $`f/f'`$ at an endpoint. Nonzero endpoint values therefore lie on the same positive ray. Critical values with distinct arguments exclude such a connection; distinct moduli are insufficient.

<span id="res:locus" label="res:locus"></span> A generic constant perturbation separates rays when the original critical values are distinct, but cannot split equal values. The companion records an unformalised argument that a linear perturbation can do so generically. Neither qualitative assertion supplies a numerical perturbation bound that preserves a near-extremal path inequality. The [forbidden-ray locus calculation](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=argument-perturbation-proof) and the local logarithmic expansion, with remainder $`nq^{N+1}/((N+1)(1-q))`$ for $`q<1`$, specify the available control. The expansion is inapplicable at the distance to the nearest zero.

<a id="res:component-local-covering"></a>

#### Inverse-branch prerequisites.

For a nonconstant complex polynomial, each component of $`\{|f|<1\}`$ [contains a root](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L349). The restriction to that component is [onto the unit disc](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L211) and has [finite fibres](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L233). Over values avoiding the critical values attained in that component, it is a [covering map](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L250). Choose finitely many nonzero slit starts that include every critical value attained in the component, and remove the outward rays beginning at those starts from the value disc. On the remaining domain, each root in the component determines a [unique continuous inverse branch](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L359), taking $`0`$ to that root. The archived Lean source states these prerequisites and supplies proof scripts; a kernel-check receipt for this module is not supplied here. The full conformal sheet decomposition, sheet count, monodromy and embedded-tree assertions remain ordinary arguments in the companion; the prerequisites give no length estimate.

<a id="sec:gap"></a>

## The failed tree estimate

<span id="sec:finite" label="sec:finite"></span> For the Cassini polynomial $`z^2-(9/10)^2`$, any connected set containing both roots has length at least $`9/5`$. The right side of Proposition 12 in the March manuscript \[march2026\], even with its proposed arbitrarily small error, is smaller than $`41/25`$ before that error. Thus the proposed spanning-tree estimate is false. At a simple saddle the local level set has four sectors, consistently with the lemniscate graph description in \[bishop-eremenko-lazebnik, Definition 1.2 and Proposition 2.4\]. The [Cassini calculation and corrected topological statement](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=cassini-counterexample) separate the metric failure from the valid sheet decomposition.

The full topological reconstruction in that discussion remains unformalised. Cutting outward from critical values to obtain inverse-sheet adjacency is classical; see \[dubinin2006critical, §1\] and \[dubinin2006capacity, §2\]. Length control requires additional estimates on the actual pieces and their attachment. An uncut Newton orbit space can even fail to be Hausdorff; it cannot automatically be identified with a finite Reeb graph. The earlier numerical searches in degrees $`5,6,8,10`$ found no counterexample on their tested grids. Such searches neither certify containment along unexamined edges nor prove a quantified statement about all polynomials.

<a id="restricted-extremal-problems"></a>

## Restricted extremal problems

The companion records the following ordinary compactness argument, which has not been formalised. In the closed lemniscate $`K_1(f)`$, a finite infimum of connecting path lengths is attained. At fixed degree, compactness of the closed root-disc class and lower semicontinuity of this infimum allow uniform upper bounds to pass to coefficient limits. These are statements about the closed lemniscate, as proved in the companion’s [compactness argument](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=closed-class-limits). The binomial family approaches length $`2`$. The assertion that the universal extremum is at most $`2`$ is refuted by the degree-seven example; its earlier formulation is not a remaining open problem. Quantitative bounds for restricted classes and for varying degree still require further work.

The precise unresolved questions about cut-open flow strips, attachment lengths and quantitative perturbation are stated in the companion’s [final questions](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=remaining-questions). The origin-spoke failure for the near-regular-pentagon family has an ordinary, unformalised proof there. The stronger failure asserted in the research addendum \[revision2026\] for every critical joining point has no available proof and is not used. Likewise the fixed degree-seven proof does not establish the whole small-parameter family.

<a id="sec:1041-sources"></a>

# Related results and verification

Eremenko and Hayman’s bound $`\mathcal H^1\{|p|=1\}<9.173\deg p`$ \[eremenko-hayman, Theorem 1\] concerns the total boundary length. Their connectedness result, the derivative estimate of Eremenko and Lempert \[eremenko-lempert, Theorem 1\], and its equality analysis \[eremenko-markov, Theorem A\] optimise different quantities from an internal root-to-root path. Kuznetsova and Tkachev \[kuznetsova2003, Theorems 1–2\] study length functions on regular levels; their log-convexity does not imply a uniform one-root perimeter bound at a critical endpoint. Dubinin’s four-point distortion theorem \[dubinin2013fourpoint, Theorem 1 and Corollary 4\] assumes a bound on all critical values and has a different normalisation. Pendyala’s work on Problem 1120 \[pendyala2026shortest, Definition 1.1 and Theorem 1.2\] asks for a path from $`0`$ to the unit circle in the intersection of a lemniscate with the closed disc. Those endpoints and that additional region restriction differ from the present question.

<a id="verification-and-reproducibility."></a>

#### Verification and reproducibility.

The supplied Lean sources prove the fixed counterexample for preconnected sets, the negation and `answer(False)` forms of the Formal Conjectures statement, and the total-variation formulation. They also prove the trinomial theorem and the other formally supported estimates identified in the companion’s [verification notes](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=verification-notes). No fresh Lean build or independent human review is reported here, including review of the correspondence with the 1958 wording. The recorded full rational replay on 29 September 2026 reproduced the stopping time and $`126`$ dual certificates; those are the computational results cited here. The analytic assertions in Remarks <a href="#res:low-critical-thirteen-twentyfifths" data-reference-type="ref" data-reference="res:low-critical-thirteen-twentyfifths">[res:low-critical-thirteen-twentyfifths]</a>–<a href="#res:critical-value-thresholds" data-reference-type="ref" data-reference="res:critical-value-thresholds">[res:critical-value-thresholds]</a>, the fourth-power mean and the later topological and compactness arguments remain outside the formal conclusions. The evidence record retains the statement identifiers and their conditional dependencies.

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1041-lemniscate-newton-flow.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

<a id="acknowledgements"></a>

# Acknowledgements

I thank Wouter van Doorn for advice on explaining restrictive hypotheses, avoiding private terminology and introducing notation only when useful.

<div class="thebibliography">

99 T. F. Bloom, *Erdős Problems*, problem 1041. <https://www.erdosproblems.com/1041> P. Erdős, F. Herzog, and G. Piranian, *Metric properties of polynomials*, J. Analyse Math. **6** (1958), 125–148, doi:[10.1007/BF02790232](https://doi.org/10.1007/BF02790232). `shtuka`, *A Short Path Joining Two Zeros Inside a Polynomial Lemniscate*, manuscript posted 24 March 2026, 48 pp. <https://shtuka123.github.io/1041/main.pdf> V. S. Pendyala, *A Degree-Four Lemniscate Path Theorem*, arXiv:[2606.24875v1](https://arxiv.org/abs/2606.24875v1) (2026), doi:[10.48550/arXiv.2606.24875](https://doi.org/10.48550/arXiv.2606.24875). V. S. Pendyala, *Shortest paths in polynomial lemniscate sublevel sets and a problem of Erdős*, arXiv:[2606.19178v1](https://arxiv.org/abs/2606.19178v1) (2026), doi:[10.48550/arXiv.2606.19178](https://doi.org/10.48550/arXiv.2606.19178). D. Kozen and K. Stefánsson, *Computing the Newtonian graph*, J. Symbolic Comput. **24** (1997), no. 2, 125–136, doi:[10.1006/jsco.1997.0118](https://doi.org/10.1006/jsco.1997.0118); authors’ copy <https://www.cs.cornell.edu/kozen/Papers/newton.pdf>. E. Crane, *The areas of polynomial images and pre-images*, Bull. London Math. Soc. **36** (2004), no. 6, 786–792, doi:[10.1112/S0024609304003509](https://doi.org/10.1112/S0024609304003509); preprint arXiv:[math/0302189v1](https://arxiv.org/abs/math/0302189v1), whose statement numbers are cited. P. Ebenfelt, D. Khavinson, and H. S. Shapiro, *Two-dimensional shapes and lemniscates*, in *Complex Analysis and Dynamical Systems IV, Part 1*, Contemp. Math. **553**, Amer. Math. Soc., Providence, RI, 2011, 45–59, doi:[10.1090/conm/553/10931](https://doi.org/10.1090/conm/553/10931); preprint arXiv:[1003.4567v1](https://arxiv.org/abs/1003.4567v1), whose statement numbers are cited. A. Eremenko and W. Hayman, *On the length of lemniscates*, Michigan Math. J. **46** (1999), no. 2, 409–415, doi:[10.1307/mmj/1030132418](https://doi.org/10.1307/mmj/1030132418); preprint arXiv:[0805.2295](https://arxiv.org/abs/0805.2295). A. Eremenko and P. Yuditskii, *Comb functions*, Contemp. Math. **578** (2012), 99–118, doi:[10.1090/conm/578/11472](https://doi.org/10.1090/conm/578/11472); preprint arXiv:[1109.1464v1](https://arxiv.org/abs/1109.1464v1). A. Eremenko and L. Lempert, *An extremal problem for polynomials*, Proc. Amer. Math. Soc. **122** (1994), no. 1, 191–193, doi:[10.1090/S0002-9939-1994-1207536-1](https://doi.org/10.1090/S0002-9939-1994-1207536-1). A. Eremenko, *A Markov-type inequality for arbitrary plane continua*, Proc. Amer. Math. Soc. **135** (2007), no. 5, 1505–1510, doi:[10.1090/S0002-9939-06-08640-0](https://doi.org/10.1090/S0002-9939-06-08640-0); preprint arXiv:[math/0606745v1](https://arxiv.org/abs/math/0606745v1). C. J. Bishop, A. Eremenko, and K. Lazebnik, *On the shapes of rational lemniscates*, Geom. Funct. Anal. **35** (2025), no. 2, 359–407, doi:[10.1007/s00039-025-00704-2](https://doi.org/10.1007/s00039-025-00704-2); preprint arXiv:[2407.14610v1](https://arxiv.org/abs/2407.14610v1). V. N. Dubinin, *Some inequalities for polynomials and rational functions associated with lemniscates*, Zap. Nauchn. Sem. POMI **404** (2012), 83–99; English translation, J. Math. Sci. **193** (2013), no. 1, 45–54, doi:[10.1007/s10958-013-1432-4](https://doi.org/10.1007/s10958-013-1432-4). G. Pólya, *Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zusammenhängende Gebiete*, Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-Mathematische Klasse (1928), printed pp. 228–232 and 280–282. <https://archive.org/details/sitzungsbericht1928preu>. V. N. Dubinin, *Inequalities for critical values of polynomials*, Sb. Math. **197** (2006), no. 8, 1167–1176, doi:[10.1070/SM2006v197n08ABEH003793](https://doi.org/10.1070/SM2006v197n08ABEH003793). E. Crane, *A bound for Smale’s mean value conjecture for complex polynomials*, Bull. London Math. Soc. **39** (2007), no. 5, 781–791, doi:[10.1112/blms/bdm063](https://doi.org/10.1112/blms/bdm063); author preprint <https://people.maths.bris.ac.uk/~maetc/SMVCbound.pdf>. V. N. Dubinin, *Four-point distortion theorem for complex polynomials*, arXiv:[1301.3985v1](https://arxiv.org/abs/1301.3985v1) (2013). O. S. Kuznetsova and V. G. Tkachev, *Length functions of lemniscates*, Manuscripta Math. **112** (2003), 519–538, doi:[10.1007/s00229-003-0411-3](https://doi.org/10.1007/s00229-003-0411-3); preprint arXiv:[math/0306327](https://arxiv.org/abs/math/0306327). D. Tischler, *Critical points and values of complex polynomials*, J. Complexity **5** (1989), no. 4, 438–456. W. Cook / Plectis, *Three refinements for the lemniscate-path programme*, 16 September 2026, unreviewed research note, Sections 1–3, together with the earlier note *Structural obstructions*. V. N. Dubinin, *Lemniscates and inequalities for the logarithmic capacities of continua*, Mat. Zametki **80** (2006), no. 1, 33–37; English translation, Math. Notes **80** (2006), no. 1, 31–35, doi:[10.1007/s11006-006-0105-8](https://doi.org/10.1007/s11006-006-0105-8). T. Ransford, *Potential Theory in the Complex Plane*, London Mathematical Society Student Texts 28, Cambridge University Press, Cambridge, 1995, doi:[10.1017/CBO9780511623776](https://doi.org/10.1017/CBO9780511623776).

</div>
