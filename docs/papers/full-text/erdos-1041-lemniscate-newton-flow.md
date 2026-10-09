<a id="erdos-1041-lemniscate-newton-flow"></a>

# Paths in Polynomial Lemniscates: A Degree-Seven Counterexample and Radial Connections

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

A monic degree-seven polynomial $`f`$ constructed by `ani` answers Erdős Problem 1041 negatively: all zeros lie in the open unit disc, but every connected subset of $`\{|f|<1\}`$ containing two zeros has one-dimensional Hausdorff measure greater than $`2`$. The obstruction lies in a single two-root component. Its slit preimage is confined near the critical point, so radial projection on the two inverse sheets forces a length greater than $`2`$. In contrast, for every monic trinomial with zeros in the open unit disc, the root equation keeps all root-to-origin segments inside the lemniscate. Further analytic criteria use small or isolated critical values; their proofs are not fully formalised in Lean.

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

Here $`\mathcal H^1`$ is one-dimensional Hausdorff measure. A rectifiable path image has measure at most its total variation, so the theorem excludes short paths as well as more general connected sets.

Five components of $`\Omega_f`$ contain one zero each; the sixth contains two and is the only possible place to join a pair. On this component, $`f`$ has degree two. Cut the value disc from its critical value to the unit circle. Inside the two-root component, the *whole* slit preimage lies in a small disc about the critical point. Connectedness forces a root-joining set to approach this disc on both inverse sheets. The two radial projections then give a lower bound: the sum of the root distances from the critical point, minus twice the small disc’s radius. For the chosen pair this bound exceeds $`2`$.

Section <a href="#sec:counterexample" data-reference-type="ref" data-reference="sec:counterexample">2</a> contrasts the quadratic with the counterexample; Section <a href="#sec:trinomial" data-reference-type="ref" data-reference="sec:trinomial">3</a> treats trinomials and the obstruction introduced by a fourth term. Section <a href="#sec:critical-proximity" data-reference-type="ref" data-reference="sec:critical-proximity">6.1</a> separates root proximity from containment. Sections <a href="#sec:constant-factor" data-reference-type="ref" data-reference="sec:constant-factor">4</a> and <a href="#sec:separation" data-reference-type="ref" data-reference="sec:separation">5</a> construct paths by component growth and continuation around an isolated critical value, respectively. These independent analytic arguments remain unformalised. The [companion paper](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf) gives their proofs, the counterexample’s rational data, and the arguments behind the later estimates and questions.

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

The degree on a component counts preimages *in that component*, with multiplicity; it equals the number of zeros there, not necessarily the degree of the polynomial \[eks2010, proof of Proposition 2.1\]. Near a simple critical point $`c`$, write $`p(c+z)-p(c)=z^2A(z)`$. The quadratic model suggests a spatial scale $`\sqrt{\delta/M}`$: the value slit has length $`\delta=1-|p(c)|`$, while $`M=|A(0)|=|p''(c)|/2`$ converts squared distance into value distance. The next lemma controls this comparison on a disc of radius $`h`$. Degree two serves a different purpose. It ensures that the two local preimages near $`c`$ exhaust every fibre in the chosen component, so a connection cannot pass through an unexamined part of the slit preimage.

<div id="lem:two-sheet-bottleneck" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L187">Lean</a></p>

**Lemma 3**. *Let $`p`$ be a polynomial and $`U`$ a component of $`\{|p|<1\}`$ on which $`p`$ has degree two, with one simple critical point $`c`$ and $`v=p(c)\ne0`$. Write $`p(c+z)-v=z^2A(z)`$ and put $`M=|A(0)|`$, $`\delta=1-|v|`$. Let $`h>0`$. If $`|A(z)/A(0)-1|\le1/4`$ for $`|z|\le h`$ and $`\delta<Mh^2/4`$, then every connected subset $`K`$ of $`U`$ containing its two roots $`a,b`$ satisfies
``` math
\mathcal H^1(K)\ge |a-c|+|b-c|-\frac83\sqrt{\delta/M}.
```*

</div>

<div class="proof">

*Proof.* Cut the value disc along $`J=\{tv:1\le t<1/|v|\}`$. The slit avoids $`0`$ and removes the only critical value of $`p|_U`$. Over its simply connected complement, the double cover splits into two inverse sheets $`U_1,U_2`$, containing $`a,b`$ respectively.

The sheet boundaries inside $`U`$ lie over the slit. To confine them, put $`r_0=(4/3)\sqrt{\delta/M}<2h/3`$. The relative-error hypothesis makes $`A`$ nonvanishing on this disc, and on $`|z|=r_0`$ gives
``` math
|p(c+z)-v|\ge\tfrac34Mr_0^2=\tfrac43\delta>\delta.
```
Every value on $`J`$ is less than $`\delta`$ from $`v`$. Rouché’s theorem compares its preimages with the double zero of $`p-v`$ and gives exactly two in $`B(c,r_0)`$, counted with multiplicity. As the value moves from $`v`$ along $`J`$, these preimages continue from $`c`$ without crossing the circle. Their values stay in the unit disc, so they remain in $`U`$. The degree-two hypothesis now identifies these local preimages with the entire fibre in $`U`$. Thus
``` math
p^{-1}(J)\cap U\subset B(c,r_0).
```

It remains to count how much of $`K`$ lies on each sheet. For $`r_0<t<|a-c|`$, suppose $`K\cap U_1`$ missed the circle $`|z-c|=t`$. Then $`K\cap U_1\cap\{|z-c|>t\}`$ would be both open and closed in $`K`$: the boundary of $`U_1`$ inside $`U`$ lies in $`B(c,r_0)`$, and the remaining boundary is on the missing circle. This set contains $`a`$ and excludes $`b`$, contradicting connectedness. Hence the radial image of $`K\cap U_1`$ contains $`(r_0,|a-c|)`$ whenever this interval is nonempty. The map $`z\mapsto|z-c|`$ is $`1`$-Lipschitz, and therefore
``` math
\mathcal H^1(K\cap U_1)\ge(|a-c|-r_0)_+.
```
Here $`x_+=\max(x,0)`$. The same argument on $`U_2`$ gives the contribution from $`b`$. The radial intervals may overlap on the real line; it is the disjointness of the *sheets in the plane* that permits addition. Hausdorff outer measure adds across disjoint open sets, without a measurability assumption on $`K`$, so
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

Starting from $`z^7-1`$, we put the roots on $`|z|=\rho<1`$ and split the multiple critical point at scale $`\varepsilon`$. The linear, quadratic and cubic perturbations below all have order $`\varepsilon^7`$ at $`z=\varepsilon w`$, so they alter the critical geometry without comparable root displacement. We must identify the only component containing a pair and make its distance surplus exceed the loss in Lemma <a href="#lem:two-sheet-bottleneck" data-reference-type="ref" data-reference="lem:two-sheet-bottleneck">3</a>. The fixed coefficients are those of `ani`’s construction. Put $`s=10^{-6}`$, $`\varepsilon=s^2=10^{-12}`$ and $`\rho=1-s^{16}`$, and let
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

<a id="putting-the-roots-on-a-circle."></a>

#### Putting the roots on a circle.

By $`F(z)=-z^7\overline{F(1/\bar z)}`$, the Cayley substitution $`z=(1+ix)/(1-ix)`$ gives a real polynomial after clearing the denominator and removing a constant phase. Symmetry alone does not locate the zeros: the decisive step is seven sign changes on disjoint rational intervals. The map parametrises the unit circle except $`-1`$, so these give seven distinct circle zeros $`\zeta_j`$, exhausting the degree. Thus $`-1`$ is not a zero and $`b_j=\rho\zeta_j`$ satisfies $`|b_j|=\rho<1`$. The distance estimate below absorbs the contraction $`1-\rho=\varepsilon^8`$.

<a id="resolving-the-critical-points."></a>

#### Resolving the critical points.

At the smaller scale $`z=\rho\varepsilon w`$, write
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
|b_j-c_s|=\rho|\zeta_j-\varepsilon w_s|
 \ge\rho\bigl(1-\varepsilon\operatorname{Re}(w_s\bar\zeta_j)\bigr).
```
The negative projection sum for $`\zeta_3,\zeta_6`$ gives a positive distance surplus of order $`\varepsilon`$; the contraction has only order $`\varepsilon^8`$. The exact bounds at the fixed parameter are:
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
The subscripts $`3,6`$ refer to Cayley roots in the intervals $`(43812,43813)/10^4`$ and $`(-4816,-4815)/10^4`$. The Taylor bound gives the lemma’s quadratic control, while the bounds on $`M`$ and $`\delta`$ give $`\sqrt{\delta/M}<\rho\varepsilon/5000`$. Thus the slit loss is smaller than the displayed distance surplus. This comparison matters only if the selected roots share a component; the following paths establish that membership, not a short connection.

<a id="identifying-the-two-roots-in-the-component."></a>

#### Identifying the two roots in the component.

In the $`w`$-plane, polygonal arcs connect a small disc about $`w_s`$ to points near $`8\zeta_3`$ and $`8\zeta_6`$. Short joining segments then reach those exact root directions, and radial segments continue to the roots. For the four inner polygonal segments we use
``` math
1-|f(\rho\varepsilon w)|^2\ge
 2\rho^{14}\varepsilon^7
 \left(7\varepsilon+\operatorname{Re}Q(w)
                       -\tfrac12\varepsilon^7|Q(w)|^2\right).
```
This follows by expanding the square and using $`1-\rho^{14}\ge14\rho^{14}\varepsilon^8`$. On each segment, the expression in parentheses is a polynomial of degree at most fourteen in the segment parameter. All fifteen coefficients in its degree-fourteen Bernstein basis are positive. The basis polynomials are nonnegative and sum to one, so the expression is positive along the whole segment, which therefore stays inside $`\{|f|<1\}`$ after scaling. The companion bounds $`Q`$ directly on the short joining segments. For the radial portions we use the root identity
``` math
F(t\zeta)=t^7-1+
       \sum_{k=1}^6\varepsilon^{7-k}q_k\zeta^k(t^k-t^7),
 \qquad Q(w)=\sum_{k=1}^7q_kw^k,
```
which gives $`|F(t\zeta)|<1`$ for $`8\varepsilon\le t\le1`$. All rational intervals, vertices and coefficient tests are specified in [the companion’s finite verification](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=counterexample-certificate). At the regular level $`|f|=1`$, the component-wise Riemann–Hurwitz calculation \[eks2010, proof of Proposition 2.1\] gives $`k-1`$ critical points in a component with $`k`$ zeros, counted with multiplicity. Since $`c_s`$ is the only critical point in $`\Omega_f`$, its component contains exactly the two roots just reached; every other component contains one.

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

If $`f(z)=z^n+b`$ has a zero $`\zeta`$ in the open unit disc, then $`|b|=|\zeta|^n<1`$. The identity $`f(t\zeta)=b(1-t^n)`$, $`0\le t\le1`$, keeps the whole segment $`[0,\zeta]`$ in the lemniscate. The same cancellation survives a middle monomial. Its coefficient may be large, so we use $`f(\zeta)=0`$ to eliminate that term *before* taking absolute values. The remaining quantities are $`b`$ and $`-\zeta^n`$, both of modulus less than one.

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
f(t\zeta)=(1-t^m)b+(t^m-t^n)(-\zeta^n).
```
Vieta’s formula gives $`|b|<1`$. For $`0\le t<1`$, the two weights are nonnegative, the first is positive, and their sum is $`1-t^n`$. Hence
``` math
|f(t\zeta)|\le |b|(1-t^m)+|\zeta|^n(t^m-t^n)<1-t^n\le1.
```
At $`t=1`$ the value is zero. We join any two distinct zeros by concatenating their segments through the origin. ◻

</div>

Abel summation identifies exactly what this argument needs. For $`f(z)=\sum_{k=0}^n a_kz^k`$ and a zero $`\zeta`$, put $`S_j=\sum_{k=0}^j a_k\zeta^k`$. Since $`S_n=0`$, summation by parts gives
``` math
f(t\zeta)=\sum_{j=0}^{n-1}(t^j-t^{j+1})S_j.
```
For $`0\le t<1`$, the weights are nonnegative and sum to $`1-t^n`$. Thus $`f(t\zeta)/(1-t^n)`$ is a convex combination of the $`S_j`$. For a trinomial, $`S_j=b`$ before the middle term and $`S_j=-\zeta^n`$ after it. Thus every partial sum lies in the unit disc. A fourth term introduces another partial sum for which root locations alone need not give that bound, as the next example shows. The conclusion concerns segments ending at zeros, not star-shapedness of the whole lemniscate.

<div id="res:sextic-spoke" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/SexticSpokeWhole.lean#L9">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1041-lemniscate-newton-flow.md#res-sextic-spoke-comparator">Comparator</a></p>

**Proposition 5** (failure of a prescribed radial segment). *There exist $`r\in(0,1)`$ for which every zero of
``` math
f_r(z)=z^6+\tfrac15 r^2 z^4-\tfrac15 r^4 z^2-r^6
```
lies in the open unit disc, yet the radial segment from the origin to the zero $`r`$ leaves $`\{|f_r|<1\}`$.*

</div>

<div class="proof">

*Proof.* We substitute $`z=rw`$ and factor the polynomial as $`r^6(w^2-1)(w^4+\tfrac65w^2+1)`$. The quadratic in $`w^2`$ has conjugate roots of product one, so all six original zeros have modulus $`r`$. At the midpoint of that segment, $`f_r(r/2)=-(327/320)r^6`$; choosing $`320/327<r^6<1`$ proves the assertion. ◻

</div>

This failure concerns the prescribed segment only. In Section <a href="#sec:solved-families" data-reference-type="ref" data-reference="sec:solved-families">6.2</a> we use the partial-sum identity again, first for power substitutions in a cubic and then for a quintic whose two missing coefficients select a suitable pair of segments.

<a id="sec:constant-factor"></a>

# A small least critical value

<div id="low-critical-short">

</div>

A small critical value leaves a long interval of levels before the unit lemniscate is reached. For a squarefree polynomial, put $`\mu=\min_{f'(c)=0}|f(c)|>0`$ and follow a component from its first merger at level $`\mu`$ to level $`1`$. If no two roots admit a connection shorter than $`2`$, conformal length estimates force them far apart in the component’s hyperbolic metric. Packing then bounds the root count from below; inverse-ray averaging turns that count into a lower bound for area growth. When $`\log(1/\mu)`$ is large enough, this growth contradicts Pólya’s area bound.

The companion proves the analytic reduction and gives the rational comparison. The resulting criterion needs no restriction on root locations, but its analytic proof has not been formalised.

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

Assume that no pair has a connection of length less than $`2`$ in $`\Omega_f`$. At a regular level $`t\in(\mu,1)`$, let $`C_t`$ contain a chosen first merger and let $`k\ge2`$ be its root count. Put $`a=\operatorname{Area}(C_t)/\pi`$ and $`x=\log(t/\mu)`$; Pólya’s inequality gives $`a\le1`$ \[crane, Theorems 1 and 6\]. Uniformise $`C_t`$ by the disc, with $`d(0,s)=2\operatorname{artanh}s`$ for $`0\le s<1`$. For roots at hyperbolic distance $`d`$, choose $`\varphi:\mathbb D\to C_t`$ sending $`\pm s`$ to them. Then $`d=4\operatorname{artanh}s`$ and $`\int_{\mathbb D}|\varphi'|^2\,dA=\pi a`$. Cauchy–Schwarz with the Bergman kernel gives
``` math
\operatorname{length}(\varphi([-s,s]))^2
 \le a\int_{-s}^{s}\int_{-s}^{s}\frac{du\,dv}{(1-uv)^2}
 =2a\log\cosh(d/2).
```
Thus pairwise root distances are at least $`D`$, where $`\cosh(D/2)=e^{2/a}`$.

To control the distances from the centre as well, choose a point $`h`$ on a connected set through the first pair in $`K_\mu(f)`$ whose intrinsic distance from every root is at least $`1`$. Here intrinsic distance means the infimum of Euclidean curve lengths in $`C_t`$. Such an $`h`$ exists: the intrinsic open unit balls about distinct roots are disjoint, since an intersection would give a path shorter than $`2`$, and disjoint open sets cannot cover a connected set containing two roots. Choose the uniformisation to send $`0`$ to $`h`$. If $`d_j`$ are the resulting hyperbolic root distances from $`0`$, then
``` math
\lambda(d_j)\le\tfrac12\delta(a),\qquad
 \sum_j\lambda(d_j)\ge x,\qquad
 \lambda(d)=-\log\tanh(d/2),\quad
 \delta(a)=-\log(1-e^{-1/a}).
```
The one-root Bergman estimate gives the first bound because every root has intrinsic distance at least $`1`$ from $`h`$. For the second, the component-wise Blaschke representation \[eks2010, (2.2)\] expresses $`f/t`$ in disc coordinates. Since $`h`$ is not a root and lies in $`K_\mu(f)`$, evaluation at $`0`$ gives $`\sum_j\lambda(d_j)=\log(t/|f(h)|)\ge x`$. Dividing the required sum $`x`$ by the maximum contribution $`\delta(a)/2`$ gives $`k\ge2x/\delta(a)`$. This uses only distances from the centre. To exploit the pairwise separation too, we intersect the disjoint hyperbolic balls about the roots with a common circle. The passage through a first merger, including simultaneous mergers, is part of the analytic input still to be formalised.

<div id="circle-packing-inputs">

</div>

On a fixed hyperbolic circle of radius $`r>0`$ centred at $`0`$, the balls of radius $`D/2`$ cut out disjoint arcs. Their angular half-widths satisfy
``` math
w(d,r)=\arccos\!\left(\operatorname{clamp}_{[-1,1]}
 \frac{\cosh d\cosh r-\cosh(D/2)}{\sinh d\sinh r}\right),
 \qquad \sum_jw(d_j,r)\le\pi.
```
Here $`\operatorname{clamp}_{[-1,1]}`$ truncates to $`[-1,1]`$. This circle-slice inequality is formalised separately. To turn it into a root count, majorise the contribution of one root by weighted slice widths: choose $`\sigma_i\ge0`$, $`r_i>0`$ and $`U>0`$ such that $`\lambda(d)\le U+\sum_i\sigma_iw(d,r_i)`$ whenever $`d>0`$ and $`\lambda(d)\le\delta(a)/2`$. Summing at the roots and using the angular bound at each $`r_i`$ gives
``` math
\begin{equation}
\label{eq:short-packing}
 k\ge\frac{x-\pi\sum_i\sigma_i}{U}.
\end{equation}
```
The circle must be fixed before taking these intersections: angular projections of disjoint balls at different distances can overlap.

We now convert the root count into area growth. Lift one common value radius from all $`k`$ roots to $`\partial C_t`$ and join successive endpoints by boundary arcs. All pieces stay in $`\Omega_f`$ because $`t<1`$. Splitting the lift integral at level $`\mu`$ bounds the mean total lift length by $`\sqrt{ka(x+2)/2}`$. Each of the $`k`$ resulting root-to-root connections has length at least $`2`$; their sum counts each lift twice and the boundary once. Hence $`2k\le\sqrt{2ka(x+2)}+\mathcal H^1(\partial C_t)`$. Combining this with $`\mathcal H^1(\partial C_t)^2\le2\pi k t\,(d/dt)\operatorname{Area}(C_t)`$ yields the ordinary differential inequality
``` math
\begin{equation}
\label{eq:short-area-growth}
 a'(x)\ge\frac1{2\pi^2}
       \bigl[2\sqrt k-\sqrt{2a(x)(x+2)}\bigr]_+^2.
\end{equation}
```
Here the derivative is with respect to $`x`$, between merger levels. The companion proves the lift estimate and accounts for the nonnegative area jumps at mergers; those jumps do not weaken the lower bound.

<a id="the-recorded-rational-comparison"></a>

## The recorded rational comparison

<div id="certificate-stopping-time">

</div>

At each level use the largest integer lower bound for the current root count $`k`$: <a href="#eq:short-packing" data-reference-type="eqref" data-reference="eq:short-packing">[eq:short-packing]</a>, $`k\ge2x/\delta(a)`$, or the companion’s two further packing estimates. The starting bound $`a(3/10^5)>10^{-6}`$ follows by integrating <a href="#eq:short-area-growth" data-reference-type="eqref" data-reference="eq:short-area-growth">[eq:short-area-growth]</a> with $`k\ge2`$ and $`a\le1`$; it is not an extra assumption on the polynomial. The recorded rational calculation then reaches $`a>1`$ by
``` math
X=\frac{635762889599}{10^{12}}.
```
It used $`18`$ area levels, $`126`$ certified weighted inequalities and a maximum step $`1/400`$. On each interval $`[u,v]`$ of possible root distances, the calculation bounds $`\lambda(d)-\sum_i\sigma_iw(d,r_i)`$ by $`\lambda(u)-\sum_i\sigma_i\min(w(u,r_i),w(v,r_i))`$; on the tail, $`\lambda`$ itself suffices. Thus numerical optimisation only proposes the weights. Rational inequalities certify a valid $`U`$ on the whole admissible half-line, as required by <a href="#eq:short-packing" data-reference-type="eqref" data-reference="eq:short-packing">[eq:short-packing]</a>. The endpoint minimum is valid because each slice width, as a function of $`d`$, increases and then decreases, or is monotone; it has no interior dip. This is an interval bound, not sampling between grid points.

Since $`t=\mu e^x`$, the contradiction $`a>1`$ occurs before level $`1`$ provided that $`\mu e^X<1`$. The recorded comparison gives $`(13/25)e^X<0.982000386<1`$. It also gives $`(529/1000)e^X<0.998996547`$, so the ordinary argument supports that sharper threshold as well. Neither threshold is claimed optimal, and this arithmetic does not formalise the analytic reduction.

<span id="res:constant-factor-path" label="res:constant-factor-path"></span> A related ordinary averaging argument, also unformalised in its analytic construction, gives the following bounds. For a monic polynomial of degree $`n\ge2`$, two zero occurrences can be joined in $`K_{2\mu}(f)`$ with length at most $`(71/10)\mu^{1/n}`$; they are distinct in the squarefree case, and a repeated root gives a constant path. When $`\mu\le1/2`$, the argument gives a path of length at most $`5.7`$ in $`\Omega_f`$. The proof, together with refinements that retain the number of zeros in the component or its logarithmic capacity, is given in the [inverse-ray averaging argument](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=constant-factor-proof).

<a id="sec:separation"></a>

# An isolated simple critical value

Smallness of the least critical value is not the only useful condition. An isolated simple critical value lets us continue the two branches meeting there without encountering further branching. After dividing values by $`v=f(c)\ne0`$, the critical value is $`1`$ and the roots lie over $`0`$. We seek a disc containing both points but no other critical value. Its centre $`w_0\in[0,1]`$ and radius $`S`$ must therefore satisfy $`S>\max(w_0,1-w_0)`$.

The ordinary construction combines a square-root coordinate, a Bergman length estimate and a component-area bound. These are the contents of the unformalised input `DiscSepBergmanArea`; the formal consequences below remain conditional on it.

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

The ordinary argument first removes the scale of $`v`$, then constructs a curve, and finally bounds its length. Choose $`\alpha^n=v`$ and set $`P(z)=v^{-1}f(c+\alpha z)`$. This polynomial is monic, with its chosen critical point at $`0`$ and critical value $`1`$; Euclidean lengths are multiplied by $`|\alpha|=|v|^{1/n}`$ on returning to the original plane. The component $`U`$ of $`P^{-1}(D(w_0,S))`$ containing $`0`$ has degree two. To apply Riemann–Hurwitz, exhaust it by components above regular inner discs: the outer boundary itself may contain other critical values. Since $`U`$ is simply connected and $`1-P`$ has only a double zero at $`0`$ there, it has a single-valued analytic square root $`\xi`$. This square root removes the simple branching. It is a proper local biholomorphism onto $`V=\{\xi:|\xi^2-(1-w_0)|<S\}`$, a star-shaped and hence simply connected domain. Thus it is biholomorphic. Its inverse maps $`-1`$ and $`1`$ to the two roots and $`[-1,1]`$ to their connection. Along this interval $`P=1-\xi^2\in[0,1]`$, which gives the required containment. Let $`L`$ be the Euclidean length of this normalised curve.

Put $`a=1-w_0`$ and $`p=w_0(1-w_0)`$. Squaring maps $`V`$ onto $`D(a,S)`$. A Möbius map from this disc to the unit disc fixing $`0`$, followed by taking a square root, gives the conformal map
``` math
\zeta=\xi\sqrt{\frac{S}{S^2+a\xi^2-a^2}}.
```
Choose the square-root factor positive at $`0`$. The endpoints $`\xi=\pm1`$ then map to $`\zeta=\pm q`$, where $`q^2=S/(S^2+p)`$. The hypothesis on $`S`$ gives $`S^2-S+p=(S-w_0)(S-(1-w_0))>0`$, so $`0<q<1`$. The Bergman segment estimate used in Section <a href="#sec:constant-factor" data-reference-type="ref" data-reference="sec:constant-factor">4</a> now applies to $`[-q,q]`$ and gives
``` math
L^2\le\frac2\pi\log\frac{S^2+S+p}{S^2-S+p}\,
                    \operatorname{Area}(U).
```
The factor $`n-1`$ comes from the roots outside $`U`$, not from Pólya’s inequality alone. For monic $`F`$ of degree $`n`$ and regular level $`t>0`$, let $`W`$ be a component of $`\{|F|<t\}`$ containing $`k<n`$ zeros counted with multiplicity. Reflecting the $`n-k`$ exterior-root factors into the disc gives a Blaschke product $`B`$ of degree $`n-k`$ with $`|B(0)|=\operatorname{cap}(\overline W)^n/t`$ and $`|B'|<n`$ on the boundary. The boundary-fibre identity gives
``` math
\frac{n-k}{n}<
 \sum_{\substack{B(\zeta)=w\\|\zeta|=1}}\frac1{|B'(\zeta)|}
 =\frac{1-|B(0)|^2}{|w-B(0)|^2},\qquad |w|=1.
```
Choosing $`w`$ opposite $`B(0)`$ gives $`(n-k)/n<(1-|B(0)|)/(1+|B(0)|)`$, hence $`\operatorname{cap}(\overline W)^n/t<k/(2n-k)`$.

Apply this to $`F=P-w_0`$ on the regular inner components exhausting $`U`$. Their degree is two, so $`k=2`$ and $`k/(2n-k)=1/(n-1)`$. Here $`k`$ counts preimages of $`w_0`$ under $`P`$. These need not be the roots joined by the curve; the component degree gives both counts. Pólya’s area–capacity inequality \[polya1928, printed pp. 280–282\], \[crane, Theorem 6\], followed by exhaustion, now gives $`\operatorname{Area}(U)\le\pi(S/(n-1))^{2/n}`$. The original curve has length $`\operatorname{length}(\Gamma)=|v|^{1/n}L`$, which gives <a href="#eq:disk-family-length" data-reference-type="eqref" data-reference="eq:disk-family-length">[eq:disk-family-length]</a>. Dubinin’s relative area inequality \[dubinin, Theorem 1\] has a different full-covering hypothesis; the absolute component estimate is needed here.

<span id="res:separation-parent" label="res:separation-parent"></span> For the conditional threshold, decrease $`S`$ to $`4/3`$. Since $`p\ge0`$ and $`n\ge3`$, the logarithm is at most $`\log7<2`$ and $`(S/(n-1))^{2/n}\le1`$, giving $`\operatorname{length}(\Gamma)<2|v|^{1/n}<2`$. For $`n=3,w_0=1,S=6/5`$, use $`(3/5)^{2/3}\log11<2`$. The chosen critical value must be nonzero and have modulus less than one. Root locations by themselves do not isolate it from the others. <span id="bdry:critical-value-separation" label="bdry:critical-value-separation"></span>

<a id="sec:other-results"></a>

# Further estimates

<div id="supplementary-results">

</div>

<a id="sec:critical-proximity"></a>

## Root distances do not ensure containment

<span id="sec:exact-obstructions" label="sec:exact-obstructions"></span> <span id="res:critical-proximity" label="res:critical-proximity"></span> Order the root distances at a non-root critical point $`c`$ as $`0<d_1\le\cdots\le d_n`$. The balance $`\sum_j(c-z_j)^{-1}=0`$ and this ordering give
``` math
\frac1{d_1}\le\frac{n-1}{d_2},\qquad
 d_1d_2^{n-1}\le|f(c)|.
```
The ratio bound $`1\le d_2/d_1\le n-1`$ permits the scalar comparison
``` math
d_1+d_2\le2(d_1d_2^{n-1})^{1/n}\le2|f(c)|^{1/n}.
```
Neither inequality supplies containment.

<span id="res:two-nearest-roots" label="res:two-nearest-roots"></span> When all zeros lie in the open unit disc, a different estimate holds: at every non-root critical point the sum of the distances to the two nearest zeros is strictly less than $`2`$. The companion gives both [root-distance estimates](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=root-distance-proofs). The nearest pair is chosen among all roots of $`f`$. It need not be the pair in the two-root component of the degree-seven example, where containment restricts which pair can be joined.

<span id="res:straight-no-go" label="res:straight-no-go"></span> Even a short segment from a critical point can leave the lemniscate. For the quintic
``` math
(z-a)(z^2+p^2)\left(z^2+\frac{902}{901}pz+p^2\right),
 \qquad p=\frac{999}{1000},\quad a=\frac{901}{902}p,
```
all roots lie in the disc and $`0`$ is a non-root critical point, but its unique nearest-root segment leaves the unit lemniscate. Moreover, every root-pair midpoint of $`z^3-(99/100)^3`$ lies outside it. This cubic still admits the two-segment connections of Theorem <a href="#res:trinomial-all-degree" data-reference-type="ref" data-reference="res:trinomial-all-degree">4</a>; it is the straight chords that fail. The [exact counterexamples](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=straight-path-counterexamples) include the escape calculations.

<span id="res:sep-or-false" label="res:sep-or-false"></span> Nor do the two critical-value criteria cover every polynomial in the root-disc class. For $`z^3+3z/100-3/4`$, the least critical-value modulus exceeds $`13/25`$, and the two normalised critical values are too close for the isolation criterion.

<span id="res:arity-not-capacity" label="res:arity-not-capacity"></span> A further cubic has two roots at its first merger but normalised component capacity one at level $`2\mu`$. By that level all three roots have merged, so the initial two-root count cannot be used at the later level. The component is now the whole filled lemniscate, whose capacity is given by $`\operatorname{cap}(K_t(f))=t^{1/n}`$ \[ransford1995, Theorem 5.2.5 and p. 153\].

<span id="res:one-root-gamma-false" label="res:one-root-gamma-false"></span> Finally, $`z^8-(3/2)z`$ has least critical-value modulus $`\mu>1`$, yet a one-root unit-level component has perimeter larger than $`\Gamma(1/4)^2/(2\sqrt\pi)`$; see [the companion’s component examples](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=component-counterexamples). No root-location restriction is imposed. The open question asks for a constant $`\beta`$ bounding each component perimeter of $`K_\sigma(f)`$ by $`\beta\sigma^{1/n}`$, uniformly over squarefree monic $`f`$ of degree $`n\ge2`$ and $`0<\sigma<\mu`$. This level restriction is stronger than a one-root condition on a single component. Although \[revision2026, Proposition 2\] reports a Runge construction of unbounded one-root perimeters, its proof is unavailable and we do not use it.

<a id="sec:solved-families"></a>

## Sparse families and binomial chords

<span id="sec:binomial" label="sec:binomial"></span> <span id="res:cubic-fibres" label="res:cubic-fibres"></span> Let $`f(z)=P((z-h)^q)`$, where $`q\ge2`$ and $`P`$ is a monic cubic, and suppose all zeros of $`f`$ lie in the open unit disc. For any root $`r=y^q`$ of $`P`$, averaging $`|h+y\zeta|^2`$ over the $`q`$th roots of unity cancels the cross term and gives $`|h|^2+|y|^2<1`$. Thus the quotient roots satisfy $`|r|=|y|^q<1`$. If $`f`$ has two distinct zeros, the companion selects a nonzero root $`r`$ with $`[0,r]\subset\{|P|<1\}`$. Choose $`y^q=r`$. Then $`f(h+ty\zeta)=P(t^qr)`$ for $`0\le t\le1`$, so the whole fibre gives contained segments through $`h`$. Two distinct fibre points are joined with length $`2|y|<2`$, using the same average.

<span id="res:primitive-quintic" label="res:primitive-quintic"></span> For $`f(z)=z^5+az^4+bz+c`$ with open-disc roots, Abel summation gives a contained radial segment whenever $`|bz_j+c|<1`$. For $`a\ne0`$, the missing coefficients fix the first three power sums. After rotation, the companion’s harmonic function sums to $`5-2|a|`$ over the roots. It is bounded above by $`4-2|a|`$ on the disc and by $`2/31`$ at roots with $`|bz_j+c|\ge1`$. Four such indices would therefore give
``` math
5-2|a|\le4-2|a|+\frac8{31}<5-2|a|,
```
a contradiction. Hence two indices satisfy $`|bz_j+c|<1`$. When $`a=0`$, the root equation gives $`|bz_j+c|=|z_j|^5<1`$ directly. Coincident selected root values give the constant path. The companion gives the [cubic-fibre proof](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=cubic-fibre-proof) and the [quintic selection argument](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=quintic-proof), including repeated root occurrences.

<span id="res:complementary-binomial-chords" label="res:complementary-binomial-chords"></span> For $`z^n-r^n`$, $`0<r<1`$, the maximum modulus on an adjacent chord of radius $`0<s\le r`$ is $`r^n+(s\cos(\pi/n))^n`$. The outer root chord therefore works below $`r_*=(1+\cos^n(\pi/n))^{-1/n}`$. At and above this value, take a slightly contracted inner radius $`s>0`$ making that maximum less than one. The radial legs remain contained, and for $`n\ge3`$ the total length is
``` math
2(r-s)+2s\sin(\pi/n)<2r<2.
```
The [chord calculation](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=binomial-chord-calculation) proves the maximum on the entire segment, not geodesic optimality. For $`n=2`$, use the diameter.

<a id="sec:collinear"></a>

## Collinear roots

<span id="bdry:solved-polynomial-families" label="bdry:solved-polynomial-families"></span> <span id="res:sharp-collinear-root-diameter" label="res:sharp-collinear-root-diameter"></span> For collinear roots of diameter $`D`$, a Chebyshev alternation argument gives two adjacent root occurrences whose segment satisfies
``` math
|f|\le\frac{(D/2)^n}{2^{n-1}\cos^n(\pi/(2n))}.
```
The constant is sharp, with equality for the appropriately scaled zeros of the Chebyshev polynomial $`T_n`$. Qualitative existence of a contained root segment was already proved in \[ehp1958, Theorem 1\]. For distinct roots, first reduce to the real monic case. If every gap maximum exceeded the bound, subtracting the endpoint-normalised monic Chebyshev polynomial would give a polynomial of degree at most $`n-1`$ with $`n`$ distinct zeros: two endpoints and $`n-2`$ intervening sign changes. See Eremenko and Yuditskii \[eremenko-yuditskii, §1 and Theorem 1\] for the critical-sequence viewpoint. The companion contains the [alternation proof and equality case](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=collinear-proof).

<a id="sec:freepoint"></a>

## Critical-value means

<span id="res:fp-weighted-all-degree" label="res:fp-weighted-all-degree"></span> For $`c_j\in\overline{\mathbb D}`$ and positive weights of sum one, set $`G(z)=\prod_j|1-\bar c_jz|^{w_j}`$. Then $`\sum_jw_jG(c_j)^2\le1`$, with equality only when all $`c_j=0`$.

For interior centres, the nonvanishing factors give an analytic $`g(z)=1+\sum_{\nu\ge1}a_\nu z^\nu`$ with $`|g|=G`$. On $`\zeta=e^{i\theta}`$ the weighted Poisson kernel is $`P=\sum_jw_j(1-|c_j|^2)/|\zeta-c_j|^2
=1-2\operatorname{Re}(\zeta g'/g)`$. With $`dm=d\theta/(2\pi)`$, subharmonicity gives the inequality below, and orthogonality gives the identity:
``` math
\sum_jw_jG(c_j)^2\le\int |g|^2P\,dm
          =1-\sum_{\nu\ge1}(2\nu-1)|a_\nu|^2.
```
Indeed, $`\int|g|^2\,dm=1+\sum|a_\nu|^2`$ and $`\int\zeta g'\overline g\,dm=\sum\nu|a_\nu|^2`$. Each nonconstant coefficient therefore contributes $`1-2\nu<0`$. For boundary centres, replace $`c_j`$ by $`rc_j`$ and let $`r\uparrow1`$ with a finite coefficient sum first; no boundary logarithm is needed. Equality forces every $`a_\nu`$ to vanish. Logarithmic differentiation of $`g=1`$, grouping repeated centres, then forces all the positive-weight centres to be zero.

<span id="res:fp-to-s" label="res:fp-to-s"></span> To apply this inequality to a monic polynomial $`f`$ of degree $`n\ge2`$ with zeros in the closed unit disc, take its $`m=n-1`$ critical points, counted with multiplicity, and give them equal weights $`1/m`$. Gauss–Lucas puts these points in the closed unit disc. The reflected-derivative comparison then gives the pointwise bound
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

Applying AM–GM to $`\sum_j|f(c_j)|^{2/(n-1)}\le n-1`$ in the unit disc gives Dubinin’s sharp critical-value product bound \[dubinin2006critical, Theorem 2\]. With a zero prescribed at the disc centre, his Theorem 3 gives a different, sharper product estimate and credits earlier work of Tischler \[tischler1989, p. 444, as discussed by Dubinin\]. The corresponding marked-zero positive-moment question in \[revision2026\] remains unresolved here. To turn any of these mean bounds into a short-path theorem, one would still have to select a pair of roots and control a curve joining them inside the lemniscate.

<a id="sec:orlicz"></a>

## Successive merger scales

<span id="res:orlicz-currency" label="res:orlicz-currency"></span> For a component with $`k\ge1`$ roots, let $`r\in(0,1]`$ be the earlier merger level divided by the later one. An integral arising in length estimates is
``` math
I_k(r)=\int_r^1
 \frac{dq}{q\log((1+q^{2/k})/(1-q^{2/k}))}
       =k\Phi\left(\frac1k\log\frac1r\right),
 \qquad \Phi(x)=\int_0^x\frac{dt}{\log\coth t}.
```
Substituting $`q=e^{-kt}`$ gives the identity; the integrand defining $`\Phi`$ has limiting value zero at $`t=0`$. It is increasing, so $`\Phi`$ is strictly convex and $`\Phi(x)/x\to0`$ as $`x\downarrow0`$. Thus, when the two merger levels approach one another ($`r\uparrow1`$), $`I_k(r)`$ becomes arbitrarily small relative to $`k^{-1}\log(1/r)`$, even for fixed $`k`$. No positive uniform lower factor exists. See the [merger-scale calculation](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=merger-integral-proof).

<a id="sec:open"></a>

# Flow constructions and remaining questions

<a id="sec:newton"></a>

## Inverse rays and perturbation

<span id="sec:arguments" label="sec:arguments"></span><span id="sec:reciprocal" label="sec:reciprocal"></span> <span id="res:value" label="res:value"></span> Along an existing real-interval trajectory $`\dot z=-f(z)/f'(z)`$ with $`f'(z(t))\ne0`$, the chain rule gives $`(f\circ z)'=-f\circ z`$, hence $`f(z(t))=e^{-(t-t_0)}f(z(t_0))`$. This classical identity fixes the ray of a nonzero value, not the Euclidean length $`\int|f(z(t))/f'(z(t))|\,dt`$; see Kozen and Stefánsson \[kozen-stefansson1997, Lemmas 2.1–2.2 and §2\] on the Newtonian graph of Shub, Tischler and Williams. The companion’s local complex-parameter identities for $`(f\circ z)'`$ and $`(e^t f(z(t)))'`$ are pointwise statements, distinct from the real-interval integration in its [value and finite-endpoint theorems](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=newton-value-proof).

<span id="res:ray" label="res:ray"></span> For a finite interval $`[a,b]`$, assume the Newton equation only for $`a<t<b`$ and continuity of $`f(z(t))`$ up to both endpoints. The interior identity then extends to $`f(z(b))=e^{a-b}f(z(a))`$, without evaluating $`f/f'`$ at an endpoint. Nonzero endpoint values therefore lie on the same positive ray. Critical values with distinct arguments exclude such a connection; distinct moduli are insufficient.

<span id="res:locus" label="res:locus"></span> Adding $`\beta`$ leaves $`f'`$ unchanged and sends each critical value $`v`$ to $`v+\beta`$. For distinct values $`a,b`$, a common positive ray requires $`\beta`$ to lie on the real line through $`-a`$ and $`-b`$. Avoiding these finitely many lines and the points $`-v`$ therefore makes the distinct values nonzero and ray-separated; equal values remain equal. The formal sources give the [one-parameter collision locus](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L107) and the [finite affine-line avoidance argument](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L162). The [companion calculation](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=argument-perturbation-proof) describes the forbidden translations; its unformalised linear-perturbation argument supplies distinct critical values. Neither qualitative step controls the slack in a near-extremal path inequality. Separately, expand $`\log|f|`$ about a non-root point and let $`q`$ be the displacement divided by the distance to the nearest zero. For $`q<1`$, the remainder after order $`N`$ is at most $`nq^{N+1}/((N+1)(1-q))`$. This local expansion cannot be used through a zero and does not itself give a coefficient-perturbation bound.

<a id="res:component-local-covering"></a>

#### Inverse-branch prerequisites.

For a nonconstant complex polynomial, each component of $`\{|f|<1\}`$ [contains a root](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L349). The restriction to that component is [onto the unit disc](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L211) and has [finite fibres](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L233). Over values avoiding the critical values attained in that component, it is a [covering map](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L250). When $`0`$ is not a critical value on the component, choose finitely many nonzero slit starts including its critical values, and remove their outward rays from the value disc. On the remaining domain, each root in the component determines a [unique continuous inverse branch](https://github.com/wcook04/plectis-erdos/blob/e98130bfe66aa33606e116791080b3ed13e1d68a/evidence/source-prerequisites/8bf96bdcae6b9201c670fff3037c49c70ec6de8d/lean/ErdosProblems/Erdos1041/OutwardSlitDomain.lean#L359), taking $`0`$ to that root. The archived Lean source states these prerequisites and supplies proof scripts; a kernel-check receipt for this module is not supplied here. The full conformal sheet decomposition, sheet count, monodromy and embedded-tree assertions remain ordinary arguments in the companion; the prerequisites give no length estimate.

<a id="sec:gap"></a>

## The failed tree estimate

<span id="sec:finite" label="sec:finite"></span> For $`z^2-(9/10)^2`$, the distance between the roots already forces any connected set containing them to have length at least $`9/5`$. Proposition 12 of the March manuscript \[march2026\] instead proposes a bound below $`41/25`$ plus an arbitrarily small error. Since $`41/25<9/5`$, choosing the error smaller than this gap contradicts the lower bound. The spanning-tree estimate is false. At a simple saddle the local level set has four sectors, consistently with the lemniscate graph description in \[bishop-eremenko-lazebnik, Definition 1.2 and Proposition 2.4\]. The [Cassini calculation and corrected topological statement](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=cassini-counterexample) separate the metric failure from the valid sheet decomposition.

The full topological reconstruction in that discussion remains unformalised. Cutting outward from critical values to obtain inverse-sheet adjacency is classical; see \[dubinin2006critical, §1\] and \[dubinin2006capacity, §2\]. Length control requires additional estimates on the actual pieces and their attachment. An uncut Newton orbit space can even fail to be Hausdorff, so it cannot be identified with a finite Reeb graph without further argument. Earlier grid searches in degrees $`5,6,8,10`$ found no counterexample, but neither certified containment along unexamined edges nor established a statement for all polynomials.

<a id="restricted-extremal-problems"></a>

## Restricted extremal problems

The companion records the following ordinary compactness argument, which has not been formalised. In the closed lemniscate $`K_1(f)`$, a finite infimum of connecting path lengths is attained. At fixed degree, compactness of the closed root-disc class and lower semicontinuity of this infimum allow uniform upper bounds to pass to coefficient limits. These are statements about the closed lemniscate, as proved in the companion’s [compactness argument](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=closed-class-limits). Closed containment survives such limits; strict containment need not. The binomial family approaches length $`2`$, but the degree-seven example rules out $`2`$ as a universal upper bound. That refuted assertion is not a remaining open problem. What remains is to determine quantitative bounds for restricted classes and as the degree varies.

The precise unresolved questions about cut-open flow strips, attachment lengths and quantitative perturbation are stated in the companion’s [final questions](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=remaining-questions). The origin-spoke failure for the near-regular-pentagon family has an ordinary, unformalised proof there. The stronger failure asserted in the research addendum \[revision2026\] for every critical joining point has no available proof and is not used. Likewise the fixed degree-seven proof does not establish the whole small-parameter family.

<a id="sec:1041-sources"></a>

# Related results and verification

Several nearby results concern different geometric quantities. Inverse branches, slit domains and capacity also occur in Crane’s work on Smale’s mean-value conjecture \[crane2007smale, Lemma 2.1 and §§2–4\], but its derivative normalisation differs from the monic normalisation used here. Eremenko and Hayman’s bound $`\mathcal H^1\{|p|=1\}<9.173\deg p`$ \[eremenko-hayman, Theorem 1\] concerns total boundary length, not an internal root-to-root path. Their connectedness result, the derivative estimate of Eremenko and Lempert \[eremenko-lempert, Theorem 1\], and its equality analysis \[eremenko-markov, Theorem A\] likewise concern different extremal quantities. Kuznetsova and Tkachev \[kuznetsova2003, Theorems 1–2\] study length functions on regular levels; log-convexity there does not give a uniform one-root perimeter bound at a critical endpoint.

The hypotheses and endpoints also matter. Dubinin’s four-point distortion theorem \[dubinin2013fourpoint, Theorem 1 and Corollary 4\] assumes a bound on all critical values, with a different normalisation. Pendyala’s Problem 1120 result \[pendyala2026shortest, Definition 1.1 and Theorem 1.2\] joins $`0`$ to the unit circle inside a lemniscate intersected with the closed disc. Neither the endpoints nor that region restriction are those of Problem 1041.

<a id="verification-and-reproducibility."></a>

#### Verification and reproducibility.

The supplied Lean sources prove the fixed counterexample for preconnected sets, the negation and `answer(False)` forms of the Formal Conjectures statement, and the total-variation formulation. They also prove the trinomial theorem and the other formally supported estimates identified in the companion’s [verification notes](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=verification-notes). No fresh Lean build or independent human review is reported here, including review of the correspondence with the 1958 wording. The recorded full rational replay on 29 September 2026 reproduced the stopping time and $`126`$ dual certificates; those are the computational results cited here. The analytic assertions in Remarks <a href="#res:low-critical-thirteen-twentyfifths" data-reference-type="ref" data-reference="res:low-critical-thirteen-twentyfifths">[res:low-critical-thirteen-twentyfifths]</a>–<a href="#res:critical-value-thresholds" data-reference-type="ref" data-reference="res:critical-value-thresholds">[res:critical-value-thresholds]</a>, the fourth-power mean and the later topological and compactness arguments remain outside the formal conclusions. The evidence record retains the statement identifiers and their conditional dependencies.

The verification concordance lists the formal proofs by statement. *Lean* links to the supporting declarations; a dagger identifies a proof that assumes a named input. *Comparator* links to a recorded kernel check against a separately written statement; *pending* means that this comparison has not been recorded. The [verification record](https://github.com/wcook04/plectis-erdos/blob/846d57d3f9926696332d782eb232aaf3cf803a99/evidence/erdos-1041-lemniscate-newton-flow.md) gives the precise correspondence, dependencies and reproducible checks. A row with only a record link has no complete formal proof recorded.

<div class="thebibliography">

99 T. F. Bloom, *Erdős Problems*, problem 1041. <https://www.erdosproblems.com/1041> P. Erdős, F. Herzog, and G. Piranian, *Metric properties of polynomials*, J. Analyse Math. **6** (1958), 125–148, doi:[10.1007/BF02790232](https://doi.org/10.1007/BF02790232). `shtuka`, *A Short Path Joining Two Zeros Inside a Polynomial Lemniscate*, manuscript posted 24 March 2026, 48 pp. <https://shtuka123.github.io/1041/main.pdf> V. S. Pendyala, *A Degree-Four Lemniscate Path Theorem*, arXiv:[2606.24875v1](https://arxiv.org/abs/2606.24875v1) (2026), doi:[10.48550/arXiv.2606.24875](https://doi.org/10.48550/arXiv.2606.24875). V. S. Pendyala, *Shortest paths in polynomial lemniscate sublevel sets and a problem of Erdős*, arXiv:[2606.19178v1](https://arxiv.org/abs/2606.19178v1) (2026), doi:[10.48550/arXiv.2606.19178](https://doi.org/10.48550/arXiv.2606.19178). D. Kozen and K. Stefánsson, *Computing the Newtonian graph*, J. Symbolic Comput. **24** (1997), no. 2, 125–136, doi:[10.1006/jsco.1997.0118](https://doi.org/10.1006/jsco.1997.0118); authors’ copy <https://www.cs.cornell.edu/kozen/Papers/newton.pdf>. E. Crane, *The areas of polynomial images and pre-images*, Bull. London Math. Soc. **36** (2004), no. 6, 786–792, doi:[10.1112/S0024609304003509](https://doi.org/10.1112/S0024609304003509); preprint arXiv:[math/0302189v1](https://arxiv.org/abs/math/0302189v1), whose statement numbers are cited. P. Ebenfelt, D. Khavinson, and H. S. Shapiro, *Two-dimensional shapes and lemniscates*, in *Complex Analysis and Dynamical Systems IV, Part 1*, Contemp. Math. **553**, Amer. Math. Soc., Providence, RI, 2011, 45–59, doi:[10.1090/conm/553/10931](https://doi.org/10.1090/conm/553/10931); preprint arXiv:[1003.4567v1](https://arxiv.org/abs/1003.4567v1), whose statement numbers are cited. A. Eremenko and W. Hayman, *On the length of lemniscates*, Michigan Math. J. **46** (1999), no. 2, 409–415, doi:[10.1307/mmj/1030132418](https://doi.org/10.1307/mmj/1030132418); preprint arXiv:[0805.2295](https://arxiv.org/abs/0805.2295). A. Eremenko and P. Yuditskii, *Comb functions*, Contemp. Math. **578** (2012), 99–118, doi:[10.1090/conm/578/11472](https://doi.org/10.1090/conm/578/11472); preprint arXiv:[1109.1464v1](https://arxiv.org/abs/1109.1464v1). A. Eremenko and L. Lempert, *An extremal problem for polynomials*, Proc. Amer. Math. Soc. **122** (1994), no. 1, 191–193, doi:[10.1090/S0002-9939-1994-1207536-1](https://doi.org/10.1090/S0002-9939-1994-1207536-1). A. Eremenko, *A Markov-type inequality for arbitrary plane continua*, Proc. Amer. Math. Soc. **135** (2007), no. 5, 1505–1510, doi:[10.1090/S0002-9939-06-08640-0](https://doi.org/10.1090/S0002-9939-06-08640-0); preprint arXiv:[math/0606745v1](https://arxiv.org/abs/math/0606745v1). C. J. Bishop, A. Eremenko, and K. Lazebnik, *On the shapes of rational lemniscates*, Geom. Funct. Anal. **35** (2025), no. 2, 359–407, doi:[10.1007/s00039-025-00704-2](https://doi.org/10.1007/s00039-025-00704-2); preprint arXiv:[2407.14610v1](https://arxiv.org/abs/2407.14610v1). V. N. Dubinin, *Some inequalities for polynomials and rational functions associated with lemniscates*, Zap. Nauchn. Sem. POMI **404** (2012), 83–99; English translation, J. Math. Sci. **193** (2013), no. 1, 45–54, doi:[10.1007/s10958-013-1432-4](https://doi.org/10.1007/s10958-013-1432-4). G. Pólya, *Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zusammenhängende Gebiete*, Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-Mathematische Klasse (1928), printed pp. 228–232 and 280–282. <https://archive.org/details/sitzungsbericht1928preu>. V. N. Dubinin, *Inequalities for critical values of polynomials*, Sb. Math. **197** (2006), no. 8, 1167–1176, doi:[10.1070/SM2006v197n08ABEH003793](https://doi.org/10.1070/SM2006v197n08ABEH003793). E. Crane, *A bound for Smale’s mean value conjecture for complex polynomials*, Bull. London Math. Soc. **39** (2007), no. 5, 781–791, doi:[10.1112/blms/bdm063](https://doi.org/10.1112/blms/bdm063); author preprint <https://people.maths.bris.ac.uk/~maetc/SMVCbound.pdf>. V. N. Dubinin, *Four-point distortion theorem for complex polynomials*, arXiv:[1301.3985v1](https://arxiv.org/abs/1301.3985v1) (2013). O. S. Kuznetsova and V. G. Tkachev, *Length functions of lemniscates*, Manuscripta Math. **112** (2003), 519–538, doi:[10.1007/s00229-003-0411-3](https://doi.org/10.1007/s00229-003-0411-3); preprint arXiv:[math/0306327](https://arxiv.org/abs/math/0306327). D. Tischler, *Critical points and values of complex polynomials*, J. Complexity **5** (1989), no. 4, 438–456. W. Cook / Plectis, *Three refinements for the lemniscate-path programme*, 16 September 2026, unreviewed research note, Sections 1–3, together with the earlier note *Structural obstructions*. V. N. Dubinin, *Lemniscates and inequalities for the logarithmic capacities of continua*, Mat. Zametki **80** (2006), no. 1, 33–37; English translation, Math. Notes **80** (2006), no. 1, 31–35, doi:[10.1007/s11006-006-0105-8](https://doi.org/10.1007/s11006-006-0105-8). T. Ransford, *Potential Theory in the Complex Plane*, London Mathematical Society Student Texts 28, Cambridge University Press, Cambridge, 1995, doi:[10.1017/CBO9780511623776](https://doi.org/10.1017/CBO9780511623776).

</div>
