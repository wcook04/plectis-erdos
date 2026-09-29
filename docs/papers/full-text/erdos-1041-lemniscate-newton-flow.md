<a id="erdos-1041-lemniscate-newton-flow"></a>

# Paths in Polynomial Lemniscates: A Degree-Seven Counterexample and Two Short-Path Criteria

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

An explicit monic polynomial of degree seven, constructed by `ani`, has its zeros in the open unit disc, yet every connected subset of its strict unit lemniscate containing two zeros has one-dimensional Hausdorff measure greater than $`2`$. We explain the two-sheeted bottleneck responsible for this counterexample. Short connections do exist for monic trinomials with zeros in the disc, and for arbitrary squarefree monic polynomials whose least critical-value modulus is at most $`13/25`$. The latter result follows from an area-growth inequality and a rational packing calculation. We also give an isolated-critical-value criterion and discuss the limitations of these constructions.

<a id="sec:problem"></a>

# Introduction

For a monic polynomial $`f`$, write
``` math
\Omega_f=\{z:|f(z)|<1\},\qquad K_t(f)=\{z:|f(z)|\le t\}.
```
Erdős, Herzog and Piranian \[ehp1958, Problem 5, p. 139\] asked whether two zeros in the open unit disc could always be connected by a short curve in $`\Omega_f`$. Their question is listed as Problem 1041 in Bloom’s catalogue \[bloom\].

<div id="res:problem" class="problem">

**Problem 1** (Erdős \#1041). Let $`f(z)=\prod_{i=1}^{n}(z-z_i)`$ be monic with $`n\ge2`$ and all $`z_i`$ in the open unit disc. Must two root occurrences be joined by a curve of length less than $`2`$ inside $`\{|f|<1\}`$?

</div>

If a root is repeated, a constant curve joins two occurrences, so the question reduces to polynomials with distinct zeros. Pendyala \[june2026, Theorem 1 and Lemma 1\] proved the degree-four case using a close-pair chord or radial segments through the centre of a smallest enclosing disc. In degree seven the answer is negative. The example was constructed by the erdosproblems.com contributor [`ani`](https://www.erdosproblems.com/forum/thread/1041#post-8861).

<div id="counterexample-statement">

</div>

<div id="res:ani-degree-seven-counterexample" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1041-lemniscate-newton-flow.md#res-ani-degree-seven-counterexample">Lean</a></p>

**Theorem 2** (`ani`’s degree-seven example). *The monic polynomial $`f`$ in <a href="#eq:ani-f" data-reference-type="eqref" data-reference="eq:ani-f">[eq:ani-f]</a> has seven distinct zeros in the open unit disc. Every connected set $`K\subset\Omega_f`$ containing two of its zeros satisfies $`\mathcal H^1(K)>2`$.*

</div>

Here $`\mathcal H^1`$ denotes one-dimensional Hausdorff measure. In particular, the theorem applies to the image of any continuous path joining two zeros. For a rectifiable path this measure is bounded above by its total variation, so that interpretation of length is excluded as well. Section <a href="#sec:counterexample" data-reference-type="ref" data-reference="sec:counterexample">2</a> gives the polynomial and the geometric proof. Its component with two zeros is a double cover of the value disc; the cut separating its two inverse sheets lies in a disc much smaller than the excess of the two root distances over $`2`$.

The positive results use additional information about the polynomial. For $`f(z)=z^n+az^m+b`$, $`1\le m<n`$, the root equation bounds $`f`$ on *every* root-to-origin segment (Section <a href="#sec:trinomial" data-reference-type="ref" data-reference="sec:trinomial">3</a>). A second result dispenses with both coefficient and root-location restrictions: if
``` math
\mu=\min_{f'(c)=0}|f(c)|\le\frac{13}{25},
```
then some pair of distinct roots of a squarefree monic polynomial has a connection of length less than $`2`$ in $`\Omega_f`$ (Section <a href="#sec:constant-factor" data-reference-type="ref" data-reference="sec:constant-factor">4</a>). Neither hypothesis holds for the counterexample. An isolated simple critical value gives another criterion in Section <a href="#sec:separation" data-reference-type="ref" data-reference="sec:separation">5</a>.

The analytic arguments use polynomial covering maps and area estimates. The component-wise Riemann–Hurwitz calculation appears in Ebenfelt, Khavinson and Shapiro \[eks2010, proof of Proposition 2.1\]; we use Pólya’s area inequality in the forms recorded by Crane \[crane, Theorems 1 and 6\]. Inverse branches, slit domains and capacity also occur in Crane’s work on Smale’s mean-value conjecture \[crane2007smale, Lemma 2.1 and §§2–4\], whose derivative normalisation differs from the monic normalisation here. The [companion paper](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf) contains the complete finite estimates and proofs of the further results described in Sections <a href="#sec:other-results" data-reference-type="ref" data-reference="sec:other-results">6</a>–<a href="#sec:open" data-reference-type="ref" data-reference="sec:open">7</a>.

<a id="sec:counterexample"></a>

# A component with a narrow bottleneck

<a id="the-polynomial"></a>

## The polynomial

Put $`s=10^{-6}`$, $`\varepsilon=s^2=10^{-12}`$ and $`\rho=1-s^{16}`$, and let
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
Since $`F(z)=-z^7\overline{F(1/\bar z)}`$, we can locate its roots by applying the Cayley substitution $`z=(1+ix)/(1-ix)`$ and checking the signs of a real polynomial at fourteen rational endpoints. The seven resulting intervals account for all zeros $`\zeta_j`$ of $`F`$, which are therefore distinct and have modulus one. Thus $`b_j=\rho\zeta_j`$ lies strictly inside the disc, as required.

The critical points are most conveniently calculated at scale $`z=\rho\varepsilon w`$. Write
``` math
F(\varepsilon w)=-1+\varepsilon^7Q(w),\qquad
 Q(w)=c_0w+bw^2+aw^3-\varepsilon\bar a w^4
                  -\varepsilon^3\bar b w^5-\varepsilon^5\bar c_0w^6+w^7.
```
Rouché estimates on six disjoint rational discs locate the six zeros of $`Q'`$. Exactly one, $`w_s`$, corresponds to a critical value of modulus less than one. It satisfies
``` math
|w_s-(0.0000000039+0.8232474662i)|<10^{-6}.
```
Let $`c_s=\rho\varepsilon w_s`$, $`v=f(c_s)`$, $`\delta=1-|v|`$, and write $`f(c_s+z)-v=z^2A_s(z)`$. The finite estimates needed below are
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
The subscripts $`3,6`$ refer to Cayley roots in the intervals $`(43812,43813)/10^4`$ and $`(-4816,-4815)/10^4`$.

To identify the two-root component, we join a small disc about $`w_s`$ to points close to $`8\zeta_3`$ and $`8\zeta_6`$ by polygonal arcs in the $`w`$-plane. Containment of the four inner segments follows by writing
``` math
7\varepsilon+\operatorname{Re}Q(w)
                       -\tfrac12\varepsilon^7|Q(w)|^2
```
in the Bernstein basis of degree fourteen and checking that all fifteen coefficients are positive on each segment. For the remaining radial portions we use the root identity
``` math
F(t\zeta)=t^7-1+
       \sum_{k=1}^6\varepsilon^{7-k}q_k\zeta^k(t^k-t^7),
 \qquad Q(w)=\sum_{k=1}^7q_kw^k,
```
which gives $`|F(t\zeta)|<1`$ for $`8\varepsilon\le t\le1`$. All rational intervals, vertices and coefficient tests are specified in [the companion’s finite verification](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=counterexample-certificate). Riemann–Hurwitz now shows that this component contains exactly two roots and every other component contains one.

<a id="the-inverse-sheets-and-length"></a>

## The inverse sheets and length

The following argument explains why the local estimates control every connection between the two roots.

<div id="lem:two-sheet-bottleneck" class="lemma">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L187">Lean</a></p>

**Lemma 3**. *Let $`p`$ be a polynomial and $`U`$ a component of $`\{|p|<1\}`$ on which $`p`$ has degree two, with one simple critical point $`c`$ and $`v=p(c)\ne0`$. Write $`p(c+z)-v=z^2A(z)`$ and put $`M=|A(0)|`$, $`\delta=1-|v|`$. If $`|A(z)/A(0)-1|\le1/4`$ for $`|z|\le h`$ and $`\delta<Mh^2/4`$, then every connected subset $`K`$ of $`U`$ containing its two roots $`a,b`$ satisfies
``` math
\mathcal H^1(K)\ge |a-c|+|b-c|-\frac83\sqrt{\delta/M}.
```*

</div>

<div class="proof">

*Proof.* We cut the value disc along $`J=\{tv:1\le t<1/|v|\}`$. Since the complement is simply connected and contains no critical value, its preimage in $`U`$ consists of two disjoint inverse sheets $`U_1,U_2`$, one containing each root. Set $`r_0=(4/3)\sqrt{\delta/M}<2h/3`$. For $`|z|=r_0`$,
``` math
|p(c+z)-v|\ge\tfrac34Mr_0^2=\tfrac43\delta.
```
Thus Rouché’s theorem gives two preimages of each point of $`J`$ in $`B(c,r_0)`$. As the value moves outwards from $`v`$, these preimages continue from $`c`$ and remain in $`U`$; they exhaust the fibre because its degree is two. We have therefore confined the whole cut $`p^{-1}(J)\cap U`$ to the small disc, including every possible crossing between the two sheets.

Suppose that $`r_0<t<|a-c|`$ and $`K\cap U_1`$ misses the circle $`|z-c|=t`$. Then $`K\cap U_1\cap\{|z-c|>t\}`$ is both open and closed in $`K`$, contains $`a`$ and excludes $`b`$, contradicting connectedness. Consequently the $`1`$-Lipschitz map $`z\mapsto|z-c|`$ consequently gives $`\mathcal H^1(K\cap U_1)\ge(|a-c|-r_0)_+`$. Adding the corresponding bound on the other sheet proves the result. The additivity used here is valid for Hausdorff outer measure across disjoint open sets, so no measurability assumption on $`K`$ is required. ◻

</div>

<div class="proof">

*Proof of Theorem <a href="#res:ani-degree-seven-counterexample" data-reference-type="ref" data-reference="res:ani-degree-seven-counterexample">2</a>.* The finite estimates give $`\sqrt{\delta/M}<\rho\varepsilon/5000`$ and $`\delta<M(\rho\varepsilon/10)^2/4`$. Thus every connected set in the component containing $`b_3,b_6`$ has measure greater than
``` math
\rho\left(2+\left(\frac{143}{1000}-\frac8{15000}\right)
                        \varepsilon\right)>2.
```
All other components contain one root. A connected set containing two roots must therefore lie in the component just considered. ◻

</div>

We use the fixed value $`s=10^{-6}`$ throughout. Extending the proof to the small-parameter family reported by `ani` requires further estimates and remains unproved here. The use of Hausdorff measure is also essential: a lower bound for the total variation of a particular parametrisation would leave open the measure of its image.

<a id="sec:trinomial"></a>

# Trinomials and radial segments

We next give a positive result in which the root equation controls a prescribed path. For a trinomial, every partial sum at a root is one of two quantities, both of modulus less than one.

<div id="res:trinomial-all-degree" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperTrinomialWholeR21.lean#L23">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1041-lemniscate-newton-flow.md#res-trinomial-all-degree-comparator">Comparator</a></p>

**Theorem 4** (all-degree monic trinomials). *Let $`1\le m<n`$ and
``` math
f(z)=z^n+az^m+b,
```
with every zero in the open unit disc. For any zero $`\zeta`$, the entire segment $`[0,\zeta]`$ lies in $`\{|f|<1\}`$. Distinct zeros $`\zeta_1,\zeta_2`$ are therefore joined by the broken line $`\zeta_1\to0\to\zeta_2`$ of length $`\|\zeta_1\|+\|\zeta_2\|<2`$ inside the open unit lemniscate.*

</div>

<div class="proof">

*Proof.* If $`f(\zeta)=0`$, then
``` math
f(t\zeta)=b(1-t^m)+\zeta^n(t^n-t^m).
```
Vieta’s formula gives $`|b|<1`$. For $`0\le t<1`$, both $`1-t^m`$ and $`t^m-t^n`$ are nonnegative, and hence
``` math
|f(t\zeta)|\le |b|(1-t^m)+|\zeta|^n(t^m-t^n)<1-t^n\le1.
```
At $`t=1`$ the value is zero. Concatenate two such segments. ◻

</div>

To see why the number of terms matters, write $`f(z)=\sum_{k=0}^n a_kz^k`$, take a zero $`\zeta`$, and put $`S_j=\sum_{k=0}^j a_k\zeta^k`$. Abel summation gives
``` math
f(t\zeta)=\sum_{j=0}^{n-1}(t^j-t^{j+1})S_j.
```
For $`t<1`$, division by $`1-t^n`$ expresses the value as a convex combination of the $`S_j`$. In the trinomial case these are $`b`$ and $`-\zeta^n`$. Additional coefficients introduce further partial sums, whose moduli need not be controlled by the root locations.

<div id="res:sextic-spoke" class="proposition">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/SexticSpokeWhole.lean#L9">Lean</a> · <a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1041-lemniscate-newton-flow.md#res-sextic-spoke-comparator">Comparator</a></p>

**Proposition 5** (failure of a prescribed radial segment). *There exist $`r\in(0,1)`$ for which every zero of
``` math
f_r(z)=z^6+\tfrac15 r^2 z^4-\tfrac15 r^4 z^2-r^6
```
lies in the open unit disc, yet the radial spoke from the origin to the zero $`r`$ leaves $`\{|f_r|<1\}`$.*

</div>

<div class="proof">

*Proof.* After $`z=rw`$, the polynomial factors as $`r^6(w^2-1)(w^4+\tfrac65w^2+1)`$, whose six zeros have modulus $`r`$. But $`f_r(r/2)=-(327/320)r^6`$. Choose $`320/327<r^6<1`$. ◻

</div>

The failed spoke leaves open other connections for this polynomial. In Section <a href="#sec:solved-families" data-reference-type="ref" data-reference="sec:solved-families">6.2</a> we describe two further applications of the partial-sum identity, to power substitutions in a cubic and to a quintic with two missing coefficients.

<a id="sec:constant-factor"></a>

# A small least critical value

<div id="low-critical-short">

</div>

For a squarefree polynomial the first merger of two root components occurs at level $`\mu=\min_{f'(c)=0}|f(c)|>0`$. We show that a sufficiently long interval of levels above $`\mu`$ forces a short connection, independently of the degree.

<div id="res:low-critical-thirteen-twentyfifths" class="theorem">

**Theorem 6** (a small critical value). *Let $`f`$ be squarefree and monic of degree $`n\ge2`$, and let $`\mu`$ be its least critical-value modulus. If $`\mu\le13/25`$, then two distinct roots are joined inside $`\{|f|<1\}`$ by a rectifiable curve of length strictly less than $`2`$.*

</div>

<div id="res:scaled-low-critical" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1041-lemniscate-newton-flow.md#res-scaled-low-critical">Lean†</a></p>

**Corollary 7** (scale-free connection). *Every squarefree monic polynomial of degree $`n\ge2`$ has two distinct roots joined in $`\{|f|<(25/13)\mu\}`$ by a curve of length less than
``` math
2\bigl((25/13)\mu\bigr)^{1/n}.
```
In every degree the length can be chosen less than $`(5/2)\mu^{1/n}`$.*

</div>

The Lean proof assumes Theorem <a href="#res:low-critical-thirteen-twentyfifths" data-reference-type="ref" data-reference="res:low-critical-thirteen-twentyfifths">6</a>.

<div class="proof">

*Proof of the corollary.* For $`n\ge3`$, apply the theorem to $`g(z)=s^{-n}f(sz)`$ with $`s=((25/13)\mu)^{1/n}`$. Its least critical-value modulus is $`13/25`$. Rescaling gives the first bound, and $`2(25/13)^{1/n}<5/2`$ for $`n\ge3`$. For $`n=2`$, write $`f(z)=(z-h)^2-d^2`$; the root segment has length $`2|d|=2\sqrt\mu`$ and lies in $`K_\mu(f)`$, which is inside the required open level. ◻

</div>

<a id="separation-in-the-conformal-disc"></a>

## Separation in the conformal disc

Suppose, towards a contradiction, that no pair has a path of length less than $`2`$ in $`\Omega_f`$. At a regular level $`t\in(\mu,1)`$, let $`C_t`$ be the component containing a chosen first merger, let $`k`$ be its number of roots, and put
``` math
x=\log(t/\mu),\qquad a=\operatorname{Area}(C_t)/\pi\le1,
 \qquad \lambda(d)=-\log\tanh(d/2).
```
The last area bound is Pólya’s inequality. Uniformise $`C_t`$ by the unit disc. If its zeros have hyperbolic distance $`d`$, the Bergman segment estimate, after a disc automorphism, gives a connecting curve of length at most
``` math
\sqrt{2a\log\cosh(d/2)}.
```
The failure assumption thus separates every two roots by at least $`D`$, where $`\cosh(D/2)=e^{2/a}`$.

There is a point $`h\in C_t`$ at intrinsic distance at least $`1`$ from every root. Otherwise the open intrinsic unit balls centred at the roots would be disjoint and cover the connected set $`C_t`$. The intersection of two such balls would already give a connection shorter than $`2`$. Normalise the Riemann map so that $`h`$ corresponds to $`0`$, and write $`d_j`$ for the hyperbolic distance of the $`j`$th root from $`0`$. The one-root Bergman estimate gives
``` math
\lambda(d_j)\le\frac{\delta(a)}2,\qquad
 \delta(a)=-\log(1-e^{-1/a}).
```
In this normalisation $`f/t`$ is a finite Blaschke product. The point $`h`$ can be chosen on a connected set joining the first pair inside $`K_\mu(f)`$; the same disjoint-ball argument applies there. Evaluating the product at $`0`$ therefore gives
``` math
\sum_j\lambda(d_j)\ge x.
```
The existence of that connected set follows by approaching the first critical level from below. These steps, including multiple simultaneous first mergers, are proved in [the companion’s small-critical-value proof](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=low-critical-proof).

<a id="packing-and-area-growth"></a>

## Packing and area growth

<div id="circle-packing-inputs">

</div>

Open hyperbolic balls of radius $`D/2`$ about the roots are disjoint. Intersect them with a circle of radius $`r`$ about $`0`$. If $`w(d,r)`$ is the angular half-width of such an intersection, then
``` math
w(d,r)=\arccos\!\left(\operatorname{clamp}_{[-1,1]}
 \frac{\cosh d\cosh r-\cosh(D/2)}{\sinh d\sinh r}\right),
 \qquad \sum_jw(d_j,r)\le\pi.
```
Choose nonnegative weights $`\sigma_i`$ and radii $`r_i`$, and establish the uniform bound
``` math
\lambda(d)\le U+\sum_i\sigma_iw(d,r_i)
 \quad\text{whenever }\lambda(d)\le\delta(a)/2,
 \qquad U>0.
```
Summing at the roots gives
``` math
\begin{equation}
\label{eq:short-packing}
 k\ge\frac{x-\pi\sum_i\sigma_i}{U}.
\end{equation}
```
Slicing at a fixed radius retains the disjointness of the balls. Their projections onto the circle of directions may overlap, so those projections cannot be substituted in this argument.

To turn the root count into an area estimate, lift one common value radius from each root to $`\partial C_t`$. The mean total length of the lifts is at most $`\sqrt{ka(x+2)/2}`$. This follows by splitting at level $`\mu`$: the low lifts are bounded by their conformal areas, and coarea bounds the high lifts. Join successive boundary endpoints by the intervening boundary arcs. In the sum over all $`k`$ adjacent-root connections each lift occurs twice and the boundary once. Since each connection has length at least $`2`$,
``` math
2k\le\sqrt{2ka(x+2)}+\mathcal H^1(\partial C_t).
```
The argument principle and Cauchy–Schwarz on a regular level give $`\mathcal H^1(\partial C_t)^2\le2\pi k\,t\,
 (d/dt)\operatorname{Area}(C_t)`$. Hence
``` math
\begin{equation}
\label{eq:short-area-growth}
 a'(x)\ge\frac1{2\pi^2}
       \bigl[2\sqrt k-\sqrt{2a(x)(x+2)}\bigr]_+^2.
\end{equation}
```
Merger levels cause only nonnegative jumps in $`a`$.

<a id="the-rational-comparison"></a>

## The rational comparison

<div id="certificate-stopping-time">

</div>

The comparison uses <a href="#eq:short-packing" data-reference-type="eqref" data-reference="eq:short-packing">[eq:short-packing]</a>, the individual bound $`k\ge2x/\delta(a)`$, and two elementary root-count bounds from ordered distances and hyperbolic area. Their derivations and the exact comparison algorithm are in the companion. The bound $`k\ge2`$ first gives $`a(3/10^5)>10^{-6}`$, without assuming a positive area at the first merger. Starting there, the rational calculation forces $`a>1`$ by
``` math
X=\frac{635762889599}{10^{12}}.
```
It uses $`18`$ area levels, $`126`$ certified weighted inequalities and a maximum step $`1/400`$. To certify $`U`$ between sampling points, it uses that $`\lambda`$ decreases and that $`w(d,r)`$ has no strict interior minimum as a function of $`d`$. On $`[u,v]`$ the required expression is at most $`\lambda(u)-\sum_i\sigma_i\min(w(u,r_i),w(v,r_i))`$. The tail beyond all ball intersections is bounded directly by $`\lambda`$. Thus the numerical optimisation only proposes weights; rational inequalities verify each accepted bound on the whole half-line.

Since $`(13/25)e^X<0.982000386<1`$, the contradiction occurs before level one, proving the theorem. The same stopping time gives $`(529/1000)e^X<0.998996547`$, so $`529/1000`$ is also sufficient. We keep $`13/25`$ in the statement for its simpler form and make no optimality claim.

<span id="res:constant-factor-path" label="res:constant-factor-path"></span> Averaging inverse rays and a boundary arc also gives a weaker absolute bound: for every monic polynomial of degree $`n\ge2`$, two zero occurrences can be joined inside $`K_{2\mu}(f)`$ by a path of length at most $`(71/10)\mu^{1/n}`$. They are distinct when the polynomial is squarefree; a repeated root gives a constant path. When $`\mu\le1/2`$, a path of length at most $`5.7`$ can be chosen in $`\Omega_f`$. The companion’s [inverse-ray averaging proof](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=constant-factor-proof) gives the component-arity and capacity versions of this estimate.

<a id="sec:separation"></a>

# An isolated simple critical value

A large disc containing no other critical value lets two inverse branches be continued together. The resulting estimate uses the size of one component, and can apply when the least critical-value criterion does not.

<div id="res:critical-value-separation" class="theorem">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1041-lemniscate-newton-flow.md#res-critical-value-separation">Lean†</a></p>

**Theorem 8** (separation of one simple critical value). *Let $`f`$ be monic of degree $`n\ge3`$, let $`c`$ be a simple critical point, and put $`v=f(c)\ne0`$. Fix $`w_0\in[0,1]`$ and $`S>\max(w_0,1-w_0)`$. Suppose every other critical point $`d`$ satisfies
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
```*

</div>

The Lean proof assumes the analytic construction in the proof below: the connector obtained through the square-root map, its Bergman length bound, and the capacity bound for the area of the two-sheeted component.

For example, $`f(z)=z^3-3a^2z`$ with $`0<a<1/\sqrt3`$ has zeros $`0,\pm\sqrt3a`$. At $`c=a`$, the critical value is $`v=-2a^3`$ and the other normalised critical value is $`-1`$. The disc centred at $`w_0=1`$ with radius $`4/3`$ therefore satisfies the hypothesis.

<div id="res:critical-value-thresholds" class="corollary">
<p class="evidence-marks"><a href="https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1041-lemniscate-newton-flow.md#res-critical-value-thresholds">Lean†</a></p>

**Corollary 9** (uniform radius $`4/3`$). *Let $`f`$ be monic of degree $`n\ge3`$ with all roots in the open unit disc. If $`c`$ is a simple critical point with $`0<|f(c)|<1`$ and, for some $`w_0\in[0,1]`$, every other critical point $`d`$ satisfies
``` math
\left|\frac{f(d)}{f(c)}-w_0\right|\ge\frac43,
```
then two roots are joined inside $`\{|f|<1\}`$ by a curve of length strictly below $`2`$. In degree three the branch-centred choice $`w_0=1`$ already works with $`4/3`$ replaced by $`6/5`$.*

</div>

The Lean proof assumes the same construction as Theorem <a href="#res:critical-value-separation" data-reference-type="ref" data-reference="res:critical-value-separation">8</a>. The numerical inequalities, including the cubic constant $`6/5`$, are checked without it.

<div class="proof">

*Proof of the theorem.* We choose $`\alpha^n=v`$ and put $`P(z)=v^{-1}f(c+\alpha z)`$, so $`P`$ is monic, $`P(0)=1`$ and $`0`$ is a simple critical point. Let $`U`$ be the component above $`D(w_0,S)`$ containing $`0`$. Exhaustion by smaller regular discs and Riemann–Hurwitz show that $`P:U\to D(w_0,S)`$ has degree two. The analytic square root $`\xi=\sqrt{1-P}`$ maps $`U`$ biholomorphically onto
``` math
V=\{\xi:|\xi^2-(1-w_0)|<S\}.
```
Indeed $`1-P`$ has one double zero, and this square root has degree one. Its inverse $`Z`$ maps $`[-1,1]`$ to a root-to-root curve in $`\{|P|\le1\}`$.

Write $`a=1-w_0`$ and $`p=w_0(1-w_0)`$. The conformal coordinate
``` math
\zeta=\xi\sqrt{\frac{S}{S^2+a\xi^2-a^2}}
```
sends $`V`$ to the unit disc and $`\xi=\pm1`$ to $`\zeta=\pm q`$, where $`q^2=S/(S^2+p)`$. The Bergman segment estimate therefore gives
``` math
L^2\le\frac{2}{\pi}
       \log\frac{S^2+S+p}{S^2-S+p}\,\operatorname{Area}(U).
```
For a monic polynomial of degree $`n`$, a component $`W`$ at a regular level $`t`$ containing $`k<n`$ roots satisfies
``` math
\frac{\operatorname{cap}(\overline W)^n}{t}<\frac{k}{2n-k}.
```
To see this, use the exterior conformal map and reflect the factors of the $`n-k`$ roots outside $`W`$ into the disc. They form a Blaschke product $`B`$ with $`|B(0)|=\operatorname{cap}(\overline W)^n/t`$. Positivity of the boundary argument derivative gives $`|B'|<n`$. Summing reciprocal $`|B'|`$ over a fibre opposite $`B(0)`$ gives
``` math
\frac{n-k}{n}<\frac{1-|B(0)|}{1+|B(0)|},
```
which is the claimed inequality. The exterior factorisation and fibre identity are proved in [the companion’s separation proof](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=critical-value-separation-proof).

Apply this with $`k=2`$, then use Pólya’s area–capacity inequality \[polya1928, printed pp. 280–282\], \[crane, Theorem 6\] and exhaustion to obtain $`\operatorname{Area}(U)\le\pi(S/(n-1))^{2/n}`$. Restoring the factor $`|v|^{1/n}`$ proves <a href="#eq:disk-family-length" data-reference-type="eqref" data-reference="eq:disk-family-length">[eq:disk-family-length]</a>. Dubinin’s relative area inequality \[dubinin, Theorem 1\] has a different full-covering hypothesis; the absolute area estimate above is what is needed here. ◻

</div>

<span id="res:separation-parent" label="res:separation-parent"></span> To prove the corollary, we decrease $`S`$ to $`4/3`$. Since $`p\ge0`$ and $`n\ge3`$, the logarithm is at most $`\log7<2`$ and $`(S/(n-1))^{2/n}\le1`$. Thus $`L<2|v|^{1/n}<2`$. At $`n=3,w_0=1,S=6/5`$ the corresponding test is $`(3/5)^{2/3}\log11<2`$. Notice that the selected critical value must be nonzero and have modulus less than one. Root positions alone do not isolate it from the other critical values. <span id="bdry:critical-value-separation" label="bdry:critical-value-separation"></span>

<a id="sec:other-results"></a>

# Further estimates

<div id="supplementary-results">

</div>

<a id="sec:critical-proximity"></a>

## Root distances and component geometry

<span id="sec:exact-obstructions" label="sec:exact-obstructions"></span> <span id="res:critical-proximity" label="res:critical-proximity"></span> The critical-point equation $`\sum_j(c-z_j)^{-1}=0`$ restricts the ratio of the two smallest distances to $`[1,n-1]`$. If $`r^n=\prod_j|c-z_j|`$, it follows that those two distances have sum at most $`2r`$.

<span id="res:two-nearest-roots" label="res:two-nearest-roots"></span> The root-disc hypothesis gives a different estimate: at every non-root critical point the sum of the two nearest-root distances is strictly less than $`2`$. Both arguments and their precise statements are in the companion’s [root-distance estimates](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=root-distance-proofs).

<span id="res:straight-no-go" label="res:straight-no-go"></span> These distance estimates alone do not imply containment. For the quintic
``` math
(z-a)(z^2+p^2)\left(z^2+\frac{902}{901}pz+p^2\right),
 \qquad p=\frac{999}{1000},\quad a=\frac{901}{902}p,
```
all roots lie in the disc and $`0`$ is a non-root critical point, but its unique nearest-root segment leaves the unit lemniscate. Moreover, every root-pair midpoint of $`z^3-(99/100)^3`$ lies outside it. The [exact counterexamples](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=straight-path-counterexamples) include the escape calculations.

<span id="res:sep-or-false" label="res:sep-or-false"></span> The cubic $`z^3+3z/100-3/4`$ illustrates the restrictions in our sufficient conditions: its least critical-value modulus exceeds $`13/25`$, while its two normalised critical values are too close for the isolation criterion.

<span id="res:arity-not-capacity" label="res:arity-not-capacity"></span> A further cubic has two roots at its first merger but normalised component capacity one at level $`2\mu`$. The normalisation uses the standard identity $`\operatorname{cap}(K_t(f))=t^{1/n}`$ \[ransford1995, Theorem 5.2.5 and p. 153\].

<span id="res:one-root-gamma-false" label="res:one-root-gamma-false"></span> Finally, $`z^8-(3/2)z`$ has a one-root unit-level component with perimeter larger than the proposed constant $`\Gamma(1/4)^2/(2\sqrt\pi)`$. These examples, with full calculations, appear in [the companion’s component examples](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=component-counterexamples). The last example has no root-disc restriction and disproves that specific perimeter constant. The existence of a uniform perimeter constant remains a separate question. Although \[revision2026, Proposition 2\] reports a Runge construction of unbounded one-root perimeters, its proof is unavailable and we do not use it.

<a id="sec:solved-families"></a>

## Sparse families and binomial chords

<span id="sec:binomial" label="sec:binomial"></span> <span id="res:cubic-fibres" label="res:cubic-fibres"></span> Suppose that all zeros lie in the open unit disc. The radial argument extends to $`P((z-h)^q)`$ when $`q\ge2`$ and $`P`$ is a monic cubic: if there are two distinct zeros, some such pair has a two-segment connector.

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

<span id="res:fp-weighted-all-degree" label="res:fp-weighted-all-degree"></span> A weighted Poisson identity gives another consequence of the root-disc hypothesis. For $`c_j\in\overline{\mathbb D}`$ and positive weights of sum one, set $`G(z)=\prod_j|1-\bar c_jz|^{w_j}`$. Then $`\sum_jw_jG(c_j)^2\le1`$, with equality only when all $`c_j=0`$. For interior points, take the analytic product $`g(z)=1+\sum_{\nu\ge1}a_\nu z^\nu`$ with $`|g|=G`$. The weighted Poisson kernel is $`P=1-2\operatorname{Re}(\zeta g'/g)`$, and
``` math
\sum_jw_jG(c_j)^2\le\int |g|^2P\,dm
          =1-\sum_{\nu\ge1}(2\nu-1)|a_\nu|^2.
```
Radial contraction gives the boundary case.

<span id="res:fp-to-s" label="res:fp-to-s"></span> The reflected derivative transfers the quadratic inequality to $`\sum_{j=1}^{n-1}|f(c_j)|^{2/(n-1)}\le(n-1)R^{2n/(n-1)}`$ when the zeros lie in a closed disc of radius $`R`$. An ordinary refinement uses $`g^2`$ in the same Poisson integral and yields the fourth-power inequality
``` math
\sum_{j=1}^{n-1}|f(c_j)|^{4/(n-1)}
       \le(n-1)R^{4n/(n-1)}
```
for the same enclosing disc. Equality is attained by $`(z-h)^n-\lambda`$ with $`|\lambda|=R^n`$. The companion supplies the [weighted identity, reflected-derivative comparison and equality analysis](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=weighted-poisson-proof).

The quadratic specialisation implies Dubinin’s sharp critical-value product bound by AM–GM \[dubinin2006critical, Theorem 2\]. With a zero prescribed at the disc centre, his Theorem 3 gives a different, sharper product estimate and credits earlier work of Tischler \[tischler1989, p. 444, as discussed by Dubinin\]. The corresponding marked-zero positive-moment question in \[revision2026\] remains unresolved here. To turn any of these mean bounds into a short-path theorem, one would still have to select a pair of roots and control a curve joining them inside the lemniscate.

<a id="sec:orlicz"></a>

## Successive merger scales

<span id="res:orlicz-currency" label="res:orlicz-currency"></span> For a component with $`k`$ roots and a ratio $`r`$ of successive merger levels, an integral arising in length estimates is
``` math
I_k(r)=\int_r^1
 \frac{dq}{q\log((1+q^{2/k})/(1-q^{2/k}))}
       =k\Phi\left(\frac1k\log\frac1r\right),
 \qquad \Phi(x)=\int_0^x\frac{dt}{\log\coth t}.
```
The substitution $`q=e^{-kt}`$ proves the identity. Since the integrand increases from zero, $`\Phi`$ is strictly convex and $`\Phi(x)/x\to0`$ at zero. Even for fixed $`k`$, no positive multiple of $`k^{-1}\log(1/r)`$ is a uniform lower bound for $`I_k(r)`$. The precise endpoint statement and its proof are retained in the companion’s [merger-scale calculation](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=merger-integral-proof).

<a id="sec:open"></a>

# Flow constructions and remaining questions

<a id="sec:newton"></a>

## Inverse rays and perturbation

<span id="sec:arguments" label="sec:arguments"></span><span id="sec:reciprocal" label="sec:reciprocal"></span> <span id="res:value" label="res:value"></span> The Newton flow $`\dot z=-f(z)/f'(z)`$ satisfies $`f(z(t))=f(z(0))e^{-t}`$. Thus its image in the value plane follows a fixed ray. This identity and the Newtonian graph of Shub, Tischler and Williams are used in the form given by Kozen and Stefánsson \[kozen-stefansson1997, Lemmas 2.1–2.2 and §2\]. The companion retains the [value and finite-endpoint theorems](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=newton-value-proof).

<span id="res:ray" label="res:ray"></span> For a finite interval $`[a,b]`$, continuity of $`f(z(t))`$ up to the endpoints extends the interior identity to $`f(z(b))=e^{a-b}f(z(a))`$. Nonzero endpoint values therefore lie on the same positive ray. Critical values with distinct arguments exclude such a connection; distinct moduli are insufficient.

<span id="res:locus" label="res:locus"></span> A generic constant perturbation separates rays when the original critical values are distinct, but cannot split equal values. A linear perturbation can do so generically. Neither qualitative assertion supplies a numerical perturbation bound that preserves a near-extremal path inequality. The [forbidden-ray locus calculation](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=argument-perturbation-proof) and the local logarithmic expansion, with remainder $`nq^{N+1}/((N+1)(1-q))`$ for $`q<1`$, specify the available control. At the nearest-root radius that expansion is inapplicable.

<a id="sec:gap"></a>

## The failed tree estimate

<span id="sec:finite" label="sec:finite"></span> For the Cassini polynomial $`z^2-(9/10)^2`$, any connected set containing both roots has length at least $`9/5`$. The right side of Proposition 12 in the March manuscript \[march2026\], even with its proposed arbitrarily small error, is smaller than $`41/25`$ before that error. Thus the proposed spanning-tree estimate is false. At a simple saddle the local level set has four sectors, consistently with the lemniscate graph description in \[bishop-eremenko-lazebnik, Definition 1.2 and Proposition 2.4\]. The [Cassini calculation and corrected topological statement](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=cassini-counterexample) separate the metric failure from the valid sheet decomposition.

Cutting outward from critical values to obtain inverse-sheet adjacency is classical; see \[dubinin2006critical, §1\] and \[dubinin2006capacity, §2\]. Length control requires additional estimates on the actual pieces and their attachment. An uncut Newton orbit space can even fail to be Hausdorff; it cannot automatically be identified with a finite Reeb graph. The earlier numerical searches in degrees $`5,6,8,10`$ found no counterexample on their tested grids. Such searches neither certify containment along unexamined edges nor prove a quantified statement about all polynomials.

<a id="restricted-extremal-problems"></a>

## Restricted extremal problems

In the closed lemniscate $`K_1(f)`$, a finite infimum of connecting path lengths is attained. At fixed degree, compactness of the closed root-disc class and lower semicontinuity of this infimum allow uniform upper bounds to pass to coefficient limits. These are statements about the closed lemniscate, as proved in the companion’s [compactness argument](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=closed-class-limits). The binomial family approaches length $`2`$. The assertion that the universal extremum is at most $`2`$ is refuted by the degree-seven example; its earlier formulation is not a remaining open problem. Quantitative bounds for restricted classes and for varying degree still require further work.

The precise unresolved questions about cut-open flow strips, attachment lengths and quantitative perturbation are stated in the companion’s [final questions](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=remaining-questions). The origin-spoke failure for the near-regular-pentagon family is proved there. The stronger failure asserted in the research addendum \[revision2026\] for every critical joining point has no available proof and is not used. Likewise the fixed degree-seven proof does not establish the whole small-parameter family.

<a id="sec:1041-sources"></a>

# Related results and verification

Eremenko and Hayman’s bound $`\mathcal H^1\{|p|=1\}<9.173\deg p`$ \[eremenko-hayman, Theorem 1\] concerns the total boundary length. Their connectedness result, the derivative estimate of Eremenko and Lempert \[eremenko-lempert, Theorem 1\], and its equality analysis \[eremenko-markov, Theorem A\] optimise different quantities from an internal root-to-root path. Kuznetsova and Tkachev \[kuznetsova2003, Theorems 1–2\] study length functions on regular levels; their log-convexity does not imply a uniform one-root perimeter bound at a critical endpoint. Dubinin’s four-point distortion theorem \[dubinin2013fourpoint, Theorem 1 and Corollary 4\] assumes a bound on all critical values and has a different normalisation. Pendyala’s work on Problem 1120 \[pendyala2026shortest, Definition 1.1 and Theorem 1.2\] asks for a path from $`0`$ to the unit circle in the intersection of a lemniscate with the closed disc. Those endpoints and that additional region restriction differ from the present question.

<a id="verification."></a>

#### Verification.

The supplied Lean sources contain proofs of the fixed counterexample for preconnected sets, the negation and `answer(False)` forms of the Formal Conjectures statement, and the total-variation formulation. The source links are collected in the companion’s [verification notes](../../../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf#nameddest=verification-notes). We report no new Lean build or independent human review, including review of correspondence with the 1958 wording. The bottleneck proof and the rational finite estimates are given in ordinary mathematical form. The complete $`13/25`$ rational program was rerun, reproducing the stated stopping time and all $`126`$ accepted dual certificates. Its analytic reduction and the isolated-value construction remain ordinary proofs: the associated Lean lemmas take those analytic inputs as hypotheses. The fourth-power critical-value mean refines the formally recorded quadratic inequality by an ordinary analytic argument. Formal links do not extend to a changed statement without a separate correspondence check. The margin links beside summaries of results proved in the companion retain the original statement identifiers. They refer to those original statements, including their stated hypotheses; the declaration-to-statement correspondence for consolidated results requires rechecking.

*Formal proofs.* A result with a kernel-checked Lean proof carries a mark in the margin. *Lean* opens the proof: the declaration itself when one declaration states the whole result, otherwise the list of declarations that together state it. *Comparator* opens the record of an independent check, in which the same statement, written again from Mathlib alone in a separate repository, was compared with our proof by Lean’s Comparator tool, allowing only the three standard axioms. A dagger on the Lean mark means that the Lean proof assumes an input named just below the result. A result without a mark has no Lean proof of its whole statement; what is checked is said below it. The [evidence record](https://github.com/wcook04/plectis-erdos/blob/cd83a19f8002856293310f4d71358b2f9d72a24e/evidence/erdos-1041-lemniscate-newton-flow.md) gives every declaration, version and check. These checks show that the stated propositions are proved; whether they are the right propositions is a question the reader can settle by comparing them with the text.

<a id="acknowledgements"></a>

# Acknowledgements

I thank Wouter van Doorn for advice on mathematical exposition, in particular on explaining restrictive hypotheses, avoiding private terminology and introducing notation only when it helps the reader. His remarks concerned another note; this acknowledgement does not imply that he reviewed or endorsed the mathematics of the present paper.

<div class="thebibliography">

99 T. F. Bloom, *Erdős Problems*, problem 1041. <https://www.erdosproblems.com/1041> P. Erdős, F. Herzog, and G. Piranian, *Metric properties of polynomials*, J. Analyse Math. **6** (1958), 125–148, doi:[10.1007/BF02790232](https://doi.org/10.1007/BF02790232). `shtuka`, *A Short Path Joining Two Zeros Inside a Polynomial Lemniscate*, manuscript posted 24 March 2026, 48 pp. <https://shtuka123.github.io/1041/main.pdf> V. S. Pendyala, *A Degree-Four Lemniscate Path Theorem*, arXiv:[2606.24875v1](https://arxiv.org/abs/2606.24875v1) (2026), doi:[10.48550/arXiv.2606.24875](https://doi.org/10.48550/arXiv.2606.24875). V. S. Pendyala, *Shortest paths in polynomial lemniscate sublevel sets and a problem of Erdős*, arXiv:[2606.19178v1](https://arxiv.org/abs/2606.19178v1) (2026), doi:[10.48550/arXiv.2606.19178](https://doi.org/10.48550/arXiv.2606.19178). D. Kozen and K. Stefánsson, *Computing the Newtonian graph*, J. Symbolic Comput. **24** (1997), no. 2, 125–136, doi:[10.1006/jsco.1997.0118](https://doi.org/10.1006/jsco.1997.0118); authors’ copy <https://www.cs.cornell.edu/kozen/Papers/newton.pdf>. E. Crane, *The areas of polynomial images and pre-images*, Bull. London Math. Soc. **36** (2004), no. 6, 786–792, doi:[10.1112/S0024609304003509](https://doi.org/10.1112/S0024609304003509); preprint arXiv:[math/0302189v1](https://arxiv.org/abs/math/0302189v1), whose statement numbers are cited. P. Ebenfelt, D. Khavinson, and H. S. Shapiro, *Two-dimensional shapes and lemniscates*, in *Complex Analysis and Dynamical Systems IV, Part 1*, Contemp. Math. **553**, Amer. Math. Soc., Providence, RI, 2011, 45–59, doi:[10.1090/conm/553/10931](https://doi.org/10.1090/conm/553/10931); preprint arXiv:[1003.4567v1](https://arxiv.org/abs/1003.4567v1), whose statement numbers are cited. A. Eremenko and W. Hayman, *On the length of lemniscates*, Michigan Math. J. **46** (1999), no. 2, 409–415, doi:[10.1307/mmj/1030132418](https://doi.org/10.1307/mmj/1030132418); preprint arXiv:[0805.2295](https://arxiv.org/abs/0805.2295). A. Eremenko and P. Yuditskii, *Comb functions*, Contemp. Math. **578** (2012), 99–118, doi:[10.1090/conm/578/11472](https://doi.org/10.1090/conm/578/11472); preprint arXiv:[1109.1464v1](https://arxiv.org/abs/1109.1464v1). A. Eremenko and L. Lempert, *An extremal problem for polynomials*, Proc. Amer. Math. Soc. **122** (1994), no. 1, 191–193, doi:[10.1090/S0002-9939-1994-1207536-1](https://doi.org/10.1090/S0002-9939-1994-1207536-1). A. Eremenko, *A Markov-type inequality for arbitrary plane continua*, Proc. Amer. Math. Soc. **135** (2007), no. 5, 1505–1510, doi:[10.1090/S0002-9939-06-08640-0](https://doi.org/10.1090/S0002-9939-06-08640-0); preprint arXiv:[math/0606745v1](https://arxiv.org/abs/math/0606745v1). C. J. Bishop, A. Eremenko, and K. Lazebnik, *On the shapes of rational lemniscates*, Geom. Funct. Anal. **35** (2025), no. 2, 359–407, doi:[10.1007/s00039-025-00704-2](https://doi.org/10.1007/s00039-025-00704-2); preprint arXiv:[2407.14610v1](https://arxiv.org/abs/2407.14610v1). V. N. Dubinin, *Some inequalities for polynomials and rational functions associated with lemniscates*, Zap. Nauchn. Sem. POMI **404** (2012), 83–99; English translation, J. Math. Sci. **193** (2013), no. 1, 45–54, doi:[10.1007/s10958-013-1432-4](https://doi.org/10.1007/s10958-013-1432-4). G. Pólya, *Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zusammenhängende Gebiete*, Sitzungsberichte der Preussischen Akademie der Wissenschaften, Physikalisch-Mathematische Klasse (1928), printed pp. 228–232 and 280–282. <https://archive.org/details/sitzungsbericht1928preu>. V. N. Dubinin, *Inequalities for critical values of polynomials*, Sb. Math. **197** (2006), no. 8, 1167–1176, doi:[10.1070/SM2006v197n08ABEH003793](https://doi.org/10.1070/SM2006v197n08ABEH003793). E. Crane, *A bound for Smale’s mean value conjecture for complex polynomials*, Bull. London Math. Soc. **39** (2007), no. 5, 781–791, doi:[10.1112/blms/bdm063](https://doi.org/10.1112/blms/bdm063); author preprint <https://people.maths.bris.ac.uk/~maetc/SMVCbound.pdf>. V. N. Dubinin, *Four-point distortion theorem for complex polynomials*, arXiv:[1301.3985v1](https://arxiv.org/abs/1301.3985v1) (2013). O. S. Kuznetsova and V. G. Tkachev, *Length functions of lemniscates*, Manuscripta Math. **112** (2003), 519–538, doi:[10.1007/s00229-003-0411-3](https://doi.org/10.1007/s00229-003-0411-3); preprint arXiv:[math/0306327](https://arxiv.org/abs/math/0306327). D. Tischler, *Critical points and values of complex polynomials*, J. Complexity **5** (1989), no. 4, 438–456. W. Cook / Plectis, *Three refinements for the lemniscate-path programme*, 16 September 2026, unreviewed research note, Sections 1–3, together with the earlier note *Structural obstructions*. V. N. Dubinin, *Lemniscates and inequalities for the logarithmic capacities of continua*, Mat. Zametki **80** (2006), no. 1, 33–37; English translation, Math. Notes **80** (2006), no. 1, 31–35, doi:[10.1007/s11006-006-0105-8](https://doi.org/10.1007/s11006-006-0105-8). T. Ransford, *Potential Theory in the Complex Plane*, London Mathematical Society Student Texts 28, Cambridge University Press, Cambridge, 1995, doi:[10.1017/CBO9780511623776](https://doi.org/10.1017/CBO9780511623776).

</div>
