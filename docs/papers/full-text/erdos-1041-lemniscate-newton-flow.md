<a id="erdos-1041-lemniscate-newton-flow"></a>

# Critical-Value Separation and Admissible Hubs

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Erdős, Herzog, and Piranian ask whether every monic polynomial of degree $`n\ge2`$ with roots in the open unit disc has two roots joined inside $`\{|f|<1\}`$ by a curve of length less than $`2`$. The problem is open. Write $`\mu=\min_{f'(c)=0}|f(c)|`$ for the least critical-value modulus and $`\rho=\mu^{1/n}`$. We prove three unconditional statements about arbitrary monic polynomials. Every squarefree $`f`$ of degree $`n\ge2`$ whose least critical-value modulus satisfies $`\mu\le13/25`$ has two distinct roots joined inside $`\{|f|<1\}`$ by a rectifiable curve of length strictly below $`2`$, with no hypothesis on where the roots lie; that proof is ordinary analysis closed by an exact rational certificate, whose certified quantity is $`X=635762889599/1000000000000`$ and whose closing inequality is $`(13/25)e^{X}<1`$. With the threshold removed, two zero occurrences of any monic $`f`$ of degree $`n\ge2`$ are joined inside $`\{|f|\le2\mu\}`$ by a path of length at most $`(71/10)\rho`$, and inside $`\{|f|<1\}`$ with length at most $`5.7`$ once the roots lie in the open unit disc and $`\mu\le1/2`$. In degree three the problem itself is settled: every cubic with roots in the open unit disc has two listed root occurrences joined inside $`\{|f|<1\}`$ by a polygonal path of length below $`2`$.

We also prove an all-degree sufficient condition in terms of the separation of critical values. If $`c`$ is a simple critical point, $`v=f(c)\ne0`$, and $`|1-f(d)/v|\ge S>1`$ at every other critical point, the two resolved inverse rays through $`c`$ join distinct roots inside $`\{|f|\le|v|\}`$ with length at most
``` math
2|v|^{1/n}(1+S)^{1/n}\sqrt{\log\!\frac{S}{S-1}}.
```
For roots in the open unit disc, this proves the desired bound when $`S=4`$ and $`n\ge3`$, $`S=3`$ and $`n\ge4`$, or $`S=2`$ and $`n\ge6`$. The proof resolves the saddle by a square-root coordinate. Critical-value separation makes the inverse branch univalent on a larger disc; Pólya’s area inequality then bounds its Taylor coefficients and hence its length.

We also prove the sharp adjacent-root bound for collinear zeros, with affine Chebyshev equality configurations, and solve the primitive sparse quintic and translated cubic quotient-fibre families. An auxiliary sharp power-sum bound $`\sum_{j=1}^{n-1}|f(c_j)|^{1/(n-1)}\le(n-1)R^{n/(n-1)}`$ holds through degree five for roots in a disc of radius $`R`$. Its proof compares critical values with the reflected derivative and uses finite-point inequalities in the unit disc. These are ordinary mathematical proofs; the paper identifies separately the Lean-checked selectors, inequalities, and Newton-flow identities they use.

The unrestricted problem remains open. Critical values near a tie and multiple saddles escape the separation argument. Exact counterexamples also show that short Euclidean chords or critical spokes need not stay in the lemniscate. The remaining task is to select and control a contained root connector; the critical-value budget alone does not bound its length.

<div class="center">

<div class="minipage">

------------------------------------------------------------------------

**Unconditional regimes, and a short path from critical-value separation**

**Unconditional results.** Theorem <a href="#res:low-critical-thirteen-twentyfifths" data-reference-type="ref" data-reference="res:low-critical-thirteen-twentyfifths">2</a> settles every squarefree monic polynomial whose least critical-value modulus is at most $`13/25`$, in every degree, with no hypothesis on root locations. Theorem <a href="#res:constant-factor-path" data-reference-type="ref" data-reference="res:constant-factor-path">4</a> removes the threshold and pays a constant factor: every monic polynomial has two zero occurrences joined by a path of length at most $`(71/10)\mu^{1/n}`$ inside $`\{|f|\le2\mu\}`$. Theorem <a href="#res:degree-three" data-reference-type="ref" data-reference="res:degree-three">5</a> settles degree three. All three are ordinary mathematics. The first is closed by an exact rational certificate carried by a replayable program in this repository, and the third has a companion Lean file in the research corpus that lies outside the pinned formal-source library, so none of the three carries a pinned-kernel receipt in this release. **Proved regime.** An isolated simple critical value gives a univalent resolved inverse branch. An area estimate bounds the branch coefficients, which control the length of its two root arms. Theorem <a href="#res:critical-value-separation" data-reference-type="ref" data-reference="res:critical-value-separation">6</a> gives the bound and Corollary <a href="#res:critical-value-thresholds" data-reference-type="ref" data-reference="res:critical-value-thresholds">7</a> gives explicit sufficient separations in every degree $`n\ge3`$. **Complementary results.** Sharp solved families and the critical-value budget through degree five supply geometric and algebraic information beyond that regime. **Open boundary.** Near-tied critical values and multiple saddles require another construction. An admissible-hub selector is one sufficient route to the target, not a proved characterization of every possible solution.

</div>

</div>

> **Contribution.** The paper proves three unconditional statements about arbitrary monic polynomials: a short contained connector whenever the least critical-value modulus is at most $`13/25`$, a constant-factor connector of length at most $`(71/10)\mu^{1/n}`$ inside $`\{|f|\le 2\mu\}`$ with no threshold at all, and the full degree-three case. It proves an all-degree critical-value-separation regime by a resolved inverse branch, the area formula, Pólya’s area–capacity inequality, and an exact coefficient estimate. It proves a sharp all-degree collinear theorem, a complete primitive sparse quintic theorem, and translated cubic quotient-fibre theorems in every degree $`3q`$. It also checks exponential Newton-value decay, positive-ray collision interfaces, finite translation avoidance, and quantified root retention, and records the current near-Fekete residual.
>
> **Relation to the open problem.** The three unconditional theorems, the separation regime and the three solved-family assemblies are ordinary mathematics, not kernel-checked authority. The $`13/25`$ threshold, the $`(71/10)`$ constant and the degree-three theorem have no formal endpoint in the pinned corpus, and the complementary regime $`13/25<\mu<1`$ is untouched. It excludes near-tied critical values and multiple saddles. The checked dynamical and perturbative inputs do not repair the global topology and metric gluing in those complementary strata, so Problem #1041 remains open. The degree-five target and the no-go witnesses are boundaries around the open theorem, not a hidden closure.
>
> **Executable review object.** Comparator selects the finite-family small-translation theorem and the quantified root-retention theorem and three solved-family kernels. Critical-value separation, including its threshold analysis, has no corresponding formal endpoint in the pinned corpus. Each formal endpoint routes to the exact paper result and boundary it supports; the covering-space and area argument and the frontier section remain ordinary evidence classes. The repository’s external-verification job compares these exact Lean propositions with separately declared challenge statements and an axiom budget, then asks Lean’s kernel to check the submitted proofs. The [formalisation manifest](https://github.com/wcook04/plectis-erdos/blob/ca0e13f8acf5ccf48506e4bdb870953d3a0856fa/formalization.yaml) and the commit-bound CI receipt record the checked statements and verification results.

The two selected perturbation interfaces have the following exact boundaries. For a finite type $`\iota`$, an injective family of critical values $`c\colon\iota\to\mathbb C`$, and every $`\varepsilon>0`$, the row `exists_small_translation_separating_arguments` supplies a shift of norm less than $`\varepsilon`$ such that every translated value is nonzero and every two distinct translated values lie on different positive rays. Separately, for a monic split polynomial of positive degree whose roots have norm at most $`\rho`$, the row `constant_perturbation_roots_in_unitDisk` requires $`\rho\ge0`$, $`\varepsilon>0`$, the margin
``` math
((\operatorname{natDegree}f+1)\varepsilon)^{1/\operatorname{natDegree}f}
   +\rho<1,
```
and a shift of norm less than $`\varepsilon`$; it then places every root of $`f+\operatorname{C}(\text{shift})`$ in the open unit disc. These are finite perturbation and stability interfaces only: neither row supplies the missing global topology or the length-$`2`$ gluing argument.

<a id="sec:problem"></a>

# The problem

<div id="res:problem" class="problem">

**Problem 1** (Erdős \#1041). Let $`f(z)=\prod_{i=1}^{n}(z-z_i)`$ be monic of degree $`n\ge2`$, with $`z_i\in\mathbb{D}`$, the open unit disc. Show that two of the roots can be joined by a curve of length less than $`2`$ lying in the open lemniscate $`E=\{z\in\mathbb{C}:|f(z)|<1\}`$.

</div>

The open-disc hypothesis is essential for this formulation. For $`f(z)=z^2-1`$, whose roots lie on the unit circle, every continuous path from $`-1`$ to $`1`$ meets the imaginary axis. There $`|f(iy)|=1+y^2\ge1`$, so no such path lies in the open unit lemniscate. Repeated roots, counted as distinct occurrences, give a constant path; the substantive case is therefore squarefree.

Numbering and current status follow Bloom’s Erdős problem catalogue \[bloom\]. The problem is open. The original source is Problem 5 on printed p. 139 of Erdős–Herzog–Piranian \[ehp1958, p. 139\]; the preceding paragraph records the known input that one component of the lemniscate contains at least two zeros.

Recent work on polynomial lemniscates separates component counts from metric path questions. Ghosh and Ramachandran characterize the number of components through critical points and critical values \[ghosh2023, Lemma 7\]; for the binomial family $`z^n-a`$, the condition $`|a|<1`$ puts the filled unit lemniscate in the connected regime. Connectedness alone gives no path-length bound. Our dynamical terminology is also standard: Sutherland calls $`\dot z=-f(z)/f'(z)`$ the continuous Newton flow and observes that $`f(z(t))`$ moves on a straight radial line \[sutherland1992, p. 42\]. We use this value-space identity, not a claim that the global trajectory graph is a tree.

Two recent manuscripts are relevant. The 48-page manuscript posted by `shtuka` on 24 March 2026 \[march2026, Theorem 1, p. 1\] claims the unrestricted statement. Its Proposition 12 (p. 16, with proof continuing through p. 30) supplies the spanning-tree decomposition used in the final proof. The defect was located publicly in the problem’s discussion thread: on 25 March 2026 Tao observed that the invocation of Lemma 8 there is unjustified and that the flow lines need not organise into connected trees, and on 26 March 2026 the manuscript’s author agreed that the statement of Proposition 12 itself, not only its printed proof, is incorrect, and set the strategy aside. Section <a href="#sec:gap" data-reference-type="ref" data-reference="sec:gap">10</a> records an independent diagnosis of the same failure through the local three-ended saddle model, together with possible repairs. No counterexample to the proposition is exhibited there. Pendyala’s independent June 2026 preprint \[june2026, Thm. 1, p. 1\] proves the degree-four case through a finite four-point radial lemma and a short polygonal connector. That is the one exactly comparable result. It settles degree four completely and reaches no other degree, while the unconditional theorems below hold in every degree $`n\ge2`$, under a hypothesis on the least critical-value modulus or under no root or threshold hypothesis at all, at the cost of a larger constant or a weaker containment level. The quartic theorem does not close the problem.

We study the Newton flow whose trajectories foliate the lemniscate.

*Status.* The original problem remains open. Statements marked as Lean-checked refer to the linked propositions accepted by the pinned kernel, with no `sorry`, added axioms, or unchecked evaluation. The note states the remaining mathematical obligations explicitly.

*Companion system context.* The [claim and trust boundary](../../../claim-faithful-publication-systems-paper.pdf#systems-trust), [cold-clone route to proof authority](../../../cold-clone-to-proof-receipt.pdf#cold-clone-authority), and [public contribution protocol](../../../open-source-mathematics-strategy.pdf#strategy-protocol) are described in sibling papers.

| Statement | Status | Exact boundary |
|:---|:---|:---|
| Erdős \#1041 | Open | No proof is claimed. |
| Low critical value $`\mu\le13/25`$ | Ordinary all-degree theorem with an exact rational certificate | Squarefree monic, $`n\ge2`$, least critical-value modulus at most $`13/25`$; no hypothesis on root locations, component arity or component capacity. The analytic chain and the certificate are ordinary; nothing here is Lean-checked; the regime $`13/25<\mu<1`$ is untouched. |
| Unconditional constant factor $`(71/10)\mu^{1/n}`$ | Ordinary all-degree theorem | Monic, $`n\ge2`$, no further hypothesis; containment is $`\{|f|\le2\mu\}`$ rather than $`\{|f|<1\}`$, and the constant $`71/10`$ exceeds the target $`2`$. Degree two is the separate exact case with constant $`2`$. |
| Degree three | Ordinary theorem, complete for that degree | Roots in the open unit disc, listed with multiplicity; the two selected roots are distinct in the squarefree case. The spoke identity and its norm bound have a Lean companion in the research corpus, outside the pinned formal-source library. |
| Critical-value separation | Ordinary all-degree theorem | A simple nonzero hub and $`(1+S)^{2/n}\log(S/(S-1))<1`$; the threshold, covering and area arguments remain ordinary; near ties and multiple saddles are excluded. |
| Critical-value budget through degree five | Ordinary theorem; scalar Lean companion | $`\sum_j|f(c_j)|^{1/n}\le(n-1)R`$ for $`2\le n\le5`$; the reflected-derivative comparison and complete finite-point inequalities remain ordinary proofs and do not control inverse-ray length. |
| Coefficient energy to path length | Checked | Termwise differentiation and the length integral of the actual power series; the inverse branch and area bound must be supplied. |
| Uniform central free-point region | Checked | Every positive number of points; $`|c_i|^2\le a<1`$ and $`e^L\le1+2L`$, where $`L=-\log(1-a)`$. |
| Newton value equation $`w'=-w`$ | Checked | Away from critical points, along any trajectory tangent to $`-f/f'`$. |
| Exponential first integral | Checked | $`\tfrac{d}{dt}\bigl(e^{t}f(z(t))\bigr)=0`$. |
| Ray separation of critical values | Checked (consumer form) | Endpoints of a finite connection share one oriented ray; distinct rays exclude a connection. |
| Ray-collision locus | Checked | $`\beta=(ra-b)/(1-r)`$, $`r>0`$, $`r\ne1`$: one real parameter per pair. |
| Quartic case | Cited | Proved in \[june2026, Thm. 1, p. 1\]; does not extend to general degree. |
| Translated quartic quotient fibres | Ordinary theorem with a Lean-checked metric kernel | For $`f(z)=P((z-h)^q)`$, $`P`$ monic quartic and $`q\ge2`$; Pendyala supplies the quartic geometry, while Lean checks the root-lift density, exact primitive, and strict endpoint budget. |
| Signed-moment cyclic tetranomials | Lean-checked two-index safe-spoke theorem | For an indexed finite root family of $`g(w)=w^m+aw^r+bw^s+c`$, an exact signed $`L^2`$ moment budget selects two distinct indices whose complete spokes are safe; distinct root values require injectivity of the indexing map. |
| Concyclic zeros with $`2\rho^n\le1`$ | Ordinary proof; finite exact and numerical checks | Distinct-root theorem; not Lean checked; the unrestricted concyclic case remains open. |
| Unrestricted proof of \[march2026, Theorem 1, p. 1\] | Proof gap | Proposition 12 uses a false three-ended local saddle block; located publicly by Tao (25 March 2026), conceded by the author at statement level (26 March 2026). No counterexample is exhibited. |
| Constant-translation ray separation and root retention | Checked | After critical-value injectivity, arbitrary small ray avoidance and an explicit unit-disc margin. |
| Coefficient perturbation and slack stability | Open | Must first create injective critical values and preserve the component, collars and length budget. |
| Reeb decomposition and length fan-in | Open | The two surviving producers. |
| Random search to degree $`10`$ | Verified finite instances | Upper bounds for sampled configurations only. |

<a id="sec:low-critical-closure"></a>

# An unconditional regime: a small least critical value

The strongest unconditional statement in this note fixes a threshold on one scalar attached to $`f`$ and asks nothing else. Throughout this section
``` math
\mu=\min_{f'(c)=0}|f(c)|
```
is the least critical-value modulus.

<div id="res:low-critical-thirteen-twentyfifths" class="theorem">

**Theorem 2** (a small least critical value forces a short connector). *Let $`f`$ be squarefree and monic of degree $`n\ge2`$ with $`\mu\le13/25`$. Then two distinct roots of $`f`$ are joined inside $`\{|f|<1\}`$ by a rectifiable curve of length strictly below $`2`$. No hypothesis is placed on the locations of the roots, on the number of roots in any component, or on the capacity of any component.*

</div>

<div id="res:low-critical-scale-free" class="corollary">

**Corollary 3** (scale-free form). *Every squarefree monic $`f`$ of degree $`n\ge2`$ has two distinct roots joined inside $`\{|f|<(25/13)\mu\}`$ by a curve of length below $`2\bigl((25/13)\mu\bigr)^{1/n}`$.*

</div>

<div class="proof">

*Proof.* Apply Theorem <a href="#res:low-critical-thirteen-twentyfifths" data-reference-type="ref" data-reference="res:low-critical-thirteen-twentyfifths">2</a> to $`s^{-n}f(sz)`$ with $`s=\bigl((25/13)\mu\bigr)^{1/n}`$, whose least critical-value modulus is $`13/25`$, and scale back. A repeated root occurrence gives the constant curve, so the squarefree case is the substantive one. ◻

</div>

<a id="mechanism."></a>

#### Mechanism.

Assume no two distinct roots are joined inside $`\{|f|<1\}`$ by a curve of length below $`2`$. Fix a regular level $`t\in(\mu,1)`$, let $`C_t`$ be the component descending from a critical point at level $`\mu`$, let $`k\ge2`$ be its root count, and put $`x=\log(t/\mu)`$ and $`a=\operatorname{Area}(C_t)/\pi`$. Uniformise $`C_t`$ by the disc, sending a point $`h`$ of $`C_t`$ whose intrinsic distance to every root is at least $`1`$ to the origin. Three consequences of the assumed failure follow. The radial Bergman kernel bound on the Riemann map forces pairwise hyperbolic separation $`d(b_i,b_j)\ge4\operatorname{artanh}\sqrt{\tanh(1/a)}`$. The one-root estimate at $`h`$ forces $`d(0,b_j)`$ below the level of the corresponding Green function, and the Blaschke product identity forces $`\sum_j\lambda(d_j)\ge x`$ with $`\lambda(d)=-\log\tanh(d/2)`$. Disjointness of the hyperbolic balls of radius half the separation, read on every hyperbolic circle about the origin through the law of cosines, converts the last two into an explicit lower bound for the arity $`k`$. Winding and Cauchy–Schwarz on the level curves give the perimeter inequality $`P_C(u)^2\le2\pi k\,u\,A_C'(u)`$, and lifting the value radius from each root and closing along boundary arcs turns the arity floor into the area growth inequality
``` math
a'(x)\ \ge\ \frac1{2\pi^2}
 \Bigl[\,2\sqrt k-\sqrt{2a(x+2)}\,\Bigr]_{+}^{2}.
```
Pólya’s inequality caps $`a`$ at $`1`$ until the level reaches $`1`$. A trajectory that is forced past that cap before $`t=1`$ contradicts the assumption.

<a id="certificate."></a>

#### Certificate.

The threshold is the level at which the forced area passes the cap. The companion program `experiments/erdos1041_low_critical_path_certificate.py` evaluates every accepted inequality in exact rational arithmetic, with directed rounding on every exponential, logarithm and square root, and with the rational brackets for $`\pi`$ and $`\log2`$ checked from Machin’s identity. The full replay uses $`18`$ area-table levels, $`14`$ radii per dual, $`126`$ certified duals, step $`1/400`$, and the single initial lower area $`10^{-6}`$. It certifies
``` math
X=\frac{635762889599}{1000000000000}<0.6357629,
 \qquad \frac{13}{25}e^{X}<1,
```
which is Theorem <a href="#res:low-critical-thirteen-twentyfifths" data-reference-type="ref" data-reference="res:low-critical-thirteen-twentyfifths">2</a>. The quick mode certifies $`X=664373027131/1000000000000`$ and the weaker threshold $`51/100`$. The floating optimiser that proposes the dual weights is outside the proof; only the rational upper bounds on the proposed pairs are used.

<a id="bdry:low-critical-closure"></a>

#### Evidence and exact boundary.

The analytic chain above is ordinary mathematics. Its general inputs are the Riemann mapping theorem, the Bergman kernel, the argument principle, the coarea formula, and Pólya’s area inequality $`\operatorname{Area}\{|f|\le t\}\le\pi t^{2/n}`$ \[polya1928, printed pp. 280–282\]. The exact rational certificate is a kernel-free replayable computation, and no part of this theorem is Lean-checked or independently reviewed. Prior art for the assembled statement is unassessed; the hyperbolic slice inequality follows from disjointness of the balls and the law of cosines and should be assumed known. The public source of record is `research_corpus/Erdos1041/LowCriticalPathCertificate.md`. The exact remaining obligation is the complementary regime $`13/25<\mu<1`$, which this argument does not touch, so Erdős #1041 remains open.

<a id="sec:constant-factor"></a>

# An unconditional all-degree constant-factor path theorem

Dropping the threshold entirely costs a constant. For a monic degree-$`n`$ polynomial put
``` math
K_t=\{z:|f(z)|\le t\},\qquad
 \mu=\min_{f'(c)=0}|f(c)|,\qquad \rho=\mu^{1/n}.
```

<div id="res:constant-factor-path" class="theorem">

**Theorem 4** (unconditional constant-factor path). *For every monic polynomial $`f`$ of degree $`n\ge2`$, two zero occurrences are joined by a possibly degenerate path of length at most
``` math
\frac{71}{10}\,\rho
```
inside $`K_{2\mu}`$. If $`f`$ is squarefree, their locations are distinct. If every root lies in the open unit disc and $`\mu\le1/2`$, the construction may be chosen inside $`\{|f|<1\}`$ with length at most $`5.7`$.*

</div>

The constant is the rationally certified specialization of a two-parameter bound. If the selected working component contains $`k\ge2`$ roots, then for every $`r\in(0,1)`$ and $`\lambda>1`$ the proof constructs a path in $`K_{\lambda\mu}`$ whose length is at most
``` math
\sqrt{\frac2k}\left(
   \frac{\sqrt2\,r}{(1-r)^2}
   +\lambda^{1/n}\left(
      \sqrt{\log(\lambda/r)}+
      \frac{\pi}{\sqrt{\log\lambda}}
    \right)
 \right)\rho.                                      \tag{CF}
```
For $`n\ge3`$, the choice $`\lambda=2`$, $`r=3/20`$ makes the bracket less than $`71/10`$: the largest case is $`n=3`$, where exact rational bounds give $`66517563/9392500<71/10`$. Degree two has the exact root-segment bound $`2\rho`$.

<div class="proof">

*Proof architecture.* Choose a critical point at level $`\mu`$ and a component at a regular level $`t\in[\mu,\lambda\mu]`$ that contains the corresponding first merge. If a regular component $`C'`$ at level $`\sigma`$ contains $`k'`$ roots, winding and Cauchy–Schwarz give the local perimeter estimate
``` math
\mathcal H^1(\partial C')^2
 \le2\pi k'\,\sigma\,\frac{d}{d\sigma}
      \operatorname{Area}(K_\sigma\cap C').         \tag{CF1}
```
Pólya’s area–capacity inequality $`\operatorname{Area}(K_T)\le\pi T^{2/n}`$ then selects $`t`$ with a degree-free boundary-length bound.

For an argument avoiding the finitely many critical-value rays, lift the radial value segment from each root to $`\partial C_t`$. Split each lift at level $`r\mu`$. Koebe distortion controls the low pieces. The exact precritical conformal-radius energy inequality
``` math
\sum_i\frac{\mu^2}{|f'(z_i)|^2}\le\rho^2          \tag{CF2}
```
aggregates those pieces without paying once per root. Coarea and (CF1) control the high pieces on average over the argument. Choose one argument realising that average, order the lift endpoints cyclically on $`\partial C_t`$, and use the shortest adjacent boundary arc. Averaging the two lifts and the boundary arcs over the $`k`$ adjacent pairs gives (CF). The strict unit-sublevel statement chooses the regular level below the top of the window when $`\lambda\mu\le1`$. ◻

</div>

<a id="bdry:constant-factor"></a>

#### Evidence and exact boundary.

Theorem <a href="#res:constant-factor-path" data-reference-type="ref" data-reference="res:constant-factor-path">4</a> is ordinary mathematics with no Lean-checked part. It uses the capacity identity, Pólya’s area inequality, Cauchy–Schwarz, the univalent-map distortion estimate, and a finite graph exit lemma; no external paper theorem is imported into it. The public source of record is `research_corpus/Erdos1041/UnconditionalConstantFactorBound.md`. Its containment level is $`2\mu`$ and its constant is $`71/10`$, so it does not reach either half of the target, and the sharp constant $`2`$ remains open. The adjacent classical literature on lemniscate length measures a different object, namely the arclength of the level curve $`\{|p|=1\}`$, which is Erdős #114: Borwein’s $`8\pi en`$ \[borwein1995\], Eremenko and Hayman’s $`9.173n`$ \[eremenkohayman1999\], Fryntov and Nazarov’s asymptotically sharp $`2n+o(n)`$ \[fryntovnazarov2008\], and Tao’s resolution for large $`n`$ \[tao2025\]. A bound $`74n^2`$ is attributed to Pommerenke in the same family, and this note records no located reference for it. None of these bounds a root-to-root path, and a dated search on 2 September 2026 located no constant-factor root-pair bound in arbitrary degree.

<a id="sec:degree-three"></a>

# Degree three

<div id="res:degree-three" class="theorem">

**Theorem 5** (the cubic case). *Let $`f(z)=\prod_{j=1}^{3}(z-z_j)`$ with $`|z_j|<1`$, the roots listed with multiplicity. Then two listed root occurrences are joined inside $`\{|f|<1\}`$ by a polygonal path of length strictly below $`2`$. If $`f`$ is squarefree the two are distinct.*

</div>

<div class="proof">

*Proof.* Multiple roots give a constant path, so assume $`f`$ squarefree. A component containing two roots contains a critical point, so the Erdős–Herzog–Piranian component lemma \[ehp1958, p. 139\] supplies a critical point with critical-value modulus below one.

Suppose first that $`f'`$ has two distinct zeros. Choose a critical point $`c`$ minimising $`|f(c)|`$, write the other one as $`c+\delta`$, and put $`v=f(c)`$, so $`0<|v|<1`$. Monicity gives the exact expansion $`f(c+d)=d^3-\tfrac32\delta d^2+v`$. Choose $`\alpha`$ with $`\alpha^3=v`$ and set $`b=\delta/\alpha`$; dividing by $`v`$ gives $`f(c+\alpha w)/v=P_b(w)`$ with
``` math
P_b(w)=w^3-\tfrac32bw^2+1 .
```
At the other critical point $`f(c+\delta)=v(1-b^3/2)`$, so minimality of $`|v|`$ is exactly the hypothesis $`|1-b^3/2|\ge1`$.

Under that hypothesis $`P_b`$ has at least two zeros, with multiplicity, in the closed unit disc. In the strict region a unit-circle zero $`w`$ would give $`b=\tfrac23(w+w^{-2})`$, and with $`w^3=e^{2iu}`$ and $`c_u=\cos u`$ a direct calculation gives $`|1-b^3/2|^2=1+\tfrac{64}{729}c_u^4(16c_u^2-27)\le1`$, an equality only at $`c_u=0`$, where $`b=0`$. So the strict region has no unit-circle zero. The radial deformation $`b\mapsto sb`$, $`s\ge1`$, stays in the strict region, since $`z=b^3/2`$ and $`|1-z|^2>1`$ give $`|1-s^3z|^2-1=s^3(s^3|z|^2-2\Re z)>0`$. For large $`s`$, Rouché’s theorem on $`|w|=1`$ compares $`P_{sb}`$ with $`-\tfrac32sbw^2`$, whose modulus $`\tfrac32s|b|`$ exceeds $`2\ge|w^3+1|`$, so $`P_{sb}`$ has exactly two zeros in the open unit disc; no zero crosses the circle along the deformation. The equality case follows by letting $`s`$ decrease to one and using continuity of the root multiset.

If $`P_b(w)=0`$ and $`0\le t\le1`$, then $`P_b(tw)=1-t^2-t^2(1-t)w^3`$, so $`|w|\le1`$ gives $`|P_b(tw)|\le(1-t^2)+t^2(1-t)|w|^3\le1-t^3\le1`$. The whole segment from $`0`$ to $`w`$ is therefore safe. Selecting two normalized roots $`w_1,w_2`$ with $`|w_i|\le1`$, the two segments from $`c`$ to $`c+\alpha w_i`$ lie in $`\{|f|\le|v|\}\subset\{|f|<1\}`$ and have combined length at most $`2|\alpha|=2|v|^{1/3}<2`$.

If instead $`f'`$ has a double zero $`c`$, then $`f(c+d)=d^3+v`$ and the roots are $`c+\alpha`$, $`c+\alpha\omega`$, $`c+\alpha\omega^2`$. Averaging their squared moduli gives $`|c|^2+|\alpha|^2<1`$, so $`|\alpha|<1`$; any two radial spokes have total length $`2|\alpha|<2`$, and along either spoke the value has modulus $`|v|(1-t^3)<1`$ away from the root endpoint. ◻

</div>

<a id="bdry:degree-three"></a>

#### Evidence and exact boundary.

The reduction, the zero-count lemma and the assembly are ordinary mathematics. The spoke identity $`P_b(tw)=1-t^2-t^2(1-t)w^3`$ and the norm bound that follows from it are stated as Lean declarations in `research_corpus/Erdos1041/CubicCriticalHub.lean`, a research-corpus file that lies outside the pinned formal-source library, so this release attaches no pinned-kernel receipt to them. The public source of record is `research_corpus/Erdos1041/CubicCriticalHub.md`. Pendyala proves the degree-four case \[june2026, Thm. 1, p. 1\]; whether degree three was already recorded on the Erdős Problem #1041 discussion thread or in \[ehp1958\] has not been adjudicated, so the priority question here is open. The argument uses the sparse normalized form $`w^3-\tfrac32bw^2+1`$, and a higher-degree proof needs a replacement for that sparsity.

<a id="sec:critical-value-separation"></a>

# An all-degree critical-value separation theorem

The first result is the strongest direct parent-theorem regime in this note. It is not a statement about a sampled family or a fixed degree: the condition is an exact inequality on the other critical values after normalising one simple first-merge hub.

<div id="res:critical-value-separation" class="theorem">

**Theorem 6** (critical-value separation). *Let $`P`$ be a polynomial of degree $`n\ge3`$ whose leading coefficient has modulus one. Suppose
``` math
P(0)=1,\qquad P'(0)=0,\qquad P''(0)\ne0,
```
and, for some $`S>1`$, every other critical point $`d\ne0`$ satisfies
``` math
|1-P(d)|\ge S.
```
If $`Z`$ is either local solution at the saddle of
``` math
P(Z(\xi))=1-\xi^2,\qquad Z(0)=0,
```
then $`Z`$ continues holomorphically and injectively to $`|\xi|<\sqrt S`$. Its endpoints $`Z(-1)`$ and $`Z(1)`$ are distinct roots, and their resolved inverse-ray connector satisfies
``` math
\int_{-1}^{1}|Z'(\xi)|\,d\xi
 \le 2(1+S)^{1/n}\sqrt{\log\!\frac{S}{S-1}}.       \tag{4}
```
In particular the connector has length strictly below $`2`$ whenever
``` math
(1+S)^{2/n}\log\!\frac{S}{S-1}<1.                 \tag{5}
```*

</div>

<div class="proof">

*Proof.* The simple saddle has local form $`P(z)=1+Az^2+O(z^3)`$ with $`A\ne0`$, so the substitution $`P(Z(\xi))=1-\xi^2`$ resolves it into two local holomorphic sheets. Normalize the algebraic curve $`X=\{(\xi,z):P(z)=1-\xi^2\}`$. A finite ramification point of its projection to the $`\xi`$-plane can occur only at a critical point $`d`$ of $`P`$, where $`\xi^2=1-P(d)`$. The node over $`(0,0)`$ is replaced in the normalization by the two resolved local points, and the separation hypothesis puts every other ramification point on or outside $`|\xi|=\sqrt S`$. Polynomial properness makes the normalized projection finite and proper. Its inverse image over $`D_{\sqrt S}`$ is therefore an unramified finite cover. Since the disc is simply connected, every connected cover component maps biholomorphically to it; in particular either resolved local sheet continues as a single holomorphic branch $`Z`$ throughout the disc.

This branch is also injective as a map into the $`z`$-plane. Indeed, $`Z(\xi_1)=Z(\xi_2)`$ implies $`\xi_1^2=\xi_2^2`$. The involution $`\iota(\xi,z)=(-\xi,z)`$ exchanges the two distinct normalized points over $`(0,0)`$ and hence exchanges their two cover components. If $`\xi_2=-\xi_1\ne0`$ and $`Z(\xi_1)=Z(\xi_2)`$, one component would meet its $`\iota`$-image; connected cover components are disjoint, so they would have to coincide, contradicting the two distinct points over $`0`$. Thus $`\xi_1=\xi_2`$.

Write $`Z(\xi)=\sum_{k\ge1}a_k\xi^k`$. For $`1<R<\sqrt S`$, injectivity and the area formula give
``` math
\pi\sum_{k\ge1}k|a_k|^2R^{2k}
   =\operatorname{Area}(Z(D_R)).                    \tag{6}
```
The identity $`P(Z(\xi))=1-\xi^2`$ places the image in $`\{|P|<1+R^2\}`$. Since the leading coefficient of $`P`$ has modulus one, Pólya’s area–capacity inequality \[polya1928, printed pp. 280–282\] yields
``` math
\operatorname{Area}(Z(D_R))
 \le \operatorname{Area}\{|P|<1+R^2\}
 \le \pi(1+R^2)^{2/n}.                              \tag{7}
```
Cauchy–Schwarz applied to (6)–(7) now gives
``` math
\sum_{k\ge1}|a_k|
 \le (1+R^2)^{1/n}
      \sqrt{\sum_{k\ge1}\frac1{kR^{2k}}}
 = (1+R^2)^{1/n}\sqrt{\log\!\frac{R^2}{R^2-1}}.   \tag{8}
```
The [checked coefficient-to-length theorem](https://github.com/wcook04/plectis-erdos/blob/0d34630e1cc9d2b1ac6edfa7cfdba83b31bdc8fe/ErdosProblems/Erdos1041/PowerSeriesDerivative.lean#L120) formalises the passage from the subradius energy bounds to the actual power-series derivative. Termwise integration on $`[-1,1]`$ gives $`\int_{-1}^{1}|Z'|\le2\sum_{k\ge1}|a_k|`$. Letting $`R\nearrow\sqrt S`$ proves (4). Injectivity makes $`Z(-1)`$ and $`Z(1)`$ distinct, while $`P(Z(\xi))=1-\xi^2\in[0,1]`$ on the real segment proves the claimed containment. Squaring (4) gives (5). ◻

</div>

<div id="res:critical-value-thresholds" class="corollary">

**Corollary 7** (exact convenient thresholds). *Condition *(5)* holds for
``` math
(n,S)=(n,4)\quad(n\ge3),\qquad
 (n,3)\quad(n\ge4),\qquad
 (n,2)\quad(n\ge6).
```
If $`f`$ is monic with roots in the open unit disc, $`c`$ is a simple critical point with $`v=f(c)\ne0`$, and every other critical point satisfies the corresponding inequality $`|1-f(d)/v|\ge S`$, then two roots of $`f`$ are joined inside $`\{|f|<1\}`$ by a curve of length strictly below $`2`$.*

</div>

<div class="proof">

*Proof.* For $`S=4`$ and $`n\ge3`$,
``` math
5^{2/n}\log(4/3)
 \le5^{2/3}\log(1+1/3)<5^{2/3}/3<1,
```
where the last radical inequality is $`25<27`$. For $`S=3`$ and $`n\ge4`$, $`4^{2/n}\log(3/2)\le2\log(1+1/2)<1`$. For $`S=2`$ and $`n\ge6`$, use the exact bound $`\log2<0.6931471808=:c`$. For example, summing the first nine terms of $`\log2=2\sum_{k\ge0}((2k+1)3^{2k+1})^{-1}`$ and bounding the positive remainder geometrically gives
``` math
\log2\le2\sum_{k=0}^{8}\frac1{(2k+1)3^{2k+1}}
       +\frac9{4\cdot19\cdot3^{19}}<c.
```
Exact rational arithmetic gives $`3c^3<1`$, so $`3^{2/n}\log2\le3^{1/3}\log2<3^{1/3}c<1`$.

For the polynomial $`f`$, set $`z=c+\rho e^{i\theta}w`$ with $`\rho=|v|^{1/n}`$ and choose $`\theta`$ so that $`P(w)=f(z)/v`$ has unit-modulus leading coefficient. The theorem gives a connector of length strictly below $`2|v|^{1/n}`$ inside $`\{|f|\le|v|\}`$. For each displayed threshold $`S\ge2`$, separation gives $`|f(d)|\ge(S-1)|v|\ge|v|`$ at every other critical point, so $`|v|=\mu`$ is the least critical-value modulus. If the roots lie in a disc of radius $`R<1`$, the resultant identity and Fekete’s Vandermonde bound give, with critical points counted with multiplicity,
``` math
\mu^{n-1}
 \le \prod_{f'(d)=0}|f(d)|
 =\frac{|\operatorname{Disc}(f)|}{n^n}
 =\frac{\prod_{i<j}|z_i-z_j|^2}{n^n}
 \le R^{n(n-1)}.
```
Thus $`|v|=\mu\le R^n<1`$, so both the length and containment are strict at the target scale. ◻

</div>

<a id="bdry:critical-value-separation"></a>

#### Evidence and exact boundary.

The analytic continuation, monodromy, area formula and Pólya inequality in Theorem <a href="#res:critical-value-separation" data-reference-type="ref" data-reference="res:critical-value-separation">6</a> are ordinary mathematics. The companion symbolic replay checks the branch-value algebra, all three exact constant chains, and the nonempty boundary example $`P(z)=1-3z^2+z^3`$, whose other critical point is $`2`$ and satisfies $`1-P(2)=4`$. The degree monotonicity, exact threshold inequalities and conversion from the squared estimate to a strict length bound are supplied by the scalar companion. The coefficient-energy estimate, termwise differentiation and length integral are now Lean-checked for the actual power series. Constructing the univalent branch and supplying its area bound remain the geometric inputs to the full theorem.

The method stops when a second critical value enters the resolved disc, and it assumes the selected saddle is simple. It therefore leaves the near-tie and multiple-saddle strata, makes no sharpness claim for the convenient thresholds, and does not prove an unrestricted admissible-hub selector, a COVER theorem, or Erdős #1041. Pólya supplies the global area inequality; the square-resolved covering and coefficient argument above assemble it into the displayed sufficient regime and exact constants.

The literature disposition for Dubinin’s Theorem 1 is settled here. The source is \[dubinin\], Theorem 1 on printed page 85 of the POMI original. It concerns a holomorphic function that gives a full $`n`$-fold covering of an annulus $`t_1<|w|<t_2`$, and, in the notation of that theorem, with $`E`$ its explicitly defined complementary set, it states
``` math
\Bigl(\frac{t_2}{t_1}\Bigr)^{2/n}\le\frac{m(E\cup D)}{m(E)}.
```
The full covering and the explicit complementary set are hypotheses of the theorem. Tao cited it on the Erdős Problem #1041 discussion page on 25 March 2026 for the relative scaling factor $`s^{2/n}`$ between the areas of two nested sublevel sets, which is the reading of the displayed inequality in which $`E`$ and $`E\cup D`$ are those two sublevel sets and the covering hypothesis holds. No step of this note uses that relative inequality. The area estimate (7) above uses the absolute inequality $`\operatorname{Area}\{|P|<T\}\le\pi T^{2/n}`$ for a polynomial with unit-modulus leading coefficient, taken from Pólya \[polya1928, printed pp. 280–282\], and the same absolute inequality is the area input to Theorem <a href="#res:low-critical-thirteen-twentyfifths" data-reference-type="ref" data-reference="res:low-critical-thirteen-twentyfifths">2</a> and to Theorem <a href="#res:constant-factor-path" data-reference-type="ref" data-reference="res:constant-factor-path">4</a>. Dubinin’s theorem is a neighbouring result on lemniscate areas under a covering hypothesis. It bounds areas and supplies no curve joining two roots, so it leaves every statement of this note unchanged. Corollary <a href="#res:critical-value-thresholds" data-reference-type="ref" data-reference="res:critical-value-thresholds">7</a> states $`S=2`$ at $`n\ge6`$; an earlier form of this threshold recorded $`n\ge7`$, which the sharp degree analysis above supersedes.

<a id="sec:solved-polynomial-families"></a>

# Three exact solved polynomial families

The next three theorems are unconditional subcases of the path problem, not proxies for the unrestricted conjecture. They are ordered by mathematical signal rather than by the date of their formalization: first an all-degree sharp theorem with equality configurations, then a complete degree-five sparse family, and finally an infinite tower of translated quotient fibres. In each case a displayed finite proposition is the exact Comparator-selected Lean endpoint. The ensuing normalization and path theorem is ordinary mathematics and is stated separately.

<a id="subsec:sharp-collinear-chebyshev"></a>

## Sharp collinear zeros

Put
``` math
r_n=\cos\frac{\pi}{2n},
 \qquad C_n=\frac{1}{2^{n-1}r_n^n}.
```

<div id="prop:sharp-collinear-chebyshev-comparator" class="theorem">

**Theorem 8** (checked Chebyshev endpoint). *Let $`m\ge0`$, let $`p\in\mathbb R[X]`$ be monic of degree $`m+2`$, and let
``` math
-1<c_0<\cdots<c_m<1,\qquad |c_i|\le1.
```
Suppose $`p(-1)=p(1)=0`$ and $`p(c_i)p(c_{i+1})<0`$ for $`0\le i<m`$. Then
``` math
\min_{0\le i\le m}|p(c_i)|\le C_{m+2}.
```*

</div>

This is exactly the statement selected as [the formal Chebyshev endpoint](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ExternalVerification1041SolvedFamilies/Solution.lean#L74). It is the kernel-facing alternation endpoint, not yet the geometric theorem.

<div id="thm:sharp-collinear-diameter" class="theorem">

**Theorem 9** (sharp collinear diameter theorem). *Let $`f`$ be a monic polynomial of degree $`n\ge2`$ whose zero occurrences are collinear, and let $`D`$ be their diameter. Some two adjacent zero occurrences are joined by a segment of length at most $`D`$ on which
``` math
|f(z)|\le
 \frac{(D/2)^n}{2^{n-1}\cos^n(\pi/(2n))}.          \tag{9}
```
The constant in *(9)* is best possible in every degree. Equality is attained by affine images of the zeros of $`T_n`$ whose extreme zeros have distance $`D`$.*

</div>

<div class="proof">

*Proof.* A repeated zero gives the constant path, so assume the zero values are distinct. A rigid motion sends their line to the real axis, their midpoint to the origin, and their extremes to $`\pm D/2`$. With $`R=D/2`$, the normalized polynomial
``` math
q(w)=R^{-n}e^{-in\theta}f(m+Re^{i\theta}w)
```
is monic with real zeros $`-1=y_1<\cdots<y_n=1`$, and $`|f(m+Re^{i\theta}w)|=R^n|q(w)|`$.

Compare $`q`$ with the monic endpoint-normalized Chebyshev polynomial
``` math
q_*(x)=\frac{T_n(r_nx)}{2^{n-1}r_n^n}.
```
Both $`q`$ and $`q_*`$ vanish at $`\pm1`$, and $`|q_*|\le C_n`$ on $`[-1,1]`$. For each gap $`[y_i,y_{i+1}]`$, choose $`c_i`$ at which $`|q|`$ is maximal. The signs of $`q(c_i)`$ alternate. If every gap maximum were larger than $`C_n`$, then $`q-q_*`$ would have the same alternating signs as $`q`$ at the $`c_i`$. It would therefore have a zero between each consecutive pair $`c_i,c_{i+1}`$, as well as the two zeros $`\pm1`$. These are $`n`$ distinct zeros, whereas the leading terms cancel and $`\deg(q-q_*)\le n-1`$; moreover $`q-q_*`$ is nonzero at every $`c_i`$. This contradiction selects a gap on which $`|q|\le C_n`$. Scaling back proves *(9)*.

For sharpness, take
``` math
y_k=\frac{\cos((2k-1)\pi/(2n))}{r_n},
 \qquad 1\le k\le n.
```
These are the zeros of $`q_*`$, have extremes $`\pm1`$, and every adjacent gap contains a scaled Chebyshev extremum where $`|q_*|=C_n`$. No smaller universal constant can work. ◻

</div>

<div id="cor:collinear-erdos-1041" class="corollary">

**Corollary 10** (collinear Erdős case). *If the zero occurrences of a monic polynomial lie on one line in the open unit disc, two of them are joined by a curve of length strictly below $`2`$ inside $`\{|f|<1\}`$.*

</div>

<div class="proof">

*Proof.* Their diameter satisfies $`D<2`$. Also $`C_n\le1`$ for $`n\ge2`$, with equality only at $`n=2`$, so *(9)* is strictly below one. The selected segment has length at most $`D<2`$. ◻

</div>

<a id="rem:sharp-collinear-formal-boundary"></a>

#### Formal boundary.

Lean checks sign preservation, the alternating root-count mechanism, the scaled Chebyshev endpoint and uniform bound, and Theorem <a href="#prop:sharp-collinear-chebyshev-comparator" data-reference-type="ref" data-reference="prop:sharp-collinear-chebyshev-comparator">8</a>. It does not check the rigid normalization, the existence of the gap maxima, transport back to the root line, or the equality-node locations used in Theorem <a href="#thm:sharp-collinear-diameter" data-reference-type="ref" data-reference="thm:sharp-collinear-diameter">9</a>. These are ordinary steps.

<a id="subsec:primitive-sparse-quintic"></a>

## The primitive sparse quintic

The next selector is finite but unusually rigid. For $`0<r<2`$ and $`0\le s_i\le1`$, $`x_i^2\le s_i`$, put
``` math
E_i=s_i^4(s_i+r^2+2rx_i).
```

<div id="prop:primitive-quintic-two-tail-energy-selector" class="theorem">

**Theorem 11** (checked two-tail energy selector). *Suppose
``` math
\sum_{i=0}^4x_i=-r,\qquad
 \sum_{i=0}^4(2x_i^2-s_i)=r^2,\qquad
 \sum_{i=0}^4(4x_i^3-3s_ix_i)=-r^3.              \tag{10}
```
Then at least one of the ten pairs $`0\le i<j\le4`$ satisfies $`E_i<1`$ and $`E_j<1`$.*

</div>

This is the exact finite conclusion selected as [the formal two-tail selector](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ExternalVerification1041SolvedFamilies/Solution.lean#L24). It selects two distinct indices. It does not assert that the corresponding complex root values are distinct.

<div id="thm:primitive-quintic-two-tail" class="theorem">

**Theorem 12** (primitive sparse quintic). *Let
``` math
p(z)=z^5+az^4+bz+c
```
and suppose its five zero occurrences $`w_0,\ldots,w_4`$ lie in the closed unit disc. At least two distinct indices satisfy
``` math
|bw_i+c|\le1.                                    \tag{11}
```
If $`a\ne0`$, two indices can be chosen with strict inequalities. If $`a=0`$, every index satisfies *(11)*, and equality holds exactly when $`|w_i|=1`$.*

*For open-disc zeros, two zero occurrences are joined inside $`\{|p|<1\}`$ by a curve of length below $`2`$: use the two radial spokes through $`0`$ when their values are distinct, and the constant path when the selected occurrences have the same value.*

</div>

<div class="proof">

*Proof.* Rotate so that $`a=re^{i\phi}`$ becomes $`r\ge0`$ and write $`z_i=e^{-i\phi}w_i`$. The missing $`z^3`$ and $`z^2`$ coefficients and Newton’s identities give
``` math
\sum z_i=-r,\qquad \sum z_i^2=r^2,\qquad
 \sum z_i^3=-r^3.                                 \tag{12}
```
At a zero,
``` math
|bw_i+c|=|w_i|^4|w_i+a|.
```
Thus, for $`x_i=\Re z_i`$ and $`s_i=|z_i|^2`$, the squared tail is exactly $`E_i`$ and *(12)* becomes *(10)*. If $`r>0`$, the third moment also gives $`r^3=|\sum_i z_i^3|\le5<8`$, so $`r<2`$ as required by the selector.

For completeness, the selector is driven by the harmonic extension
``` math
H_r(x,s)=(-r/2-x)(1-x)^2
 +(1-s)\left(1-\frac r4-\frac{3x}{4}\right).
```
The three moments give the exact sum
``` math
\sum_{i=0}^4H_r(x_i,s_i)=5-2r,                  \tag{13}
```
while $`H_r\le4-2r`$ throughout the unit disc. If $`E_r(x,s)\ge1`$, then
``` math
5(1-s)\le2r(x+r/2).
```
Put $`d=x+r/2`$, $`u=1-x`$, $`A=1-r/4-3x/4`$, and $`P=-u^2+(2r/5)A`$. The unsafe inequality gives $`0\le d<2`$. Since $`H_r=-du^2+(1-s)A`$, it is nonpositive when $`A\le0`$; when $`A>0`$, the preceding bound gives $`H_r\le dP`$. The remaining estimate is the exact sum-of-squares identity
``` math
\frac1{31}-P
 =\frac25\left(d-\frac{38}{31}
               +\frac14(u-\frac3{31})\right)^2
  +\frac{31}{40}\left(u-\frac3{31}\right)^2\ge0,
```
which gives $`P\le1/31`$, and hence $`H_r(x,s)\le2/31`$ whether $`P`$ is positive or nonpositive. Thus every unsafe tail has this smaller score. If four tails were unsafe, *(13)* would give
``` math
5-2r\le4-2r+\frac8{31}<5-2r,
```
a contradiction. This proves the two-index conclusion. The case $`r=0`$ is the direct identity $`|bw_i+c|=|w_i|^5`$.

Finally, at a zero $`w`$,
``` math
p(tw)=(1-t)c+(t-t^4)(bw+c)-t^4(1-t)w^5.
```
For $`0\le t\le1`$ the three nonnegative coefficients sum to $`1-t^5`$. The tail bound, $`|w|\le1`$, and $`|c|\le1`$ therefore give the radial unit-sublevel path. Under the open-disc hypothesis the relevant bounds and the total spoke length $`|w_i|+|w_j|`$ are strict. ◻

</div>

<a id="rem:primitive-quintic-formal-boundary"></a>

#### Formal boundary.

Lean checks the five-index moment hypotheses, the harmonic cap, the sum-of-squares unsafe estimate, and the ten-pair conclusion in Theorem <a href="#prop:primitive-quintic-two-tail-energy-selector" data-reference-type="ref" data-reference="prop:primitive-quintic-two-tail-energy-selector">11</a>. The rotation, derivation of Newton moments from the roots, root-tail identity, Abel decomposition, path assembly, and any passage from distinct indices to distinct complex values remain ordinary mathematics.

<a id="subsec:translated-cubic-quotient-fibres"></a>

## Translated cubic quotient fibres

<div id="lem:cubic-safe-root-spoke" class="theorem">

**Theorem 13** (checked cubic safe spoke). *If $`r,s,v\in\mathbb C`$ have modulus below one, at least one $`u\in\{r,s,v\}`$ satisfies
``` math
\left|(tu-r)(tu-s)(tu-v)\right|\le1
 \qquad(0\le t\le1).
```*

</div>

This is exactly [the formal cubic safe-spoke theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ExternalVerification1041SolvedFamilies/Solution.lean#L14).

<div id="thm:translated-cubic-quotient-fibres" class="theorem">

**Theorem 14** (translated cubic quotient fibres). *Let $`q\ge2`$, $`h\in\mathbb C`$, $`P`$ be monic cubic, and
``` math
f(z)=P((z-h)^q).
```
If every zero of $`f`$ lies in the open unit disc and $`f`$ has at least two distinct zero values, then two zeros are joined through $`h`$ by a two-segment path of length below $`2`$ inside $`\{|f|<1\}`$. Equivalently this closes the coefficient family
``` math
(z-h)^{3q}+A(z-h)^{2q}+B(z-h)^q+C
```
in every degree $`3q\ge6`$.*

</div>

<div class="proof">

*Proof.* Fix a $`q`$th root $`y`$ of a quotient root and a primitive $`q`$th root of unity $`\zeta`$. The full fibre consists of $`h+y\zeta^k`$. Since every fibre point lies in the open unit disc,
``` math
\frac1q\sum_{k=0}^{q-1}|h+y\zeta^k|^2
   =|h|^2+|y|^2<1.                                \tag{14}
```
Thus $`|y|<1`$, and the corresponding quotient root has modulus $`|y|^q<1`$. This verifies the open-disc hypothesis for all quotient roots before applying the following selector. The identity retains more information than these separate bounds: $`|h|<1`$ and every fibre radius is strictly below $`\sqrt{1-|h|^2}`$. Consequently, any two safe fibre spokes constructed below have total length strictly less than $`2\sqrt{1-|h|^2}`$. The position of the symmetry centre therefore controls the metric budget; the bound $`2`$ discards this information.

Write $`P(w)=(w-r)(w-s)(w-v)`$ and assign to $`r`$ the charge $`A_r=\Re(r\overline{s+v})`$, cyclically. The exact sum is
``` math
A_r+A_s+A_v=|r+s+v|^2-(|r|^2+|s|^2+|v|^2)>-3,
```
so one charge, say $`A_r`$, exceeds $`-1`$. For $`0\le t\le1`$, AM–GM and the distance-square identity give
``` math
|tr-s|\,|tr-v|<1+t+t^2.
```
Consequently, for $`0\le t<1`$,
``` math
|P(tr)|<(1-t)(1+t+t^2)=1-t^3\le1.              \tag{15}
```
At $`t=1`$ the polynomial vanishes. The entire spoke is therefore strictly contained, including its origin endpoint.

For a nonzero safe quotient root from *(15)*, two distinct fibre points satisfy
``` math
f(h+ty\zeta^k)=P(t^qr),
```
and their two spokes through $`h`$ have total length $`2|y|<2\sqrt{1-|h|^2}\le2`$. If the selected quotient root is zero, choose a nonzero quotient root and use the direct estimate $`|P(ts)|<2t(1-t)\le1/2`$ for $`0<t<1`$, with zero values at both endpoints; if none exists, $`f`$ has only one distinct zero value, contrary to the hypothesis. ◻

</div>

<a id="rem:cubic-quotient-formal-boundary"></a>

#### Formal boundary.

Lean checks the charge identity and selection, the two-distance envelope, the cubic product bound, the safe-spoke disjunction in Theorem <a href="#lem:cubic-safe-root-spoke" data-reference-type="ref" data-reference="lem:cubic-safe-root-spoke">13</a>, and an exact quartic falsifier for this charge method. It does not check the finite $`q`$-fibre construction, root-of-unity average *(14)*, zero-root fallback, pullback, or geometric path assembly. These remain ordinary proof steps.

<a id="bdry:solved-polynomial-families"></a>

#### Shared assurance boundary.

The three Comparator declarations route respectively to Theorems <a href="#prop:sharp-collinear-chebyshev-comparator" data-reference-type="ref" data-reference="prop:sharp-collinear-chebyshev-comparator">8</a>, <a href="#prop:primitive-quintic-two-tail-energy-selector" data-reference-type="ref" data-reference="prop:primitive-quintic-two-tail-energy-selector">11</a>, and <a href="#lem:cubic-safe-root-spoke" data-reference-type="ref" data-reference="lem:cubic-safe-root-spoke">13</a>. They support, but are strictly weaker than, the ordinary assembled Theorems <a href="#thm:sharp-collinear-diameter" data-reference-type="ref" data-reference="thm:sharp-collinear-diameter">9</a>, <a href="#thm:primitive-quintic-two-tail" data-reference-type="ref" data-reference="thm:primitive-quintic-two-tail">12</a>, and <a href="#thm:translated-cubic-quotient-fibres" data-reference-type="ref" data-reference="thm:translated-cubic-quotient-fibres">14</a>. The displayed Lean endpoints and the assembled geometric theorems therefore have different formalization boundaries.

<a id="sec:frontier"></a>

# The current frontier: what survives near Fekete configurations

The August 29 public research update changes the useful first reading of this problem. It does not add a proof of Erdős #1041; it identifies the geometric regime in which the remaining difficulty is concentrated and kills several attractive but false shortcuts. The source of the update is pinned to commit [`f214a6b4`](https://github.com/wcook04/plectis-erdos/tree/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041) and the dated synthesis is [`FRONTIER.md`](https://github.com/wcook04/plectis-erdos/blob/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041/FRONTIER.md). The distinctions below are part of the result: a theorem, a refutation, a certificate, and a measurement do not have interchangeable force.

<a id="near-fekete-stability-removes-the-radial-distraction"></a>

## Near-Fekete stability removes the radial distraction

Write $`a_i=\rho_i u_i`$, with $`|u_i|=1`$, and put $`D=|\operatorname{disc}(f)|/n^n`$. The quantitative Fekete–Hadamard estimate in [`NearFeketeRadialAngularSplit.md`](https://github.com/wcook04/plectis-erdos/blob/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041/NearFeketeRadialAngularSplit.md) says that, when $`D\ge1-\eta`$ and $`\eta\le1/(80n^2)`$,
``` math
1-\rho_i^2\le \frac{n\eta}{n-1},\qquad
  |a_i-a_j|\ge \frac{2-2\sqrt\eta-n\eta}{n-1},
```
and the roots lie within $`7\sqrt\eta`$ of a rotated regular $`n`$-gon, after a bijection. The mechanism is a normalised Vandermonde Gram determinant: near equality in Hadamard’s inequality forces both the radii and the angular separation to be near extremal. This is an ordinary mathematical result in the public research corpus, not a new Lean declaration.

The associated radial monotonicity theorem is the more important reader conclusion. Under the stronger near-Fekete condition $`\eta\le1/(10n^4)`$ used by this corollary, replacing the radii by one can only increase the values along the corresponding radial spoke. Thus radial deficits help containment; the unresolved near-Fekete problem is angular. On exact regular-gon directions this becomes unconditional for $`n\le6`$: arbitrary radii in the stated band give
``` math
|f(s\,\omega\zeta^i)|\le1-s^n
 \quad(0\le s\le\rho_i),
```
so every two-radii path is contained. The good spoke in the general on-circle averaging identity may move with $`s`$, however; that is why an existence statement at one level does not supply a fixed pair of roots.

<a id="a-bounded-radius-concyclic-class"></a>

## A bounded-radius concyclic class

There is nevertheless a clean theorem for a different on-circle mechanism. Let $`f`$ be monic of degree $`n\ge3`$ with distinct zeros on a circle of radius $`\rho`$. If $`2\rho^n\le1`$, two adjacent zeros are joined by their straight chord, whose length is at most $`2\rho\sin(\pi/n)<2`$, and the chord lies in $`\{|f|<1\}`$. (If a zero is repeated, the short-connection conclusion is immediate; the distinct case is the substantive one.)

After normalisation to the unit circle, self-inversive realification and alternation against $`z^n-c`$ select a zero-free gap on which the polynomial modulus is at most $`2`$; a harmonic normal-derivative argument transfers this arc bound strictly to the chord. The complete ordinary proof is [`ConcyclicAlternation.md`](https://github.com/wcook04/plectis-erdos/blob/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041/ConcyclicAlternation.md).

The argument is an ordinary proof outside Lean. The [exact-rational checker](https://github.com/wcook04/plectis-erdos/blob/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041/scripts/check_erdos1041_concyclic_exact_witness.py) checks finitely many load-bearing identities and configurations, while the [numerical checker](https://github.com/wcook04/plectis-erdos/blob/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041/scripts/check_erdos1041_concyclic_alternation.py) is regression and stress-test evidence. The arc constant $`2`$ is sharp on the regular $`n`$-gon, so this chord argument does not reach radii tending to $`1`$; the unrestricted concyclic case and Erdős #1041 remain open.

<a id="cyclic-trinomial-fibres"></a>

## Cyclic trinomial fibres

The spoke identity and strict bound are formalized in [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/CyclicTrinomialFiberCase.lean#L46) and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/CyclicTrinomialFiberCase.lean#L103).

There is also a positive structured family in every cyclic lift degree. Fix integers $`1\le r\le m`$ and $`q\ge1`$, and consider the translated polynomial
``` math
f(z)=(z-h)^{qm}+a(z-h)^{qr}+c.
```
Writing $`w=(z-h)^q`$ reduces the root equation to $`w^m+aw^r+c=0`$. At such a quotient root the middle coefficient can be eliminated exactly: for $`0\le u\le1`$,
``` math
u^mw^m+au^rw^r+c
   =(1-u^r)c-(u^r-u^m)w^m.
```
The two coefficients on the right are nonnegative and have total at most one. The [formal strict-spoke theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/CyclicTrinomialFiberCase.lean#L103) therefore proves that, if $`|w|<1`$ and $`|c|<1`$, the complete radial spoke is strictly contained in the open unit lemniscate. This is an all-root statement; no Vieta-small root selection is needed for the containment bound.

For a nontrivial cyclic fibre, two selected displacements $`y_1,y_2`$ with $`|y_1|,|y_2|<1`$ also satisfy $`|y_1|+|y_2|<2`$. The formal source checks the factorization, strict spoke estimate, and this metric budget. It does not yet check the ordinary finite argument selecting a suitable quotient root and two distinct members of its fibre, lifting both quotient spokes, or assembling their union as a path in the relevant component. Thus the Lean theorem is the load-bearing analytic kernel for this translated cyclic-trinomial family, not the complete path theorem and not a proof of unrestricted Erdős #1041.

<a id="coefficient-controlled-cyclic-tetranomial-spokes"></a>

## Coefficient-controlled cyclic tetranomial spokes

The first additional lower monomial admits an exact Abel-tail criterion. Let
``` math
g(w)=w^m+aw^r+bw^s+c,\qquad m>r>s\ge1,
```
assume all roots of $`g`$ lie in the open unit disk, and let $`w_1,w_2`$ be roots of the two smallest moduli. If
``` math
|c|+|b|\,|w_2|^s<1,
```
then the complete radial spokes from $`w_1`$ and $`w_2`$ to the origin lie in $`\{|g|<1\}`$, and their broken line has length strictly below $`2`$. The simpler coefficient condition
``` math
|b|+|c|\le1
```
makes every root spoke safe; the coefficient $`a`$ is unrestricted.

The mechanism is visible in one identity. At a root $`w`$ and for $`0\le u\le1`$,
``` math
\begin{split}
 g(uw)={}&(1-u^s)c
  -(u^s-u^r)(aw^r+w^m)
  -(u^r-u^m)w^m,\\
 aw^r+w^m={}&-(c+bw^s).
\end{split}
```
The three scalar coefficients are nonnegative and sum to $`1-u^m`$. Thus the root-dependent budget $`|c|+|b||w|^s<1`$, together with $`|w|<1`$ and $`|c|<1`$, puts every vector in the Abel decomposition strictly inside the unit ball. Lean checks the [factorization](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/CyclicTetranomialCoefficientCase.lean#L27) and the resulting [strict spoke theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/CyclicTetranomialCoefficientCase.lean#L145) under the exact weak exponent hypotheses $`1\le s\le r\le m`$; it also checks the coefficient-only corollary above.

There is a stronger, genuinely two-index formal theorem. Let $`S`$ index a finite family of roots, $`N=|S|\ge2`$, and
``` math
M=\sum_{i\in S}w_i^s.
```
The [formal energy identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/TetranomialL2Selector.lean#L33) gives
``` math
\sum_{i\in S}|c+bw_i^s|^2
 =N|c|^2+|b|^2\sum_{i\in S}|w_i^s|^2
   +2\mathop{\rm Re}(\overline c\,bM).
```
Consequently, if every $`|w_i|<1`$, $`|c|<1`$, and
``` math
N\bigl(|b|^2+|c|^2\bigr)
   +2\mathop{\rm Re}(\overline c\,bM)<N-1,
```
then two distinct indices $`i,j\in S`$ satisfy $`|c+bw_i^s|<1`$ and $`|c+bw_j^s|<1`$. Feeding those inequalities into the [formal Abel-spoke consumer](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/TetranomialL2Selector.lean#L208) proves that both complete root spokes lie strictly in $`\{|g|<1\}`$. The signed cross term is essential: this interface can certify configurations outside the coefficient-only triangle $`|b|+|c|\le1`$. The formal hypotheses do not require $`i\mapsto w_i`$ to be injective, so distinct indices need not denote distinct root values; the ordinary two-root consequence requires a root enumeration without repetition.

For $`q\ge2`$ and $`f(z)=g((z-h)^q)`$, the ordinary regular-fibre mean-square identity puts every quotient root inside the unit disk. Lifting two selected quotient spokes gives a path through $`h`$ whose two displacement lengths sum to less than $`2`$. The new Lean theorem assumes the finite root family, its signed moment $`M`$, and the displayed budget; it does not derive that budget from arbitrary tetranomial coefficients, prove that the supplied family is a complete root multiset, perform cyclic-fibre lifting, or construct the final path object. Without the signed-moment, root-dependent, or coefficient-only budget, the tetranomial case remains open; this family does not solve unrestricted Erdős #1041.

<a id="sec:translated-quartic-quotient-fibres"></a>

## Translated quartic quotient fibres

Pendyala’s degree-four theorem can also be lifted through every nontrivial cyclic power. Let $`P`$ be a monic quartic, let $`q\ge2`$, and set
``` math
f(z)=P((z-h)^q).
```
If all listed zeros of $`f`$ lie in the open unit disk, averaging the squared moduli over each complete $`q`$-point fibre shows that every quotient root $`w`$ of $`P`$ satisfies $`|w|<1`$. Pendyala’s chord-or-radial proof then supplies the quotient geometry. The extra issue is metric: a short chord in the $`w`$-plane need not lift isometrically through $`y\mapsto y^q`$.

Put $`\alpha=1/q`$. Along a quotient chord whose supporting line has distance $`d`$ from the origin, the root-lift density is controlled pointwise by
``` math
\bigl(\sqrt{d^2+x^2}\bigr)^{\alpha-1}
    \le x^{\alpha-1}\qquad(x>0),
```
and Lean checks the [exact primitive](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/research_corpus/Erdos1041/QuarticQuotientFiberCase.lean#L37)
``` math
\alpha\int_0^A x^{\alpha-1}\,dx=A^\alpha.
```
Splitting at the perpendicular foot, and at the origin when the chord crosses it, yields the ordinary power-map chord-lift estimate
``` math
\operatorname{length}(\widetilde{[a,b]})
    \le |a|^{1/q}+|b|^{1/q}.
```
The [formal endpoint consumer](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/research_corpus/Erdos1041/QuarticQuotientFiberCase.lean#L59) also proves that if $`0\le a,b<1`$, $`\alpha>0`$, and a candidate length $`L`$ is at most $`a^\alpha+b^\alpha`$, then $`L<2`$. Thus both Pendyala branches survive the power-map lift, giving the asserted short path for every translated quartic quotient fibre, in each degree $`4q\ge8`$.

The attribution and proof boundary are exact. Pendyala proves the quartic geometric theorem and its four-point radial lemma. The local Lean module checks the antitone density inequality, its integral, the strict powered endpoint budget, and the final length fan-in. It does not formalize Pendyala’s geometric lemma, the continuous covering-space construction of the root lift, or the ordinary chord/radial case assembly. This is a structured all-scale family, not a proof of unrestricted Erdős #1041.

<a id="a-critical-value-budget-through-degree-five"></a>

## A critical-value budget through degree five

The critical values satisfy a sharp aggregate bound in the first four nontrivial degrees. This gives a budget for the merge levels; it does not bound the lengths of the paths that reach them.

<div id="res:critical-value-budget" class="theorem">

**Theorem 15** (critical-value budget in degrees two through five). *Let $`f`$ be monic of degree $`2\le n\le5`$, with roots in a disk of radius $`R`$. If $`c_1,\ldots,c_{n-1}`$ are its critical points counted with multiplicity, then
``` math
\begin{equation}
\label{eq:critical-value-power-budget}
 \sum_{j=1}^{n-1}|f(c_j)|^{1/(n-1)}\le(n-1)R^{n/(n-1)}.
\end{equation}
```
Consequently
``` math
\sum_{j=1}^{n-1}|f(c_j)|^{1/n}\le(n-1)R.
```
The constant is attained by $`f(z)=(z-\tau)^n-\lambda`$ with enclosing disk centred at $`\tau`$ and radius $`R=|\lambda|^{1/n}`$.*

</div>

The finite inequality behind the theorem concerns arbitrary points of the disk, without asking them to arise as critical points. Write $`(\mathrm{FP}_m)`$ for
``` math
\sum_{j=1}^m\left(\prod_{k=1}^m
       |1-\overline{c_j}c_k|\right)^{1/m}\le m,
 \qquad |c_j|\le1.
```
The following pointwise bound explains why these finite inequalities control critical values in every degree.

<div id="res:reflected-critical-value" class="lemma">

**Lemma 16** (reflected-derivative bound). *If $`f`$ is monic of degree $`n\ge2`$ with roots in the closed unit disk, and $`c_1,\ldots,c_{n-1}`$ list its critical points with multiplicity, then
``` math
\begin{equation}
\label{eq:critical-reflected-product}
 |f(c_j)|\le\prod_{k=1}^{n-1}|1-\overline{c_j}c_k|.
\end{equation}
```*

</div>

<div class="proof">

*Proof.* First put all roots $`a_i`$ strictly inside the disk. Gauss–Lucas does the same for the $`c_k`$, so
``` math
N(z)=nf(z)-zf'(z),\qquad
 G(z)=n\prod_k(1-\overline{c_k}z)
```
have $`G\ne0`$ on the closed disk. On $`|\zeta|=1`$, $`|G(\zeta)|=|f'(\zeta)|`$, while
``` math
\operatorname{Re}\frac{\zeta f'(\zeta)}{f(\zeta)}
 =\sum_i\left(\frac12+
       \frac{1-|a_i|^2}{2|1-a_i\bar\zeta|^2}\right)\ge\frac n2.
```
Writing the logarithmic derivative as $`w`$, the identity $`|n-w|^2-|w|^2=n^2-2n\operatorname{Re}w\le0`$ gives $`|N|\le|G|`$ on the circle. The maximum-modulus principle applied to $`N/G`$ gives the same comparison inside. At $`c_j`$, $`N(c_j)=nf(c_j)`$; dividing by $`n`$ and conjugating each factor proves <a href="#eq:critical-reflected-product" data-reference-type="eqref" data-reference="eq:critical-reflected-product">[eq:critical-reflected-product]</a>. For closed-disk roots apply this result to $`f_r(z)=r^nf(z/r)`$, $`0<r<1`$, whose critical points are $`rc_k`$:
``` math
r^n|f(c_j)|\le\prod_k|1-r^2\overline{c_j}c_k|.
```
Let $`r\uparrow1`$. This also handles boundary critical points and all multiplicities without selecting local branches. ◻

</div>

Set $`m=n-1`$. By Gauss–Lucas and the lemma, $`(\mathrm{FP}_m)`$ gives
``` math
\sum_j |f(c_j)|^{1/m}\le m
```
on the unit disk. Apply this to $`R^{-n}f(h+Rz)`$ for a root disk centred at $`h`$ with $`R>0`$. Scaling the critical values back gives <a href="#eq:critical-value-power-budget" data-reference-type="eqref" data-reference="eq:critical-value-power-budget">[eq:critical-value-power-budget]</a>. If $`R=0`$, all critical values vanish. For the linear consequence put $`y_j=|f(c_j)|^{1/m}`$ in the unit-disk normalization and use
``` math
y^{m/(m+1)}\le\frac{my+1}{m+1}\quad(y\ge0).
```
Summation gives $`\sum_j|f(c_j)|^{1/n}\le m`$, and scaling back multiplies this sum by $`R`$. It remains to prove $`(\mathrm{FP}_m)`$ for $`m\le4`$. The same argument works in any degree in which $`(\mathrm{FP}_{n-1})`$ holds.

The stronger exponent controls concentration of the critical values. For $`R>0`$, write $`r_j=|f(c_j)|^{1/n}`$ and $`p=n/(n-1)`$. Then
``` math
\sum_j(r_j/R)^p\le n-1,\qquad
 \#\{j:r_j\ge tR\}\le\frac{n-1}{t^p}\quad(t>0).
```
The counting bound follows by retaining just those summands. Thus a large critical value consumes more of the budget than the linear estimate records; the radial equality family has every $`r_j=R`$. This distributional control still leaves the geometry of the joining paths to be supplied.

<a id="the-three-point-mechanism."></a>

#### The three-point mechanism.

The one-point inequality is $`1-|c_1|^2\le1`$. For two points put $`a=|c_1|`$, $`b=|c_2|`$, and $`d=|1-\overline c_1c_2|\le1+ab`$. The square of the left side of $`(\mathrm{FP}_2)`$ is at most
``` math
2(1+ab)(2-a^2-b^2)\le4(1-a^2b^2)\le4,
```
by Cauchy–Schwarz and $`a^2+b^2\ge2ab`$.

For three points put $`x_i=1-|c_i|^2`$, $`d_{ij}=|1-\overline c_ic_j|`$, and
``` math
S=\sum_{i=1}^3(x_i d_{ij}d_{ik})^{1/3},\qquad
 Q=\sum_i|c_i|^2,\quad E_2=\sum_{i<j}|c_i|^2|c_j|^2,
 \quad s=\sum_i c_i,
```
where $`\{i,j,k\}=\{1,2,3\}`$ in each summand. Hölder and Cauchy–Schwarz give
``` math
S^3\le(3-Q)(d_{12}+d_{13}+d_{23})^2
 \le3(3-Q)(3+Q-|s|^2+E_2).
```
The last expression has an exact nonnegative defect:
``` math
(3-Q)(3+Q-|s|^2+E_2)=9-\Delta,
 \qquad
 \Delta=\frac12\sum_{i<j}(|c_i|^2-|c_j|^2)^2
          +QE_2+(3-Q)|s|^2\ge0.
```
Thus $`S\le3`$. Equality forces equal moduli and $`QE_2=0`$, hence all three points are zero; conversely the zero configuration attains equality. The bound comes from this defect identity, rather than from separately maximising the pairwise factors.

<a id="a-uniform-central-region-in-every-degree."></a>

#### A uniform central region in every degree.

For $`m\ge1`$, let $`|c_i|^2\le a<1`$, with $`a\ge0`$, and put $`L=-\log(1-a)`$. The [uniform-radius theorem](https://github.com/wcook04/plectis-erdos/blob/457e0c74b2666f7fb2d825c967e49e439a600b23/ErdosProblems/Erdos1041/FreePointUniformRadius.lean#L84) gives the actual geometric-mean inequality
``` math
e^L\le1+2L\quad\Longrightarrow\quad
 \sum_{i=1}^m\left(\prod_{j=1}^m|1-\overline c_i c_j|\right)^{1/m}\le m.
```
Its mechanism is an adaptive logarithmic certificate. Write $`H_i=m^{-1}\sum_j\log|1-\overline c_i c_j|`$ and $`D_i=-\log(1-|c_i|^2)`$. For nonnegative caps $`M_i\ge H_i`$, the [checked adaptive theorem](https://github.com/wcook04/plectis-erdos/blob/0d34630e1cc9d2b1ac6edfa7cfdba83b31bdc8fe/ErdosProblems/Erdos1041/LogKernelCentralCertificate.lean#L99) requires only $`\sum_i\Phi(M_i)D_i\le m`$, where $`\Phi(t)=\int_0^1(1-s)e^{st}\,ds`$. The uniform radius gives $`H_i,D_i\le L`$, so $`\Phi(L)L\le1`$ suffices; the displayed exponential condition is exactly this inequality when $`L>0`$, and $`L=0`$ is immediate.

<a id="four-points-require-two-complementary-estimates."></a>

#### Four points require two complementary estimates.

For four points the inequality is again true, with equality only when all points are zero. Its proof divides at $`\max_j|c_j|^2=21/25`$. In the central region put
``` math
h_j=\frac14\log\prod_k|1-\overline c_jc_k|,
 \quad L_j=-\log(1-|c_j|^2),\quad
 E=\frac14\sum_{r\ge1}\frac{|\sum_kc_k^r|^2}{r}.
```
The convergent logarithmic expansion gives $`\sum_jh_j=-E`$ and $`\sum_jh_j^2\le E\,\frac14\sum_jL_j`$. Exact polynomial and Taylor estimates give $`h_j<11/50`$, $`\frac14\sum_jL_j<11/6`$, and $`\Phi(11/50)<6/11`$, where $`\Phi(t)=(e^t-1-t)/t^2`$ is increasing, with $`\Phi(0)=1/2`$. Consequently
``` math
\sum_je^{h_j}\le4-E+\Phi(11/50)\sum_jh_j^2<4
```
when $`E>0`$; when $`E=0`$, all power sums vanish and all four points are zero.

In the outer region put $`x_j=1-|c_j|^2`$ and
``` math
W=(\sum_jx_j)(d_{12}+d_{34})(d_{13}+d_{24})(d_{14}+d_{23}).
```
Hölder applied to the three perfect matchings of four vertices gives $`S_4^4\le8W`$. If $`a`$ is the largest squared radius and $`s`$ is the sum of the other three, Cauchy–Schwarz and AM–GM give
``` math
W\le(4-a-s)
 \left[\frac23\left(6+a+(1+a)s+\frac{s^2}{3}\right)\right]^{3/2}<32
 \qquad(a\ge21/25).
```
For the last inequality the right side decreases in $`a`$; at $`a=21/25`$ its maximum occurs at $`s=(-27+3\sqrt{473})/50`$ and is strictly below $`32`$. Thus $`S_4<4`$ in the outer region. The full polynomial, Taylor and radical certificates for these estimates are given in the public [four-point proof](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/research_corpus/Erdos1041/FreePointZeroInsertionFP4Matching.md); the preceding short defect proof is recorded in the [three-point proof](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/research_corpus/Erdos1041/FreePointMeanInequalityFP3.md).

The complete budget is an ordinary theorem. The scalar concavity step is checked by [formal concavity bridge](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/research_corpus/Erdos1041/FreePointTorusPshReduction.lean#L62) and explained in the earlier [boundary-reduction note](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/research_corpus/Erdos1041/FreePointTorusPshReduction.md); the pointwise polynomial comparison above replaces its plurisubharmonic argument. The four-point companion includes [exact stationary-point slack inequality](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/research_corpus/Erdos1041/FreePointFP4Complete.lean#L69); the logarithmic and calculus estimates are proved above.

The budget guarantees a critical value at most $`R^n`$, but does not force the smaller quintic threshold $`1/M_5`$ below. On the unit radial family all critical values have modulus one, so a uniformly strict improvement is unavailable. Nor does the value budget bound inverse-ray lengths: a path selection or metric comparison is still needed.

<a id="the-degree-five-target-is-now-explicit"></a>

## The degree-five target is now explicit

The degree-five analysis sharpens the two-nearest-spoke threshold. If a critical point $`c`$ satisfies $`|f(c)|\le1/M_n`$, then both straight segments to the two nearest roots remain in $`\{|f|\le1\}`$ and their total length is at most $`2`$. The envelope is obtained by maximising the exact product along the second spoke; at degree five,
``` math
M_5=(1-t_*)(1+t_*)^3\sqrt{16t_*^2-4t_*+1},
 \qquad
 t_*={5\over16}+{3\sqrt{105}\over80},
 \qquad
 {1\over M_5}=0.2760461\ldots.
```
This is an 11-fold improvement over the earlier deep-low threshold, but it does not assert that every quintic has a critical value below this level.

The exact remaining degree-five statement is therefore not “improve the constant” but the following selection problem:

> For every monic quintic with roots in the closed unit disc, there is a critical point $`c`$ with $`|f(c)|\le1`$ and two roots $`a,b`$ such that $`|f|\le1`$ on $`[c,a]\cup[c,b]`$ and $`|c-a|+|c-b|\le2`$.

The public file calls this (SPOKE-5). Together with the existing two-segment reduction it would settle degree five, but (SPOKE-5) is not proved. Coverage experiments put the residual in rapid, nearly simultaneous merging near the regular pentagon: the generic sampled families were covered, whereas the surviving band has every named merge threshold active and $`D`$ near $`1`$. Those percentages locate the work; they are not a theorem.

At the same degree, the terminal connected component admits a sharper area identity. If $`K_t=\{|f|\le t\}`$ is connected and the centred exterior map is
``` math
\psi(\zeta)=t^{1/n}\zeta+a_0+
 \sum_{k\ge1}a_k\zeta^{-k},
```
then Grönwall’s identity gives
``` math
\operatorname{Area}(K_t)=\pi\left(t^{2/n}-
 \sum_{k\ge1}k|a_k|^2\right),
 \qquad
 a_1=-\frac{c_{n-2}}{n\,t^{1/n}}
 \quad\text{after centring}.
```
It replaces a Pólya upper bound at that terminal node, but extending it to proper components and connecting it to the parent theorem remains open. The degree-five statements and their evidence classes are recorded in [`Degree5AssemblyAndSharpenedCuts.md`](https://github.com/wcook04/plectis-erdos/blob/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041/Degree5AssemblyAndSharpenedCuts.md).

<a id="the-no-go-boundaries-force-hub-selection"></a>

## The no-go boundaries force hub selection

The same frontier is useful because it closes off three misleading readings. First, the strict-argmin first-merge hub need not have two-arm length below $`2`$. A degree-five tie-locus witness, moved into the open unit disc, has
``` math
L(c_*)=2.0573432753\ldots>2,
```
with a 50-digit two-instrument reconstruction and a margin about 97 times that of the earlier degree-four witness. This is computational certificate evidence, not an exact rational theorem; the parent remains viable because a different hub at the same configuration supplies the relevant pair.

Second, the aggregate estimate $`\sum_cL(c)\le2(n-1)R`$ is refuted at degree four on an open violating region and at one degree-five witness. Its algebraic factor
``` math
\sum_{k=1}^{n-1}|f(c_k)|^{1/n}\le(n-1)R
```
is proved for $`n\le5`$ in Theorem <a href="#res:critical-value-budget" data-reference-type="ref" data-reference="res:critical-value-budget">15</a> and remains conjectural in higher degrees. The metric factor is not automatic even in the proved degrees. These two boundaries, including the distinction between the surviving algebraic budget and the failed length aggregate, are in [`MinimalHubArmBudgetRefutation.md`](https://github.com/wcook04/plectis-erdos/blob/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041/MinimalHubArmBudgetRefutation.md) and [`SeparatrixAggregateReduction.md`](https://github.com/wcook04/plectis-erdos/blob/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041/SeparatrixAggregateReduction.md).

Third, the origin is not a uniform near-Fekete hub. An exact rational quintic with roots scaled by $`999999/1000000`$ has four of five origin spokes escaping $`\{|f|\le1\}`$ at explicit rational sample points, even though $`1-D=3.19991\cdot10^{-4}`$. Consequently no fixed $`\eta`$-neighbourhood of the Fekete locus can force two contained origin spokes in degree five. The mechanism is angular: the first several Fourier modes can point against different spokes. The certificate is exact for the displayed witness; the claim that the phenomenon persists throughout a limiting family is computational. The full witness and replay route are in [`NearFeketeRadialAngularSplit.md`](https://github.com/wcook04/plectis-erdos/blob/f214a6b45528dc5eefe20ffadc35f2e981627d4c/research_corpus/Erdos1041/NearFeketeRadialAngularSplit.md).

<a id="the-surviving-carrier-and-the-actual-open-endpoint"></a>

## The surviving carrier and the actual open endpoint

These refutations leave a selector as the surviving carrier. On the ray-separated dense class, the public frontier records the canonical open row
``` math
\min_{c\ \mathrm{admissible}} L(c)\le2,
```
where admissibility includes the two inverse-ray arms being contained in the relevant lemniscate component. Its measured values remain below $`2`$ at the refuting configurations, and the existing attachment and lower semicontinuity reductions would turn this row into the parent theorem. No proof of the row is currently available. In particular, the nonzero hub that rescues the origin-spoke witnesses is evidence for the selector, not a universal construction.

The honest current endpoint is therefore a containment selector with three separate obligations: choose the hub, keep both arms inside the component, and control the metric fan-in. The Lean module cited elsewhere in this note checks the Newton value equation, ray-collision avoidance, and root-retention inputs; the new frontier files above are ordinary proof, exact-certificate, and computational research records, not formal authority for (SPOKE-5), the no-go generalisations, or the parent theorem. Keeping those authority boundaries visible is part of making the frontier reusable.

<a id="sec:newton"></a>

# The Newton value equation

Away from the critical set, define the complex Newton field
``` math
N(z)=-\frac{f(z)}{f'(z)} .
```
Let $`z(t)`$ be differentiable with $`z'(t)=N(z(t))`$, and put $`w(t)=f(z(t))`$.

<div id="res:value" class="theorem">

**Theorem 17** (value equation). *$`w'(t)=-w(t)`$.*

</div>

The computation is one line: $`w'=f'(z)\,z'=f'(z)\cdot(-f(z)/f'(z))=-f(z)=-w`$. The kernel checks it as [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L50), together with the differential form of the first integral, [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L64):
``` math
\frac{d}{dt}\Bigl(e^{t}f(z(t))\Bigr)=0,
  \qquad\text{equivalently}\qquad
  f(z(t))=e^{-t}f(z(0)) .
```
Observe what this says about the geometry. The value moves radially inward at exponential rate and never changes argument. The lemniscate $`\{|f|<1\}`$ is therefore forward-invariant, and the flow lines are exactly the preimages of rays from the origin.

<div id="res:ray" class="corollary">

**Corollary 18** (ray separation). *The endpoints of any finite Newton-flow connection lie on the same oriented ray from $`0`$. Consequently, if two critical values lie on distinct positive rays, no Newton-flow saddle connection joins the corresponding critical points.*

</div>

This is checked in consumer form: the kernel accepts the implication from the hypothesis of distinct rays to the absence of a connection. It is the statement the topology needs, and it is a genuine sharpening of the criterion used in the literature.

<a id="sec:arguments"></a>

# Arguments, not moduli

It is tempting to arrange a generic perturbation so that the critical values are pairwise distinct, or that their moduli are pairwise distinct, and to conclude that saddle connections are excluded. Neither is enough.

Two distinct critical values can lie on one ray, and two critical values with distinct moduli certainly can: the ray records the argument, and the modulus is exactly the coordinate the flow contracts. By Corollary <a href="#res:ray" data-reference-type="ref" data-reference="res:ray">18</a> the invariant that excludes connections is the argument. What a perturbation must therefore achieve is pairwise distinct critical-value *arguments*, which is a condition on $`n-1`$ points modulo the circle rather than on their positions in the plane.

The cost of that condition is also checked, and it is small.

<div id="res:locus" class="theorem">

**Theorem 19** (ray-collision locus). *Let $`a\ne b`$ be complex. Every common translation $`\beta`$ for which $`a+\beta`$ and $`b+\beta`$ lie on the same positive ray has the form
``` math
\beta=\frac{ra-b}{1-r},
  \qquad r\in\mathbb{R}_{>0},\ r\ne1 .
```*

</div>

So each pair of critical values contributes a one-real-parameter forbidden locus in the translation plane, given in closed form ([](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L107)). A finite union of such loci has empty interior, which is the shape one wants for an avoidance argument. Turning that into a perturbation of $`f`$ is not immediate: the translation model must be replaced by an actual perturbation of the roots that keeps them inside $`\mathbb{D}`$ and preserves the length slack. That is the first open producer of §<a href="#sec:open" data-reference-type="ref" data-reference="sec:open">12</a>.

<a id="sec:gap"></a>

# A proof gap in the unrestricted argument

The March manuscript’s Proposition 12 claims the following load-bearing statement. For $`u=-\log|f|`$, a connected component $`V`$ of $`\{u>c\}`$ carrying $`m\ge2`$ simple zeros, and the stated regularity and Morse hypotheses, it constructs, for every $`\varepsilon>0`$, an embedded spanning tree $`G_\varepsilon\subset V`$ with
``` math
\operatorname{len}(G_\varepsilon)
 \le\frac1{2\pi}\int_{2\alpha}^{\infty}P_V(t)\,dt+\varepsilon.
\tag{5.1}\label{eq:prop12-bound}
```
The final theorem uses this estimate, so the issue below cannot be bypassed by calling the proposition auxiliary.

At an interior index-one critical point $`p`$, the proof invokes a Morse chart
``` math
u=\mu+x^2-y^2
```
and replaces the saddle by a three-ended neighbourhood having one connected lower cross-section and two connected upper cross-sections. That local model is false as written. Because $`p\in V`$ and $`V`$ is open, a sufficiently small closed disc around $`p`$ lies entirely in $`V`$. In that disc the full Morse chart has four sectors: two components of $`u>\mu`$ and two components of $`u<\mu`$. A global component argument cannot delete one local sector from a disc already contained in $`V`$.

This diagnoses a proof step, not the proposition’s statement. A repair might cut an adjoining regular annulus along a separatrix or regular flow arc before forming the block, retain a four-pronged saddle neighbourhood and change the assembly, or replace the local construction by the ray-cut decomposition proposed below. Any repair must prove that its connector cost can be made arbitrarily small uniformly in the attachment points and that the repaired blocks still assemble to an embedded tree satisfying <a href="#eq:prop12-bound" data-reference-type="eqref" data-reference="eq:prop12-bound">[eq:prop12-bound]</a>. The shorter descriptions of the same three-ended block do not repair the four-sector topology.

Corollary <a href="#res:ray" data-reference-type="ref" data-reference="res:ray">18</a> supplies one independent input for a different route: distinct critical-value arguments exclude saddle-to-saddle Newton connections. It does not itself prove the compact planar decomposition, classify all orbit endpoints or provide the metric gluing estimate. Those are separate problems below.

<a id="sec:finite"></a>

# Finite evidence

A search was run over random monic polynomials with roots in the unit disc. For each sample the region $`\{|f|<1\}`$ was rasterised and shortest grid paths were computed between every pair of roots. The best upper bounds obtained were
``` math
\begin{array}{lrr}
    \text{degree } 5, & 500 \text{ trials}: & 1.1052648928\\
    \text{degree } 6, & 1500 \text{ trials}: & 0.8450414343\\
    \text{degree } 8, & 1500 \text{ trials}: & 0.6203916714\\
    \text{degree } 10, & 1500 \text{ trials}: & 0.4303640486 .
  \end{array}
```
No counterexample candidate was found, and the measured values sit well below the threshold $`2`$. These are grid distances for the sampled configurations: upper bounds on those samples, not bounds over the family. The apparent decrease with degree is a property of the sample, and we draw no conjecture from it. Future searches should target four named failure modes: near-degenerate saddles, thin necks, boundary-critical configurations, and almost-connected separatrices. They should report those diagnostics. Raster paths remain candidate finders, never continuous certificates.

<a id="sec:open"></a>

# Complements and further questions

The dependency chain has five separate gates. A proof, a minimally corrected hypothesis set, or an explicit polynomial or planar counterexample is a decisive answer to any one of them.

<a id="repair-or-refute-the-saddle-block"></a>

## 1. Repair or refute the saddle block

<div id="prob:saddle1041" class="problem">

**Problem 20** (corrected local saddle assembly). Under the hypotheses of Proposition 12, replace the invalid three-ended local model by a four-pronged block or by a block formed after a specified annular cut. Prove that for every $`\eta>0`$ its connector has total Euclidean length below $`\eta`$, uniformly over the selected attachment points, and that the corrected blocks assemble to an embedded tree satisfying
``` math
\operatorname{len}(G_\varepsilon)
 \le\frac1{2\pi}\int_{2\alpha}^{\infty}P_V(t)\,dt+\varepsilon;
```
or give a polynomial or harmonic planar counterexample to that statement.

</div>

The full-disc model $`x^2-y^2`$, an annulus in which lower branches rejoin, two saddles joined by a separatrix and simultaneous saddle levels are mandatory tests. Repeating the one-lower/two-upper assertion does not answer the problem.

<a id="the-compact-ray-cut-decomposition"></a>

## 2. The compact ray-cut decomposition

Let $`p`$ have simple roots, simple nonzero critical points and let $`u=-\log|p|`$. For regular values $`c<T`$, take
``` math
M_{c,T}=\overline{V\cap\{c<u<T\}},
```
and assume explicitly that this is a compact genus-zero surface, its lower boundary is one smooth Jordan curve, its upper boundary consists of $`m`$ smooth root curves, all interior critical points are nondegenerate index-one saddles, the normalised gradient field
``` math
X=\frac{\nabla u}{|\nabla u|^2}=-\frac{p}{p'}
```
is transverse to the level boundaries, and no maximal $`X`$-trajectory has two saddle endpoints.

<div id="prob:reeb1041" class="problem">

**Problem 21** (finite strip decomposition after ray cuts). For every $`\eta>0`$, construct disjoint Morse neighbourhoods $`N_j`$ with $`\sum_j\operatorname{diam}N_j<\eta`$ and a finite set of complete separatrix or regular-flow cuts so that every component of the complement is flow-diffeomorphic to a rectangle
``` math
[a_S,b_S]\times[0,1],\qquad u(\Phi_S(t,s))=t,
```
with connected level sections and no uncut annular component. Give an explicit finite bound $`E(s,m)`$ for the number of strips, or exhibit the minimal missing hypothesis or a counterexample.

</div>

No particular formula such as $`2s+1`$ is presumed. Boundary tangencies, simultaneous levels, branch reunion through an annulus and non-Hausdorff orbit spaces must be handled rather than suppressed.

<a id="metric-fan-in-without-losing-the-coefficient"></a>

## 3. Metric fan-in without losing the coefficient

For a strip $`S`$, write
``` math
\Gamma_t^S=S\cap\{u=t\},\qquad
 P_S(t)=\mathcal H^1(\Gamma_t^S),
```
and let $`k_S`$ be its number of root ends. The flux identity
``` math
\int_{\Gamma_t^S}|\nabla u|\,ds=2\pi k_S
```
gives the average trajectory estimate
``` math
\int_{\Gamma_{t_0}^S}\operatorname{len}(\gamma_x)\,d\mu_{t_0}(x)
 =
 \frac1{2\pi k_S}\int_{a_S}^{b_S}P_S(t)\,dt.
```

<div id="prob:metric1041" class="problem">

**Problem 22** (additive-error strip gluing). Assuming Problem <a href="#prob:reeb1041" data-reference-type="ref" data-reference="prob:reeb1041">21</a>, select trajectories in all strips and connect them through the saddle and root neighbourhoods so that, for every $`\eta>0`$, the resulting embedded tree contains all $`m`$ roots and obeys
``` math
\operatorname{len}(G)
 \le\frac1{2\pi}\int_{2\alpha}^{\infty}P_V(t)\,dt+\eta.
\tag{6.1}\label{eq:metric-fanin1041}
```
The total saddle, annular-cut and root-cap cost must be below $`\eta`$ without a multiplicative loss in $`1/(2\pi)`$.

</div>

For the final strict inequality, use the actual collar slack
``` math
q=\frac1{2\pi}\int_{\alpha}^{2\alpha}P_V(t)\,dt>0
```
and give budgets that keep the perturbation, tree error and transfer cost below fixed fractions of $`q`$. Independently choosing a shortest trajectory in each strip is not enough unless the attachment mismatch is controlled.

<a id="coefficient-perturbation-and-stability"></a>

## 4. Coefficient perturbation and stability

The constant-translation stage is no longer open. Once a finite critical-value family is injective, Lean proves an arbitrarily small translation making every value nonzero and pairwise positive-ray separated ([](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L197)). It also proves the explicit root-retention estimate; a shift below $`\varepsilon`$ keeps all roots in the unit disc when
``` math
((n+1)\varepsilon)^{1/n}+\rho<1
```
([](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L287)). A constant translation cannot separate initially equal critical values.

<div id="prob:perturb1041" class="problem">

**Problem 23** (two-stage generic perturbation with slack). For fixed root discs, compact collar $`K`$, regular levels $`\alpha/2,\alpha,2\alpha,5\alpha/2`$ and collar slack $`q>0`$, prove that an arbitrarily small
``` math
g_{\lambda,\beta}(z)=f(z)+\lambda z+\beta
```
can be chosen so that:

1.  $`f+\lambda z`$ has simple relevant critical points and injective complex critical values;

2.  the checked constant translation $`\beta`$ makes those values nonzero and pairwise ray-separated;

3.  no critical point enters the protected collar or truncation boundary;

4.  the relevant component remains in $`K`$, contains exactly the corresponding perturbed roots and has slack $`q_g>q/2`$; and

5.  root displacement and straight-line transfer back to the original roots consume less than a prescribed fraction of $`q/m`$.

If the one-coefficient perturbation $`\lambda z`$ cannot ensure all five properties, give the smallest additional lower-coefficient direction that can, or an explicit obstruction.

</div>

Finite planar avoidance and the subsequent constant translation must not be relisted as missing; coefficient genericity, component stability and slack stability are the open content.

<a id="the-global-newton-flow-claim-ceiling"></a>

## 5. The global Newton-flow claim ceiling

<div id="prob:globalflow1041" class="problem">

**Problem 24** (relative global Newton-flow theorem). On a compact regular band
``` math
M_{a,b}=\{z:a\le-\log|p(z)|\le b\},
```
prove real-time existence and the identities
``` math
p(z(t))=e^{-(t-t_0)}p(z(t_0)),\qquad
 u(z(t))=u(z(t_0))+t-t_0
```
throughout every maximal orbit; classify both limiting endpoints among the regular boundary, root ends and finite saddle set; and exclude recurrent, accumulating and non-Hausdorff orbit phenomena. Under pairwise ray separation of the critical values, decide whether the flow is Morse–Smale relative to the boundary or whether the strongest valid conclusion is only absence of saddle-to-saddle connections.

</div>

The checked algebra proves the pointwise value equation and the endpoint-ray consumer. It does not supply global solution theory or an orbit-space graph. A positive stronger theorem must give the graph and a finite edge bound; a negative answer should exhibit the simplest ray-separated polynomial carrying the remaining pathology.

Erdős #1041 remains open. Four separate statements are proved above, with different degree ranges, root hypotheses, containment levels and constants. Theorem <a href="#res:low-critical-thirteen-twentyfifths" data-reference-type="ref" data-reference="res:low-critical-thirteen-twentyfifths">2</a> holds in every degree $`n\ge2`$ for squarefree $`f`$ under the single hypothesis $`\mu\le13/25`$, with no condition on where the roots lie, and gives a connector inside $`\{|f|<1\}`$ of length below $`2`$; the regime $`13/25<\mu<1`$ is untouched. Theorem <a href="#res:constant-factor-path" data-reference-type="ref" data-reference="res:constant-factor-path">4</a> drops every threshold and every root hypothesis, and pays for that with the constant $`71/10`$ and the weaker containment level $`\{|f|\le2\mu\}`$; the containment $`\{|f|<1\}`$ with length at most $`5.7`$ needs roots in the open unit disc and $`\mu\le1/2`$, and both fall short of the target constant $`2`$. Theorem <a href="#res:degree-three" data-reference-type="ref" data-reference="res:degree-three">5</a> settles degree three completely for roots in the open unit disc. Theorem <a href="#res:critical-value-separation" data-reference-type="ref" data-reference="res:critical-value-separation">6</a> holds in every degree and is conditional on the critical-value separation $`S`$, with the convenient thresholds $`S=4`$ for $`n\ge3`$, $`S=3`$ for $`n\ge4`$ and $`S=2`$ for $`n\ge6`$ from Corollary <a href="#res:critical-value-thresholds" data-reference-type="ref" data-reference="res:critical-value-thresholds">7</a>. All four are ordinary proofs. Their Lean companions check named numerical, algebraic and power-series steps inside them, the degree-three companion lies outside the pinned formal-source library and carries no kernel receipt in this release, and the univalent branch, the area bounds and the certificate chain remain ordinary mathematics. The source now publicly verifies the Newton kernel, finite ray avoidance and quantitative constant-translation root control; the coefficient perturbation, corrected planar decomposition and metric gluing remain the exact unresolved producers.

<a id="statements-and-declarations"></a>

# Statements and declarations

Lean does not check the exposition, citation choices, or interpretation. This manuscript cites Lean only for the formal statements and proofs that the pinned kernel accepts. The checked core is the Newton value equation, the exponential first integral, the consumer form of ray separation, the finite planar-avoidance theorem, quantitative constant-translation root retention, and the ray-collision parameterisation. The decomposition and length statements of §<a href="#sec:open" data-reference-type="ref" data-reference="sec:open">12</a> are not proved. The diagnosis of Proposition 12 in §<a href="#sec:gap" data-reference-type="ref" data-reference="sec:gap">10</a> concerns its printed local saddle construction; it does not refute the proposition’s statement. The search results of §<a href="#sec:finite" data-reference-type="ref" data-reference="sec:finite">11</a> are computations.

<a id="app:sources"></a>

# Guide to the formal sources

The public `ErdosProblems.Erdos1041.NewtonFlowRaySeparation` module contains the checked source for this note. The search of §<a href="#sec:finite" data-reference-type="ref" data-reference="sec:finite">11</a> is `scripts/search_counterexample.py` in the source package. The declaration table below is pinned to the shared formal-source commit used throughout this problem-note series.

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L34)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L38)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L50)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L64)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L77)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L80)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L84)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L92)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L107)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L127)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L130)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L147)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L152)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L162)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L179)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L197)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L230)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L257)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L287)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L325)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L334)

<a id="checked-declarations-behind-the-translated-quotient-fibre-families."></a>

#### Checked declarations behind the translated quotient-fibre families.

For the translated cubic and quartic quotient families $`f(z)=P((z-h)^q)`$ the metric theorems are ordinary; the kernel checks the cyclic-fibre mean square and the quotient-disk bridge. The fibre norm identity is [fibre mean square](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/CyclicFiberMeanSquare.lean#L21), the strict unit bound is [fibre unit bound](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/CyclicFiberMeanSquare.lean#L37), the quotient roots land in the open disk by [quotient disk bridge](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/CyclicFiberMeanSquare.lean#L60), and the composition vanishes on the fibre by [fibre zero identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos1041/CyclicFiberMeanSquare.lean#L73).

<div class="thebibliography">

9 G. Pólya, *Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zusammenhängende Gebiete*, Sitzungsber. Preuss. Akad. Wiss., Phys.-Math. Kl. (1928), 228–232 and 280–282. T. F. Bloom, *Erdős Problems*, problem 1041. <https://www.erdosproblems.com/1041> P. Erdős, F. Herzog, and G. Piranian, *Metric properties of polynomials*, J. Analyse Math. **6** (1958), 125–148. <https://doi.org/10.1007/BF02790232> S. Ghosh and K. Ramachandran, *Number of Components of Polynomial Lemniscates: A Problem of Erdős, Herzog, and Piranian*, arXiv:2312.13673v1 (2023). <https://arxiv.org/abs/2312.13673> S. Sutherland, *Bad Polynomials for Newton’s Method*, in B. Bielefeld and M. Lyubich (eds.), *Conformal Dynamics Problem List*, Stony Brook IMS preprint (1992), 42–44. <https://www.math.stonybrook.edu/preprints/ims92-7.pdf> `shtuka`, *A Short Path Joining Two Zeros Inside a Polynomial Lemniscate*, manuscript posted 24 March 2026, 48 pp. <https://shtuka123.github.io/1041/main.pdf>. The file at this URL has since been replaced by a shorter partial version that no longer contains Proposition 12; the durable public record of the March version, its defect, and the author’s 26 March 2026 concession is the discussion thread at <https://www.erdosproblems.com/forum/thread/1041>. V. S. Pendyala, *A Degree-Four Lemniscate Path Theorem*, arXiv:2606.24875v1 (2026). <https://arxiv.org/abs/2606.24875>, doi:[10.48550/arXiv.2606.24875](https://doi.org/10.48550/arXiv.2606.24875). V. N. Dubinin, *Some inequalities for polynomials and rational functions associated with a lemniscate*, Zap. Nauchn. Sem. POMI **404** (2012), 83–99; English translation, J. Math. Sci. **193** (2013), no. 1, 45–54, doi:[10.1007/s10958-013-1432-4](https://doi.org/10.1007/s10958-013-1432-4). Theorem 1, printed page 85, assumes a holomorphic function giving a full $`n`$-fold covering of an annulus $`t_1<|w|<t_2`$ and, with $`E`$ the complementary set defined there, states $`(t_2/t_1)^{2/n}\le m(E\cup D)/m(E)`$. This is a Pólya-type area inequality under a covering hypothesis. T. Tao cited it on the Erdős Problem #1041 discussion page, 25 March 2026, for the relative area scaling factor. It is recorded here as a neighbouring result, and no argument in this note uses it; the area input used is the absolute Pólya inequality \[polya1928\]. P. Borwein, *The arc length of the lemniscate $`\{|p(z)|=1\}`$*, Proc. Amer. Math. Soc. (1995), doi:[10.1090/S0002-9939-1995-1223265-3](https://doi.org/10.1090/S0002-9939-1995-1223265-3). Bound $`8\pi en`$ for the level-curve arclength of Erdős #114. A. Eremenko and W. Hayman, *On the length of lemniscates*, Michigan Math. J. **46** (1999), no. 2, 409–415; preprint arXiv:0805.2295. <https://arxiv.org/abs/0805.2295>. Bound $`9.173\,n`$ for the same level-curve arclength. A. Fryntov and F. Nazarov, arXiv:0808.0717 (2008). <https://arxiv.org/abs/0808.0717>. Asymptotically sharp $`2n+o(n)`$ for the level-curve arclength, extremal at $`p(z)=z^n-1`$. The title of this preprint is not recorded in this repository’s prior-art file. T. Tao, *The maximal length of the Erdős–Herzog–Piranian lemniscate in high degree*, arXiv:2512.12455 (December 2025). <https://arxiv.org/abs/2512.12455>. Resolves the Erdős #114 level-curve conjecture for large $`n`$.

</div>
