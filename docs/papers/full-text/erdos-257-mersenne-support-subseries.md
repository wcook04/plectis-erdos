<a id="erdos-257-mersenne-support-subseries"></a>

# Settled Supports and Exact Finite Periods

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Erdős #257 asks whether $`X_A=\sum_{a\in A}(2^a-1)^{-1}`$ is irrational for every infinite $`A\subseteq\mathbb{N}_{>0}`$. It remains open. This note separates the content already proved from the universal endpoint.

For every finite nonempty exponent set $`F`$ and every integer base $`b\ge2`$, the multiplicative order of $`b`$ modulo the reduced denominator of $`\sum_{n\in F}(b^n-1)^{-1}`$ is exactly $`\operatorname{lcm}(F)`$: reduction never collapses the period. For infinite supports, seven structured families are irrational in every base $`b\ge2`$, and periodic integer weights satisfy an irrational-or-base-terminating dichotomy. These are unconditional theorems, not reformulations of universal \#257; their prior-art boundaries are stated where they occur.

The note also records the achievement-set geometry and exact open dichotomy at $`1/2`$, then proves a method limitation on the squarefree support. Its divisor incidence is $`2^{\omega(n)}-1`$, hence odd for every $`n\ge2`$, so the two certificate engines requiring first-block divisibility have no instance there. This does not decide the squarefree value; it names exactly which methods fail and which weaker engine survives.

*Status.* The problem treated here is open, and this note does not close it. Every statement below marked as checked is a proposition that the pinned Lean kernel accepts from the sources this note links to, with no `sorry`, no added axiom, and no unchecked evaluation. That is a claim about the formal statement, not about its mathematical interest, its novelty, or the original problem. The unresolved obligations are named exactly, in their own section, and none of the finite computations, reductions, or no-go results here removes one of them.

<a id="sec:problem"></a>

# The problem

<div id="res:problem" class="problem">

**Problem 1** (Erdős \#257). For every infinite $`A\subseteq\mathbb{N}_{>0}`$, is $`X_A=\sum_{a\in A}\dfrac1{2^a-1}`$ irrational?

</div>

Numbering and status follow [Bloom’s catalogue](https://www.erdosproblems.com/257). Write $`w_{n}=(2^n-1)^{-1}`$. Interchanging sums gives the coordinate this note works in: with the *divisor incidence* $`\operatorname{sc}_A(n)=\#\{d\mid n: d\in A\}`$,
``` math
X_A=\sum_{a\in A}\frac1{2^a-1}=\sum_{n\ge1}\frac{\operatorname{sc}_A(n)}{2^n}.
  \tag{1}\label{eq:incidence}
```
So \#257 is the question of which $`0/1`$ weights make a Lambert series irrational, and every argument below reads the coefficient sequence $`\operatorname{sc}_A`$ rather than $`A`$ itself.

<a id="sec:period"></a>

# Exact period of every finite partial sum

For a finite nonempty $`F\subseteq\mathbb{N}_{>0}`$ and an integer $`b\ge2`$, write
``` math
x_F(b)=\sum_{n\in F}\frac1{b^n-1}=\frac{N_F}{D_F}
  \qquad (\gcd(N_F,D_F)=1,\ D_F>0).
```

<div id="res:period" class="theorem">

**Theorem 2** (finite-period noncollapse). *The reduced denominator is coprime to $`b`$, and
``` math
\operatorname{ord}_{D_F}(b)=\operatorname{lcm}\{n:n\in F\}.
```
Thus cancellation in the numerator never lowers the base-$`b`$ period below the least common multiple of the selected exponents.*

</div>

The general theorem is [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L5091); the reduced-denominator and coprimality forms are [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L5246) and [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L5061). This is an unconditional statement about every finite support, not a bounded table of examples and not an implication with an open hypothesis. It does not settle any infinite support. Denominator-period control is part of the classical engine behind Erdős’s 1948 argument; whether this exact sharp noncollapse statement appears in the literature has not been assessed, so no novelty claim is made here.

<a id="sec:map"></a>

# The map of settled supports

| Support $`A`$ | Bases | Authority |
|:---|:---|:---|
| all of $`\mathbb{N}_{>0}`$ | every $`b\ge2`$ | Erdős 1948; [checked here](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L8000) |
| primes | $`b=2`$ (and $`b\ge2`$) | Tao–Teräväinen \[taoteravainen2025\]; not formalised here |
| prime powers | $`b=2`$ | *ibid.*, stated as a remark; not formalised here |
| factorials $`\{n!\}`$ | every $`b\ge2`$ | [checked here](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L5754) |
| powers of two $`\{2^k\}`$ | every $`b\ge2`$ | [checked here](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L5762) |
| multiples of a fixed $`d`$ | every $`b\ge2`$ | [checked here](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L8775) |
| a residue class | every $`b\ge2`$ | [checked here](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L11344) |
| the odd numbers | every $`b\ge2`$ | [checked here](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L11358) |
| eventually periodic | every $`b\ge2`$ | [checked here](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L11276) |
| pairwise coprime, $`\sum_{a\in A}a^{-1}<\infty`$ | every $`b\ge2`$ | [checked here](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L10448) |
| squarefree numbers | — | **Open**; outside two divisibility-first engines here (Section <a href="#sec:squarefree" data-reference-type="ref" data-reference="sec:squarefree">4</a>) |
| arbitrary infinite $`A`$ | — | **Open** (Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a>) |

Three things about this table are worth stating plainly.

First, the families checked here are proved for *every* integer base $`b\ge2`$, not only base $`2`$; the general statement is [the base-$`b`$ full-support theorem](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L8717) and the family results specialise it. Prior art is acknowledged rather than absorbed: for eventually periodic *rational* coefficient sequences Luca and Tachiya prove a broader theorem by different methods \[lucatachiya\], and no priority is claimed for the formalised versions.

Second, the two method families are *complementary, not nested*. The analytic method of \[taoteravainen2025\] reaches the primes and prime powers, which are neither eventually periodic nor pairwise coprime with summable reciprocals, so they are outside every row proved here. The rows proved here — factorials, powers of two, residue classes — are not “sufficiently similar to the primes” in the sense that method needs. Neither list contains the other, and their union does not exhaust the infinite supports.

Third, none of this approaches the universal statement. A list of settled families, however long, is a list; Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a> quantifies over all infinite $`A`$, and the gap between the two is not narrowed by adding rows.

<div id="res:signed" class="theorem">

**Theorem 3** (periodic signed-weight dichotomy). *Let $`u:\mathbb{N}_{>0}\to\mathbb Z`$ be periodic and $`b\ge2`$. Then
``` math
\sum_{n\ge1}\frac{u(n)}{b^n-1}
```
is irrational, or some power of $`b`$ times this value is an integer.*

</div>

This is [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L13847); the source also proves the full-block certificate supply used by the theorem. For nonnegative support indicators the terminating alternative is excluded in the settled rows above. For genuinely mixed signs it is not excluded in general, so Theorem <a href="#res:signed" data-reference-type="ref" data-reference="res:signed">3</a> is a dichotomy rather than a blanket irrationality theorem. Prior art for this mixed-sign periodic formulation has not been assessed.

<a id="sec:squarefree"></a>

# A support outside two certificate engines

Let $`A_{\mathrm{sf}}=\{d\ge2: d\text{ squarefree}\}`$. This is a natural support of density $`6/\pi^2`$ — far denser than the primes, and not periodic.

<div id="res:sfcount" class="theorem">

**Theorem 4** (squarefree divisor incidence). *For every $`n\ge1`$ the number of squarefree divisors of $`n`$ is $`2^{\omega(n)}`$, where $`\omega(n)`$ is the number of distinct prime factors, and hence
``` math
\operatorname{sc}_{A_{\mathrm{sf}}}(n)=2^{\omega(n)}-1 .
```
In particular $`\operatorname{sc}_{A_{\mathrm{sf}}}(n)`$ is *odd* for every $`n\ge2`$.*

</div>

The count is [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L53), the incidence formula is [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L70), and the parity conclusion is [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L100). The proof is the bijection between squarefree divisors of $`n`$ and subsets of its prime factors ([Lean](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L30)), so the count is $`2^{\omega(n)}`$; removing $`d=1`$ leaves an odd number whenever $`\omega(n)\ge1`$.

<div id="res:blind" class="corollary">

**Corollary 5** (two block-certificate engines cannot see this support). *For the squarefree support and every even base $`b\ge2`$, the digitwise and carry-aware block-certificate schemas have no instance already at precision $`q=b^2`$. Their first-block divisibility condition would require $`b`$ to divide the odd coefficient $`\operatorname{sc}_{A_{\mathrm{sf}}}(N+1)`$.*

</div>

The current source contains direct Lean declarations for both exclusions. They postdate this problem-note series’ pinned hyperlink snapshot, so they are not hyperlinked here. The argument does *not* reach the divisibility-free low-carry engine, odd bases, the support with $`1`$ adjoined, or methods based on lcm gaps or near-integer estimates.

We are deliberate about what this does and does not say.

*It does not say* that $`X_{A_{\mathrm{sf}}}=\sum_{d\ \mathrm{squarefree},\,d\ge2}(2^d-1)^{-1}`$ is rational, or that it is hard, or that it is irrational. That value’s status is open and this note does not move it.

*It does say* that two fully specified proof schemas provably cannot certify one natural support at even bases, for a reason internal to the support rather than to the search. The obstruction is a parity accident rather than a scaling one: the shifted coefficient $`2^{\omega(n)}`$ still satisfies $`2^{\omega(n)}\le n`$ ([checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L117)), so it remains inside the coefficient range those arguments require. Repairing the parity is therefore not obviously impossible — but a repaired first block does not discharge the remaining tail and head obligations, and we make no claim that it does.

<a id="sec:geometry"></a>

# Achievement-set geometry

The set of all values obtainable from the base-$`2`$ Mersenne weights is the achievement set $`\mathcal A=\{\sum_{n\ge1}\varepsilon_nw_{n}:\varepsilon_n\in\{0,1\}\}`$.

<div id="res:geometry" class="theorem">

**Theorem 6** (geometry of $`\mathcal A`$). *$`\mathcal A`$ is compact, perfect, totally disconnected and nowhere dense, and has Lebesgue measure $`1`$.*

</div>

Checked as [perfect](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/GreedyAchievementSet.lean#L1620), [totally disconnected](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/GreedyAchievementSet.lean#L1636), [nowhere dense](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/GreedyAchievementSet.lean#L1645), and [of measure one](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/GreedyAchievementSet.lean#L996). The strict-tail Cantor geometry is recorded by Kovač and Tao; no novelty is claimed for the formalised refinements. Membership is equivalent to survival of the greedy expansion at every level ([Lean](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/GreedyAchievementSet.lean#L1445)), and exact rational death certificates prove non-membership: $`3/4\notin\mathcal A`$ ([Lean](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/GreedyAchievementSet.lean#L1748)).

<a id="sec:hereditary"></a>

## Rigidity is hereditary

Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a> quantifies over *every* infinite support, so it matters whether the base-$`2`$ coding survives deleting weights. It does, and the argument is short. For any set $`J`$ of future offsets, write $`T_J(n)=\sum_{k\in J}w_{n+k+1}`$ for the tail restricted to $`J`$.

<div id="res:hereditary" class="theorem">

**Theorem 7** (hereditary strict superincreasingness). *For every $`J\subseteq\mathbb{N}`$ and every $`n\ge1`$, $`T_J(n)<w_{n}`$. Consequently the digit map is injective on strings supported in $`J`$: every Mersenne subseries retains unique binary coding.*

</div>

Checked as [the hereditary inequality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L27) and [injectivity on a chosen support](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L51), with summability of the restricted tail at [Lean](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L21). The coding is stated on the subtype of [digit strings vanishing off $`J`$](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L42), evaluated by the [restricted digit map](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L46), so the statement is about the subseries itself rather than a projection of the full one. The content is that strict superincreasingness is inherited by *arbitrary* subfamilies, not merely by tails: deleting weights can only shrink $`T_J(n)`$, which already sits below $`w_{n}`$ at the full support. So no choice of infinite $`A`$ escapes the rigidity used throughout this note, and a counterexample to \#257 cannot be sought by weakening the coding. This constrains where a counterexample could live; it does not produce one, and it decides no value.

<a id="sec:half"></a>

# The half-value dichotomy

A rational point of $`\mathcal A`$ attained by an infinite support would refute Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a>. The distinguished candidate is $`1/2`$.

<div id="res:half" class="theorem">

**Theorem 8** (exact dichotomy at $`1/2`$). *$`1/2\in\mathcal A`$ if and only if the canonical greedy expansion of $`1/2`$ omits infinitely many exponents. Moreover no finite support has value $`1/2`$, so membership would automatically produce an *infinite* support of rational value, and hence a counterexample to universal \#257.*

</div>

The equivalence is [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/GreedyAchievementSet.lean#L2514), and the finite-support exclusion is [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfCarryReachability.lean#L589).

This is an equivalence, and we mark it as such rather than as progress: both sides are open, and proving them equivalent does not decide either. It is included because it fixes what a counterexample would have to look like, and because the negative branch is genuinely one-sided — non-membership is witnessed by a finite fatal gap and is therefore semi-decidable, whereas membership is an infinite conjunction that no finite computation certifies. Computing the greedy orbit further can only ever raise a lower bound on where death could occur; it cannot establish survival.

<a id="sec:ask"></a>

# What we need from a mathematician

Three points in this development stop for mathematical rather than engineering reasons. Each is set out below as a specification: the statement wanted, what is already checked around it, which kind of answer would help most, and exactly what would follow from one.

Two remarks apply to all three. Each item is self-contained; answering one needs no engagement with the other items, with the Lean sources, or with the rest of this note, and an answer in ordinary mathematics is what is being asked for. And a negative answer is worth as much as a positive one: a proof that a named route cannot work, or a reference showing it is a known dead end, would be acted on by withdrawing the route from this note rather than by defending it.

<a id="sec:ask:univ"></a>

## A method reaching a support outside both lists

*Statement wanted.* An infinite $`A\subseteq\mathbb{N}_{>0}`$, with a proof that $`X_A`$ is irrational, such that $`A`$ is not eventually periodic, is not pairwise coprime with $`\sum_{a\in A}a^{-1}<\infty`$, and is neither the primes nor the prime powers; better, a theorem covering an infinite class of such $`A`$. Every family checked here is produced, directly or after a base change, by one engine, whose only hypothesis is that for each precision $`q`$ the incidence sequence $`\operatorname{sc}_A`$ admits a block certificate. That hypothesis is the premise of [irrational erdos support series of weighted coeff certificates](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L8703) and of its carry-aware form [checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L9053). A method that does not factor through certificates at all is equally admissible, and would be more informative.

*Already checked.* The reduction from irrationality to certificate supply is proved for every base $`b\ge2`$; the supply itself, for a general $`A`$, is what is missing, and the theorem statements say so. The supports for which it has been produced are the rows of Section <a href="#sec:map" data-reference-type="ref" data-reference="sec:map">3</a>, and that section also records that they neither contain nor are contained in the primes and prime powers of \[taoteravainen2025\]. Two constraints on any answer are already fixed: every finite partial sum has base-$`b`$ period exactly the least common multiple of its exponents (Theorem <a href="#res:period" data-reference-type="ref" data-reference="res:period">2</a>), and strict superincreasingness is inherited by every subfamily (Theorem <a href="#res:hereditary" data-reference-type="ref" data-reference="res:hereditary">7</a>), so no counterexample can be obtained by weakening the binary coding.

*What would help most.* A reason no single method can reach every infinite $`A`$: for instance an infinite $`A`$ whose series is irrational but which provably admits no certificate of the form above. That would say the engine has the wrong shape rather than too little fuel, and it is the answer we are least able to produce ourselves. Next best, a construction reaching one support outside both lists. A reference doing either is worth as much as doing it.

*If it were answered.* Neither answer closes Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a>. A construction adds one row to Section <a href="#sec:map" data-reference-type="ref" data-reference="sec:map">3</a> and settles only the class it reaches; as that section says, a list of families does not approach a universal statement. A no-single-method result settles no case of the problem at all, and would still be the more useful of the two, because it would say which programmes to abandon.

<a id="sec:ask:sf"></a>

## The squarefree support, without first-block divisibility

*Statement wanted.* Decide $`X_{A_{\mathrm{sf}}}=\sum_{n\ge1}\bigl(2^{\omega(n)}-1\bigr)2^{-n}`$ by an argument that never requires a first block of coefficients to be divisible by the base. Writing $`f(n)=2^{\omega(n)}-1`$, the engine that survives Corollary <a href="#res:blind" data-reference-type="ref" data-reference="res:blind">5</a> asks, for every $`q\ge1`$, for $`N`$, $`K\le L`$ and $`C`$ with
``` math
\sum_{r=K+1}^{L}f(N+r)\,2^{L-r}\le C,
  \qquad
  V=\Bigl(\sum_{r=1}^{K}f(N+r)\,2^{K-r}\Bigr)\bmod 2^{K},
```
some nonzero coefficient beyond $`N+L`$, and
``` math
q\bigl(V\cdot 2^{L-K}+C+N+L+2\bigr)<2^{L}.
```
Nothing is asked of the first block except that its carry residue $`V`$ be small enough to be absorbed. That premise is the hypothesis of [irrational coeff series of weighted coeff low carry block certificates](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/CertificateKernel.lean#L14707).

*Already checked.* The incidence identity $`f(n)=2^{\omega(n)}-1`$ and its oddness for every $`n\ge2`$ (Theorem <a href="#res:sfcount" data-reference-type="ref" data-reference="res:sfcount">4</a>), and the resulting exclusion of the two divisibility-first engines at every even base (Corollary <a href="#res:blind" data-reference-type="ref" data-reference="res:blind">5</a>). The growth envelope this engine needs, $`f(n)\le n`$, follows from the bound $`2^{\omega(n)}\le n`$ recorded in Section <a href="#sec:squarefree" data-reference-type="ref" data-reference="sec:squarefree">4</a>, so the coefficient sequence is admissible and only the certificate supply is missing. The value itself is open in both directions; nothing here bears on which way it goes.

*What would help most.* A reference. The function $`2^{\omega}`$ is standard, and $`\sum_{n\ge1}2^{\omega(n)}2^{-n}`$ differs from $`X_{A_{\mathrm{sf}}}`$ by $`\sum_{n\ge1}2^{-n}=1`$, so either determines the other; if that Lambert-type series has already been treated, the pointer retires this item outright. Failing that, a construction: an explicit supply of low-carry certificates for $`f`$, or any analytic route to the value.

*If it were answered.* Irrationality of $`X_{A_{\mathrm{sf}}}`$ closes the open row in Section <a href="#sec:map" data-reference-type="ref" data-reference="sec:map">3</a> and item 2 of Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">8</a>. It does not touch Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a>, which quantifies over all infinite supports. Rationality would answer Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a> in the negative, the squarefree numbers being infinite; we have no evidence for that, and record it only because the item is two-sided.

<a id="sec:ask:half"></a>

## The two surviving cells at the half value

By Theorem <a href="#res:half" data-reference-type="ref" data-reference="res:half">8</a>, $`1/2\in\mathcal A`$ exactly when the greedy expansion of $`1/2`$ omits infinitely many exponents. Suppose it does not. In the coordinates this development works in, the expansion is then eventually right and has a last non-right transition at some rank $`D\ge13`$ ([checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfCylinderLastProducerContradiction.lean#L178)), of one of two kinds. The first kind is excluded unconditionally ([checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfCylinderLastProducerContradiction.lean#L250)). The second carries an integer $`c(D)`$, its producer carry, and the surviving obligation is that the complete future divisor-incidence tail from row $`2D+2`$ lies strictly below $`c(D)`$. That tail is nonnegative, so a cell with $`c(D)<0`$ cannot be settled by the comparison and has to be excluded outright. Cell $`-3`$ has been excluded ([checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfCylinderLastProducerContradiction.lean#L315)); cells $`-2`$ and $`-1`$ have not.

*Statement wanted.* The tail comparison at every last middle transition with $`D\ge13`$ and $`c(D)\ne-3`$. That statement is [seam middle producer tail escape except neg three](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfCylinderLastProducerContradiction.lean#L54), and it contains three separable pieces of work.

1.  Cell $`-2`$ does not occur. What is checked is a conditional bound: when the lazy support — the finite word below $`D`$ together with every rank above $`D`$ — has value below $`1/2`$, a cell $`-2`$ forces its divisor-incidence tail at row $`2D+2`$ below $`2`$ ([Lean](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfCylinderFinalMiddleTailSocket.lean#L56)). It is therefore enough to show that same tail is at least $`2`$, which is done whenever $`D\not\equiv2\pmod3`$ ([Lean](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfFinalMiddlePhaseSieve.lean#L50)). A further sieve through rank $`26`$ leaves $`412`$ joint residue classes modulo $`2730`$ ([Lean](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfFinalMiddlePhaseSieve.lean#L2050)), and those are not excluded.

2.  Cell $`-1`$ does not occur. The same conditional bound holds with threshold $`3`$ ([Lean](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfCylinderFinalMiddleTailSocket.lean#L74)), so a tail of at least $`3`$ would settle it. No comparable sieve is recorded for this cell.

3.  The comparison itself at every remaining cell: at every $`c(D)\ge0`$, and at any cell below $`-3`$ should one occur. A cruder sufficient form asks only $`c(D)>2\sqrt{2D+2}+4`$ ([Lean](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfCylinderLastProducerContradiction.lean#L84)).

*What would help most.* Item 3, proved or refuted. Items 1 and 2 are finite-looking and would shrink the obligation, but neither decides anything on its own. A demonstration that the comparison fails at infinitely many middle transitions would show the route cannot work, and we would record that here.

*If it were answered.* The three together give $`1/2\in\mathcal A`$ ([checked](https://github.com/wcook04/plectis-lean-erdos249-257/blob/571ec44f2aad98b44d51bdf607b70b33fd2079d0/Erdos249257/HalfCylinderLastProducerContradiction.lean#L387)), and by Theorem <a href="#res:half" data-reference-type="ref" data-reference="res:half">8</a> the support realising it is infinite, so Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a> would be answered in the negative. We attach no likelihood to that outcome: the hypothesis is open, and its failure would prove nothing about Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a> in either direction. Taken singly the three settle nothing: items 1 and 2 close one branch each and decide no value, and item 3 leaves both cells standing. A proof that $`1/2\notin\mathcal A`$ would retire this item as well, and by Theorem <a href="#res:half" data-reference-type="ref" data-reference="res:half">8</a> it would take the form of a finite fatal gap in the greedy orbit.

<a id="sec:open"></a>

# What remains open

1.  Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">1</a> itself, for arbitrary infinite $`A`$. The map in Section <a href="#sec:map" data-reference-type="ref" data-reference="sec:map">3</a> is a list of families and does not approach a universal statement.

2.  Irrationality of $`X_{A_{\mathrm{sf}}}`$ for the squarefree support. Section <a href="#sec:squarefree" data-reference-type="ref" data-reference="sec:squarefree">4</a> closes one method against it and supplies no replacement.

3.  Membership of $`1/2`$ in $`\mathcal A`$. Theorem <a href="#res:half" data-reference-type="ref" data-reference="res:half">8</a> makes it exactly equivalent to infinitely many greedy skips; neither side is proved.

4.  Which supports the analytic method of \[taoteravainen2025\] reaches. The authors name this themselves and do not pursue it; it is, in our view, the most valuable open question in the immediate neighbourhood of \#257, and it is not one this development is currently equipped to answer.

<a id="statements-and-declarations"></a>

# Statements and declarations

This manuscript is authored exposition, not proof authority. The linked Lean snapshot is authoritative only for its exact propositions; kernel checking establishes that a proposition was proved, not that it is interesting, novel, or sufficient. Results attributed to Tao and Teräväinen, to Luca and Tachiya, and to Kovač and Tao are cited from the literature and are not formalised here. Erdős Problem #257 remains open.

<div class="thebibliography">

9 T. Tao and J. Teräväinen, *Quantitative correlations and some problems on prime factors of consecutive integers*, arXiv:2512.01739 (submitted December 2025, revised April 2026). Proves $`\sum_{n\ge1}\omega(n)/2^n=\sum_{p}(2^p-1)^{-1}`$ irrational, settling the prime-support case of \#257; remarks that the method also gives the prime-power support and every integer base $`b\ge2`$. K. Pratt, *The irrationality of a prime factor series under a prime tuples conjecture*, arXiv:2409.15185. F. Luca and Y. Tachiya, *Irrationality of Lambert series associated with a periodic sequence*. P. Erdős, *On arithmetical properties of Lambert series*, J. Indian Math. Soc. 12 (1948), 63–66. T. Bloom, *Erdős Problems*, <https://www.erdosproblems.com/257>.

</div>
