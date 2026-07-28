<a id="erdos-1049-rational-base-lambert"></a>

# Multiplicative Obstructions at Base 3/2

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Let $`F(t)=\sum_{n\ge1}(t^{n}-1)^{-1}`$. At the rational base $`3/2`$ we prove exclusions for the approach to irrationality by integer linear forms, and formalise them in Lean. Rowwise content scales the analytic error and the exterior determinant by exactly the same factors, including the absolute determinant height, so a local divisor supplied only by the two row contents is paid for by exactly the same factor in the Archimedean determinant height. Homogeneous specialisation at $`(3,2)`$ sees the constant endpoint modulo $`3`$ and the top endpoint modulo $`2`$, so unit endpoints exclude both primes from any common multiplier. Together: when one entry of a coefficient pair has a unit top endpoint and the other a unit constant endpoint, neither rowwise scalar content nor a common multiplier of the two specialised evaluations can manufacture the two local primes required at $`3/2`$. The missing local gain must therefore survive primitive normalisation. What remains is a growing-rank additive kernel cancelling both endpoint jets in both specialised coefficient sequences while preserving a nonzero, sufficiently small remainder; we count the four-jet target exactly and prove the concrete sufficient threshold $`n\ge 4R+2S`$ at positive bottom depth.

We also record what the elementary route costs. Erdős’s argument for the irrationality of $`\sum_{n\ge1}c(n)b^{-n}`$ at an integer base $`b\ge2`$ proceeds by clearing denominators at a cut level and trapping a positive integer below $`1`$. At a rational base $`r/s`$ with $`s\ge2`$ the same clearing leaves a factor $`s^{N+1}`$ behind. Writing a coordinatewise corridor for the surviving arithmetic, we prove that a corridor forces $`s^{N+K+1}<r(N+K)`$, and that at the base $`3/2`$ this is impossible once the shift and the cleared window are both nonempty. We also prove the exact denominator-cleared tail recurrence $`U_{N+1}=rU_N-Bc(N+1)s^{N+1}`$ and the bound $`2^{N+1}\le Bc(N+1)s^{N+1}`$ for $`s\ge2`$ and positive data, against the exact collapse of that term to $`Bc(N+1)`$ at $`s=1`$. The height criterion of Bundschuh and Väänänen (1994), which settles a restricted family of rational bases containing $`7/2`$, is used as an external theorem. We formalise the complete elementary Archimedean height inequality required at $`7/2`$, while leaving the source theorem’s analytic irrationality argument external. Separately we check polynomial bounds on the denominator exponents of a homogenised Padé construction, with the analytic remainder left untouched.

Problem #1049 is open, and nothing here decides it. The results are exclusions of particular constructions, not statements about the arithmetic nature of any value: we do not prove irrationality at $`3/2`$, at any other rational base, or in the unrestricted problem.

<a id="sec:problem"></a>

# Introduction

Let $`t>1`$ be a rational number and let $`\tau(n)`$ count the divisors of $`n`$. Erdős Problem #1049 asks whether
``` math
F(t)=\sum_{n\ge1}\frac{1}{t^{n}-1}=\sum_{n\ge1}\frac{\tau(n)}{t^{n}}
```
is irrational \[erdos1988, p. 102\]. The two forms agree by expanding $`(t^{n}-1)^{-1}=\sum_{k\ge1}t^{-nk}`$ and collecting the terms with the same exponent, the coefficient of $`t^{-m}`$ being the number of divisors of $`m`$. The question is a conjecture of Chowla; Erdős proved it for every integer $`t\ge2`$ \[erdos1948\]. Numbering and status follow Bloom’s catalogue \[erdosproblems\]. For non-integer rational $`t`$ the problem is open.

Write $`t=r/s`$ in lowest terms with $`r>s\ge1`$, so that $`s=1`$ is exactly the integer case Erdős settled. The smallest resistant explicit base is $`t=3/2`$. A published height criterion of Bundschuh and Väänänen \[bv1994\] settles a family of rational bases restricted by a height condition; that family contains $`7/2`$ and does not contain $`3/2`$. Between the two lies the question this note is about: what exactly stops the integer-base argument from running at $`3/2`$?

<a id="relation-to-prior-work."></a>

#### Relation to prior work.

The statement of Problem #1049 has been formalised before, as a conjecture with an unfilled proof, in the *Formal Conjectures* collection \[formalconjectures1049\]. That is a statement of the question; the present note formalises propositions about the clearing argument, and neither answers it. Erdős’s positive-integer theorem of 1948 \[erdos1948\] sits inside a larger integer-base literature. In 1991 Borwein proved the irrationality of shifted series $`\sum_{n\ge1}(t^{n}+w)^{-1}`$ at integer bases, for suitable rational $`w`$, by Padé approximation rather than by digit clearing \[borwein1991\]. In 2001 Van Assche recovered the integer-base irrationality and an irrationality-measure bound using little $`q`$-Legendre Padé approximants \[vanassche2001, Thm. 1\], and in 2013 Vandehey completed the elementary digit method for negative integer bases and bounded coefficient sequences \[vandehey2013, Thm. 1.2\]. All three retain an integer base. In 2004 Zudilin obtained integer-base irrationality-exponent estimates for $`q`$-harmonic series on a parameter cone, by way of Heine’s basic transform and a permutation group \[zudilin2004\]; the coefficient polynomials specialised in Section <a href="#sec:endpoints" data-reference-type="ref" data-reference="sec:endpoints">3</a> are those of that construction. The neighbouring problem of Lambert subseries $`\sum_{n\in A}(t^{n}-1)^{-1}`$ over a restricted index set $`A`$ is treated by Kovač and Tao \[kovactao2024\]. The rational non-integer progress relevant here is instead the height criterion of Bundschuh and Väänänen \[bv1994\]. No claim of priority is made for anything below, which concerns the formal status of an argument rather than a new theorem about $`F(t)`$.

<a id="the-integer-base-argument-in-outline."></a>

#### The integer-base argument, in outline.

Suppose $`F(b)=p/q`$. Cut the series at a level $`N`$, multiply by $`q b^{N}`$, and subtract the cleared prefix. What remains is a positive integer, since every term of the prefix has been cleared and the tail is positive; and it is smaller than $`1`$, since the tail of a geometric-type series is small. A positive integer below $`1`$ does not exist. The argument is elementary and it is sensitive in exactly one place: the clearing must remove every denominator.

At $`\beta=r/s`$ the term $`c(n)\beta^{-n}`$ is $`c(n)s^{n}/r^{n}`$. Clearing the power of $`r`$ leaves the numerator factor $`s^{n}`$ in place. That factor is invisible when $`s=1`$ and grows geometrically when $`s\ge2`$. At $`3/2`$ it is $`2^{n}`$.

<a id="the-shortfall-at-32."></a>

#### The shortfall at $`3/2`$.

The elementary route and the linear-form route are both examined below. For the coordinatewise clearing scheme the leftover is the forcing term, of size at least $`2^{N+1}`$ once the data are positive (Theorem <a href="#res:forcing" data-reference-type="ref" data-reference="res:forcing">12</a>), and the scheme itself is excluded at $`3/2`$ once the shift and the cleared window are both nonempty (Theorem <a href="#res:nocorridor" data-reference-type="ref" data-reference="res:nocorridor">10</a>). For the linear-form constructions the shortfall is the $`2`$-adic and $`3`$-adic gain that has to remain after the coefficient rows have been divided by their contents (Section <a href="#sec:primitive" data-reference-type="ref" data-reference="sec:primitive">2</a>). Each multiplicative device examined here for supplying that gain is excluded: rowwise content is exactly neutral, since it scales the exterior determinant and its absolute height by the same factor (Theorem <a href="#res:content" data-reference-type="ref" data-reference="res:content">1</a>), and unit endpoints keep both $`2`$ and $`3`$ out of any common multiplier of the two specialised evaluations (Theorem <a href="#res:endpoints" data-reference-type="ref" data-reference="res:endpoints">2</a> and Proposition <a href="#res:commonmult" data-reference-type="ref" data-reference="res:commonmult">3</a>). Corollary <a href="#res:nomult" data-reference-type="ref" data-reference="res:nomult">4</a> states the two together. Separately, the scalar parameter margin is negative under the assumed source inequality (Theorem <a href="#res:scalar" data-reference-type="ref" data-reference="res:scalar">6</a>). The device pursued here instead is additive: an integer relation among rows that cancels the endpoint jets. Theorem <a href="#res:jetkernel" data-reference-type="ref" data-reference="res:jetkernel">5</a> shows that a nonzero relation with coefficients in $`\{-1,0,1\}`$ cancelling all four jets exists whenever the bottom depth is positive and the number of coefficient pairs is at least $`4R+2S`$. It does not show that the resulting combination has a nonzero polynomial pair or a nonzero remainder, which is what Problem <a href="#prob:kernel" data-reference-type="ref" data-reference="prob:kernel">15</a> asks for. Sections <a href="#sec:sevenhalves" data-reference-type="ref" data-reference="sec:sevenhalves">6</a> and <a href="#sec:pade" data-reference-type="ref" data-reference="sec:pade">7</a> record two external routes and what each leaves unproved at $`3/2`$.

<a id="sharpness."></a>

#### Sharpness.

Two questions of scope are worth isolating. The corridor bound of Theorem <a href="#res:corridorbound" data-reference-type="ref" data-reference="res:corridorbound">8</a> is exponential on the left and linear on the right, so for a fixed numerator and any $`s\ge2`$ a corridor can survive only for bounded $`N+K`$; the base $`3/2`$ is the case in which the crossing has already happened at the smallest admissible window, which is why the exclusion there holds for all $`N\ge1`$ and $`K\ge1`$ with no further restriction. The height criterion of \[bv1994\] is restricted by a height condition satisfied at $`7/2`$ and not at $`3/2`$, so the two bases are separated by that criterion rather than by anything proved here.

*Status.* The problem treated here is open, and this note does not close it. Every statement below marked as checked is a proposition that the pinned Lean kernel accepts from the sources this note links to, with no `sorry`, no added axiom, and no unchecked evaluation. That is a claim about the formal statement, not about its mathematical interest, its novelty, or the original problem. The unresolved obligations are named exactly, in their own section, and none of the finite computations, reductions, or no-go results here removes one of them.

| Statement | Status | Treatment here |
|:---|:---|:---|
| Irrationality of $`F(3/2)`$ | Open | Not proved, and no partial result here bears on it. |
| Irrationality at some rational non-integer base | Proved elsewhere | The height criterion of \[bv1994\]; cited, not formalised. |
| Row content is neutral for the local-to-Archimedean balance | Proved here | Theorem <a href="#res:content" data-reference-type="ref" data-reference="res:content">1</a>, including the absolute determinant height. |
| Homogeneous endpoint residues at $`(3,2)`$ | Proved here | Theorem <a href="#res:endpoints" data-reference-type="ref" data-reference="res:endpoints">2</a>. |
| Common multiplier of the two specialised evaluations avoids $`2`$ and $`3`$ | Proved here | Proposition <a href="#res:commonmult" data-reference-type="ref" data-reference="res:commonmult">3</a>; under unit endpoint hypotheses. |
| No multiplicative local gain at $`3/2`$ | Deduced here | Corollary <a href="#res:nomult" data-reference-type="ref" data-reference="res:nomult">4</a>; an ordinary deduction from the two preceding rows, not separately formalised. |
| Four-jet collision at $`n\ge4R+2S`$ | Proved here | Theorem <a href="#res:jetkernel" data-reference-type="ref" data-reference="res:jetkernel">5</a>; sufficient, at positive bottom depth. |
| Scalar-cone product-formula margin | Negative under source input | Theorem <a href="#res:scalar" data-reference-type="ref" data-reference="res:scalar">6</a>; the source inequality is assumed. |
| Corridor forces $`s^{N+K+1}<r(N+K)`$ | Proved here | Theorem <a href="#res:corridorbound" data-reference-type="ref" data-reference="res:corridorbound">8</a>. |
| No corridor at base $`3/2`$ | Proved here | Theorem <a href="#res:nocorridor" data-reference-type="ref" data-reference="res:nocorridor">10</a>; a statement about the clearing scheme. |
| Cleared-tail recurrence | Proved here | Theorem <a href="#res:tailrec" data-reference-type="ref" data-reference="res:tailrec">11</a>, an exact identity. |
| Forcing term at least $`2^{N+1}`$ for $`s\ge2`$ | Proved here | Theorem <a href="#res:forcing" data-reference-type="ref" data-reference="res:forcing">12</a>; at $`s=1`$ the term is $`Bc(N+1)`$. |
| The elementary $`7/2`$ height condition | Proved here | Theorem <a href="#res:sevenhalves" data-reference-type="ref" data-reference="res:sevenhalves">13</a>; the analytic theorem of \[bv1994\] remains external. |
| Padé denominator-exponent bounds | Proved here | Section <a href="#sec:pade" data-reference-type="ref" data-reference="sec:pade">7</a>; exponent arithmetic only. |
| Padé remainder positivity and decay | Not treated | Section <a href="#sec:pade" data-reference-type="ref" data-reference="sec:pade">7</a>. |
| Growing-rank simultaneous endpoint-jet kernel | Open | Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">8</a>; the exact remaining obligation. |

<a id="structure."></a>

#### Structure.

Section <a href="#sec:primitive" data-reference-type="ref" data-reference="sec:primitive">2</a> proves that rowwise content is neutral for the local-to-Archimedean balance. Section <a href="#sec:endpoints" data-reference-type="ref" data-reference="sec:endpoints">3</a> proves the endpoint congruences at $`(3,2)`$, deduces from them and from Section <a href="#sec:primitive" data-reference-type="ref" data-reference="sec:primitive">2</a> that no multiplicative device supplies the missing local gain, and gives the four-jet collision count. Sections <a href="#sec:corridor" data-reference-type="ref" data-reference="sec:corridor">4</a> and <a href="#sec:tail" data-reference-type="ref" data-reference="sec:tail">5</a> return to the elementary clearing scheme and record what the residue $`s^{n}`$ costs there, first as an exclusion and then as an exact recurrence with a lower bound on the surviving term. Sections <a href="#sec:sevenhalves" data-reference-type="ref" data-reference="sec:sevenhalves">6</a> and <a href="#sec:pade" data-reference-type="ref" data-reference="sec:pade">7</a> record what is and is not formalised of two external routes. Section <a href="#sec:open" data-reference-type="ref" data-reference="sec:open">8</a> states the remaining obligations. Linked phrases open the corresponding Lean declaration at the pinned source revision 08d83b6689c8.

**Keywords.** irrationality; Lambert series; rational base; Padé approximation; Lean 4. **MSC 2020.** 11J72 (primary); 11J82, 68V20 (secondary).

<a id="sec:primitive"></a>

# Row content does not change the local-to-Archimedean balance

An irrationality argument by linear forms replaces the clearing scheme by explicit rational approximation: one constructs integer linear forms in $`1`$ and $`F(\beta)`$ whose analytic decay outruns the height of their common denominator. For an integer coefficient pair $`(U,V)`$ and a real target $`S`$, put
``` math
L_S(U,V)=US-V,
 \qquad
 \Delta\bigl((U_n,V_n),(U_m,V_m)\bigr)=U_nV_m-U_mV_n.
```
The second expression eliminates $`S`$ exactly:
``` math
\Delta=U_mL_S(U_n,V_n)-U_nL_S(U_m,V_m).
```

<div id="res:content" class="theorem">

**Theorem 1** (row-content no-go). *For integers $`c_n,c_m`$,
``` math
L_S(c_nU_n,c_nV_n)=c_nL_S(U_n,V_n),
```
``` math
\Delta\bigl(c_n(U_n,V_n),c_m(U_m,V_m)\bigr)
 =c_nc_m\Delta\bigl((U_n,V_n),(U_m,V_m)\bigr),
```
and consequently
``` math
\left|\Delta\bigl(c_n(U_n,V_n),c_m(U_m,V_m)\bigr)\right|
 =|c_n|\,|c_m|\,
   \left|\Delta\bigl((U_n,V_n),(U_m,V_m)\bigr)\right|.
```
In particular $`c_nc_m`$ divides the scaled determinant. Hence a local divisor supplied only by the two row contents is paid for by exactly the same factor in the Archimedean determinant height.*

</div>

<div class="proof">

*Proof.* All three identities are routine expansions in $`\mathbb{Z}`$ or $`\mathbb{R}`$; the divisibility statement uses the primitive determinant as its witness. ◻

</div>

Lean checks the error identity in [error scaling](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L84), the determinant identity in [content factorisation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L94), the exact absolute-height identity in [absolute determinant scaling](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L104), and the divisor statement in [content-product divisibility](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L116). The elimination identity is the checked [exterior determinant identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L124).

The key point is that the two scalings are the same scaling. Each identity on its own is a one-line expansion, and the interest of the theorem is not in any one of them. Taken together they say that the factor $`c_nc_m`$ which a rescaling introduces into the determinant reappears undiminished, as $`|c_n|\,|c_m|`$, in the absolute value of that determinant. The third identity is displayed with absolute values for exactly that reason: it is what makes the statement one about the Archimedean height and not about divisibility alone. Whatever $`c_n`$ and $`c_m`$ are, a rescaling therefore leaves the balance between the local divisor and that height where it was.

The theorem does not construct primitive Padé rows, estimate their remainders, or prove that their exterior determinant is nonzero. It removes one source of apparent gain: multiplying a useful row by a large common integer cannot improve the local-to-Archimedean balance. Every candidate family must first be divided by its rowwise common contents; the required $`2`$-adic and $`3`$-adic gain must remain afterwards. The theorem quantifies over arbitrary integer coefficient pairs, so it applies to the rows of any construction of this shape, whatever produced them.

<a id="sec:endpoints"></a>

# Endpoint residues at $`(3,2)`$ and the four-jet kernel

The Heine–Zudilin forms have integral coefficient polynomials before specialisation. For $`P(X)=\sum_i p_iX^i\in\mathbb{Z}[X]`$ and a declared width $`W`$, put
``` math
H_W(P)=\sum_{i=0}^{W}p_i\,3^i2^{W-i}.
```
This is the [homogeneous endpoint evaluation](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L96).

<div id="res:endpoints" class="theorem">

**Theorem 2** (endpoint residues). *For every integral polynomial $`P`$,
``` math
H_W(P)\equiv p_0\,2^W\pmod 3,\qquad
 H_W(P)\equiv p_W\,3^W\pmod 2.
```
Consequently a unit constant coefficient prevents divisibility by $`3`$, and a unit top coefficient prevents divisibility by $`2`$.*

</div>

<div class="proof">

*Proof.* Modulo $`3`$, every summand with $`i>0`$ vanishes; modulo $`2`$, every summand with $`i<W`$ vanishes. The remaining powers are units in the corresponding residue fields. ◻

</div>

The congruences are the [bottom-endpoint identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L201) and [top-endpoint identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L215); the unit consequences are the [constant-endpoint obstruction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L233) and [top-endpoint obstruction](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L251).

The proof is two lines, but the shape of the statement is not incidental. The difficulty lies in the fact that the specialisation sees a different endpoint at each of the two primes: modulo $`3`$ only the constant coefficient survives, and modulo $`2`$ only the top one does. The two exclusions are therefore conditions at opposite ends of the coefficient vector, and the statement below imposes one at each end, on the two entries of a single coefficient pair.

<div id="res:commonmult" class="proposition">

**Proposition 3** (common multiplier). *If $`U`$ has unit top endpoint, $`V`$ has unit constant endpoint, and an integer $`c`$ divides both $`H_W(U)`$ and $`H_W(V)`$, then
``` math
2\nmid c\qquad\text{and}\qquad 3\nmid c.
```*

</div>

This is the checked [common-multiplier exclusion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L293).

<div id="res:nomult" class="corollary">

**Corollary 4** (no multiplicative local gain at $`3/2`$). *Under the endpoint hypotheses of Proposition <a href="#res:commonmult" data-reference-type="ref" data-reference="res:commonmult">3</a>, neither rowwise scalar content nor a common multiplier of the two specialised evaluations $`H_W(U)`$ and $`H_W(V)`$ can manufacture the two local primes required at $`3/2`$.*

</div>

<div class="proof">

*Proof.* By Theorem <a href="#res:content" data-reference-type="ref" data-reference="res:content">1</a> rowwise content multiplies the analytic error and the exterior determinant, including the absolute determinant height, by exactly the factors it introduces, so a divisor obtained that way is paid for by the same factor in that height. By Proposition <a href="#res:commonmult" data-reference-type="ref" data-reference="res:commonmult">3</a> an integer dividing both specialised evaluations is divisible by neither $`2`$ nor $`3`$. ◻

</div>

Both ingredients are Lean-checked; the combination is an ordinary deduction and is not separately formalised. The corollary excludes two ways of producing the required gain. It does not show that a gain of that kind is necessary for a proof by linear forms at $`3/2`$.

Corollary <a href="#res:nomult" data-reference-type="ref" data-reference="res:nomult">4</a> closes the two multiplicative devices above, and what the rest of this section pursues in their place is additive: rather than multiplying one row by a scalar, take an integer combination of several rows and ask that the combination be divisible where the individual rows are not. The endpoint congruences are the first case of a divisibility condition that can be imposed to any depth, and it is that condition, read additively, which is counted below.

For higher powers define the bottom and top jets by reducing $`H_W(P)`$ modulo $`3^R`$ and $`2^S`$, respectively. Their vanishing is exactly the requested divisibility:
``` math
J_{3,R}(P)=0\iff 3^R\mid H_W(P),\qquad
 J_{2,S}(P)=0\iff 2^S\mid H_W(P).
```
These are the checked [bottom-jet divisibility criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L189) and [top-jet divisibility criterion](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L195). They turn the missing local divisor into an additive congruence-kernel problem: what is sought is no longer a scalar multiplier of the two evaluations, but a vector of small integer coefficients on which four residues vanish at once. Since $`H_W`$ is linear in the coefficients of $`P`$, the four-jet signature of a combination is the corresponding combination of signatures, which is what makes the following count possible.

<div id="res:jetkernel" class="theorem">

**Theorem 5** (binary four-jet collision). *Let $`(U_j,V_j)_{j<n}`$ be any $`n`$ integral coefficient pairs. If the $`2^n`$ binary selectors outnumber the finite four-jet target
``` math
(\mathbb{Z}/3^R\mathbb{Z})^2\times(\mathbb{Z}/2^S\mathbb{Z})^2,
```
then two distinct subsets have the same four-jet sum. Subtracting their indicator vectors gives a nonzero coefficient vector in $`\{-1,0,1\}^n`$ cancelling all four jets. The target has exact cardinality
``` math
(3^R)^2(2^S)^2.
```
In particular, if $`R>0`$ and $`4R+2S\le n`$, such a collision exists.*

</div>

<div class="proof">

*Proof.* Send each binary selector to the sum of the four-jet signatures it selects. The claimed cardinal inequality and the pigeonhole principle give two distinct selectors in the same fibre. The cardinality formula is the product of the four cyclic-modulus cardinalities. For $`R>0`$,
``` math
(3^R)^2(2^S)^2<(4^R)^2(2^S)^2=2^{4R+2S}\le2^n,
```
which proves the stated sufficient threshold. ◻

</div>

The target count is the checked [four-jet target cardinality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L129); the abstract collision is the checked [four-jet pigeonhole kernel](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L140), and the linear sufficient condition is the checked [rank–depth collision threshold](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L159). The count is a routine pigeonhole; the reformulation above is what makes it relevant. Pigeonhole cancellation itself requires no independence. Independence or a non-collapsed deformation is needed only to ensure that the resulting nonzero selector difference has a nonzero polynomial pair and analytic remainder. None of the statements proved here produces a sufficiently large primitive non-collapsed family, or proves that a collision has nonzero polynomial pair or nonzero remainder.

<div id="res:scalar" class="theorem">

**Theorem 6** (scalar margin no-go). *Let $`C_1>0`$. If $`C_0\le0`$ or $`2C_0\le C_1`$, then
``` math
C_0\log 3-C_1\log 2<0.
```*

</div>

The inequality is immediate from $`\log3<2\log2`$ and $`C_1>0`$, and is the checked [three-halves scalar margin](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L323). The interest is in the fence around it. The primary Zudilin theorem \[zudilin2004\] supplies an integer-base irrationality-exponent estimate on its parameter cone, and the elementary inequality $`\mu\ge2`$ then forces $`2C_0\le C_1`$ whenever $`C_0>0`$; Lean checks that implication separately. The primary theorem assumes an integer base $`p=1/q`$. It does not state a rational $`p=3/2`$ theorem, so the all-scale coefficient construction and rational specialisation remain external to the checked result, which is the scalar parameter margin alone.

<a id="sec:corridor"></a>

# Failure of coordinatewise clearing at $`3/2`$

This section and the next return to the elementary route and record what the residue $`s^{n}`$ costs there. We first isolate the arithmetic that the clearing scheme leaves behind, in a form that does not mention the series.

<div id="def:corridor" class="definition">

**Definition 7** (coordinatewise corridor). Let $`a,b,N,K,Q,D`$ be natural numbers. Say that $`(a,b,N,K,Q,D)`$ is a *coordinatewise corridor* when
``` math
a>0,\qquad Q>0,\qquad D>0,\qquad D\le N+K,\qquad
 a^{K}\mid QD,\qquad Q\,b^{\,N+K+1}<a^{\,K+1}.
```

</div>

The reading is: $`a`$ and $`b`$ are the numerator and denominator of the base, $`N`$ is the shift, $`K`$ is the width of the cleared window, $`Q`$ is the accumulated clearing factor, and $`D`$ is the final coefficient being cleared. The bound $`D\le N+K`$ is the only property of the coefficient used; for the divisor-counting coefficient it holds because $`d(n)\le n`$. The divisibility $`a^{K}\mid QD`$ is the requirement that clearing succeeded coordinatewise, and the last inequality is the tail estimate that makes the trapped integer smaller than $`1`$. The definition is the [corridor predicate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L106).

<div id="res:corridorbound" class="theorem">

**Theorem 8** (corridor bound). *If $`(a,b,N,K,Q,D)`$ is a coordinatewise corridor, then
``` math
b^{\,N+K+1}<a\,(N+K).
```*

</div>

<div class="proof">

*Proof.* A routine divisibility computation. Since $`QD>0`$ and $`a^{K}\mid QD`$, we have $`a^{K}\le QD`$, and $`D\le N+K`$ gives $`a^{K}\le Q(N+K)`$. Hence
``` math
Q\,b^{\,N+K+1}<a^{\,K+1}=a^{K}\cdot a\le Q(N+K)\cdot a,
```
and cancelling the positive factor $`Q`$ gives the claim. ◻

</div>

Formalised as the [power-versus-linear consequence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L114).

The inequality of Theorem <a href="#res:corridorbound" data-reference-type="ref" data-reference="res:corridorbound">8</a> is where the integer and rational cases part. At $`b=1`$ it reads $`1<a(N+K)`$, which holds for every $`a\ge2`$ and every nonempty window; the corridor imposes no obstruction at all. At $`b\ge2`$ the left side is exponential in $`N+K`$ and the right side is linear, so the corridor can survive only for small $`N+K`$. At $`b=2`$ the crossing has already happened at the smallest admissible window.

<div id="res:exp" class="proposition">

**Proposition 9**. *For every natural number $`x\ge2`$ we have $`3x<2^{\,x+1}`$.*

</div>

<div class="proof">

*Proof.* A routine induction from $`x=2`$, where $`6<8`$. For the step, $`2^{x+1}\ge2^{2}>3`$ when $`x\ge1`$, so $`3(x+1)=3x+3<2^{x+1}+2^{x+1}=2^{x+2}`$. ◻

</div>

Formalised as the [exponential comparison](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L135).

<div id="res:nocorridor" class="theorem">

**Theorem 10** (no corridor at base $`3/2`$). *For all $`N\ge1`$ and $`K\ge1`$ and all natural $`Q,D`$, the tuple $`(3,2,N,K,Q,D)`$ is not a coordinatewise corridor.*

</div>

<div class="proof">

*Proof.* A corridor would give $`2^{\,N+K+1}<3(N+K)`$ by Theorem <a href="#res:corridorbound" data-reference-type="ref" data-reference="res:corridorbound">8</a>, contradicting Proposition <a href="#res:exp" data-reference-type="ref" data-reference="res:exp">9</a> applied to $`x=N+K\ge2`$. ◻

</div>

Formalised as the [corridor exclusion at three halves](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L148).

Theorem <a href="#res:nocorridor" data-reference-type="ref" data-reference="res:nocorridor">10</a> excludes the coordinatewise clearing scheme at $`3/2`$, and nothing else: it does not bound the denominator of $`F(3/2)`$, it does not show that $`F(3/2)`$ is irrational, and it does not show that $`F(3/2)`$ is rational. It also does not cover a clearing scheme of a different shape, since the corridor fixes one divisibility pattern and one tail inequality.

<a id="sec:tail"></a>

# The cleared-tail recurrence and the size of the forcing term

Theorem <a href="#res:nocorridor" data-reference-type="ref" data-reference="res:nocorridor">10</a> says that one scheme fails. This section identifies the quantity responsible, as an exact recurrence.

Throughout, $`r,s,B,F`$ are rationals with $`r\ne0`$, and $`c:\mathbb{N}\to\mathbb{Q}`$ is arbitrary. Define the prefix and the cleared tail state by
``` math
P_N=\sum_{m=0}^{N-1}\frac{c(m+1)\,s^{\,m+1}}{r^{\,m+1}},
 \qquad
 U_N=B\,r^{N}\bigl(F-P_N\bigr).
```
Thus $`P_N`$ is the partial sum of $`\sum_{n\ge1}c(n)(s/r)^{n}`$ through level $`N`$, and $`U_N`$ is the tail of a putative value $`F`$ after that level, scaled by $`Br^{N}`$. These are the [rational-base prefix](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L161) and the [cleared tail state](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L174).

<div id="res:tailrec" class="theorem">

**Theorem 11** (cleared-tail recurrence). *For every $`N`$,
``` math
U_{N+1}=r\,U_N-B\,c(N+1)\,s^{\,N+1}.
```*

</div>

<div class="proof">

*Proof.* An immediate computation. Expanding $`P_{N+1}=P_N+c(N+1)s^{N+1}/r^{N+1}`$ and $`r^{N+1}=r^{N}\cdot r`$ in the definition of $`U_{N+1}`$ and clearing the denominator $`r^{N+1}`$, which is nonzero, gives the identity. ◻

</div>

Formalised as the [cleared-tail recurrence](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L180).

The recurrence has a linear part $`rU_N`$ and a forcing term $`Bc(N+1)s^{N+1}`$. The integer-base argument works by keeping the state in a bounded window, and the forcing term is what it must absorb at each step. Its size is exactly the point of departure.

<div id="res:forcing" class="theorem">

**Theorem 12** (the forcing term). *Let $`s,B`$ be natural numbers and $`c:\mathbb{N}\to\mathbb{N}`$, and put $`G_N=B\,c(N+1)\,s^{\,N+1}`$.*

1.  *If $`s\ge2`$, $`B\ge1`$ and $`c(N+1)\ge1`$, then $`2^{\,N+1}\le G_N`$.*

2.  *If $`s=1`$, then $`G_N=B\,c(N+1)`$.*

</div>

<div class="proof">

*Proof.* Both parts are routine. For the first, $`2^{N+1}\le s^{N+1}=1\cdot s^{N+1}\le Bc(N+1)s^{N+1}`$, using $`B\,c(N+1)\ge1`$. The second part is the definition with $`s=1`$. ◻

</div>

Formalised as the [exponential lower bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L197) and the [integer-base collapse](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L211).

At $`s=1`$ the forcing term is $`Bc(N+1)`$, so it grows only as fast as the coefficient; for the divisor function that is $`O(N^{\varepsilon})`$ for every $`\varepsilon>0`$, and a bounded-state argument has room. At $`s\ge2`$ the same term is at least $`2^{N+1}`$ whenever the coefficient is nonzero.

This is an exact lower bound on one quantity, and it is all that is proved. It is not a proof that no bounded-state argument exists at $`s\ge2`$; the theorem that one particular scheme fails is Theorem <a href="#res:nocorridor" data-reference-type="ref" data-reference="res:nocorridor">10</a>, and the bound here records the size of the term that scheme would have to absorb.

<a id="sec:sevenhalves"></a>

# The height criterion at $`7/2`$

In 1994 Bundschuh and Väänänen proved an irrationality criterion for a family of rational bases cut out by a height condition \[bv1994, Theorem 2, pp. 176–177\]. In its special case $`\alpha=-1`$, the printed hypothesis is
``` math
\lambda<\left(\frac12+\frac1{\pi^2}\right)^{-1}.
```
At $`q=7/2`$ the Archimedean parameter is $`\lambda=\log 7/\log(7/2)`$. The criterion therefore applies once the following strict inequality is checked.

<div id="res:sevenhalves" class="theorem">

**Theorem 13** (the $`7/2`$ height condition).
*``` math
\frac{\log 7}{\log(7/2)}
 <
 \left(\frac12+\frac1{\pi^2}\right)^{-1}.
```*

</div>

The Lean proof factors the estimate into the [integer certificate](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L32) $`2^{18}<7^7`$, the resulting [logarithmic ratio bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L41) $`\log2/\log7<7/18`$, the [$`\pi`$-bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L57) $`1/\pi^2<1/9`$, and the [strict margin](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L66)
``` math
\frac{\log2}{\log7}<\frac12-\frac1{\pi^2}.
```
The [final height inequality](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L76) then rewrites $`\log(7/2)=\log7-\log2`$ and closes the displayed condition.

This formalises the complete elementary parameter check at $`q=7/2`$; it does not formalise Bundschuh and Väänänen’s analytic irrationality theorem, whose proof occupies pp. 189–193 of the source. The conclusion that $`F(7/2)`$ is irrational is consequently cited from that theorem, not claimed as a Lean theorem here.

The criterion does not cover $`3/2`$, and the results of Sections <a href="#sec:corridor" data-reference-type="ref" data-reference="sec:corridor">4</a> and <a href="#sec:tail" data-reference-type="ref" data-reference="sec:tail">5</a> give no evidence either way about whether $`F(3/2)`$ is irrational.

<a id="sec:pade"></a>

# Denominator exponents for a homogenised Padé construction

A second external route builds the linear forms of Section <a href="#sec:primitive" data-reference-type="ref" data-reference="sec:primitive">2</a> by Padé approximation. For a homogenised construction over integer parameters the proposed common denominator exponent is $`E_n=(3n^{2}-n)/2`$. Since only doubled exponents occur below, every statement lives over $`\mathbb{Z}`$ and no parity bookkeeping is needed; we write $`\widetilde{E}_n=2E_n=3n^{2}-n`$.

<div id="res:pade" class="proposition">

**Proposition 14** (summand bound and exact gap). *Put
``` math
\widetilde{P}(n,k)=2\bigl(k(n-k)+nk\bigr)+k(k-1),
```
``` math
\widetilde{Q}(n,m)=2(n^{2}-n)+j^{2}+2jm+j-m^{2}+3m,
 \qquad j=n-m-1 .
```
Then, for integers $`n,k,m`$:*

1.  *if $`0\le k\le n`$, then $`\widetilde{P}(n,k)\le\widetilde{E}_n`$, and the gap factors as $`\widetilde{E}_n-\widetilde{P}(n,k)=(n-k)(3n-k-1)`$;*

2.  *$`\widetilde{E}_n-\widetilde{Q}(n,m)=2\bigl(n+m(m-1)\bigr)`$ identically;*

3.  *if $`n\ge0`$ and $`m\ge1`$, then $`\widetilde{Q}(n,m)\le\widetilde{E}_n`$.*

</div>

Part (1) is the [summand exponent bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L30), part (2) the [exact gap identity](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L52), and part (3) the [maximal exponent bound](https://github.com/wcook04/plectis-lean-erdos249-257/blob/08d83b6689c85fc501f4051960d4c35bddb0f431/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L60). The gap in (2) is an identity in $`\mathbb{Z}[n,m]`$, so (3) follows from $`m(m-1)\ge0`$ and $`n\ge0`$; the hypothesis $`m\ge1`$ names the range in which the corresponding summand does not vanish, and it is not the sharpest hypothesis under which the inequality holds.

These are routine inequalities between polynomials in the exponents. They establish that the proposed common denominator is large enough to clear the construction, and nothing further. Positivity of the remainder, its rate of decay, and the comparison of that rate against the denominator height are the analytic obligations, and none of them is treated here, so nothing in this section is an irrationality measure.

<a id="sec:open"></a>

# Complements and further questions

Problem #1049 is open. The following is the exact statement that a construction at $`3/2`$ would have to supply.

<div id="prob:kernel" class="problem">

**Problem 15** (growing-rank simultaneous endpoint-jet kernel). For positive quadratic target depths $`R_n,S_n`$, exhibit at least $`4R_n+2S_n`$ *primitive-normalised* Heine–Zudilin coefficient pairs from a genuinely non-collapsed deformation, and prove that at least one resulting checked collision satisfies
``` math
J_{3,R_n}\!\left(\sum_j\lambda_jU_j\right)=
 J_{3,R_n}\!\left(\sum_j\lambda_jV_j\right)=0,
\qquad
 J_{2,S_n}\!\left(\sum_j\lambda_jU_j\right)=
 J_{2,S_n}\!\left(\sum_j\lambda_jV_j\right)=0,
```
where $`R_n,S_n`$ have the required quadratic order, while the resulting remainder is nonzero and its local gain beats the Archimedean height. The checked collision already has coefficients in $`\{-1,0,1\}`$. A rank-saturated contiguous-shift family or a genuinely independent deformation would be a first candidate.

</div>

A scalar ray, growth in the row contents, a multiplicative cyclotomic factor, or a further common-multiplier computation does not address the obstruction that survives Corollary <a href="#res:nomult" data-reference-type="ref" data-reference="res:nomult">4</a>. A theorem showing that every available family is too small or too degenerate to meet the requirements of Problem <a href="#prob:kernel" data-reference-type="ref" data-reference="prob:kernel">15</a> would show that no argument of this shape can succeed.

The unrestricted question, which rational bases give an irrational value, remains open, and is not reduced to the problem above.

<a id="statements-and-declarations"></a>

## Statements and declarations

<a id="artefact-and-data-availability."></a>

#### Artefact and data availability.

The [pinned formal-source revision](https://github.com/wcook04/plectis-lean-erdos249-257/tree/08d83b6689c85fc501f4051960d4c35bddb0f431) contains the Lean sources, the fixed toolchain, and the library manifest used in the verification. This manuscript provides navigation rather than proof authority.

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

Each linked phrase opens its Lean declaration at the pinned source revision 08d83b6689c8. The declarations of this note live in three modules: the corridor, the cleared-tail recurrence, and the two arithmetic certificates in the first; the Padé exponent arithmetic in the second; and the Heine–Zudilin endpoint arithmetic in the third. The link coordinates are validated against that pinned revision, so they remain correct as later work moves lines in the working tree.

<div class="thebibliography">

9

P. Erdős, [*On arithmetical properties of Lambert series*](https://users.renyi.hu/~p_erdos/1948-04.pdf), J. Indian Math. Soc. (N.S.) **12** (1948), 63–66. P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). P. B. Borwein, *On the irrationality of $`\sum1/(q^{n}+r)`$*, J. Number Theory **37** (1991), no. 3, 253–259. P. Bundschuh and K. Väänänen, [*Arithmetical investigations of a certain infinite product*](https://numdam.org/item/CM_1994__91_2_175_0.pdf), Compositio Math. **91** (1994), no. 2, 175–199. W. Zudilin, [*Heine’s basic transform and a permutation group for $`q`$-harmonic series*](https://www.impan.pl/shop/en/publication/transaction/download/product/82435), Acta Arith. **111** (2004), no. 2, 153–164. W. Van Assche, [*Little $`q`$-Legendre polynomials and irrationality of certain Lambert series*](https://arxiv.org/abs/math/0101187), Ramanujan J. **5** (2001), 295–310. J. Vandehey, [*On an incomplete argument of Erdős on the irrationality of Lambert series*](https://arxiv.org/abs/1206.0340), Integers **13** (2013), Paper A58. V. Kovač and T. Tao, [*On several irrationality problems for Ahmes series*](https://arxiv.org/abs/2406.17593), arXiv:2406.17593, 2024. T. F. Bloom, [*Erdős Problem \#1049*](https://www.erdosproblems.com/1049), `erdosproblems.com/1049`, accessed 22 July 2026. The Formal Conjectures Authors, [*FormalConjectures.ErdosProblems.`1049`*](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1049.lean), Lean source, 2025, accessed 27 July 2026.

</div>
