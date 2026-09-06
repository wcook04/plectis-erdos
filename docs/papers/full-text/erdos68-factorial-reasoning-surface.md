<a id="erdos68-factorial-reasoning-surface"></a>

# The Factorial-Denominator Series: Complete Reasoning Record

<div class="center">

<span class="smallcaps">Abstract</span>

</div>

Erdős asked whether
``` math
S=\sum_{n\ge2}\frac1{n!-1}
```
is irrational. The problem remains open. The strongest unconditional partial result here is a quantitative obstruction to the finite-channel strategy, and its complete statement is checked by the Lean kernel: for all $`t,M,R\in\mathbb N`$ with $`t\ge2^{32}`$, $`M>0`$, $`L_{2t^2}\mid M`$ and $`M<(R+1)!-1`$,
``` math
3t^3<2(R+1).
```
All four hypotheses are carried inside the formal statement, the proof is finite, and the conclusion excludes eventual $`3/2`$ upper bounds for the normalized channel radius together with little-$`o(t^3)`$ growth in this architecture. The obligation it leaves is explicit: derive the divisibility and factorial-size hypotheses from the factorial-gap series itself, and prove that the channels through $`2t^2`$ vanish for the resulting family. A complementary conditional advance proves that one moving prefix-private prime, together with explicit global complementary-residue and local collision-core scale bounds, implies irrationality; arbitrary factors of one moving private modulus suffice under the corresponding normalized projection hypotheses. Wilson’s theorem supplies the moving private factors cofinally, so the surviving obligation there is the pair of scale bounds. The two quantitative producers remain open.

The note also proves two finite denominator exclusions and an exact prime-pole cancellation law. A GMP certificate gives $`300000\nmid Z_{300000}`$ and hence $`q\nmid299999!`$ in any representation $`S=a/q`$ with $`q>0`$; an independent continued-fraction certificate gives $`q\ge2^{39990}>10^{12038}`$. These are two different constraints. The first is a divisibility restriction that no denominator magnitude discharges; the second is a magnitude bound that no smoothness restriction discharges. Both exponents are read from the replay receipt `verification/erdos68-continued-fraction.json`, which records scale $`80000`$ bits, bracket width $`7053`$, $`23449`$ certified partial quotients, power-of-two exponent $`39990`$, and strict decimal exponent $`12038`$. For a finite prefix, the complete maximal power $`q^e`$ of a prime survives reduction exactly when a reciprocal maximal-hit cofactor sum is nonzero; full cancellations occur at $`q=139`$ and $`q=2593`$.

Two exact coordinates are recorded after these advances. For $`C=\sum_{n\ge2}(n!(n!-1))^{-1}`$, one has
``` math
S\in\mathbb Q\iff \lfloor m!C\rfloor\equiv-2\pmod m
 \quad\hbox{eventually}.
```
For $`H_m=\sum_{2\le n\le m}(n!-1)^{-1}`$ and $`Z_m=\lfloor m!H_m\rfloor+1`$, irrationality is equivalent to cofinally many failures of $`m\mid Z_m`$. These equivalences isolate the producer but do not supply it. Finally, two consecutive unit carries reduce to the universal inequality $`0<U_{m+2}\le V_{m+2}`$, so a divisibility obstruction derived only after assuming that pair cannot exclude it.

Two further exact reformulations are recorded in the working tree and are named here so that the frontier is visible in one place. A shrinking-target normal form states that irrationality is equivalent to cofinal escape of the canonical factorial orbit from a lower endpoint cylinder whose radius is $`O(m^{-2})`$. A uniform family boundary states, for every integer $`t\ge-1`$, that $`\sum_{n\ge2}1/(n!+t)`$ is rational exactly when $`\lceil t\,m!\,C_t\rceil\equiv2\pmod m`$ for all sufficiently large $`m`$, with $`C_t=\sum_{n\ge2}1/(n!(n!+t))`$, and it recovers the irrationality of $`e`$ at $`t=0`$. Both statements sit outside the formal-source commit pinned by this note, they carry no declaration link below, and they are scheduled for the next formalisation cycle.

<div class="center">

<div class="minipage">

------------------------------------------------------------------------

**Main results and exact open boundary**

**Unconditional obstruction.** The square-subsequence channel radius is at least $`3/2`$ under the exact cancellation architecture, excluding eventual $`3/2`$ upper bounds and little-$`o`$ decay. **Conditional advance.** One moving prefix-private factor plus two explicit scale bounds implies irrationality; the moving factors exist cofinally, while the scale bounds are open. **Exact coordinates.** The fixed companion orbit and strict successor give lossless eventual/cofinal reformulations without the missing producer; both extend the classical factorial-base rationality criterion of Cantor \[cantor1869\] in the form recorded by Galambos \[galambos1976, Ch. 1\]. **Evidence split.** The channel radius, the moving-factor split, the two exact coordinates and the prime-pole law are Lean-checked at the pinned commit; the $`299999!`$ and continued-fraction denominator exclusions are ordinary proofs whose kernel-checked part is the implication from one non-unit carry, with the numbers supplied by replayable integer certificates. **Held outside the checkpoint.** The shrinking-target normal form and the uniform boundary for $`\sum_{n\ge2}1/(n!+t)`$ are proved in the working tree and are not part of the pinned formal source. **Open boundary.** No result here proves a cofinal miss or irrationality of $`S`$.

</div>

</div>

<a id="sec:problem"></a>

# The problem

<div id="res:problem" class="problem">

**Problem 1** (Erdős \#68). Is
``` math
S=\sum_{n\ge2}\frac1{n!-1}
```
irrational?

</div>

<div class="center">

| Contribution | Exact scope |
|:---|:---|
| Channel-radius obstruction | Under the exact cancellation and factorial-size hypotheses, the square-subsequence normalized radius is at least $`3/2`$; eventual $`3/2`$ upper bounds and little-$`o`$ decay are impossible. |
| Moving-factor criteria | One moving prefix-private prime plus two explicit scale bounds implies irrationality; arbitrary factors of one moving private modulus suffice under normalized projection disagreement. The scale producers remain open. |
| Finite denominator exclusions | If $`S=a/q`$ with $`q>0`$, then $`q\nmid299999!`$ and independently $`q\ge2^{39990}>10^{12038}`$. |
| Prime-pole cancellation law | A maximal prime power survives finite-prefix reduction exactly when its reciprocal maximal-hit cofactor sum is nonzero. |
| Fixed companion orbit | $`S`$ is rational iff $`\lfloor m!C\rfloor\equiv-2\pmod m`$ eventually; this is an exact coordinate, not the missing producer. |
| Integral frontier | $`S\notin\mathbb Q`$ iff for every $`B`$ some $`m>B`$ satisfies $`m\nmid Z_m`$. |
| Adjacent-unit no-go | Under two consecutive unit carries, the complete cleared window cancels to the universal bound $`0<U_{m+2}\le V_{m+2}`$; it cannot exclude the pair. |
| Not a contribution | No cofinal miss, cofinal strict residual nonvanishing, or irrationality theorem is proved. |

</div>

Erdős states the problem on p. 102 of his 1988 survey and, in the same passage, records the broader expectation that $`\sum_n1/(n!+t)`$ is irrational—indeed transcendental—for every integer $`t`$ \[erdos1988, p. 102\]. This is conjectural context, not a theorem proved in that source.

Numbering and current status follow [Bloom’s Erdős problem catalogue](https://www.erdosproblems.com/68) \[bloom\]. The problem is open. The companion series $`\sum_{n\ge0}1/n!=e`$ and $`\sum_{n\ge2}1/(n!+1)`$ sit in the same family, and the difficulty here is the same one that makes the Erdős–Borwein constant hard: the denominators $`n!-1`$ grow fast enough that convergence is trivial and slow enough, in the arithmetic sense, that no single congruence controls them.

*Status.* The original problem remains open. Statements marked as Lean-checked refer to the linked propositions accepted by the pinned kernel, with no `sorry`, added axioms, or unchecked evaluation. The note states the remaining mathematical obligations explicitly.

*Companion system context.* The [claim and trust boundary](../../../claim-faithful-publication-systems-paper.pdf#systems-trust), [cold-clone route to proof authority](../../../cold-clone-to-proof-receipt.pdf#cold-clone-authority), and [public contribution protocol](../../../open-source-mathematics-strategy.pdf#strategy-protocol) are described in sibling papers.

| Statement | Status | Exact boundary |
|:---|:---|:---|
| Irrationality of $`S`$ | Open | No proof is claimed. |
| Moving-factor irrationality criteria | Checked conditional theorems | Moving private factors exist cofinally, but the global complementary-residue and local collision-core scale bounds are not proved. |
| Canonical factorial digit kernel | Checked | Floor formula, digit bounds, remainder recurrence, finite expansion, zero-tail propagation. |
| Channel integrality | Checked | $`(d!)^{\lfloor i/d\rfloor}\mid i!`$, with exact denominator cancellation. |
| Channel congruence and LCM obstruction | Checked | $`V_{d}(\lambda)\equiv M\pmod{d!-1}`$; annihilating channels through $`D`$ forces $`L_D\mid M`$. |
| Square-subsequence channel radius | Checked | If $`M>0`$, $`L_{2t^2}\mid M`$, and $`M<(R+1)!-1`$, then $`3t^3<2(R+1)`$ for $`t\ge2^{32}`$; the reverse cubic bound cannot hold eventually. |
| Two-term prime channel corrector | Checked | The pair $`(p,-1)`$ on $`(p-1,p)`$ has moment $`0`$, all channels $`0`$ except $`d=p`$, and $`p`$-channel numerator $`p!-1`$. |
| Weighted projection rigidity | Checked | If $`Z\equiv T\pmod R`$, $`Q_i\mid R`$, and $`Z\le B<Q_i`$, then unequal residues $`T\bmod Q_1`$ and $`T\bmod Q_2`$ exclude that endpoint. |
| Factor-split projection reduction | Checked | Two divisor factors of one private modulus support the same cancellation and disagreement bounds; coprime factors give a branch-free floor and may lie in one private quotient. |
| Zero plateau and first-exit carry | Checked | Grid threshold, plateau equality of grid integers, forced zero digit, carry $`b\in\{0,-1\}`$. |
| Prime-power prefix obstruction | Checked | Rationality forces $`p^k`$ to divide the strict successor at $`kp`$ whenever the factorial clears the denominator and $`p`$ is coprime to it. |
| Exact carry characterization | Checked | The normalized strict successors converge to $`S`$; $`S`$ is rational exactly when $`b_m=1`$ eventually, equivalently $`S`$ is irrational exactly when non-unit carries occur cofinally. |
| Fixed companion-orbit boundary | Checked | Rationality is equivalent to eventual residue $`-2`$ for the fixed factorial orbit; irrationality is equivalent to cofinal misses. No theorem produces those misses. |
| Adjacent-unit cancellation normalizer | Checked | Under consecutive unit carries, the exact offset and denominator share the same positive two-step normalizer, so their window inequality reduces to the universal future numerator bound. |
| Explicit denominator bound | Checked implication; exact finite certificate | Exact reduction gives $`60\nmid Z_{60}`$, $`64\nmid Z_{64}`$, and $`67\nmid Z_{67}`$. An exact GMP computation certifies all carries through $`300000`$ and $`b_{300000}\ne1`$; the Lean-checked carry theorem gives $`q\ge300000`$ in every rational representation $`S=a/q`$ with $`q>0`$. |
| Digits eventually zero $`\iff`$ $`S`$ rational | Checked | The equivalence holds for the canonical factorial expansion of every real number. |
| Factorial-gap lcm growth $`\gg N^{4/3}\log N`$ | Derived, source-verified | Derived below from a cited factorial-congruence theorem; not kernel-checked and not used as an input to any claim below. |
| Finite certificates ($`D=3`$, $`D=9`$, $`D\le12`$) | Verified finite instances | Each excludes only the denominators it names. |
| Unbounded strict nonvanishing | Open | Required to turn the channel rounding argument into an irrationality proof. |

<a id="sec:lead"></a>

# Leading contributions

Each entry below states the hypotheses it carries, separates the kernel-checked part from the ordinary part and from any replayable certificate, records the attribution where prior art applies, and names the exact obligation that remains. The order is by strength of what is supported, and every statement is repeated in full in its own section.

<a id="res:lead-channel-radius"></a>

#### 1. Square-subsequence channel radius.

For all $`t,M,R\in\mathbb N`$ with $`t\ge2^{32}`$, $`M>0`$, $`L_{2t^2}\mid M`$ and $`M<(R+1)!-1`$, one has $`3t^3<2(R+1)`$; the sequence form says that no radius function satisfies $`2(R(t)+1)\le3t^3`$ eventually, and a third form says that $`R(t)+1`$ is not $`o(t^3)`$ under the corresponding hypotheses from $`t\ge4096`$ onward. This is Theorem <a href="#res:channel-radius" data-reference-type="ref" data-reference="res:channel-radius">5</a>. *Evidence.* The complete advertised endpoint is Lean-checked at [the sharp radius theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1222), with the sequence form at [the eventual no-go theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1241) and the little-$`o`$ form at [the little-o obstruction](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1043). The method’s own ceiling is checked separately at [the logarithmic-constraint evaluation](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L764): for $`t\ge4`$ and $`9(R+1)=16t^3`$ the finite logarithmic constraint is already satisfied, so that constraint alone cannot force the asymptotically optimized constant $`16/9`$. No part of this entry rests on a certificate or on an ordinary supplement. *Attribution.* The prior-art relation for this family is recorded as unassessed, so no novelty is asserted for it here. *Remaining obligation.* Derive $`L_{2t^2}\mid M`$ and $`M<(R+1)!-1`$ from the factorial-gap series, and prove that the channels through $`2t^2`$ vanish for the resulting family.

<a id="res:lead-moving-factor-split"></a>

#### 2. Moving-factor scale split.

If cofinally many $`m\ge4`$ carry a large prefix-private prime $`q`$ of $`m!-1`$ such that, at $`p=m/2+1`$, both $`(2p+1)L_p<2p^2(2p-1)!\,\rho_p`$ and $`(2p+1)C_pq<2p^2(2p-1)!`$ hold, then $`S`$ is irrational. This is §<a href="#res:moving-factor-scale-split" data-reference-type="ref" data-reference="res:moving-factor-scale-split">[res:moving-factor-scale-split]</a>. *Evidence.* The implication is Lean-checked at [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L1574). The split that removes the opaque floor premise is the exact equivalence [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4766), resting on the floor identity [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4701). The arithmetic supply is unconditional and also Lean-checked: [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3097) produces, for every cutoff, a prime $`q`$ and an index $`m`$ beyond it with $`q\mid m!-1`$ and $`q`$ coprime to every earlier factorial gap. *Attribution.* The supply proof uses Wilson’s theorem, which is classical; the cofinality packaging is recorded as unassessed. *Remaining obligation.* Prove both sides of the branch-free scale split cofinally. Neither side follows from the existence of the selected prime.

<a id="res:lead-companion-orbit"></a>

#### 3. Fixed companion-orbit boundary.

With $`C=\sum_{n\ge2}1/(n!(n!-1))`$, the series $`S`$ is rational exactly when $`(\lfloor m!C\rfloor+2)\bmod m=0`$ for every sufficiently large $`m`$, and irrational exactly when that residue is missed cofinally. This is Theorem <a href="#res:companion-orbit-rationality-boundary" data-reference-type="ref" data-reference="res:companion-orbit-rationality-boundary">8</a>. *Evidence.* Lean-checked in both directions at `ErdosProblems/Erdos68/CompanionOrbitRationality.lean`, endpoints `not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two` and `irrational_factorialGapSeries_iff_cofinal_companion_floor_misses`. *Attribution.* The statement extends the classical factorial-base rationality criterion, that a real number is rational exactly when its canonical factorial-base digits vanish from some index on, due to Cantor \[cantor1869\] and recorded in Galambos \[galambos1976, Ch. 1\]. The addition here is the telescope $`C=S-e+2`$, the identification of the digit value $`m-2`$, and the transport of the criterion to the factorial-gap series. *Remaining obligation.* Show that $`\lfloor m!C\rfloor\bmod m`$ differs from $`-2`$ at arbitrarily large indices.

<a id="res:lead-carry-equivalence"></a>

#### 4. Strict-successor carry equivalence.

With $`H_m=\sum_{2\le n\le m}(n!-1)^{-1}`$ and $`Z_m=\lfloor m!H_m\rfloor+1`$, irrationality of $`S`$ is equivalent to cofinally many failures of $`m\mid Z_m`$, equivalently to cofinally many non-unit carries. This is §<a href="#res:strict-successor-complete-characterization" data-reference-type="ref" data-reference="res:strict-successor-complete-characterization">[res:strict-successor-complete-characterization]</a>. *Evidence.* Lean-checked at [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L986) with the carry form at [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L945). *Attribution.* Same antecedent as entry 3. *Remaining obligation.* Produce the cofinal failures. The equivalence supplies no producer.

<a id="res:lead-denominator-exclusions"></a>

#### 5. Finite denominator exclusions, two different constraints.

If $`S=a/q`$ with $`q>0`$, then $`q\nmid299999!`$, and independently $`q\ge2^{39990}>10^{12038}`$. *Evidence.* The first exclusion is an ordinary proof with a kernel-checked part. The kernel-checked part is the implication from one non-unit carry, at [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L836) and, in the magnitude form, at [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L812); the exact non-unit carry at $`m=300000`$ comes from a separately implemented GMP integer computation, whose payload, driver and backend are hash-bound in the companion research packet. The second exclusion is an ordinary continued-fraction proof whose input is the replayable integer certificate `verification/erdos68-continued-fraction.json`, recording scale $`80000`$ bits, bracket width $`7053`$, $`23449`$ certified partial quotients, power-of-two exponent $`39990`$, and strict decimal exponent $`12038`$. A kernel-internal instance of the same implication gives $`q\ge67`$ at [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialZeroPlateauCertificates.lean#L136). Neither exclusion implies the other: a denominator with no prime factor above $`299999`$ can still exceed $`10^{12038}`$, and a denominator far below that size can still fail to divide $`299999!`$ by carrying one prime to a high power. *Attribution.* The continued-fraction method is textbook, and the adjudicated disposition records the numbers as new with no antecedent located. *Remaining obligation.* Both exclusions are finite. Ruling out an eventual all-unit carry tail is what would convert them into a proof.

<a id="res:lead-prime-pole"></a>

#### 6. Prime-pole cancellation law.

For a finite prefix, the complete maximal power $`p^e`$ of a prime survives reduction exactly when the reciprocal maximal-hit cofactor sum is nonzero in $`\mathbb F_p`$. This is Proposition <a href="#res:prime-pole" data-reference-type="ref" data-reference="res:prime-pole">9</a>. *Evidence.* Lean-checked at [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimePoleCriterion.lean#L223), with the denominator-side criterion in `ErdosProblems/Erdos68/PrimePoleDenominator.lean`. The two full cancellations at $`p=139`$ and $`p=2593`$ are exact integer computations displayed in §<a href="#sec:finite" data-reference-type="ref" data-reference="sec:finite">10</a>. *Attribution.* Recorded as unassessed. *Remaining obligation.* The law classifies survival at a finite prefix and supplies no statement about the infinite series.

<a id="res:lead-held-outside-checkpoint"></a>

#### 7. Two normal forms held outside the pinned formal source.

The first is a shrinking-target normal form: $`S`$ is irrational exactly when the canonical factorial orbit escapes a lower endpoint cylinder cofinally, and because the scaled tail lies strictly between $`0`$ and $`2/m`$ the trapping target has radius $`O(m^{-2})`$. The second is a uniform boundary for the family Erdős stated on p. 102: for every integer $`t\ge-1`$, with $`C_t=\sum_{n\ge2}1/(n!(n!+t))`$, the series $`\sum_{n\ge2}1/(n!+t)`$ is rational exactly when $`\lceil t\,m!\,C_t\rceil\equiv2\pmod m`$ for all sufficiently large $`m`$; the member $`t=0`$ is $`e-2`$, and its orbit never meets the residue class, so the family boundary reproves that $`e`$ is irrational. *Evidence.* Both are proved in the working tree and neither is part of the formal-source commit pinned by this note, so neither carries a declaration link here. They are named because the shrinking-target form is the only recorded formulation that gives the measure-theoretic shape of the obstruction, and the family form is the only one that covers the statement Erdős actually made. *Attribution.* Prior art for both is unassessed. The $`t=0`$ specialisation recovers a classical fact. *Remaining obligation.* Formalise both into the pinned checkpoint in the next cycle, and prove cofinal escape from the endpoint cylinder.

<a id="sec:digits"></a>

# Canonical factorial digits

Write $`\theta_0=\{x\}=x-\lfloor x\rfloor`$ and, for $`m\ge1`$,
``` math
d_m=\lfloor m\,\theta_{m-1}\rfloor,
  \qquad
  \theta_m=m\,\theta_{m-1}-d_m .
```
This is the factorial base taken in its canonical form. The kernel checks the floor formula, the digit bounds $`0\le d_m<m`$, the recurrence $`\theta_{m+1}=(m+1)\theta_m-d_{m+1}`$, the finite telescoping expansion
``` math
x=\lfloor x\rfloor+\sum_{m=2}^{N}\frac{d_m}{m!}
   +\frac{\theta_N}{N!},
```
and the propagation rule: a zero remainder at one index forces every later digit to vanish. These are [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L124), [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L146), [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L153), [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L162), the [finite factorial expansion](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L196), and the [zero-remainder termination theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L269); they hold for every real $`x`$, including $`S`$.

The rational direction is also kernel-checked. If $`q>0`$ and $`q\le n`$, then
``` math
\operatorname{facFloor}(a/q,n)=((n!/q):\mathbb{Z})a,
```
and the canonical digit at radix $`n+1`$ vanishes. These are the [cleared-floor formula](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L47) and the [rational-input termination theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialDigits.lean#L81). They imply that every rational input has an eventually zero canonical factorial-digit expansion.

The converse is also formalised, and holds for every real input:
``` math
x\in\mathbb Q\quad\Longleftrightarrow\quad
 d_m(x)=0\ \text{for all sufficiently large }m.
```
The [termination equivalence](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialTermination.lean#L78) follows from the growth of a positive remainder, through the [zero-tail remainder lemma](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialTermination.lean#L38) and the [rational witness](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/CanonicalFactorialTermination.lean#L54). If all digits after index $`N\ge1`$ vanish, the recurrence gives $`\theta_{N+k}\ge(k+1)\theta_N`$. Since every canonical remainder is less than one, $`\theta_N`$ must vanish. Thus $`x=\lfloor N!x\rfloor/N!`$.

A zero canonical digit is not the same event as a zero-branch hit: the returned data contain canonical zero digits at $`m=5`$ and $`m=23`$, while the zero-branch list is empty through $`m=100000`$.

A second exact reformulation runs through a defect automaton. For a rational centre recurrence $`F_m=mF_{m-1}+1+\varepsilon_m-C_m`$, the kernel checks that the integer ceiling defect code equals $`\lfloor m\delta_{m-1}-\varepsilon_m\rfloor`$ and that $`\delta_m=m\delta_{m-1}-\varepsilon_m-q_m`$, with the specialisation $`\varepsilon_m=1/(m!-1)`$ written out. What is checked is the algebra of the automaton. Proving that the finite-sum residual centre satisfies the premise is a separate step and is not done.

A nearby floor criterion makes one tempting shortcut precise and also shows where it breaks. Koepf and Schmersau prove that eventual equality between the floors of $`n`$ times a partial sum and $`n`$ times its limit forces irrationality \[koepf-schmersau, Theorem 1.1, p. 117\]; their rational-term version obtains that equality from prefix integrality at a scale $`p_n`$ and the strict tail bound $`a-s_n<1/(np_n)`$ \[koepf-schmersau, Theorems 2.2–2.3, pp. 119–120\]. For the natural termwise clearing choice
``` math
p_n=\operatorname{lcm}\{k!-1:2\le k\le n\},
```
the last two denominators already show the obstruction:
``` math
p_n\ge
  \frac{(n!-1)((n-1)!-1)}{n-1},
```
because $`\gcd(n!-1,(n-1)!-1)=\gcd((n-1)!-1,n-1)\le n-1`$. For $`n\ge4`$, the first omitted summand $`1/((n+1)!-1)`$ is then already larger than $`1/(np_n)`$, so this natural $`p_n`$ cannot satisfy their tail hypothesis. Cancellation in the reduced prefix denominator could in principle give a smaller scale, but proving enough cancellation is another form of the present denominator problem.

Duverney’s fast-series criteria fail at a different, equally exact boundary. His Theorem 3.1 assumes two-sided quadratic denominator growth $`cu_n^2\le u_{n+1}\le c'u_n^2`$, while for $`u_n=n!-1`$ one has $`u_{n+1}/u_n^2\to0`$ \[duverney, pp. 275, 285–286\]. The all-positive specialization in Corollary 3.2 additionally requires
``` math
\sum_n\left|\frac{u_{n+1}}{u_n^2}-1\right|<\infty,
```
whereas the summands tend to one here \[duverney, Corollary 3.2, p. 287\]. Neither criterion applies. Lean checks both this nonsummability and the preceding ratio limit in [ratio-limit theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialAnalyticBoundary.lean#L52) and [nonsummability theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialAnalyticBoundary.lean#L84). The ratio proof divides numerator and denominator by $`(n!)^2`$; the resulting terms tend to zero while $`(1-1/n!)^2`$ tends to one.

The sharp recent theorem of Barreto, Kang, Kim, Kovač, and Zhang has a similarly explicit ceiling. Its $`d=1`$ case proves irrationality of $`\sum_n1/a_n`$ when $`a_n^{1/2^n}\to\infty`$, whereas
``` math
(n!-1)^{1/2^n}\longrightarrow1
```
for the present choice $`a_n=n!-1`$ \[barreto-et-al, Theorems 2–3, pp. 2–4\]. The latter limit is also checked in [dyadic-root limit theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialAnalyticBoundary.lean#L131): for $`n\ge2`$, the bound $`0\le\log(n!-1)\le n^2`$ gives $`\log(n!-1)/2^n\to0`$, and exponentiation gives the limit one. The proof of the cited theorem identifies a useful exact criterion: Mahler’s elementary rationality floor is contradicted by prefix-clearing integers $`D_N`$ for which the cleared positive tails satisfy $`\liminf_ND_Nr_N=0`$ \[barreto-et-al, Lemma 8 and Proposition 12, pp. 6, 9–12\]. The ordinary product of the factorial-gap denominators is far too large for that estimate; a transfer would need a low-height clearing subsequence, or enough exact cancellation in their least common multiple. Thus the new theorem supplies a precise target inequality and adaptive-cutoff architecture, but not the missing arithmetic bound.

The ordinary factorial-series direction survives more usefully. Dividing the strict-successor recurrence $`Z_m=mZ_{m-1}+1-b_m`$ by $`m!`$ and telescoping gives the exact finite identity
``` math
\frac{Z_M}{M!}
  =\frac{Z_2}{2!}
   +\sum_{m=3}^{M}\frac{1-b_m}{m!}.
```
Thus the carry defects $`1-b_m`$ are genuine factorial-series coefficients. Hančl and Tijdeman give exact rationality classifications for polynomial coefficients and finite-difference criteria for broader ordinary factorial series \[hancl-tijdeman, Theorem 3.1 and Corollary 3.1, pp. 390–391\]. Their denominator is the cumulative linear product $`\prod_{n\le N}(an+b)`$, not the individual number $`N!-1`$. Applied to the display above, the classical Cantor–Oppenheim criterion still needs $`1-b_m\ne0`$ infinitely often—precisely the missing cofinal non-unit-carry assertion that remains open.

<a id="sec:channels"></a>

# Finite channel congruences and the LCM obstruction

Fix $`d\ge2`$. The kernel proves the divisibility
``` math
(d!)^{\lfloor i/d\rfloor}\ \Big|\ i!
  \qquad(i\ge0),
```
defines the integral channel weight $`W_{d,i}`$ obtained by cancelling that factor, and checks the exact cancellation. It also checks the consecutive channel event
``` math
n\,W_{d,n-1}-W_{d,n}=0
  \qquad\text{whenever } d\nmid n .
```
So the channel weight is arithmetically inert except at multiples of $`d`$. The formal statements are [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L25), [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L43), and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L65).

There is a separate finite rigidity before any congruence is taken. For a finite coefficient family $`(c_j,i_j)`$, write

``` math
M=\sum_j c_j i_j!,\qquad
  C_d=\sum_j c_j\frac{i_j!}{(d!)^{\lfloor i_j/d\rfloor}}.
```
If all indices lie in one quotient band $`kd\le i_j<(k+1)d`$, then the quotient $`\lfloor i_j/d\rfloor`$ is constant and the factorial moment factors exactly:

<div id="res:bandbreakpoint" class="theorem">

**Theorem 2** (quotient-band breakpoint). *Under the band hypothesis,
``` math
M=(d!)^k C_d.
```
In particular, in the first band $`d\le i_j<2d`$, channel cancellation $`C_d=0`$ forces $`M=0`$. If all indices are at least $`d`$, channel cancellation and $`M\ne0`$ therefore force at least one index $`i_j\ge2d`$.*

</div>

The exact factorisation is checked for every quotient band at [the band identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean#L71), and its zero-channel consequence is [band cancellation](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean#L91). The first-band form is explicit at [first-band factorisation](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean#L101); the final breakpoint alternative is [breakpoint witness](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean#L130). The hard step is the constant quotient, not a valuation estimate: within one band every factorial has the same extracted power of $`d!`$. Thus a nonzero moment cannot be hidden entirely below $`2d`$ while the $`d`$-channel cancels. This is a finite-family obstruction only. It constructs no cancelling family, says nothing about simultaneous channels or residual size, and does not by itself address the cofinal non-unit-carry input for Problem #68.

Let $`\lambda`$ be a finitely supported integer vector on indices $`n\ge2`$, let $`M=M(\lambda)`$ be its factorial moment, and let $`V_{d}(\lambda)`$ be the $`d`$-th channel numerator. The kernel checks two facts about them.

<div id="res:congruence" class="theorem">

**Theorem 3** (channel congruence). *For every finite integer support and every $`d\ge2`$,
``` math
V_{d}(\lambda)\equiv M(\lambda)\pmod{d!-1}.
```
Consequently $`d!-1`$ divides $`M(\lambda)-V_{d}(\lambda)`$, a vanishing $`d`$-th channel forces $`(d!-1)\mid M(\lambda)`$, and annihilating every channel $`2\le d\le D`$ forces
``` math
L_D=\operatorname{lcm}_{2\le d\le D}(d!-1)\ \Big|\ M(\lambda).
```*

</div>

<div id="res:normalform" class="theorem">

**Theorem 4** (integral normal form). *For every finite integer support and every $`d\ge2`$ there is an integer $`k`$ with $`V_{d}(\lambda)=M(\lambda)+(d!-1)k`$.*

</div>

Theorem <a href="#res:normalform" data-reference-type="ref" data-reference="res:normalform">4</a> is the sharper of the two for design purposes. It says that every zero-moment variation of the support changes the normalised $`d`$-th channel contribution by an integer only. Zero-moment variations therefore cannot manufacture an extra fractional cancellation coordinate: the congruence forces every normalised channel defect to be integral.

Theorem <a href="#res:congruence" data-reference-type="ref" data-reference="res:congruence">3</a> is an obstruction rather than a source of cancellation. Any finite family that kills the low channels must have moment divisible by $`L_D`$. The following checked theorem quantifies the resulting radius cost without assuming an unproved asymptotic for $`L_D`$.

<div id="res:channel-radius" class="theorem">

**Theorem 5** (square-subsequence channel radius). *Let $`t,M,R\in\mathbb N`$. Suppose that $`t\ge2^{32}`$, $`M>0`$,
``` math
L_{2t^2}\mid M,
  \qquad
  M<(R+1)!-1.
```
Then
``` math
3t^3<2(R+1).
```
Consequently, for sequences $`M(t),R(t)`$ satisfying the same three hypotheses for every sufficiently large $`t`$, there is no $`T`$ such that $`2(R(t)+1)\le3t^3`$ for all $`t\ge T`$.*

</div>

The proof is finite. It takes the final block of $`2t`$ factorial gaps below $`D=2t^2`$, bounds their product by $`L_D`$ times an explicit power of $`D`$, and counts the loss from pairwise gcds by the cubic exponent $`\binom{2t+1}{3}`$. A Stirling estimate then converts the factorial upper bound on $`M`$ into the displayed lower bound for $`R`$. The pointwise statement is checked at [the sharp radius theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1222), and its sequence form at [the eventual no-go theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1241). A coarser checked form says that $`R(t)+1`$ cannot be $`o(t^3)`$ under the corresponding hypotheses from $`t\ge4096`$ onward [the little-o obstruction](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1043).

The theorem does not show that a kernel attached to the factorial-gap series has vanishing channels through $`2t^2`$, nor does it construct the positive moment $`M`$ and radius $`R`$ with the stated factorial inequality. It therefore restricts any such channel construction but does not supply the missing cofinal non-unit carries.

For comparison, the returned analysis also proposes the asymptotic form
``` math
\log \operatorname{lcm}_{2\le n\le N}(n!-1)\ \gg\ N^{4/3}\log N
  \qquad(N\to\infty).
```
For the derivation from the cited multiplicity theorem, put
``` math
Q_N=\prod_{2\le n\le N}(n!-1),
  \qquad
  L_N=\operatorname{lcm}_{2\le n\le N}(n!-1).
```
For an odd prime $`p`$, let $`m_p`$ count the indices $`2\le n\le N`$ for which $`p\mid n!-1`$. Such an index necessarily satisfies $`n<p`$. The factorial congruence multiplicity estimate of Garaev, Luca, and Shparlinski \[garaev-luca-shparlinski, arXiv v1, Thm. 12, p. 16\], applied on the interval $`1\le n\le\min(N,p-1)`$, therefore gives $`m_p\ll N^{2/3}`$. (The prime $`2`$ divides none of these factors.) If
``` math
E_p=\max_{2\le n\le N}v_p(n!-1),
```
then
``` math
\log Q_N
  =\sum_p\sum_{n=2}^{N}v_p(n!-1)\log p
  \le \bigl(\max_p m_p\bigr)\sum_p E_p\log p
  \ll N^{2/3}\log L_N .
```
On the other hand, Stirling summation gives $`\log Q_N\asymp N^2\log N`$, proving the displayed lower bound for $`\log L_N`$. The source states the multiplicity theorem, not this lcm corollary; the latter is derived here and is not kernel-checked. It is recorded because it is the shape of the obstruction the returns describe, and it is used nowhere below.

The primitive lcm divisibility survives cofactor removal: factorial valuations do not remove the obstruction once every common cofactor divisor has been removed. A separate corank-one cofactor/determinant argument for constructing such primitive kernels has not yet been formalised; the divisibility theorem does not establish that construction.

<a id="sec:translator"></a>

# A two-term prime channel corrector

The channel obstruction raises a natural question: can a finite support affect exactly one channel? The following two-term construction does so.

<div id="res:translator" class="theorem">

**Theorem 6** (two-term prime channel corrector). *Let $`p`$ be prime and take the coefficient–index pair $`(p,-1)`$ on the indices $`(p-1,p)`$. Then the factorial moment is $`0`$; every channel $`d<p`$ vanishes, by the exact quotient identity $`\lfloor(p-1)/d\rfloor=\lfloor p/d\rfloor`$; every channel $`d>p`$ vanishes, because both indices lie below $`d`$; and the $`p`$-channel numerator is exactly $`p!-1`$.*

</div>

The theorem holds uniformly over all primes. Its use is arithmetic: at zero cost in the moment it supplies a unit in the $`p`$-channel. Adding an integer multiple of this corrector to any candidate kernel shifts the $`p`$-channel numerator by multiples of $`p!-1`$ and leaves every other channel and the moment untouched.

The consequence is already uniform in the support location. For every channel rank and every prescribed cutoff, Lean constructs a factorial-grid kernel and a remote prime-corrector pair entirely beyond that cutoff, with all requested low channels zero, nonzero factorial moment, and residual in $`[-1/2,1/2]`$; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeUnitTranslator.lean#L1657). What is not available is strict nonvanishing: nothing proved here rules out the rounded residual being exactly zero, and no cofinal family with a strictly nonzero rounded residual has been produced. This is the most direct remaining hypothesis, stated in §<a href="#sec:open" data-reference-type="ref" data-reference="sec:open">11</a>.

<a id="sec:plateau"></a>

# Zero plateaux, first exit, and denominator bounds

A second, independent argument works on the rational grid rather than on channels. Let $`H`$ be a partial sum and $`q`$ a candidate denominator. The kernel checks the algebraic grid threshold: writing $`qH=k+r`$ and $`q(S-H)=u`$, the next $`q^{-1}`$ grid point $`(k+1)/q`$ lies below $`S`$ exactly when $`1\le r+u`$. It also checks the [factorial plateau theorem](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L82): if $`H<G\le S`$, if $`n!G`$ is integral, and if $`n!(S-H)<1`$, then the strict successor of $`n!H`$ and the canonical floor of $`n!S`$ are the same grid integer.

Two rigidity statements follow. Consecutive plateau floors, scaled by the next radix, force the canonical factorial digit to vanish. And any first-exit offset $`\delta\in[0,2)`$ with carry $`b=-\lfloor\delta\rfloor`$ satisfies $`b\in\{0,-1\}`$: the exit is rigid, with exactly two alternatives.

The first-crossing argument continues from the exit to a denominator lower bound. For a rational grid level $`G`$, suppose that $`\tau`$ is its first crossing by the literal partial sums and write
``` math
G-H_{\tau-1}=\frac{a}{v},\qquad a,v>0.
```
Then $`v\ge\tau!-1`$. On the $`-1`$ exit branch this strengthens to $`v\ge\tau!(\tau!-1)`$. No coprimality hypothesis on $`a`$ and $`v`$ is required.

There is also a direct obstruction at prime indices. Let
``` math
H_m=\sum_{2\le n\le m}\frac1{n!-1},\qquad
  Z_m=\lfloor m!H_m\rfloor+1,
```
and let $`\Delta_m`$ be the distance from $`(m-1)!H_{m-1}`$ to its strict integer successor. The kernel checks, for $`m\ge3`$, the exact criterion
``` math
m\mid Z_m
  \quad\Longleftrightarrow\quad
  1+\frac1{m!-1}<m\Delta_m\le2+\frac1{m!-1}.
```
If $`S=a/q`$ with $`q>0`$, then for every prime $`p>q`$ the tail bound forces $`p\mid Z_p`$. Consequently, one exact missed prime $`p`$ implies $`q\ge p`$. The rational implementation of $`Z_p`$ agrees with the real-floor definition, and exact kernel reduction gives $`11\nmid Z_{11}`$. Thus every rational representation of $`S`$ has denominator at least $`11`$.

<span id="res:strict-successor-complete-characterization" label="res:strict-successor-complete-characterization"></span> The all-index recurrence is stronger. Define its exact carry by
``` math
Z_m=mZ_{m-1}+1-b_m .
```
If $`S=a/q`$ and $`m-1\ge q`$, the plateau theorem identifies
``` math
Z_{m-1}=\frac{(m-1)!}{q}\,a,\qquad
  Z_m=\frac{m!}{q}\,a=mZ_{m-1},
```
so necessarily $`b_m=1`$. Hence one exact non-unit carry at index $`m`$ forces $`q\ge m`$. Conversely, if $`b_m=1`$ eventually, then $`Z_m/m!`$ is eventually constant. The one-cell bound
``` math
H_m<\frac{Z_m}{m!}\le H_m+\frac1{m!}
```
and the exact tail estimate show that $`Z_m/m!\to S`$; hence that eventual constant is $`S`$ and is rational. Thus
``` math
S\notin\mathbb Q
  \quad\Longleftrightarrow\quad
  (\forall B)(\exists m>B)\ b_m\ne1.
```
The full Erdős problem is now reduced without loss to producing those cofinally many non-unit carries. Exact rational normalization gives
``` math
60\nmid Z_{60},\qquad 64\nmid Z_{64},\qquad 67\nmid Z_{67}.
```

<a id="sec:adjacent-unit-no-go"></a>

## Why the adjacent-unit window is circular

One proposed argument tries to exclude two consecutive unit carries by extracting a prime-power or quotient-gcd obstruction from their cleared width-one window. The exact two-step recurrence shows why this cannot work. Let $`U_k`$ and $`V_k`$ be the positive numerator and denominator of the reduced predecessor gap, and let $`G_k>0`$ be the exact transition normalizer. For $`m\ge3`$, the two unit carries are equivalent to an integer offset $`\Omega_m`$ satisfying
``` math
0<\Omega_m\le D_m.
```
The window denominator telescopes independently of the carry values:
``` math
D_m=V_{m+2}G_{m+1}G_m
     =V_m(m!-1)((m+1)!-1).
```
Under the adjacent-unit assumption, the offset has the matching factorization
``` math
\Omega_m=U_{m+2}G_{m+1}G_m.
```
Cancelling the common positive normalizer therefore reduces the complete window to
``` math
0<U_{m+2}\le V_{m+2},
```
the universal numerator bound for a reduced strict-successor gap.

The four load-bearing formal statements are the [positive-offset window](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L148), [denominator telescope](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L215), [window-denominator identity](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L243), and [unit-pair offset factorization](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L337). They do not disprove adjacent unit carries. They prove that a surviving-prime, prime-power, or quotient-gcd obstruction obtained only after imposing the pair is circular: it rewrites a bound that every reduced positive fraction already satisfies. A successful cofinal argument must constrain the raw predecessor state before the pair assumption, for example through independent prefix arithmetic or an Archimedean non-concentration estimate.

At $`m=60`$ the recurrence also proves $`b_{60}\ne1`$, and hence $`q\ge60`$. Since $`67`$ is prime, the prime-miss theorem applied at $`67`$ gives the stronger checked bound
``` math
S=\frac aq,\ q>0 \quad\Longrightarrow\quad q\ge67.
```
The two formal declarations behind this finite bound make its hypotheses explicit. The generic theorem [single non-unit carry bound](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L812) assumes $`m\ge3`$, an exact carry miss at that index, a positive denominator, and the displayed rational representation, then concludes $`m\le q`$. The source-level specialization [index-$`67`$ denominator bound](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialZeroPlateauCertificates.lean#L136) supplies the prime-index miss used above.

There is a second, more arithmetic mechanism at doubled prime indices. For every odd prime $`p`$, the kernel now specializes the strict-successor prime-power criterion to the literal prefixes:
``` math
p^2\mid Z_{2p}
  \quad\Longleftrightarrow\quad
  \bigl(b_{2p}=1\ \text{and}\ p\mid Z_{2p-1}\bigr)
  \ \text{or}\
  \bigl(b_{2p}=1+p\ \text{and}\ p\mid 2Z_{2p-1}-1\bigr).
```
Consequently, failure of both displayed branches for a cofinal family of odd primes proves $`S`$ irrational. This is a sharper two-stage target than a bare square nondivisibility assertion: it exposes separately the only two carry values and predecessor residues that can survive.

The formal theorem is not restricted to those hand-reduced indices. A separately implemented exact GMP integer computation certifies all $`299998`$ carry cells for $`3\le m\le300000`$. Its unit carries occur exactly at
``` math
52,\ 591,\ 1030,\ 1407,\ 1438,\ 2164,\ 4258,\ 10991,\ 21236,
```
so no further unit carry occurs through the endpoint, where $`b_{300000}\ne1`$. Feeding that exact finite fact to the non-unit-carry theorem strengthens the bound to
``` math
S=\frac aq,\ q>0 \quad\Longrightarrow\quad q\ge300000.
```
The computation uses no floating-point arithmetic; its canonical payload, Python driver, and GMP backend are hash-bound in the companion research packet. This remains a finite exclusion. The new target is to rule out an eventual all-unit carry tail.

There is also a finite peeling identity. For $`x\ne0,1`$ and $`K\ge0`$,
``` math
\frac1{x-1}
  =\sum_{j=1}^{K}\frac1{x^j}
   +\frac1{x^K(x-1)}.
```
When $`x=k!`$ and a chosen factorial scale is divisible by $`(k!)^K`$, the scaled finite sum is integral and only the last term retains the factor $`k!-1`$ in its denominator. The identity isolates one residual fraction before exact bounding; it does not yet give a cofinal family of nonzero residuals.

One proposed strengthening is false and is recorded as such: the divisibility $`(m!-1)\mid\operatorname{den}(V_m)`$ fails at the reported strict events $`m=52`$ and $`m=591`$. Only the Archimedean first-crossing lower bound survives.

<a id="sec:projection"></a>

# Weighted projection rigidity

The third formal layer converts modular disagreement into exclusion.

<div id="res:projection" class="theorem">

**Theorem 7** (projection rigidity). *Suppose the natural endpoint numerator $`Z`$ is congruent to a weighted numerator $`T`$ modulo $`R`$. Then every divisor $`Q`$ of $`R`$ with $`Z\le B<Q`$ satisfies $`T\bmod Q=Z`$. Consequently two divisors $`Q_1,Q_2>B`$ with unequal projected residues exclude any such bounded endpoint; and unequal projections force $`\min(Q_1,Q_2)\le T`$.*

</div>

The leave-one-out specialisation $`Q=R/r`$ also follows. More generally, let $`a,b`$ divide $`R`$ and take the complementary projection moduli $`R/a`$ and $`R/b`$. Lean checks the same quotient cancellation and collision-cap comparison for these factor projections. If $`\gcd(a,b)=1`$, then $`\operatorname{lcm}(R/a,R/b)=R`$, and the resulting branch-free factor-pair floor is at most the global complementary residue. The factors $`a,b`$ may both divide one private quotient. Thus the reduction needs no analytic input and no pair of distinct denominator indices, only suitable factors whose projections or factor-pair floor satisfy the stated bound. This is checked in [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4387) and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4854). <span id="res:split-factor-normalized-collision" label="res:split-factor-normalized-collision"></span>

The transport to the literal factorial block is established directly rather than advisory. Lean builds the collision core $`C`$, private quotients $`r_i`$, private modulus $`R`$, and weighted numerator $`T`$ for the actual denominators $`i!-1`$, and proves both the endpoint congruence modulo $`R`$ and the required coprimality. Moreover, if $`m!-1`$ has canonical large prefix-private primes, then their complete prime-power product divides the single quotient owned by $`m`$ on the tailored block with parameter $`\lfloor m/2\rfloor+1`$, hence divides that block’s $`R`$.

The collision core itself has an exact incremental law. For the positive factorial-gap denominators, adjoining $`d_a`$ to an old finite family $`S`$ gives
``` math
C(S\cup\{a\})
 =\operatorname{lcm}\!\left(C(S),\,
     \gcd\!\left(d_a,\operatorname{lcm}_{j\in S}d_j\right)\right).
```
Indeed, finite-family gcd–lcm distributivity collapses the lcm of all pairwise gcds against $`d_a`$ to this single gcd. The same formula holds after adjoining the distinguished base; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L556) and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L586). Thus each step needs only the old denominator lcm and the old collision core, with no pairwise rescan.

There is also an exact product–lcm bound. If $`\widetilde C(S)`$ denotes the collision core after cancelling a positive distinguished base, while $`L(S)=\operatorname{lcm}_{j\in S}d_j`$ and $`P(S)=\prod_{j\in S}d_j`$, then Lean proves
``` math
\widetilde C(S)L(S)\mid P(S),
 \qquad\text{hence}\qquad
 \widetilde C(S)\le \frac{P(S)}{L(S)}.
```
See [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L800). For the actual factorial block this specializes to
``` math
\operatorname{factorialBlockNormalizedCollisionCore}(p)
 \le
 \frac{\displaystyle\prod_{n\in I_p}(n!-1)}
      {\displaystyle\operatorname{lcm}_{n\in I_p}(n!-1)},
```
where $`I_p`$ is the block index set; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3327). This is an exact quantitative bridge from lower estimates for the factorial-gap lcm to upper estimates for the normalized collision core. It does not itself close the local scale bound: one still needs cofinal estimates strong enough at the selected private factor and factorial scale. A fixed-modulus hit count alone does not supply such control.

The distinguished-base cancellation is now exact prime by prime. Writing $`B=(p-1)!`$ and $`C`$ for the unnormalised factorial-block collision core,
``` math
\widetilde C_p=\frac{\operatorname{lcm}(B,C)}{B}
 =\frac{C}{\gcd(B,C)},\qquad
 v_q(\widetilde C_p)=v_q(C)-\min\{v_q(B),v_q(C)\}.
```
See [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L698), [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L739), and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3394). Consequently $`q^e\mid\widetilde C_p`$ exactly when the pairwise core carries $`q^{e+v_q(B)}`$; in the factorial block this forces two distinct gaps to be divisible by that higher power. Lean moreover proves the sharp surviving valuation cap
``` math
v_q(\widetilde C_p)+v_q((p-1)!)<q.
```
Thus every support prime satisfies $`p-1<q(q-1)<q^2`$, and, whenever $`k(k-1)\le p-1`$, $`\widetilde C_p`$ is coprime to $`k!`$; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3790), [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3982), and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3997). This removes every factorial channel below the moving square-root cutoff, but does not yet bound the aggregate product of the remaining large prime powers at the selected quotient, nor force the complementary projections or residues cofinally. It therefore supplies a stronger exact reduction, not an irrationality proof.

For collision estimates that already provide an upper-half hit, no exponent is lost to normalization. If $`q`$ divides a displayed factorial gap at some $`n\ge p`$, then $`q\nmid(p-1)!`$, and Lean proves for every $`e>0`$ that
``` math
q^e\mid\widetilde C_p\quad\Longleftrightarrow\quad q^e\mid C_p.
```
See [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5012) and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5113). Combined with the two-hit theorem, this identifies every complete normalized upper-hit contribution with repeated full-power load in two distinct displayed gaps. The remaining arithmetic task is to aggregate those moving loads strongly enough for the normalized collision cap; this equivalence does not provide that estimate or the complementary-residue bound.

This bridge has an exact incidence-count form. For an upper-hit prime $`q`$ and every $`e>0`$, Lean proves
``` math
q^e\mid\widetilde C_p
 \quad\Longleftrightarrow\quad
 1<\#\{i\in I_p:q^e\mid i!-1\}.
```
See [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5144). Hence a source estimate giving at most one $`q^e`$-hit deletes that exponent from the normalized core and yields $`v_q(\widetilde C_p)<e`$; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5187). The remaining problem is genuinely aggregate: obtain sufficiently uniform incidence bounds over all moving support primes and exponents, multiply the surviving valuation contributions, and still close the complementary-residue coordinate.

The local aggregation is now exact. For every upper-hit prime $`q`$, Lean proves
``` math
v_q(\widetilde C_p)
 =
 \#\left\{e\in[1,q-1]:
   1<\#\{i\in I_p:q^e\mid i!-1\}\right\};
```
see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5213). There is therefore no additional valuation loss between prime-power incidence estimates and the complete local collision exponent. The open step is to bound these layer counts uniformly as $`q`$ and $`p`$ move, then control the product over all surviving primes strongly enough for the normalized collision cap; this theorem does not supply that global estimate.

The same local load now has a distance-sensitive witness. Put $`B=(p-1)!`$. If $`q`$ is prime, $`e>0`$, and $`q^e\mid\widetilde C_p`$, Lean produces $`i<j`$ in $`I_p`$ such that
``` math
q^{e+v_q(B)}\mid i!-1,\qquad
 q^{e+v_q(B)}\mid j!-1,\qquad
 q^{e+v_q(B)}\le j^{\,j-i}.
```
See [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3668). Consequently, if
``` math
(2p-1)^d<q^{e+v_q(B)},
```
then some such two hits satisfy $`d<j-i`$; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3698). The spacing hypothesis in that reduction is now discharged internally.

If $`q`$ is prime, then any two $`q^e`$-hits $`i<j`$ satisfy $`e<j-i`$, without an endpoint or large-prime hypothesis; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3472). The point is that $`q\mid j!-1`$ already forces $`j<q`$, while the preceding gap-power inequality converts this automatic size relation into strict separation.

Consequently Lean proves the global primewise diameter ceiling
``` math
q\mid\widetilde C_p
 \quad\Longrightarrow\quad
 v_q(\widetilde C_p)+v_q((p-1)!)<2p-3
```
for every prime $`q`$ and $`p\ge2`$; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3848). The exponent-level version is [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3817). Thus the earlier endpoint-prime estimate is a special case, and even primes already present in the normalization base pay for their base valuation inside the same block-diameter budget. This still does not control how many collision primes occur or the product of their bounded powers; those global estimates, together with the complementary-residue bound, remain open.

The pairwise statement is stronger than the selected-witness form used in that proof. For arbitrary $`q,e`$ and any displayed hits $`i<j`$, Lean proves
``` math
q^e\mid(i!-1),\quad q^e\mid(j!-1)
 \quad\Longrightarrow\quad q^e\le j^{\,j-i};
```
see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3443). Consequently, when $`q`$ is prime and $`e>0`$, every two $`q^e`$-hits in the block satisfy $`e<j-i`$, so the condition holds for every pair and one chosen pair does not suffice; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3472). Every prime-power hit layer is therefore an $`e`$-separated subset of the block. Lean now proves the finite cardinality corollary itself:
``` math
(e+1)\#\{i\in I_p:q^e\mid i!-1\}\le 2p+e-2
```
for $`p\ge2`$, prime $`q`$, and $`e>0`$; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L3602). The unweighted packing step is therefore complete. What remains is to combine it with the exact repeated-layer valuation identity, sum the prime-power weights over all moving collision primes, and prove a global product bound strong enough for the normalized collision cap.

For an endpoint prime carrying one upper-half hit, Lean now performs the first combination exactly. If $`p\ge2`$, $`q`$ is prime, and $`2p-1<q`$, then
``` math
v_q(\widetilde C_p)
 =
 \#\left\{e\in[1,2p-4]:
   1<\#\{i\in I_p:q^e\mid i!-1\}\right\};
```
see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5277). Thus every repeated-hit layer outside the block-diameter window has been removed from the exact local valuation formula. The remaining estimate is still global and weighted: these truncated layer counts must be aggregated over the moving endpoint primes strongly enough to bound their complete prime-power product, and the independent complementary-residue coordinate remains open.

The endpoint incidence criterion itself no longer needs a selected upper-half anchor. For every prime $`q>2p-1`$ and $`e>0`$, Lean proves
``` math
q^e\mid\widetilde C_p
 \quad\Longleftrightarrow\quad
 1<\#\{i\in I_p:q^e\mid i!-1\};
```
see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5389). Thus an at-most-one $`q^e`$ incidence estimate forces $`v_q(\widetilde C_p)<e`$ without first choosing an upper hit; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5410). At $`e=2`$ this gives the conditional squarefree conclusion $`v_q(\widetilde C_p)\le1`$; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5436).

More generally the endpoint inequality can be replaced by the exact condition $`q\nmid(p-1)!`$. For every such prime and every $`e>0`$, Lean proves the same hit-count equivalence; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5319). The at-most-one estimate cuts the normalized valuation below $`e`$, and its $`e=2`$ specialization gives conditional squarefreeness; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5344) and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L5370). Every prime $`q\ge p`$ is absent from $`(p-1)!`$, so this covers the entire moving prime range at and above the block parameter. The result remains conditional: no theorem here supplies the uniform prime-square incidence premise or the global weighted product estimate.

The squarefreeness premise is not proved. An exhaustive modular scan through $`q\le2{,}000{,}000`$ and $`n\le240`$ found four individual square hits and no prime with two such hits. Separately, all $`498{,}501`$ pairs $`2\le a<b\le1000`$ have squarefree $`\gcd(a!-1,b!-1)`$, and the aggregate squarefree-collision scan through $`p=499`$ stays below $`0.374`$ of the upper-descending-factorial logarithmic scale. These are finite exact computations, not theorem authority or an asymptotic incidence bound.

Cofinal prefix-private support itself is unconditional. Given any cutoff $`B`$, Lean chooses a prime $`q\ge B!+5`$, uses Wilson’s theorem to obtain $`q\mid(q-2)!-1`$, and takes the least factorial-gap hit $`m`$ of $`q`$. If $`m\le B`$, then $`q\le m!-1\le B!`$, a contradiction. Hence $`m>B`$; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3097). A finite variant compares the product of a chosen set of primes, each at least $`5`$, with
``` math
\prod_{2\le k\le B}(k!-1).
```
If the prime product is larger, at least one chosen prime has no hit through $`B`$, while Wilson still bounds its least hit by $`q-2`$; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3047). These statements supply private factors, but they do not prove either scale estimate below. In particular, the unconditional construction gives no useful upper bound for $`q`$ in terms of its least hit $`m`$.

Wilson reflection also limits what can be inferred from a prime factor merely because it is linear in a later index. If $`n`$ is odd, $`n<q`$, and $`q\mid n!-1`$, then $`q\mid(q-n-1)!-1`$. When both indices lie in the same block and the reflected hit is earlier, equivalently $`q<2n+1`$, this repeated hit survives predecessor-factorial normalization and its full-block incidence count exceeds one; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3139) and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3231) and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3252). Thus a linear-size divisor need not be private.

Stewart states that for every $`\varepsilon>0`$ there are infinitely many odd $`n`$ whose least prime factor $`q`$ of $`n!-1`$ satisfies
``` math
n<q<
 \left(\frac{\sqrt{145}-1}{8}+\varepsilon\right)n;
```
the printed text explicitly transfers estimate (9) from $`n!+1`$ to $`n!-1`$ \[stewart2004, p. 464\]. Wilson reflection then supplies the earlier hit $`q\mid(q-n-1)!-1`$. The source controls $`q`$ relative to the later index $`n`$, but it does not control $`q`$ relative to the private first-hit index $`m`$. Accordingly it is collision-core input, not the missing private-anchor or global product estimate.

In fact one selected prime $`q`$ already furnishes the exact coprime factor pair $`(1,q)`$: its projection moduli are $`R`$ and $`R/q`$, whose least common multiple is $`R`$. Thus no second selected prime is needed; see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L1419) and [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L1524). There is no hidden equality/disagreement branch in this specialization.

Writing $`\rho`$ for the global complementary residue, Lean proves that the unit-pair floor is exactly
``` math
\min\{\rho,R/q\};
```
see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4701). Consequently the remaining factor-pair scale comparison must simultaneously beat the global complementary-residue coordinate and the local $`R/q`$ coordinate. After using $`L=CR`$, the latter is precisely the collision-cap comparison with the selected factor $`q`$, while the former is the global complementary-residue lower bound. Lean records this as the exact equivalence
``` math
(2p+1)L < 2p^2(2p-1)!\min\{\rho,R/q\}
 \quad\Longleftrightarrow\quad
 \begin{cases}
  (2p+1)L < 2p^2(2p-1)!\rho,\\
  (2p+1)Cq < 2p^2(2p-1)!,
 \end{cases}
```
see [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4766). Thus the factor reduction has no opaque floor premise left: the two surviving arithmetic estimates are exposed independently and neither follows merely from the existence of the selected prime.

<span id="res:moving-factor-scale-split" label="res:moving-factor-scale-split"></span> The irrationality implication works for every natural block parameter at least three, including composite parameters. What remains open is the arithmetic input. Wilson supplies cofinal prefix-private factors without analytic input. The stronger source-backed large-prime selection remains relevant because it supplies a positive-density family and a linear lower bound for $`q`$ relative to the original hit; neither result proves the global complementary-residue bound or the local collision-core bound. The surviving obligation is therefore to prove both sides of this exact branch-free scale split cofinally, packaged by [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L1574).

<a id="sec:companion-orbit"></a>

# A fixed companion-orbit coordinate

The preceding criteria and obstructions change what an attack must prove. There is also a particularly clean exact coordinate for the surviving open problem. Define
``` math
C=\sum_{n\ge2}\frac1{n!(n!-1)}.
```
The elementary identity
``` math
\frac1{n!-1}=\frac1{n!}+\frac1{n!(n!-1)}
```
and absolute convergence give
``` math
\begin{equation}
 C+(e-2)=S.                                      \label{eq:companion-decomposition}
\end{equation}
```

<div id="res:companion-orbit-rationality-boundary" class="theorem">

**Theorem 8** (fixed companion-orbit rationality boundary). *The following statements are equivalent:*

1.  *$`S\in\mathbb Q`$;*

2.  *$`(\lfloor m!C\rfloor+2)\bmod m=0`$ for every sufficiently large $`m`$.*

*Consequently,
``` math
\begin{equation}
 S\notin\mathbb Q
 \quad\Longleftrightarrow\quad
 (\forall B)(\exists m>B)\;
   (\lfloor m!C\rfloor+2)\bmod m\ne0 .
 \label{eq:companion-cofinal}
\end{equation}
```*

</div>

<div class="proof">

*Proof.* First suppose $`S=a/q`$ with $`q>0`$, and take $`m`$ so large that $`q\mid(m-1)!`$. Write
``` math
E_m=m!\sum_{2\le n\le m}\frac1{n!},
 \qquad
 \varepsilon_m=m!\sum_{n>m}\frac1{n!}.
```
Then $`E_m`$ is an integer, $`0<\varepsilon_m<1`$, and $`m!S`$ is an integer divisible by $`m`$. Multiplying <a href="#eq:companion-decomposition" data-reference-type="eqref" data-reference="eq:companion-decomposition">[eq:companion-decomposition]</a> by $`m!`$ therefore gives
``` math
\lfloor m!C\rfloor=m!S-E_m-1.
```
Every summand of $`E_m`$ except the endpoint $`m!/m!=1`$ is divisible by $`m`$. Thus $`E_m\equiv1\pmod m`$ and $`\lfloor m!C\rfloor\equiv-2\pmod m`$.

Conversely, assume the displayed congruence from some index onward. Let $`d_m(C)=\lfloor m!C\rfloor-m\lfloor(m-1)!C\rfloor`$ be the canonical factorial digit. Since $`0\le d_m(C)<m`$, for $`m\ge3`$ the congruence is equivalent to
``` math
d_m(C)=m-2.
```
Choose $`N`$ beyond the exceptional indices. The canonical factorial expansion of $`C`$ then has the form
``` math
C=\lfloor C\rfloor+
   \sum_{m=2}^{N}\frac{d_m(C)}{m!}+
   \sum_{m>N}\frac{m-2}{m!}.
```
Adding $`e-2=\sum_{m\ge2}1/m!`$ and using the telescoping identity
``` math
\sum_{m>N}\frac{m-1}{m!}
 =\sum_{m>N}\left(\frac1{(m-1)!}-\frac1{m!}\right)
 =\frac1{N!}
```
gives
``` math
S=\lfloor C\rfloor+
   \sum_{m=2}^{N}\frac{d_m(C)+1}{m!}+\frac1{N!},
```
which is rational. Negating the eventual statement yields the cofinal formulation above. ◻

</div>

<div id="bdry:companion-orbit-nonconcentration" class="remark">

*Remark 1* (the exact remaining boundary). The remaining problem is to show that $`\lfloor m!C\rfloor\bmod m`$ differs from $`-2`$ at arbitrarily large indices.

</div>

<a id="sec:nogo"></a>

# Limits of fixed-coordinate arguments

- Residue vectors, their recurrences, and window widths admit synthetic all-hit blocks. They cannot prove irrationality on their own.

- Known pointwise prime congruences, prime-dilation congruences, parity, and the exact prime coefficient formula admit a synthetic rational countermodel.

- Wilson quotients, harmonic sums, $`p`$-adic gamma identities, and factorial residues do not control the required Archimedean floor without an additional coupling theorem. Every prime-window test factors into a sharp Archimedean strict-ceiling condition and a modular divisibility condition, and the missing ingredient is the coupling between them, not more congruences.

- Fixed-denominator scalar canonical-product localisers and rank-saturated consecutive-jet Hermite–Padé systems pay the full factorial-gap denominator. For $`E(z)=\prod_{n\ge2}(1-z/n!)`$ the genus-zero product satisfies $`-E'(1)/E(1)=S`$, and the natural scalar linear form carries the coefficient $`Q_N=\prod_{2\le n\le N}(n!-1)`$, for which $`Q_N`$ times the tail diverges. Exact first-order interpolation, scalar residue weighting, the natural Wronskian, and rank-saturated consecutive jets all reassemble the same prohibitive denominator.

- Zero-moment variations cannot create an additional fractional cancellation coordinate (§<a href="#sec:channels" data-reference-type="ref" data-reference="sec:channels">4</a>), and factorial valuations cannot absorb the channel LCM obstruction.

- <span id="bdry:fixed-owner-absorption" label="bdry:fixed-owner-absorption"></span>A fixed pair of low-index private owners cannot make the projection argument cofinal. If the owner index $`n`$ is fixed and $`p>n!-1`$, then $`n!-1\mid(p-1)!`$, so its private quotient in the factorial block at $`p`$ is exactly one. Lean checks this uniformly in [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L2677) and checks the two-owner consequence in [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L2707). Thus the large private quotients seen at small blocks—for example the factor $`719`$ owned at $`n=6`$—are finite-range phenomena. The factor-level reduction does not require two moving denominator indices: two factors inside one moving private quotient can suffice. It still requires selected nontrivial factors that escape with $`p`$.

<a id="sec:finite"></a>

# Finite certificates

<a id="a-denominator-bound-from-a-certified-interval"></a>

## A denominator bound from a certified interval

An exact continued-fraction computation gives
``` math
S=a/q,\quad q>0
 \qquad\Longrightarrow\qquad
 q\ge 2^{39990}>10^{12038}.
```
Set $`D=2^B`$, and let $`N`$ be the first index with $`N!-1>D`$. Define
``` math
\ell=\sum_{n=2}^{N-1}\left\lfloor\frac{D}{n!-1}\right\rfloor,
 \qquad
 u=\ell+(N-2)+\left\lfloor\frac{2D}{N!-1}\right\rfloor+1.
```
Each rounded prefix term loses less than one. Also $`(n+1)!-1>(n+1)(n!-1)`$, so the tail starting at $`N`$ is less than $`2/(N!-1)`$. Hence $`\ell/D<S<u/D`$.

Apply the continued-fraction algorithm to both rational endpoints. Retain a partial quotient only when their integer parts agree; subtract that integer and invert the two remainders, reversing their order. Stop when the integer parts disagree or an endpoint remainder is zero. Every retained quotient therefore belongs to every real number in the interval. If such a number is rational, its continued fraction cannot terminate before this shared prefix. Its reduced denominator is consequently at least the denominator of the last retained convergent, computed by
``` math
Q_{-2}=1,\qquad Q_{-1}=0,\qquad Q_k=a_kQ_{k-1}+Q_{k-2}.
```
For $`B=80000`$, the enclosure has scaled width $`u-\ell=7053`$ and forces $`23449`$ partial quotients. The last convergent denominator is at least $`2^{39990}`$. The replay also verifies directly that the preceding convergent lies outside the enclosure. All enclosure, quotient, and denominator operations use integers; the decimal inequality above is checked by integer exponentiation. The [integer replay](https://github.com/wcook04/plectis-erdos/blob/cd3bd6fe245867a435e15d503ccedd699c5d02e2/scripts/check_erdos68_continued_fraction.py) and its [receipt](https://github.com/wcook04/plectis-erdos/blob/cd3bd6fe245867a435e15d503ccedd699c5d02e2/verification/erdos68-continued-fraction.json) accompany the calculation.

The divisibility exclusion $`q\nmid299999!`$ from the carry certificate is a different restriction. It requires a prime-power divisor that does not divide $`299999!`$, whereas the continued-fraction certificate bounds the denominator’s size. In particular, a denominator with no prime factor above $`299999`$ can still satisfy the divisibility exclusion if one prime occurs to a sufficiently high power.

<a id="which-prime-powers-survive-prefix-reduction"></a>

## Which prime powers survive prefix reduction

A prime dividing a displayed denominator can disappear when the prefix is reduced. The cancellation is controlled by all indices with maximal valuation, rather than by a single factorial congruence.

<div id="res:prime-pole" class="proposition">

**Proposition 9** (maximal-hit cancellation). *Let $`M\ge2`$, put $`d_n=n!-1`$ for $`2\le n\le M`$, and write
``` math
L=\operatorname{lcm}(d_2,\ldots,d_M),\qquad
 B=\sum_{n=2}^M L/d_n,\qquad H_M=B/L.
```
For a prime $`p\mid L`$, let $`e=v_p(L)`$ and $`J=\{n:2\le n\le M,\ v_p(d_n)=e\}`$. If $`d_n=p^e u_n`$ for $`n\in J`$, then
``` math
B\equiv \frac{L}{p^e}\sum_{n\in J}u_n^{-1}\pmod p.
```
Consequently the reduced denominator of $`H_M`$ contains $`p^e`$ if and only if $`\sum_{n\in J}u_n^{-1}\ne0`$ in $`\mathbb F_p`$.*

</div>

<div class="proof">

*Proof.* Write $`L=p^eW`$, where $`p\nmid W`$. If $`v_p(d_n)<e`$, then $`p\mid L/d_n`$. If $`n\in J`$, the integer identity $`u_n(L/d_n)=W`$ gives $`L/d_n\equiv Wu_n^{-1}\pmod p`$. Summing proves the congruence. The reduced denominator is $`L/\gcd(B,L)`$; the [prime-power survival criterion](https://github.com/wcook04/plectis-erdos/blob/0d34630e1cc9d2b1ac6edfa7cfdba83b31bdc8fe/ErdosProblems/Erdos68/PrimePoleDenominator.lean#L41) gives $`p`$-valuation $`e`$ exactly when $`p\nmid B`$. Since $`W`$ is nonzero modulo $`p`$, this is the [maximal-hit cancellation criterion](https://github.com/wcook04/plectis-erdos/blob/6e28e93fc9d8d67c382260b5f3d5fa65ceb2363d/ErdosProblems/Erdos68/PrimePoleCriterion.lean#L223). ◻

</div>

At the endpoint $`M=p-1`$ with $`p\ge5`$, Wilson’s theorem supplies the hit $`n=p-2`$. It need not survive reduction. Exact multiplication modulo $`p^2`$ gives
``` math
\begin{array}{c|c|c|c}
 p & J & (u_n\bmod p)_{n\in J} & \sum_{n\in J}u_n^{-1}\bmod p\\
 \hline
 139 & 69,122,137 & 6,49,73 & 116+122+40=0\\
 2593 & 349,2243,2591 & 1508,1566,1678 & 1367+356+870=0
\end{array}
```
In both cases $`e=1`$, so $`p`$ disappears from the reduced prefix denominator. The calculation requires only the recurrence $`r_1=1`$, $`r_n\equiv nr_{n-1}\pmod{p^2}`$: a hit has $`r_n\equiv1\pmod p`$, and its lifted cofactor is $`(r_n-1)/p\pmod p`$. Neither list contains a hit with $`r_n=1`$ modulo $`p^2`$.

<a id="finite-channel-and-carry-certificates"></a>

## Finite channel and carry certificates

The finite-support vector $`\lambda=2e_3-e_4`$ has, by kernel check, $`V_2=0`$, factorial moment $`-12`$, $`V_3=-2`$, $`V_4=11`$, and $`V_d=-12`$ for every $`d\ge5`$. Under the exact rational tail enclosure $`1/119<\Theta_4<1/50`$, its [residual](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L156) lies strictly between $`-93/575`$ and $`-309/13685`$; in particular it is nonzero and subunit.

Exact integer regeneration verifies the canonical primitive kernels for every $`2\le D\le12`$: channels $`2`$ through $`D`$ vanish, the factorial moment is $`L_D`$, and the coefficient content is one. At $`D=9`$ the moment is $`L_9=31540008254514077395`$ and, after the stated prime-unit shift, $`1353/100000<R_9<1354/100000`$. At $`D=3`$ the vector $`c=(-40,55,-10,1)`$ on the support $`(3,4,5,6)`$ annihilates channels $`2`$ and $`3`$, has moment $`600`$, and satisfies
``` math
0.09925341997208298<L_3(c)<0.09925341997208300 .
```
This excludes denominators dividing $`600`$.

There are two different computations at the same endpoint. A returned interval computation reports the stronger geometric statement that no zero-branch event occurs at any $`m\le100000`$; its cited executable and source digest were not supplied, so that zero-branch classification remains external finite evidence. The strict-successor carry computation used above is local and independently regenerated: its exact source, GMP backend, canonical payload, and receipt digests form the certificate archive. The local certificate establishes $`b_{300000}\ne1`$. It excludes more than denominators below $`300000`$. If $`q\mid(m-1)!`$ and $`m\ge3`$, the two numbers $`(m-1)!S`$ and $`m!S`$ are integers. The tail bound
``` math
0<k!(S-H_k)<\frac{2k!}{(k+1)!-1}<1\qquad(k\ge2)
```
then gives $`Z_k=k!S`$ at $`k=m-1,m`$. Substitution into $`Z_m=mZ_{m-1}+1-b_m`$ forces $`b_m=1`$. Thus the certified non-unit carry at $`m=300000`$ gives $`q\nmid299999!`$, and in particular $`q\ge300000`$.

<a id="sec:open"></a>

# Open problems

The exact frontier comes first:
``` math
S\notin\mathbb{Q}
 \quad\Longleftrightarrow\quad
 (\forall B)(\exists m>B)\;m\nmid Z_m
 \quad\Longleftrightarrow\quad
 (\forall B)(\exists m>B)\;b_m\ne1.
\tag{9.1}\label{eq:exact-frontier68}
```
The finite mechanisms in the preceding sections need one of the following cofinal inputs. The table pairs each missing input with the formal result that would consume it.

<div class="center">

| Missing input | Available consequence | Present limitation |
|:---|:---|:---|
| Cofinal non-unit carries, or equivalently cofinal misses $`m\nmid Z_m`$ | Irrationality by <a href="#eq:exact-frontier68" data-reference-type="eqref" data-reference="eq:exact-frontier68">[eq:exact-frontier68]</a> | Only isolated finite misses are known. |
| Cofinal quantitative private-residue and collision-scale bounds | Endpoint exclusion on an unbounded family of prime blocks | Private-prime hits are qualitative; no required lower bound is proved. |
| Cofinal lower-endpoint escape or failure of both doubled-prime branches | A non-unit carry at each selected index | The relevant cylinder and branch theorems are conditional. |
| Cofinal strictly nonzero translated Cramer residuals | Remote finite channel cancellation without integral collapse | Rounding gives absolute value at most $`1/2`$, but the residual may be zero. |

</div>

Each problem below gives a sufficient input for <a href="#eq:exact-frontier68" data-reference-type="eqref" data-reference="eq:exact-frontier68">[eq:exact-frontier68]</a>; none is an equivalent reformulation.

<a id="weighted-collision-mass-and-the-complementary-residue"></a>

## 1. Weighted collision mass and the complementary residue

For the factorial block $`I_p=\{2,\ldots,2p-1\}`$, let $`\widetilde C_p`$ be the normalised collision core and put
``` math
h_{r,e}(p)=\#\{i\in I_p:r^e\mid i!-1\}.
```
The formal spacing bound is
``` math
h_{r,e}(p)(e+1)\le2p+e-2,
```
and on the relevant upper-hit or base-omitted support the complete local valuation is the repeated-layer count
``` math
v_r(\widetilde C_p)=\#\{e\ge1:h_{r,e}(p)>1\}.
```
Let $`M_p`$ denote the moving private modulus, let $`q\mid M_p`$ be the selected prefix-private factor, let $`L_p=\widetilde C_pM_p`$, and write $`\rho_p=(-T_p)\bmod M_p`$ for the least nonnegative complementary residue of the explicit reciprocal-tail numerator.

<div id="prob:weighted-collision68" class="problem">

**Problem 10** (weighted collision-product control). Prove on an unbounded family of tailored prime blocks both
``` math
\sum_r\#\{e:h_{r,e}(p)>1\}\log r
 <
 \log\!\left(
  \frac{2p^2}{2p+1}\,
  \frac{\prod_{j=p}^{2p-1}j}{q}\right),
\tag{9.2}\label{eq:weighted-collision68}
```
and the independent complementary-residue inequality
``` math
(2p+1)L_p<2p^2(2p-1)!\rho_p.
\tag{9.3}\label{eq:complementary68}
```
An average-over-$`p`$ theorem is admissible if its constants force these strict inequalities cofinally.

</div>

The first inequality is the local collision-core half of the exact factor-pair scale split; the second is its Archimedean half. A count of collisions without the weights $`\log r`$, a terminal Wilson event by itself, or a fixed finite scan does not answer the problem. Nor may reflected hits be discarded: the reflection theorem shows that they can contribute genuine collision primes.

<a id="nonterminal-prime-power-amplification"></a>

## 2. Nonterminal prime-power amplification

Write the reduced predecessor gap as
``` math
\Delta_n=\frac{u_n}{v_n},
```
and let $`B_n`$ be the repeated-support part of $`n!-1`$. The amplification modulus is
``` math
A_n=\prod_{\substack{q\mid B_n\\
             v_q(v_n)<v_q(n!-1)}}q^{v_q(n!-1)}.
```
Lean proves the [divisibility $`A_n\mid v_{n+1}`$](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L5604) and, when $`A_n>1`$, the [nonzero numerator projection](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L5619) modulo the whole product.

<div id="prob:amplification68" class="problem">

**Problem 11** (cofinal valuation amplification). Prove that there is $`\eta>0`$ and infinitely many genuinely nonterminal indices $`n`$ such that
``` math
\log A_n\ge\eta\log v_{n+1},
\tag{9.4}\label{eq:amplification-mass68}
```
or, closer to the endpoint criterion, that with $`m=n+1`$ and $`d=A_n`$,
``` math
\bigl((m+2)m!-2\bigr)v_m
 \le m^2(m!-1)(u_m\bmod d).
\tag{9.5}\label{eq:amplification-endpoint68}
```
Equivalently, establish an infinitude or quantitative frequency theorem for the exact first-order lift
``` math
q^2\mid n!-1
 \quad\Longleftrightarrow\quad
 \frac{k!-1}{q}+\frac{D-1}{q}\equiv0\pmod q,
 \qquad D=n(n-1)\cdots(k+1),
```
at repeated nonterminal hits $`q\mid k!-1`$ and $`q\mid n!-1`$.

</div>

Mere nonzero projection is insufficient: the least representative in <a href="#eq:amplification-endpoint68" data-reference-type="eqref" data-reference="eq:amplification-endpoint68">[eq:amplification-endpoint68]</a> must be of order roughly $`v_m/m`$. Fixed-modulus $`q`$-adic convergence and finitely many record events do not change the quantifier.

<a id="escape-from-the-lower-endpoint-interval"></a>

## 3. Escape from the lower endpoint interval

Let
``` math
\mathcal E_p=p!\sum_{n>p}\frac1{n!-1}.
```
The lower unit-carry branch is exactly
``` math
1+\frac1{p!-1}<p\Delta_p
 \le1+\frac1{p!-1}+\mathcal E_p,
 \qquad \mathcal E_p<\frac2p.
```

<div id="prob:lower-cylinder68" class="problem">

**Problem 12** (cofinal lower-endpoint escape). Prove for infinitely many primes $`p`$ that
``` math
1+\frac1{p!-1}+\frac2p\le p\Delta_p.
\tag{9.6}\label{eq:lower-cylinder68}
```
Equivalently, prove the integer inequality
``` math
\bigl((p+2)p!-2\bigr)v_p
 \le p^2(p!-1)u_p,
```
or a growing-modulus version with $`u_p`$ replaced by $`u_p\bmod d_p`$ for a specified divisor $`d_p\mid v_p`$.

</div>

Any positive answer yields a non-unit carry directly and proves irrationality. Congruence recurrences alone do not count: synthetic models satisfy the available congruences while remaining in the unit-carry branch. Nor is a zero canonical digit the same statement as membership in this narrow Archimedean cylinder.

<a id="failure-of-the-two-exact-doubled-prime-branches"></a>

## 4. Failure of the two exact doubled-prime branches

For every odd prime $`p`$, the [doubled-prime criterion](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L257) is
``` math
p^2\mid Z_{2p}
 \quad\Longleftrightarrow\quad
 \begin{cases}
 b_{2p}=1\ \text{and}\ p\mid Z_{2p-1},\\
 \text{or}\\
 b_{2p}=1+p\ \text{and}\ p\mid2Z_{2p-1}-1.
 \end{cases}
\tag{9.7}\label{eq:double-prime68}
```

<div id="prob:double-prime68" class="problem">

**Problem 13** (cofinal doubled-prime branch failure). Prove that infinitely many odd primes $`p`$ satisfy simultaneously
``` math
\neg\bigl(b_{2p}=1\land p\mid Z_{2p-1}\bigr),
 \qquad
 \neg\bigl(b_{2p}=1+p\land p\mid2Z_{2p-1}-1\bigr).
\tag{9.8}\label{eq:double-branch-fail68}
```
A valid generalisation may replace $`2p`$ by $`kp`$ for one fixed $`k`$, provided it uses the checked unique-slot prime-power criterion.

</div>

Controlling only the predecessor residue or only the possible Archimedean carry does not meet the hypotheses; the theorem must couple them.

<a id="a-finite-cramer-block-across-floor-discontinuities"></a>

## 5. A finite Cramer block across floor discontinuities

For $`n,t\ge0`$, put $`s_n=((n+2)!)^2`$ and $`i_{n,t}(j)=(t+j)s_n`$ for $`0\le j\le n+1`$. Let $`A_{n,t}`$ be the $`(n+2)\times(n+2)`$ integer matrix whose first row is $`i_{n,t}(j)!`$ and whose row indexed by $`d\in\{2,\ldots,n+2\}`$ is
``` math
\frac{i_{n,t}(j)!}{(d!)^{\lfloor i_{n,t}(j)/d\rfloor}}.
```
This is the literal augmented factorial-grid channel/moment matrix. Let $`c_{n,t}`$ be its Cramer vector, and
``` math
N_d(n,t)=
 \det\!\bigl(A_{n,t}\text{ with its moment row replaced by the $d$-channel row}\bigr).
```
The determinant identities give
``` math
\mathcal R_{n,t}
 =\sum_{d>n+2}\frac{N_d(n,t)}{d!-1}
 =\det(A_{n,t})S+K_{n,t},
 \qquad K_{n,t}\in\mathbb{Z},
\tag{9.9}\label{eq:cramer-residual68}
```
and $`N_d(n,t)=\det(A_{n,t})\ne0`$ after the largest support index. The finite intermediate block crosses floor discontinuities and has genuine sign changes.

<div id="prob:cramer68" class="problem">

**Problem 14** (Cramer residual nonintegrality). Construct an unbounded family $`(n,t)`$ for which
``` math
\mathcal R_{n,t}\notin\mathbb{Z},
```
preferably by an exact certificate
``` math
0<
 \left|\mathcal R_{n,t}
   -\operatorname{round}(\mathcal R_{n,t})\right|
 \le\frac12,
```
or by the integral cofactor inequality
``` math
0<|N(I,D)|<\Delta(I,D),
\tag{9.10}\label{eq:cramer-minors68}
```
where $`\Delta(I,D)`$ is the gcd of the maximal minors.

</div>

A termwise sign assertion is not admissible: adjacent signs already change. Nor does simply asking for $`\det(A_{n,t})S\notin\mathbb{Z}`$ add information to the original scalar problem. A solution must use an exact determinant or finite-difference identity, a valuation or parity obstruction, a cancellation bound, or a gcd-of-minors argument controlling the finite oscillatory block.

Erdős #68 remains open. Every rational representation with positive denominator has $`q\ge300000`$.

<a id="statements-and-declarations"></a>

# Statements and declarations

The checked core is the canonical factorial digit kernel, the finite defect automaton algebra, floor-factorial channel arithmetic, the channel congruence and its integral normal form, the two-term prime corrector, weighted projection rigidity, the factor-split projection reduction, the fixed-index factorial-base absorption no-go, the rational-grid plateau and first-exit results, the first-crossing denominator bounds, and the literal-prefix prime obstruction through the exact $`p=11`$ instance, strengthened by the all-index eventual-unit-carry theorem and the exact reductions at $`m=60,64,67`$, the bound $`q\ge67`$, and the finite geometric peeling identity. It also checks the normalized strict-successor step and its finite factorial-series expansion in the carry defects $`1-b_m`$, the convergence $`Z_m/m!\to S`$, and the exact equivalence between irrationality and cofinally many non-unit carries. Source-current Lean additionally checks the fixed companion-orbit rationality boundary and its cofinal-miss dual; the staged Comparator package exposes those endpoints as one concise composite and keeps them subordinate to the actual channel and moving-factor advances. The GMP carry certificate through $`m=300000`$ is regenerated separately and hash-bound; combined with the checked carry theorem it gives $`q\ge300000`$, but it is not itself a Lean evaluation.

The weighted primitive support decomposition and the determinant-quotient reduction are returned derivations that have not been kernel-checked here, and are labelled as such wherever they appear. The factorial-gap lcm growth bound is derived here from the exact factorial-congruence multiplicity theorem of Garaev–Luca–Shparlinski \[garaev-luca-shparlinski, arXiv v1, Thm. 12, p. 16\]; it is source-verified, not kernel-checked here, and unused in the preceding results.

<a id="app:sources"></a>

# Guide to the formal sources

The public `ErdosProblems.Erdos68` package contains the checked source for this note. The cited modules include: `AdjacentUnitCarryWindow`, `CanonicalFactorialDigits`, `ChannelBreakpointRigidity`, `ChannelIntegralCongruence`, `DivisorFactorialCentre`, `EndpointWeightedPrivateSupport`, `FactorialAnalyticBoundary`, `FactorialCarry`, `FactorialChannelCertificate`, `FactorialZeroPlateau`, `FiniteDefectAutomaton`, `GapScalarNormalForm`, `PrimeThresholdParity`, `PrimeUnitTranslator`, `PrimeZeroBranch`, and `StrictSuccessorArithmetic`. The declaration links are pinned to the formal-source commit listed at the start of this note.

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L148)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L215)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L243)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/AdjacentUnitCarryWindow.lean#L337)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L812)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialZeroPlateauCertificates.lean#L136)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L986)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialGapPlateauCore.lean#L945)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L6146)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/EndpointWeightedPrivateSupport.lean#L4766)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/PrimeUnitTranslator.lean#L1559)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L34)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L39)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L44)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L49)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L80)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L88)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L102)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L129)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L146)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L170)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L179)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/DivisorFactorialCentre.lean#L188)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L25)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L39)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L43)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L51)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L55)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L59)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L65)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L101)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L105)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L109)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L112)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L119)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L126)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L133)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L140)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L151)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L156)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1006)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1023)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1043)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1222)

- [](https://github.com/wcook04/plectis-erdos/blob/4ab50e144847a3393fb340341760e5d6907d702e/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L1241)

<a id="source-current-companion-orbit-and-comparator-routes."></a>

#### Source-current companion orbit and Comparator routes.

The complete infinite rationality boundary is checked in `ErdosProblems/Erdos68/CompanionOrbitRationality.lean`. Its paper-facing endpoints are `not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two` and `irrational_factorialGapSeries_iff_cofinal_companion_floor_misses`. The coherent Comparator composite `companionOrbit_completeCharacterization` routes to Theorem <a href="#res:companion-orbit-rationality-boundary" data-reference-type="ref" data-reference="res:companion-orbit-rationality-boundary">8</a> and Remark <a href="#bdry:companion-orbit-nonconcentration" data-reference-type="ref" data-reference="bdry:companion-orbit-nonconcentration">1</a>. The moving-factor Comparator endpoints route to <a href="#res:moving-factor-scale-split" data-reference-type="ref" data-reference="res:moving-factor-scale-split">[res:moving-factor-scale-split]</a>, <a href="#res:split-factor-normalized-collision" data-reference-type="ref" data-reference="res:split-factor-normalized-collision">[res:split-factor-normalized-collision]</a>, and <a href="#bdry:fixed-owner-absorption" data-reference-type="ref" data-reference="bdry:fixed-owner-absorption">[bdry:fixed-owner-absorption]</a>. These source-current modules, Comparator packages, and this manuscript stage require one common immutable public checkpoint before terminal external replay or Palomar readiness is claimed.

<a id="sec:erdos-68-complete-family-map"></a>

# Complete result-family map

This section places every registered family for this problem in the shared 93-family reader order. The five display bands control exposition only; the separate promotion state currently covers 23 families and is reported but does not hide or strengthen any family. Mathematical statements and evidence modes come from the public claim registry. Across all eight problems the public result-atom catalog contains 704 exact packet coordinates; this problem contributes 114. Catalog rows expose bounded statement excerpts plus full-source digests, not a claim that every complete packet statement is reproduced here.

<a id="factorial-carry-characterisation"></a>

## Factorial carry characterisation

**Reader position.** 1 of 93; display band: front door. Formal editorial disposition: promote. These are separate classifications.

**Reader entry.** Erdős 68 is irrational exactly when non-unit carries, equivalently strict-successor divisibility failures, occur arbitrarily far out.

Exact equivalence between irrationality, cofinally many non-unit carries, and cofinal strict-successor divisibility failures.

**Authority and reach.** Lean kernel; Comparator-selected; locally proved result; novelty unassessed.

**Exact boundary.** An exact reformulation does not supply the required cofinal failures.

**Result-atom population.** 33 of 704 public coordinates. The public atom catalog groups them under this family.

**Comparator assurance.** exact selected interface; 2 executable interface(s), 2 repository-registered selected result interface(s).

**Publication placement.** This family remains in the complete long record and is not a short-note headline.

- `ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_nonunit_carries`

- `ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses`

<a id="factorial-channel-and-projection-rigidity"></a>

## Factorial channel and projection rigidity

**Reader position.** 40 of 93; display band: mechanism. Formal editorial disposition: split. These are separate classifications.

**Reader entry.** Two complementary toolkits test Erdős 68: channel linear algebra and weighted endpoint residue rigidity.

Finite quotient-band channel factorisation and breakpoint, channel congruences, a two-term prime-channel corrector, and endpoint-weighted projection rigidity.

**Authority and reach.** Lean kernel; locally proved result; novelty unassessed.

**Exact boundary.** These finite and structural results do not produce a cofinal obstruction.

**Result-atom population.** 63 of 704 public coordinates. The public atom catalog groups them under this family.

**Comparator assurance.** represented by selected interface; 0 executable interface(s), 0 repository-registered selected result interface(s).

**Publication placement.** This family is also admitted to the short note.

- `Erdos68.factorialMoment_eq_factorial_pow_mul_channelNumerator_band`

- `Erdos68.exists_index_ge_two_mul_of_factorialMoment_ne_zero_of_channel_eq_zero`

- `Erdos68.channelNumerator_mod_factorialMoment`

- `Erdos68.primeTranslator_channelResidual_eq_one`

- `ErdosProblems.Erdos68.projection_disagreement_excludes_bounded_endpoint`

<a id="canonical-factorial-digit-termination"></a>

## Canonical factorial digit termination

**Reader position.** 45 of 93; display band: mechanism. Formal editorial disposition: retain. These are separate classifications.

**Reader entry.** For every real x, its canonical factorial digits eventually vanish if and only if x is rational. A zero digit tail forces the initial fractional remainder to vanish: otherwise the radix recurrence grows beyond the canonical bound of one. The proof also constructs the rational witness from the factorial-scale floor.

For every real x, its canonical factorial digits eventually vanish if and only if x is rational. A zero digit tail forces the initial fractional remainder to vanish: otherwise the radix recurrence grows beyond the canonical bound of one. The proof also constructs the rational witness from the factorial-scale floor.

**Authority and reach.** Lean kernel; formalized canonical expansion criterion.

**Exact boundary.** This completes the canonical-expansion equivalence for arbitrary real inputs; no nontermination proof for the factorial-gap series or external challenge replay is supplied.

**Result-atom population.** 1 of 704 public coordinates. The public atom catalog groups them under this family.

**Comparator assurance.** not selected for comparator; 0 executable interface(s), 0 repository-registered selected result interface(s).

**Publication placement.** This family remains in the complete long record and is not a short-note headline.

- `ErdosProblems.Erdos68.exists_rat_eq_iff_eventually_zero_canonicalDigit`

- `ErdosProblems.Erdos68.canonicalRemainder_eq_zero_of_zero_digit_tail`

- `ErdosProblems.Erdos68.exists_rat_eq_of_canonicalRemainder_eq_zero`

<a id="factorial-analytic-growth-boundaries"></a>

## Factorial analytic growth boundaries

**Reader position.** 48 of 93; display band: mechanism. Formal editorial disposition: retain. These are separate classifications.

**Reader entry.** For u_n=n!-1, u\_(n+1)/u_n^2 tends to zero and u_n^(1/2^n) tends to one. The absolute quadratic-growth errors are not summable.

For u_n=n!-1, u\_(n+1)/u_n^2 tends to zero and u_n^(1/2^n) tends to one. The absolute quadratic-growth errors are not summable.

**Authority and reach.** Lean kernel; formalized applicability boundary; no novelty claim.

**Exact boundary.** These limits rule out direct application of the cited fast-growth criteria; they neither formalize those external criteria nor decide factorial-gap irrationality.

**Result-atom population.** 1 of 704 public coordinates. The public atom catalog groups them under this family.

**Comparator assurance.** not selected for comparator; 0 executable interface(s), 0 repository-registered selected result interface(s).

**Publication placement.** This family remains in the complete long record and is not a short-note headline.

- `Erdos68.tendsto_factorialGap_succ_div_sq`

- `Erdos68.not_summable_abs_factorialGap_succ_div_sq_sub_one`

- `Erdos68.tendsto_factorialGap_rpow_one_div_two_pow`

<a id="factorial-conditional-producers"></a>

## Factorial conditional producers

**Reader position.** 64 of 93; display band: frontier. Formal editorial disposition: hold. These are separate classifications.

**Reader entry.** These theorems say exactly which cofinal arithmetic pattern would finish Erdős 68, without proving that the pattern occurs.

Cofinal zero-branch or large private-factor hypotheses imply the required irrationality conclusion.

**Authority and reach.** Lean kernel; conditional reduction.

**Exact boundary.** The producer hypotheses are unproved.

**Result-atom population.** 1 of 704 public coordinates. The public atom catalog groups them under this family.

**Comparator assurance.** not selected for comparator; 0 executable interface(s), 0 repository-registered selected result interface(s).

**Publication placement.** This family is also admitted to the short note.

<a id="factorial-lcm-growth"></a>

## Factorial lcm growth

**Reader position.** 69 of 93; display band: frontier. Formal editorial disposition: hold. These are separate classifications.

**Reader entry.** Factorial-gap denominators grow too quickly for one natural low-height scalar localization strategy.

A paper deduction gives a lower bound for the lcm of factorial-gap denominators using an external multiplicity theorem.

**Authority and reach.** paper argument plus cited theorem; paper plus external theorem.

**Exact boundary.** Comparator cannot certify the cited input or authored deduction.

**Result-atom population.** 3 of 704 public coordinates. The public atom catalog groups them under this family.

**Comparator assurance.** not applicable to comparator; 0 executable interface(s), 0 repository-registered selected result interface(s).

**Publication placement.** This family is also admitted to the short note.

<a id="factorial-finite-certificates"></a>

## Factorial finite certificates

**Reader position.** 82 of 93; display band: technical support. Formal editorial disposition: hold. These are separate classifications.

**Reader entry.** Exact scans reveal which carry patterns survive to index 300000 and where a tempting prime shortcut first fails.

Lean checks small exact misses; a hash-bound GMP scan reaches index 300000 and yields the corresponding finite denominator exclusion.

**Authority and reach.** Lean finite theorem plus external exact certificate; finite computation.

**Exact boundary.** Finite computation does not change the cofinal quantifier.

**Result-atom population.** 12 of 704 public coordinates. The public atom catalog groups them under this family.

**Comparator assurance.** not applicable to comparator; 0 executable interface(s), 0 repository-registered selected result interface(s).

**Publication placement.** This family is also admitted to the short note.

<div class="thebibliography">

9

P. Erdős, *On the irrationality of certain series: problems and results*, in A. Baker (ed.), *New Advances in Transcendence Theory*, Cambridge UP, 1988, pp. 102–109, doi:[10.1017/CBO9780511897184.009](https://doi.org/10.1017/CBO9780511897184.009). T. F. Bloom, *Erdős Problem \#68*. <https://www.erdosproblems.com/68>, accessed 28 July 2026. G. Cantor, *Über die einfachen Zahlensysteme*, Z. Math. Phys. **14** (1869), 121–128. J. Galambos, *Representations of Real Numbers by Infinite Series*, Lecture Notes in Mathematics **502**, Springer, 1976, Chapter 1. doi:[10.1007/BFb0081642](https://doi.org/10.1007/BFb0081642). M. Z. Garaev, F. Luca, and I. E. Shparlinski, *Character sums and congruences with $`n!`$*, Trans. Amer. Math. Soc. **356** (2004), no. 12, 5089–5102. <https://doi.org/10.1090/S0002-9947-04-03612-8>; arXiv:[math/0403422v1](https://arxiv.org/abs/math/0403422). C. L. Stewart, *On the greatest and least prime factors of $`n!+1`$, II*, Publ. Math. Debrecen **65** (2004), no. 3–4, 461–480. <https://publi.math.unideb.hu/paper/989/download/10_5486_PMD_2004_3190.pdf>. W. Koepf and D. Schmersau, *Irrationality of certain infinite series II*, Analysis **31** (2011), 117–124. <https://doi.org/10.1524/anly.2011.1094>. D. Duverney, *Irrationality of fast converging series of rational numbers*, J. Math. Sci. Univ. Tokyo **8** (2001), 275–316. <https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf>. J. Hančl and R. Tijdeman, [*On the irrationality of factorial series*](https://geodesic.mathdoc.fr/articles/10.4064/aa118-4-5/), Acta Arith. **118** (2005), no. 4, 383–401. doi:10.4064/aa118-4-5. K. Barreto, J. Kang, S.-h. Kim, V. Kovač, and S. Zhang, *Irrationality of rapidly converging series: a problem of Erdős and Graham*, arXiv:[2601.21442v3](https://arxiv.org/abs/2601.21442v3), 2026.

</div>
