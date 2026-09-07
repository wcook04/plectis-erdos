# Finite-source certificates and remote support constraints

## Research and exposition report for Erdős problem 68, round 6

7 September 2026. Reviewed against the supplied round-6 short note, research packet, disposition, frozen corpus route and Lean slice. The current short note is **11 pages**, not the 27-page source used in earlier rounds. Its title and first companion-orbit theorem are retained. All statements identified below as new have ordinary proofs in this report; no new Lean build or external priority certification is claimed.

### Main findings

The infinite tail gcd in the channel construction is determined by a prefix of length strictly less than $2D^2$. The previous sufficient horizon was $D^4$. A finite-source test gives substantially smaller certificates in practice and preserves cancellations between the remaining sources. At depth $24$, the scalar prefix through $32$ and two net-source cancellations at $36$ and $48$ certify the same unrestricted minimum moment previously certified using the lcm envelope through $728$.

The same argument extends from one forbidden coefficient to an arbitrary forbidden initial segment. For every fixed cancellation depth $D$ and starting index $r$, the exact minimum positive moment among integer channel kernels supported on $n\ge r$ is computable from a finite integer lattice. An explicit remote determinant proves that lattice has full rank; a factorial cutoff proves that its computed generators exhaust the uncomputed tail.

These statements complete arithmetic optimisation problems inside the channel method. They do not prove irrationality of
\[
S=\sum_{n\ge2}\frac1{n!-1}.
\]
The remaining step concerns the actual real residual, not the solvability of its integer coefficient constraints.

## 1. What is already present

For a finite integer vector $\lambda$, write
\[
W_{d,n}=\frac{n!}{(d!)^{\lfloor n/d\rfloor}},\qquad
M(\lambda)=\sum_n\lambda_n n!,\qquad
V_d(\lambda)=\sum_n\lambda_n W_{d,n}.
\]
Allow an auxiliary coordinate $e_1$ while constructing the coefficient lattice; this introduces no summand $1/(1!-1)$ into $S$. The supplied divisor basis is
\[
T_n=ne_{n-1}-e_n,\qquad
U_n=T_n-\sum_{\substack{d\mid n\\2\le d<n}}W_{d,n}U_d.
\]
It satisfies
\[
M(U_n)=0,\qquad V_d(U_n)=(d!-1)\mathbf1_{d=n}.
\]
The vectors $e_1,U_2,U_3,\ldots$ form an integral basis. With
\[
L_D=\operatorname{lcm}_{2\le d\le D}(d!-1),\qquad
K_D=L_De_1-\sum_{d=2}^D\frac{L_D}{d!-1}U_d,
\]
every low-channel kernel has the unique form
\[
\lambda=tK_D+\sum_{n>D}z_nU_n,\qquad M(\lambda)=tL_D.
\]
The sum is finite. For the actual support $n\ge2$, put
\[
a_D=[e_1]K_D,\qquad u_n=[e_1]U_n.
\]
The single support equation and minimum moment are
\[
t a_D+\sum_{n>D}z_nu_n=0,\qquad
\mu_D=L_D\frac{g_D}{\gcd(g_D,a_D)},\quad
 g_D=\gcd\{u_n:n>D\}.
\]
The scalar recurrence is
\[
u_2=2,\qquad
u_n=-\sum_{\substack{d\mid n\\2\le d<n}}W_{d,n}u_d\quad(n>2).
\]
Odd $u_n$ vanish. For a prime $\ell$,
\[
u_{2\ell}=-\frac{(2\ell)!}{2^{\ell-1}}.
\]
These basis, support and prime-index facts are inherited from the packet. The novelty of this report begins with the use of *finite sources* in the recurrence.

## 2. The finite-source principle

The earlier certificate used a universal divisibility envelope, $\operatorname{lcm}(1,\ldots,n)\mid u_n$. A stronger way to use the recurrence is to separate its already-controlled tail terms from the finite initial segment which can still inject a nonzero residue.

**Proposition 1 (finite-source closure).** Let $N>D\ge2$ and let $g>0$ divide $u_{D+1},\ldots,u_N$. Suppose that, for every $n>N$,
\[
 g\mid B_D(n),\qquad
 B_D(n)=\sum_{\substack{2\le d\le D\\d\mid n}}W_{d,n}u_d.
\tag{1}
\]
Then $g\mid u_n$ for every $n>D$.

**Proof.** Induct strongly on $n$. The indices up to $N$ are assumed. At $n>N$, split the recurrence into divisors $d\le D$ and $d>D$. The first sum is divisible by $g$ by (1). Every term in the second sum is divisible by $g$ by the induction hypothesis, since $D<d<n$. Their negative sum is divisible by $g$. $\square$

The quantifier in (1) is still infinite. The next elementary divisibility makes it finite.

**Lemma 2 (unordered blocks).** For positive integers $d,k$,
\[
 k!\mid W_{d,dk}=\frac{(dk)!}{(d!)^k}.
\tag{2}
\]

**Proof.** The quotient $(dk)!/((d!)^k k!)$ counts partitions of a labelled set of size $dk$ into $k$ unordered blocks, each of size $d$. It is an integer. Equivalently, permuting the $k$ nonempty disjoint blocks acts freely on their ordered partitions. $\square$

The counting fact is classical. Its use to control the finite sources of this particular recurrence is the contribution here; no priority claim is made for (2).

**Corollary 3 (factorial source cutoff).** Suppose $g\mid q!$ and $N\ge D(q-1)$. If $g$ divides $u_{D+1},\ldots,u_N$, then it divides the entire tail after $D$.

**Proof.** If $n>N$ and $d\le D$ divides $n$, then $n/d>q-1$, so $n/d\ge q$. Thus
\[
 g\mid q!\mid(n/d)!\mid W_{d,n}.
\]
Every source in (1) vanishes separately. Apply Proposition 1. $\square$

The mechanism is reusable: once the tail entries are in a target ideal, only the finite initial segment can obstruct invariance of that ideal. It is enough to extinguish those sources. Cancellation between sources may extinguish them earlier than termwise divisibility does.

## 3. A quadratic universal horizon

**Theorem 4.** Let $D\ge2$ and choose a prime $\ell$ with $D/2<\ell\le D$. Put
\[
 H=D(2\ell-1).
\]
Then
\[
\boxed{g_D=\gcd(u_{D+1},\ldots,u_H),\qquad H<2D^2.}
\tag{3}
\]

**Proof.** Bertrand's postulate supplies $\ell$ for $D\ge3$; for $D=2$ take $\ell=2$. The index $2\ell$ is larger than $D$ and at most $H$. If $g$ is the finite gcd through $H$, the inherited prime-index formula gives
\[
 g\mid |u_{2\ell}|=\frac{(2\ell)!}{2^{\ell-1}}\mid(2\ell)!.
\]
In particular $g>0$. Apply Corollary 3 with $q=2\ell$ and $N=H$. Thus $g$ divides every term after $D$, and the finite gcd is the infinite gcd. Finally $H\le D(2D-1)<2D^2$. $\square$

This improves the earlier $D^4$ horizon and shortens its proof. No prime-power valuation identities are required. It is a bound on the largest scalar index needed, not an assertion of polynomial time in the binary length of $D$. The integers themselves can be large.

The choice of $\ell$ matters for a concrete bound: the first prime above $D/2$ gives $H$ close to $D^2$ when that prime is close to $D/2$. Neither an optimal constant nor a universal linear horizon is proved.

## 4. A much smaller certificate which retains cancellation

For a proposed positive finite gcd $g$, define
\[
 h_d=\frac{g}{\gcd(g,u_d)},\qquad
 s_d=\min\{k\ge1:h_d\mid k!\}\quad(2\le d\le D).
\]
The convention $s_d=1$ applies when $h_d=1$. For every $k\ge s_d$, (2) gives $g\mid W_{d,dk}u_d$.

Consequently only the finite pairs
\[
2\le d\le D,\qquad 2\le k<s_d
\]
can produce a nonzero source residue. Record those for which $W_{d,dk}u_d\not\equiv0\pmod g$. At targets $n=dk>N$, add *all* early-source residues, including those from other divisors of the same target. If each such net sum is zero, (1) holds for every $n>N$ and Proposition 1 certifies the tail.

This is an exact finite test with no factorisation requirement. Computing $s_d$ uses factorial divisibility, and all remaining arithmetic is over integers modulo $g$.

### The depth-24 certificate

The scalar prefix through $32$ gives
\[
 g=\gcd(u_{25},\ldots,u_{32})=21684626964000.
\]
The only targets beyond $32$ with individual nonzero early-source residues are $36$ and $48$. Their residues are:

| Target $n$ | Source $d$ | $W_{d,n}u_d\bmod g$ |
|:---:|:---:|---:|
| $36$ | $12$ | $7228208988000=g/3$ |
| $36$ | $18$ | $14456417976000=2g/3$ |
| $48$ | $12$ | $14456417976000=2g/3$ |
| $48$ | $24$ | $7228208988000=g/3$ |

All other early-source terms at these targets vanish modulo $g$. Each net sum is $g$, hence zero modulo $g$. Lemma 2 covers every unlisted target. Proposition 1 therefore proves that this $g$ is $g_{24}$.

The old envelope certificate waited until $728$ because it needed $3^6=729$ inside the ordinary initial-segment lcm. The new certificate uses the scalar values only through $32$, plus finite arithmetic on the early-source terms. The supplied checker separately computes the scalars through $1000$ as an independent diagnostic; those later scalar values are not premises of the compressed certificate.

The two cancellations are also a falsifying example for a tempting strengthening. Requiring each source term to vanish separately would reject a valid tail certificate. Only the sum must vanish. Conversely, observing a gcd plateau at $32$ without these checks would still be insufficient.

The checker returns 59 certified rows, for $2\le D\le60$, using scalar prefixes through $2D$. This is evidence that a linear bound may hold; it is not a proof of a universal $2D$ horizon. The theorem available uniformly is (3).

## 5. Arbitrary forbidden initial segments

The previous scalar calculation excluded only coordinate $1$. A remote-support requirement excludes several coordinates at once, so the natural object is a finite-rank integer lattice.

Fix $D,r\ge2$ and let
\[
P_r:\bigoplus_{n\ge1}\mathbb Ze_n\longrightarrow\mathbb Z^{r-1}
\]
retain coordinates $1,\ldots,r-1$. Put
\[
b_n=P_rU_n,\qquad k=P_rK_D,\qquad
\Gamma_{D,r}=\sum_{n>D}\mathbb Zb_n.
\]
All sums defining generated lattices mean finite integer combinations. A low-channel kernel is supported on $n\ge r$ precisely when
\[
 tk+\sum_{n>D}z_nb_n=0.
\tag{4}
\]
We first prove that $\Gamma_{D,r}$ has full rank, with an explicit finite witness.

**Lemma 5 (remote projection determinant).** Let $\ell>\max(D,r)$ be prime. The $r-1$ columns
\[
 b_{2\ell},b_{3\ell},\ldots,b_{r\ell}
\]
are linearly independent over $\mathbb Q$, and
\[
\boxed{
\left|\det(b_{2\ell},\ldots,b_{r\ell})\right|
=r!\prod_{d=2}^{r}W_{d,d\ell}=:\Delta.
}
\tag{5}
\]

**Proof.** For $2\le d\le r$, the proper divisors of $\ell d$ are either divisors of $d$ or numbers $\ell f$ with $f\mid d$, $f<d$. The projection of $T_{\ell d}$ is zero because both its indices exceed $r-1$. Also $b_\ell=0$. Induction on $d$ in the divisor recursion therefore shows that $b_{\ell d}$ is an integer linear combination of $P_rU_e$, for $e\mid d$, $2\le e\le d$, with diagonal coefficient $-W_{d,d\ell}$. This is a triangular change of columns.

The change from $T_2,\ldots,T_r$ to $U_2,\ldots,U_r$ is integral triangular with diagonal one. The projected columns $P_rT_2,\ldots,P_rT_r$ form a triangular matrix with diagonal $2,3,\ldots,r$. Their determinant is $r!$. Multiplying the diagonal changes proves (5). $\square$

The determinant is generally not a unit. Rational full rank alone would therefore lose the integer obstruction which the optimisation is meant to retain.

### A finite horizon for the whole lattice

Let $q\ge1$ satisfy $\Delta\mid q!$, and set
\[
N_* =\max\{r\ell, D(q-1)\}.
\]

**Theorem 6 (finite remote-support optimisation).** One has
\[
\boxed{\Gamma_{D,r}=\sum_{D<n\le N_*}\mathbb Zb_n.}
\tag{6}
\]
The exact minimum positive moment among integer vectors supported on $n\ge r$ and cancelling channels $2,\ldots,D$ is
\[
\boxed{\mu_{D,r}=L_D\,\operatorname{ord}_{\mathbb Z^{r-1}/\Gamma_{D,r}}(k).}
\tag{7}
\]
It is attained by a primitive vector with upper support at most $N_*$.

**Proof.** Let $\Gamma_*$ be the finite lattice on the right of (6). Its generators include the columns in (5). The adjugate identity gives
\[
\Delta\mathbb Z^{r-1}\subseteq\Gamma_*.
\]
For $n>N_*$, the projection of $T_n$ is zero. Induct strongly in the recurrence for $b_n$. Terms with divisor $d>D$ already lie in $\Gamma_*$. For terms with $d\le D$, one has $n/d\ge q$, so
\[
\Delta\mid q!\mid(n/d)!\mid W_{d,n}.
\]
These terms lie in $\Delta\mathbb Z^{r-1}\subseteq\Gamma_*$. Hence $b_n\in\Gamma_*$, proving (6).

Equation (4) is solvable exactly when $tk\in\Gamma_*$. Since the quotient is finite, its positive solutions $t$ are precisely the multiples of the order in (7). The order can be attained using the finite generators in (6), hence by a vector with upper support at most $N_*$. If an attaining vector had content greater than one, dividing its coefficients by that content would give a smaller positive admissible moment. It is therefore primitive. $\square$

A basis matrix $B$ for $\Gamma_*$, obtained by integer Hermite or Smith normal form, makes the order explicit:
\[
\operatorname{ord}(k)=\operatorname{lcm}\{
\operatorname{den}((B^{-1}k)_j):1\le j<r\}.
\]
This also supplies a dual impossibility certificate. A row of $B^{-1}$ takes integral values on $\Gamma_*$; a nonintegral value on $tk$ proves that the proposed moment multiplier cannot satisfy the support constraints. The integer normal-form facts are standard; (5), (6) and their application to these factorial channels are proved here.

### A sharp small example and a dual certificate

With cancellation depth $D=2$ and starting index $r=4$, the exact minimum is
\[
\boxed{\mu_{2,4}=360.}
\]
For every integer vector supported on $n\ge4$,
\[
360\mid M(\lambda)-4V_2(\lambda).
\]
At $n=4,5$ the summand is zero because $n!=4W_{2,n}$. For $n\ge6$, $360\mid n!$ and $90\mid W_{2,n}$: writing $n=2k$ or $2k+1$, with $k\ge3$, the product
\[
W_{2,2k}=k!\prod_{j=1}^k(2j-1)
\]
is divisible by $6\cdot15=90$, and the odd case has one additional integer factor. Thus the congruence holds term by term. Channel cancellation forces $360\mid M$.

The primitive vector $-15e_4+e_6$ has $V_2=0$ and moment $360$, so the bound is attained. This is an explicit dual obstruction together with a matching construction. Merely imposing $4!\mid M$ would miss the additional factor $15$.

### Consequences and scope

At $r=2$, formula (7) reduces to the supplied scalar minimum-moment formula. Both parameters give divisibility monotonicity:
\[
\mu_{D,r}\mid\mu_{D+1,r},\qquad
\mu_{D,r}\mid\mu_{D,r+1}.
\]
Moreover $r!\mid\mu_{D,r}$, because every supported factorial is divisible by $r!$. Thus minimum-moment families with $r\to\infty$ automatically absorb every fixed denominator. This property does not require nonvanishing of all the fixed-start p-adic limits $\beta_p$.

The older compressed grids already supply denominator absorption for another family. The new result solves the exact minimum-moment problem with *both* cancellation depth and starting index prescribed. Its general finite cutoff can be large, and no competitive bit-complexity claim is made.

## 6. Why the new arithmetic still leaves the real problem

The admitted residual identity is
\[
\mathcal R(\lambda)=M(\lambda)S+K,\qquad K\in\mathbb Z.
\]
More specifically,
\[
\mathcal R\left(tK_D+\sum_{n>D}z_nU_n\right)
=tL_D(S-H_D)+\sum_{n>D}z_n.
\]
At fixed moment, every support correction acts by an integer translation. The new lattice calculations determine the allowable multiplier and give a coefficient witness; they do not generate another fractional coordinate.

For an actual kernel with positive moment $M$ and upper support $N$, put
\[
A_N=\sum_{d=D+1}^{N}\frac{V_d(\lambda)}{d!-1}.
\]
Then
\[
\mathcal R(\lambda)=A_N+M\sum_{d>N}\frac1{d!-1}.
\]
A sufficient separation is
\[
\frac{2M}{(N+1)!-1}<\lfloor A_N\rfloor+1-A_N.
\tag{8}
\]
The tail is positive, so (8) places the residual above $A_N$ and strictly below its next integer, including the case that $A_N$ is integral. Cofinally many such inequalities on an absorbing family would prove irrationality. This report does not establish them.

### A natural route run to its failure point

One might try to use the shortest-support kernels and hope that primitive normalisation also makes the positive tail small. The supplied bounds rule this out for that template. Every nonzero low-channel moment satisfies $L_D\mid M$, while
\[
\log L_D\ge\left(\frac{2\sqrt2}{3}-o(1)\right)D^{3/2}\log D.
\]
If $N=D+O(1)$, then $\log((N+1)!-1)=O(D\log D)$. Therefore
\[
\frac{2|M|}{(N+1)!-1}\longrightarrow\infty.
\]
No strict gap, which is at most one, can meet (8). More generally the already-recorded radius obstruction is
\[
\liminf\frac{N}{D^{3/2}}\ge\frac{4\sqrt2}{9}
\]
for this tail-smallness strategy. It is an inherited result, not a new constant of this round.

The two optimisation objectives must therefore be separated. A short-support theorem answers a linear-algebra question. A real-tail construction needs larger support and control of the signed finite block. The minimum-moment theorem helps only with the multiplier side of that comparison.

The fixed-start $\beta_p$ question likewise has a precise role. All-prime nonvanishing concerns denominator absorption of the minimum-moment sequence with starting index $2$. Absorbing remote families are already available, and Theorem 6 gives arithmetically optimal ones for prescribed starts. Thus resolving $\beta_p\ne0$ for every prime would be useful structural information, but it is not a prerequisite for attacking (8).

## 7. A structural map of the failed routes

**Common-denominator size.** This controls potential prime-power mass. The actual reciprocal cancellations at $139$ and $2593$ show that it does not control the reduced denominator. The missing quantity is the weighted reciprocal-cofactor sum at the maximal valuation layer. Even survival of a layer must then be coupled to a real endpoint gap. The general valuation formula is already attributed in the short note to Louwsma and Martino, Lemma 4.1.

**Private modulus and coprimality.** These ensure a nonzero complementary residue, but allow the residue to equal one. In the global criterion, putting $\eta_p=\rho_p/R_p$ and $\widetilde C_p=C_p/(p-1)!$, the exact missing comparison is
\[
\log\widetilde C_p-\log\eta_p
<\log\frac{2p^2(2p-1)!}{(2p+1)(p-1)!}.
\tag{9}
\]
The right side is $p\log p+(2\log2-1)p+O(\log p)$. The modulus cancels. The collision loss and the complementary-gap loss must be bounded at the same parameters. A joint mean estimate can suffice; estimates on unrelated cofinal sets cannot be combined without an intersection argument.

**Denominator valuation of a predecessor gap.** Writing the reduced gap as $U_m/V_m$, the checked consumer needs
\[
((m+2)m!-2)V_m\le m^2(m!-1)U_m.
\tag{10}
\]
The model gaps $1/q^e$ falsify an implication from high denominator valuation alone to (10). They do not constitute a counterexample arising from the factorial series. A nonterminal amplification argument must retain numerator information and certify the exact threshold. The report does not prove cofinal lower-endpoint escape.

**Marginal carry and residue data.** At twice an odd prime, the two exact branches are
\[
\begin{split}
p^2\mid Z_{2p}\ \Longleftrightarrow\;&
(b_{2p}=1\ \&\ p\mid Z_{2p-1})\\
&\text{or }(b_{2p}=1+p\ \&\ p\mid2Z_{2p-1}-1).
\end{split}
\]
The missing result is a joint exclusion of both events on infinitely many odd primes. Neither a carry frequency nor a separate residue frequency supplies that joint exclusion.

**Zero-moment channel corrections.** These change individual channels but translate the residual integrally. At fixed moment, a determinant or a new basis vector cannot supply a new real fractional coordinate. A successful argument must control (8), or a different exact nonintegrality test for the same residual.

**A finite gcd plateau.** This is insufficient to certify the infinite tail. The new finite-source theorem specifies the missing invariant: invariance of the target ideal under the recurrence after accounting for every early source. The depth-24 cancellations show why the correct invariant concerns the net source rather than its individual summands.

## 8. What the short note should make easy to remember

The current opening already does several things well. It states the two finite exclusions, gives the factorial-divisibility consumer immediately, and keeps a complete proof of the companion-orbit criterion. The revised preview fits the complete divisibility argument on page one. Those are improvements to preserve. The remaining editorial problem is the order inside the channel argument: the residual identity explaining its relevance arrives after the detailed gcd certificate.

Move the residual identity directly after the low-channel classification. The reader should see that a support correction changes the residual by an integer *before* spending a page on the moment ideal. Then the next question, which multipliers are arithmetically available, is motivated rather than imposed.

Keep one local example beside the abstract mechanism. The depth-4 comparison, moment $1380$ with upper support $8$ versus moment $4140$ on support through $6$, is suitable. After adjudication, the quadratic cutoff theorem can replace the longer first stopping discussion. The complete finite-source cancellation example belongs immediately after the proof in the research record; it need not add another large numerical table to the short note.

The first numbered companion theorem should remain first. Its proof is not shortened by hiding the endpoint computation or the canonical-digit bounds. The title and finite lead also remain unchanged. The finite exclusions are theorems about possible rational representations of $S$; they must not be described as an irrationality theorem for $S$ itself.

The last section of the short note should retain the exact canonical target,
\[
(\forall B)(\exists m>B)\ m\nmid Z_m,
\]
followed by the two actual sufficient comparisons (8) and (9). The detailed lower-endpoint, doubled-prime and adjacent-window alternatives belong in the long record. This preserves the failures while avoiding a five-route programme at the conclusion of an otherwise focused note.

## 9. Sources and scholarly positioning

Tao's account of partial progress supports analysing a failed method until the remaining difficulty can be stated precisely [1]. His results-to-effort advice supports including inexpensive explanatory consequences while keeping lengthy variants subordinate [2]. His assessment rubric explicitly includes reusable methods, clarified limitations, instructive near-counterexamples and coherent organisation [3]. These criteria guide the proposed reorganisation; they do not establish that Tao, a journal, or a referee would endorse this paper.

The established ingredients used here include unordered equal-block partitions, Bertrand's postulate, strong induction, finite-index lattice arithmetic, and Hermite/Smith normal form. The contribution claimed within this review is their concrete combination with the supplied factorial-channel recurrence, yielding the quadratic cutoff, cancellation-preserving certificate, and two-parameter remote-support optimisation. External novelty remains unassessed.

The search located Myerson's *What the Least Common Multiple Divides*, **1994**, and the 1996 sequel [4]. The full first paper was not retrievable in this run, so no statement that it lacks the present theorem is warranted. Exact searches for the scalar prefix and factorial-divisor recurrence did not locate a direct antecedent. This is a bounded search outcome, not a proof of priority.

The public GitHub connector successfully returned problem 269's `WeightedPhaseCarry.lean` at the note's supplied public pin [5]. Its exact carry decomposition separates a bounded residue from an integer transfer term. That supplies a genuine cross-problem comparison: eliminating a finite observable does not automatically control the complementary integer transfer. The new lattice theorem transfers only to recurrences with the stated factorial absorption and finite-rank hypotheses; Boolean support restrictions or unrelated dynamical recurrences need a separate admissibility argument.

Palomar's stated mechanical and semantic screening does not replace assessment of mathematical interest or novelty [6]. No acceptance, submission, or fresh Comparator run is claimed here.

### References

[1] T. Tao, *On the importance of partial progress*, author's website, accessed 7 September 2026. <https://terrytao.wordpress.com/career-advice/on-the-importance-of-partial-progress/>

[2] T. Tao, *Maximising the results-to-effort ratio*, author's website, accessed 7 September 2026. <https://terrytao.wordpress.com/advice-on-writing-papers/maximising-the-results-to-effort-ratio/>

[3] T. Tao, *Submit to an appropriate journal*, assessment rubric, author's website, accessed 7 September 2026. <https://terrytao.wordpress.com/advice-on-writing-papers/submit-to-an-appropriate-journal/>

[4] G. Myerson, *What the Least Common Multiple Divides*, Journal of Number Theory **48** (1994), 80–87, doi:10.1006/jnth.1994.1054. G. Myerson and J. W. Sander, *What the Least Common Multiple Divides, II*, Journal of Number Theory **61** (1996), 67–84, doi:10.1006/jnth.1996.0138. Bibliographic records inspected; full antecedent comparison remains outstanding.

[5] W. Cook and contributors, *WeightedPhaseCarry.lean*, supplied public repository snapshot, theorem `carry_eq_residueDigit_add_coboundary`. <https://github.com/wcook04/plectis-erdos/blob/32545d77c4b5cfd72ebd36c8dcd2418bf7cc4d31/ErdosProblems/Erdos269/WeightedPhaseCarry.lean>

[6] T. Tao, *Palomar – a registry of Lean verified mathematics*, 18 August 2026. <https://terrytao.wordpress.com/2026/08/18/palomar-a-registry-of-lean-verified-mathematics/>

## 10. Verification and remaining questions

The exact standard-library checker produced 59 finite-source certificates for depths $2$ through $60$, 32862 finite block-divisibility tests, and 14 remote projection determinant tests. It also checked the small remote-support witness and 97 instances of its termwise dual congruence. It independently checked scalar divisibility through $1000$. The depth-24 certificate is reproduced separately with its shorter prefix and two source cancellations. These finite checks test the proofs; the proofs of (2), Proposition 1 and Theorem 4 justify their infinite reach.

No new Lean build was possible in the local environment: `lean` and `lake` were absent, and the attempted toolchain fetch failed at DNS resolution. The returned Lean file is an uncompiled draft of the finite-source closure argument with its hypotheses explicit. It does not formalise the unordered-partition divisibility or claim that the factorial specialisation has been kernel-checked. The existing packet's formalisation claims have not been reclassified.

The $300000$ carry census and $80000$-bit continued-fraction enclosure were not rerun. Their displayed bounds remain supplied evidence. None of the five cofinal producers in the mandate was established or refuted for the actual factorial series.

The most natural additional questions are now specific. Does the empirical cutoff $2D$ hold for every depth? Can the remote-support minimum-moment algorithm be made quantitatively efficient? Can an absorbing family with appropriately large upper support satisfy the signed-block comparison (8) cofinally? The first two concern the arithmetic classification developed here. The third would change the status of the original irrationality problem.
