# Audit of Sun v1: the same-scalar estimate does not yield its claimed decay

**Source and scope.** Zhi-Wei Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1, submitted 3 September 2026. The supplied original TeX is `literature/arxiv-2609-04176/tex/P99g.tex`. Its PDF and the public v1 PDF were compared at printed pages 4 and 18: the index/polynomial claim and the final cancellation claim are present in the original, not artefacts of text extraction. The endpoint theorem is not used as an axiom.

The main outcome is a falsifier of the **asymptotic calculation used in the proof**, not a proof that Catalan's constant is rational or that the conditional inequality in Proposition 9.5 can never be established by a different argument. The exact fixed scalar has a valid interpretation, several local ingredients survive, and the nonvanishing argument has a coherent repair. But the upper majorant actually obtained from the displayed estimates has a positive `B^2 log B` term. Even an optimistic repair that restores the omitted fixed Vandermonde valuations leaves a positive lower bound at scale `B^2`.

## 1. Definitions and index repair

Use a letter `Q_0` for a hypothetical denominator of Catalan's constant, reserving `Q=p^nu` for a local prime-power layer. Let
\[
T_m=\sum_{r\ge0}\frac{(-1)^r}{(2(m+r)+1)^2},\quad
T_m+T_{m+1}=\frac1{(2m+1)^2},\quad
u_m=\frac{T_m}{2m+1},\quad
\Pi_i=\prod_{h=1}^B(2(i+h)+1)^2.
\]
For `1<=S<B`, set
\[
\mathcal R_{a,j}=\sum_{i=0}^{a+2B}(-1)^i\binom{a+2B}{i}\Pi_i u_{i+j},
\quad 0\le a\le S+2,\quad 1\le j\le S.
\]

### 1.1 A literal non-polynomial correction in the original proof

After expanding about `T_i`, the source calls
\[
\frac{\Pi_i}{2(i+j)+1}\sum_{k=0}^{j-1}
\frac{(-1)^{j-1-k}}{(2(i+k)+1)^2}
\]
a polynomial of degree at most `2B-3`. This is false. At `B=2,j=1`, it is
\[
\frac{(2i+3)(2i+5)^2}{(2i+1)^2},
\]
which has a double pole at `i=-1/2`, with numerator `32` there. The `k=0` denominator was not among the factors of `Pi_i`. The subsequent displayed replacement of `T_i` by `T_{i+1}` also lacks the associated sign change. Original locators: TeX lines 209–280; PDF printed page 4; source equation (2.3) and the two following displays.

### 1.2 A repair that does prove full column rank

Expand about `T_{i+1}` instead:
\[
T_{i+j}=(-1)^{j-1}T_{i+1}
+\sum_{k=1}^{j-1}\frac{(-1)^{j-1-k}}{(2(i+k)+1)^2}.
\]
After multiplication by `Pi_i/(2(i+j)+1)`, this correction really is a polynomial, of degree at most `2B-3`. It is annihilated by the indicated differences. Therefore the repaired residual identity is
\[
\mathcal R_{a,j}=(-1)^{j-1}
\sum_{i=0}^{a+2B}(-1)^i\binom{a+2B}{i}
\frac{\Pi_iT_{i+1}}{2(i+j)+1}.
\]
The corrected column signs have no effect on the absolute determinant formula later used.

Here is the full-rank argument, including its zero count. Suppose a nonzero column vector `lambda` annihilates all residual rows. Define
\[
L_S(X)=\prod_{j=1}^S(2X+2j+1),\quad
E(X)=\prod_{j=S+1}^B(2X+2j+1),
\]
\[
P^*(X)=\sum_{j=1}^S(-1)^{j-1}\lambda_j
\frac{L_S(X)}{2X+2j+1},\qquad
D(X)=L_S(X)E(X)^2P^*(X).
\]
The partial fraction numerators are independent, so `P*` and `D` are nonzero. Also `deg D<=2B-1`. The differences of `f_i=T_{i+1}D(i)` vanish at every order
`2B,2B+1,...,2B+S+2`.
The correct Newton coefficient is
\[
c_n=(-1)^n\sum_{i=0}^n(-1)^i\binom ni f_i.
\]
Hence a polynomial `A(X)` of degree at most `2B-1` agrees with `f_i` at every integer `0<=i<=2B+S+2`. The source's set notation listing only two orders must likewise be replaced by the full interval.

Consider the defect
\[
K(X)=(2X+3)^2\{A(X)D(X+1)+A(X+1)D(X)\}
-D(X)D(X+1).
\]
Its degree is at most `4B`. The tail recurrence makes it zero at `2B+S+2` nonnegative integers, from `0` through `2B+S+1`.

There are additional negative roots with multiplicity. A fixed divisor of `gcd(D(X),D(X+1))` has roots
`-h-1/2`, with multiplicity one for `2<=h<=S+1` and multiplicity two for `S+2<=h<=B`. Its degree is `2B-S-2`. This divisor also divides `K`. The further factor `2X+3` divides `K`, because it divides `D`, and the first term of `K` already has its square. These roots are disjoint from the nonnegative sample points. We have at least
\[
(2B+S+2)+(2B-S-2)+1=4B+1
\]
zeros counted with multiplicity. Thus `K=0`.

It would follow that the rational function `R=A/D` satisfies
\[
R(X)+R(X+1)=\frac1{(2X+3)^2}.
\]
No rational function does. In any additive integer orbit of poles, a rightmost pole of `R` cannot cancel against `R(X+1)`, and a leftmost pole shifted down by one cannot cancel against `R(X)`. Both would have to be the unique pole `-3/2` of the right side. This requires the leftmost pole of `R` to be `-1/2` while its rightmost pole is `-3/2`, a contradiction. If `R` has no finite poles it is polynomial, which is also impossible. This proves full column rank and hence the existence of a nonzero selected `S` by `S` minor.

**Disposition:** retain the elementary nonvanishing mechanism with these corrections; do not dismiss every ingredient of the preprint because the final estimate fails.

## 2. The exact scalar and its actual integeriser

Choose any row set `A` of size `S` with nonzero minor and put
\[
N=2B+S+3,\quad U=N-1,\quad F_B=\prod_{r=0}^{2B-1}r!.
\]
In source §3 the undefined `D` must be `2B`; the later `F_D` is the same `F_B`, not a new normalising factor. Apply the signed finite-difference transform to the completed square matrix. The monomial columns have pivots `±r!`; the three binomial auxiliary columns become unit vectors in the three omitted rows. It follows exactly that
\[
\widehat q_B=\pm\frac{F_B\det\mathcal R[A,J]}{\prod_{i=0}^{N-1}\Pi_i},
\qquad J=\{1,\ldots,S\}.
\]
The scalar is nonzero by the repaired full-rank result.

Under `G=A_0/Q_0` in lowest terms, define `H_B^min` to be the denominator of `Q_0^S qhat_B`. For every prime,
\[
v_p(H_B^{\min})=
\left[v_p\!\left(\prod_i\Pi_i\right)-v_p(F_B)
-v_p\!\left(Q_0^S\det\mathcal R[A,J]\right)\right]_+.
\]
Then `Q_0^S H_B^min qhat_B` is a nonzero integer. This is the integer gap that an irrationality contradiction would have to violate; changing scalar midway would not suffice.

## 3. The summands and the local model

The corrected signs do not change the exact absolute Cauchy–Binet summands. Set
`X_I=|Xi_I|/Q_0^S`, so that `X_I` is defined using the actual positive tails and does not require rationality. For a set `I` of size `S`,
\[
X_I=2^{S(S-1)}V(J)V(I)^2|\Psi_A(I)|
\frac{\prod_{a\in A}(2B+a)!}{\prod_{i\in I}i!(U-i)!}
\prod_{i\in I}\frac{T_{i+1}\Pi_i}
{\prod_{j=1}^S(2(i+j)+1)}.
\]
Here
\[
V(I)=\prod_{i<i'\in I}(i'-i),\quad
V(J)=\prod_{j=0}^{S-1}j!,\quad \Psi_A(I)\in\mathbb Z.
\]
Integrality of `Psi` follows by dividing the alternating determinant of the integral falling-factorial polynomials by its Vandermonde. Both copies of `V(I)` matter. The fixed `V(J)` also matters to the asymptotic valuation budget, even though it can legally be discarded in a one-sided local bound.

For an odd prime power `Q`, use precisely the source definitions
\[
\Phi_Q(n)=\sum_{r<n}\lfloor r/Q\rfloor,\quad
N_{K,Q}(i)=\#\{1\le h\le K:Q\mid2(i+h)+1\},
\]
\[
C_Q^A=\sum_{a\in A}\left\lfloor\frac{2B+a}{Q}\right\rfloor,
\quad F_{N,Q}(i)=\lfloor i/Q\rfloor+\lfloor(U-i)/Q\rfloor,
\]
\[
\lambda_Q^A(I)=C_Q^A+2\sum_{r\bmod Q}\binom{n_{Q,r}(I)}2
+\sum_{i\in I}\{2N_{B,Q}(i)-N_{S,Q}(i)
-2\mathbf1_{Q\le2i+1}-F_{N,Q}(i)\},
\]
\[
m_{Q,B}^A=\min_{|I|=S}\lambda_Q^A(I),\qquad
 a_{Q,B}=2\sum_{i=0}^{U}N_{B,Q}(i)-\Phi_Q(2B).
\]
The source lower bound
\[
v_p(Q_0^S\det\mathcal R[A,J])\ge\sum_{\nu\ge1}m_{p^\nu,B}^A
\]
is valid. It drops both the fixed `V(J)` and the integer factor `Psi_A(I)`, and bounds the denominators of `Q_0T_{i+1}` by the square of the odd least common multiple through `2i+1`. The order of minimisation and summation is in the safe direction.

### 3.1 Saturation and positive parts

The saturation proof is valid in the intended range
\[
B\ge20,\qquad1\le S\le B/20.
\]
The stated theorem should carry that restriction on `S`; it is explicitly used in its proof.

For completeness, testing `I={0,...,S-1}` and dropping nonnegative terms reduces saturation to
\[
2\sum_{i=S}^{N-1}N_{B,Q}(i)\ge\Phi_Q(N)+2\Phi_Q(S).
\]
The two residue blocks of lengths `2B+3` and `B` give the collision lower bound
\[
\sum_{i=S}^{N-1}N_{B,Q}(i)\ge
\Phi_Q(3B+3)-\Phi_Q(2B+3)-\Phi_Q(B).
\]
Use the exact identity
\[
\Phi_Q(n)=\frac{n^2}{2Q}-\frac n2+\frac{r(Q-r)}{2Q},\quad
0\le r<Q,
\]
whose final term lies between zero and `Q/8`. For `Q<=N`, the difference of the proposed left and right sides is at least
\[
\frac{2B^2-2BS-\tfrac32S^2-3S-\tfrac92}{Q}
+\frac N2+S-\frac{7Q}{8}.
\]
It decreases with `Q` in the stated range; at `Q=N` it is bounded below by
`33B/160-21/8>0`. For `Q>N`, the right side of the required inequality is zero. This proves `a_Q>=m_Q`, and therefore permits the displayed removal of the positive part at odd primes.

At the prime `2`, all `Pi_i` are odd, and `Q_0T_m` has only odd denominators. The height's positive part is indeed zero. **It does not follow that the factor `v_2(F_B) log 2` disappears from the real normalisation.**

### 3.2 Selected rows and support

The local minimisers for the full model and the consecutive model differ by
`O(1+B/Q)`: only three extra candidate indices and at most three changed row labels are involved. Replacing an extra selected index by an unused common index changes a residue occupancy by at most `1+U/Q`; the additive floor costs have the same bound. The prime-weighted sum of these local errors is `O(B log B)=o(B^2)`.

The source's assertion that all nonzero layers satisfy `Q<5B` for large `B` is false. A safe support bound is `Q<7B`, because the largest odd factor of a `Pi_i` is `6B+2S+5`.
There is an unbounded explicit counterexample family: for `Q=3^nu`, take
`B=ceil(Q/6)=(Q+3)/6`, `S=floor(B/20)`, for sufficiently large `nu`. Then
`5B<Q<6B`, `a_Q>0`, and `m_Q=0`. Indeed every local cost is nonnegative in this range, while the test set `I={0,...,S-1}` has zero cost; one can take `h=B`, `i=(Q-1)/2-B` to exhibit a factor divisible by `Q` in the full product. The executed script includes `nu=5,...,9`, as well as the small witness `B=20,S=1,Q=127`.

Replacing `5B` by `7B` repairs the support bound for the stability estimate, but it does not repair the final asymptotic calculation below. We do not rely on the stronger source assertion of termwise real stability; the following real estimate is proved directly and uniformly over all allowed row sets.

## 4. The displayed same-scalar majorant has the wrong leading term

Define the unconditional real quantity
\[
\mathcal U_B=
\log\sum_{|I|=S}X_I+v_2(F_B)\log2
-\sum_{p\text{ odd},\nu\ge1}m_{p^\nu,B}^A\log p.
\]
Under the hypothetical rationality assumption, combining exactly the fixed-scalar identity, the source height bridge and the real triangle inequality gives
\[
\log H_B^{\min}+\log|\widehat q_B|\le\mathcal U_B.
\]
The products `prod Pi_i` and the odd part of `F_B` cancel in this calculation. The two-adic part of `F_B` remains. A factor `Q_0^S` in the final integer gap changes logarithms by only `O(B)` for fixed `Q_0`.

**Theorem (falsifier of the asserted cancellation).** Uniformly over allowed selected row sets, for fixed `0<rho<=1/20` and `S=rho B+O(1)`,
\[
\boxed{\mathcal U_B=\frac{\rho^2}{2}B^2\log B+O_\rho(B^2).}
\]
In particular, at `rho=1/20`, the uncancelled coefficient is **exactly `1/800`**, and is positive.

**Proof of the local leading term.** Uniformly in odd `Q<=7B`,
\[
C_Q^A=\frac{2BS+S^2/2}{Q}+O(B).
\]
Each additive local cost is `-2S/Q+O(1)`. The smallest double-collision count is `2 Phi_Q(S)=S^2/Q+O(B)`, attained by consecutive indices; additive errors remain `O(B)` for every selected set. Therefore
\[
m_{Q,B}^A=\frac{(2\rho-\rho^2/2)B^2}{Q}+O_\rho(B).
\]
The elementary prime-power estimates
\[
\sum_{p^\nu\le7B}\frac{\log p}{p^\nu}=\log B+O(1),\quad
\sum_{p^\nu\le7B}\log p=O(B)
\]
give
\[
\sum_{p\text{ odd},\nu}m_{p^\nu,B}^A\log p
=(2\rho-\rho^2/2)B^2\log B+O_\rho(B^2).
\]
Removing the prime `2` changes only the `B^2` term, not this leading coefficient.

**Proof of the real leading term.** Uniformly for `0<=i<=U`,
\[
\log\Pi_i=2B\log B+O(B).
\]
The Pascal minor is at most `S! 2^{SU}=exp(O(B^2))`; the absolute Cauchy determinant is at most `S!`; and every tail is at most one. There are at most `2^N` summands. Thus
\[
\log\sum X_I\le2\rho B^2\log B+O(B^2).
\]
For a matching lower bound take `I={0,...,S-1}`. The Pascal determinant is `V(A)/V(J)>=1`, since the `a`'s are distinct integers. The exact Cauchy determinant is at least `exp(-O(S^2))`, as follows by combining its two factorial Vandermondes with the denominator bounded by `(4S+1)^{S^2}`. The tail bound
\[
T_{i+1}\ge\frac1{(2i+3)^2}-\frac1{(2i+5)^2}>0
\]
contributes only `-O(B log B)` to its logarithm. This one term gives
`log sum X_I >= 2rho B^2 log B-O(B^2)`.

Finally `v_2(F_B)=2B^2+O(B log B)`, by `v_2(r!)=r-s_2(r)`. Subtracting the local leading term proves the displayed result.

**What this invalidates.** Proposition 9.5, original equation (9.4), asserts cancellation of these `B^2 log B` terms before identifying a remaining raw coefficient `4rho-2rho^2=39/200`. The displayed ingredients instead give the positive term above. The `39/200` and the final negative decimal cannot be certified by that calculation. This is a genuine asymptotic defect, not a rounding issue.

## 5. Restoring the omitted fixed Vandermonde does not suffice

One might repair the missing leading term by restoring the discarded odd valuations of
`V(J)=prod_{j<S}j!`. Define the **optimistic, unclipped** expression
\[
\mathcal U_B^{\rm flat}=\mathcal U_B
-\sum_{p\text{ odd}}v_p(V(J))\log p.
\]
Its subtraction has leading term `(rho^2/2)B^2 log B`, so it cancels the defect just found. However,
\[
\boxed{\liminf_{B\to\infty}\frac{\mathcal U_B^{\rm flat}}{B^2}
\ge(2+2\rho^2)\log2>0.}
\]
At `rho=1/20` the lower bound is `(401/200) log 2`.

**Proof.** Again take the single nonzero summand `I={0,...,S-1}`, and write
`X_I=R_I prod_{i in I}T_{i+1}`, with `R_I` a positive rational number. The exact Pascal–Cauchy formula gives
\[
v_2(R_I)\ge S(S-1)+2v_2(V(J)),
\]
because the Pascal determinant is an integer, the two Cauchy Vandermondes agree with `V(J)`, and all remaining linear factors are odd.

At odd primes, the definition of `lambda` gives the identity
\[
\log R_{I,\rm odd}
=\sum_{p\text{ odd},\nu}\lambda_{p^\nu}^A(I)\log p
+\log V(J)_{\rm odd}+\log|\Psi_A(I)|_{\rm odd}
+2\sum_{i\in I}\log\operatorname{lcm}_{\rm odd}(1,\ldots,2i+1).
\]
Here `log R_{I,odd}` means the sum of its odd prime valuations times `log p`, which is well-defined also for a rational number. The last two terms are nonnegative, and every `lambda_Q(I)>=m_Q`. Consequently
\[
\mathcal U_B^{\rm flat}\ge
\{v_2(F_B)+S(S-1)+2v_2(V(J))\}\log2
+\sum_{i\in I}\log T_{i+1}.
\]
Use `v_2(F_B)=2B^2+O(B log B)`,
`v_2(V(J))=S^2/2+O(S log S)`, and the two-term tail lower bound from the previous proof. Dividing by `B^2` proves the result.

There is a necessary **positive-part qualification**. The unclipped expression need not itself be a legal improved upper bound: after adding `v_p(V(J))`, the former saturated difference can become negative. The correctly restored height bound retains
`[A_p-sum_nu m_{p^nu}-v_p(V(J))]_+`. This is at least the same expression without the positive part. Therefore the legal repaired majorant is **no smaller** than `U_B^flat`; its positive lower bound remains an obstruction to deriving decay by this repair.

Actual cancellation among Cauchy–Binet terms, stronger correlated local minima, or additional integer factors could in principle improve a different estimate. They are not proved here to be absent. What is ruled out is the displayed aggregation and the specific fixed-Vandermonde repair, not every weighted-tail method.

## 6. Executed checks and unresolved portions of the source

`checks/sun_layers.py` implements the exact occupancy minimisation by sorting marginal costs in each residue class. It checks it against exhaustive subset enumeration in four small cases, tests 221 saturation layers, includes an unbounded prime-power support-counterexample family, and prints the exact rational leading coefficients `1/10`, `79/800`, `1/800`. It also prints floating-point **one-term lower bounds on the majorant**, not numerical evaluations of `H_B^min |qhat_B|` and not proofs of any limit. The largest displayed sample uses `B=640`.

`checks/primitive_tail_lattice.py` includes the symbolic double-pole falsifier and verifies the corrected finite polynomial corrections at small parameters.

The complete optimal `B^2` coefficient for the source's full local minimisation has not been evaluated independently. In particular this return does not certify every breakpoint integral in §§6–8 or their decimals. That calculation is unnecessary to the disproof of the asserted `B^2 log B` cancellation, and the positive lower bound above already shows that merely restoring `V(J)` cannot recover the claimed decay. A proposed further repair must specify a new bound for the **same scalar** and overcome the positive contribution just exhibited; it cannot reuse Proposition 9.5 as an established input.

## 7. Transfer to the Lambert question

The transferable ingredients are the corrected finite-difference nonvanishing argument, the exact determinant completion, the elementary valuation identity, and the use of residue occupancy to optimise local costs. They do not themselves yield a Lambert approximation with a better denominator budget.

The Lambert weighted determinant and primitive lattice have been constructed separately in `ARITHMETIC_ROUTES.md`. Its positivity, real asymptotic and high cyclotomic poles are proved for that actual new object. The 2004 polynomial region remains a separate construction; neither Sun's endpoint claim nor a denominator from the 2016 coefficients is substituted into it.
