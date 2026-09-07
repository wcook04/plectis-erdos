<!-- Companion long-record migration for Erdős #269 round 6. -->
<!-- Destination label: long:cut-arithmetic-normal-form -->
<!-- Not frozen R. Source: erdos_269_research_memorandum_r6.md. -->

## 2. An arithmetic normal form for every finite cut matrix

### 2.1 The normal form over a ring

Let $R$ be a commutative ring, let $c\in R$ be a unit, and let $m\ge1$. Define
$$
v_s=(\underbrace{1,\ldots,1}_{s},\underbrace{c,\ldots,c}_{m-s})^{\mathsf T},
\qquad 0\le s\le m.
$$
Let $C_E$ be a nonempty matrix of these columns, and let $E\subseteq\{0,\ldots,m\}$ be the set of cuts that occur, counting each repeated cut once. Write
$$
\rho=|E|-\mathbf1_{\{0,m\}\subseteq E}.
$$

**Theorem 2.1 (arithmetic cut normal form).** Invertible row and column operations over $R$ transform $C_E$ to a rectangular diagonal matrix with nonzero-designated entries
$$
1,\quad \underbrace{1-c,\ldots,1-c}_{\rho-1},
$$
and all remaining entries zero. The assertion allows $1-c$ to be a zero divisor, or zero. It is a matrix-equivalence statement, rather than a rank convention over a ring.

*Proof.* Subtract representatives from duplicate columns. List the remaining cuts as $k_1<\cdots<k_t$, and replace successive columns by their differences, working from the last column backwards. Besides the first column, the columns become
$$
(1-c)\mathbf1_{[k_j,k_{j+1})},\qquad 1\le j<t.
$$
Within each interval all rows coincide; subtract one representative from the others. The surviving row types are a prefix row $(1,0,\ldots,0)$ when $k_1>0$, an interval row $(c,(1-c)e_j)$ for each gap, and a suffix row $(c,0,\ldots,0)$ when $k_t<m$.

If there is a prefix or suffix, its first entry is a unit. Use it as pivot to clear the first coordinate of the interval rows. This leaves $1$ and $t-1$ copies of $1-c$, with zero rows and columns elsewhere. If both prefix and suffix are absent, the cuts include $0,m$ and only the $t-1$ interval rows remain. Pivot on the unit $c$ in one interval row. Subtract that row from the other interval rows. In the difference columns, those rows are $(1-c)(e_j-e_1)$. Clearing the first pivot row leaves an identity submatrix of size $t-2$, multiplied by $1-c$, and one dependent column. Thus the diagonal entries are $1$ and $t-2$ copies of $1-c$. These are the two cases in the formula for $\rho$. Every operation described is invertible. $\square$

Over a field with $c\ne0,1$, this recovers the existing cut-rank formula. The proof also explains why the two extreme cuts cause the only loss: their columns are proportional.

### 2.2 The exact bad residue characteristics

For distinct primes $p,q,r$, let
$$
H(x)=p^{\lfloor\log_p x\rfloor}q^{\lfloor\log_q x\rfloor}r^{\lfloor\log_r x\rfloor},
\qquad K(i,j,k)=H(p^iq^jr^k)^{-1}.
$$
The live factorisation is
$$
K(i,j,k)=U_i(k)^{-1}C_{ij}V_j(k)^{-1},\qquad
C_{ij}=r^{-\mathbf1_{\{x_i+y_j\ge1\}}},
$$
where $x_i=\{i\log_r p\}$ and $y_j=\{j\log_r q\}$. Every $U_i,V_j$ is a product of powers of $p,q,r$.

**Corollary 2.2.** Over $\mathbb Z[1/(pqr)]$, every nonempty finite sampled kernel matrix of rational rank $\rho$ is equivalent to
$$
\operatorname{diag}(1,r-1,\ldots,r-1,0,\ldots),
$$
with $\rho-1$ copies of $r-1$. The normal form is independent of $k$.

*Proof.* The row and column factors are units in the stated ring. Apply Theorem 2.1 with $c=1/r$, then multiply the diagonal entries by suitable units. $\square$

Let $B\ge2$ satisfy $(B,pqr)=1$. Reduction is well defined on this localisation. The image of the corresponding map between finite free $\mathbb Z/B\mathbb Z$-modules has cardinality
$$
\boxed{\quad B\left(\frac{B}{\gcd(B,r-1)}\right)^{\rho-1}.\quad} \tag{2.1}
$$
For a prime $\ell\notin\{p,q,r\}$, the rank is $\rho$ if $\ell\nmid r-1$, and is $1$ if $\ell\mid r-1$. At modulus $\ell^s$, putting $e=v_\ell(r-1)$, the image cardinality is
$$
\ell^{s+(\rho-1)\max(s-e,0)}.
$$
These assertions follow coordinatewise from the diagonal form: multiplication by $d$ on $\mathbb Z/B\mathbb Z$ has image of size $B/\gcd(B,d)$.

For $\{2,3,5\}$, every admissible $B$ is odd, so $4=r-1$ is a unit. Consequently every finite sampled rank survives in the precise sense of the normal form, and every staircase minor selected by the live theorem is invertible modulo every $B$ coprime to $30$, simultaneously for all $k$. This last statement also has a four-line direct proof from the live determinant
$$
\det T_n(1/5)=5^{-1}(-4/5)^{n-1}.
$$
It is the version proposed as a short-note corollary.

There is an exact general criterion: the selected staircase minors survive modulo **every** $B$ coprime to $pqr$ if and only if every prime divisor of $r-1$ lies in $\{p,q\}$. Necessity follows by taking $B$ to be any prime divisor outside that set, and sufficiency follows from the determinant. For example, a fixed-layer kernel for $(p,q,r)=(2,3,11)$ has rank one modulo $5$, although it has arbitrary-order rational minors. This example concerns the stated flattening; it makes no claim that all tensor flattenings collapse.

Matrix equivalence, Smith normal forms and cokernel decomposition are classical tools; Stanley's survey [S] supplies that background. The particular normal form above is derived explicitly rather than attributed to the survey. Its scope is linear algebra. It does not force a scalar pairing of the kernel with its actual multiplicities to be irrational.
