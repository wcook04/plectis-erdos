# Effective signed-atomic Hankel asymptotics

Let 1>=x_1>x_2>...>0, let a_j be nonzero real numbers, and suppose
A=sum_j |a_j|x_j<infinity. For r>=1 put m_r=sum_j a_j x_j^r.
For a fixed N>=1 let X=product_{j<=N}x_j, rho=x_{N+1}/x_N<1,
Delta=product_{i<j<=N}(x_j-x_i), and

    L(s)=(product_{j<=N}a_j) X^s Delta^2.

Then, for integer s>=1,

    |det(m_{s+i+j})_{0<=i,j<N}/L(s)-1|
      <= C_N rho^{s-1},
    C_N = A^N/(N! |product_{j<=N}a_j| X Delta^2).             (1)

This is an ordinary proof. It strengthens the returned eventual-sign argument
by an explicit exponential error bound. No Lean validation or priority is claimed.

For finite support the Cauchy--Binet formula gives the determinant as a sum
over increasing N-tuples J of (product_{j in J} a_j x_j^s) Delta_J^2.
Absolute convergence follows from |Delta_J|<=1 and
sum_J product_{j in J}|a_j|x_j <= A^N/N!. Passing to infinite support is
legitimate by this summable bound and continuity of the finite determinant.
The leading tuple J_0=(1,...,N) is unique. Every other tuple satisfies
X_J/X<=rho: replacing the smallest leading node x_N by x_{N+1} maximises
the product among nonleading tuples. Therefore

    sum_{J!=J_0} |a_J| X_J^s Delta_J^2
      <= (rho X)^{s-1} sum_J |a_J|X_J
      <= (rho X)^{s-1} A^N/N!.

Dividing by |L(s)| proves (1). Once C_N rho^{s-1}<1, the determinant is
nonzero with sign product_{j<=N}a_j. Arbitrarily large nonsingular finite
minors prove infinite Hankel rank directly, without a recurrence theorem.

For the power ladder P_r=sum_{d>=1} mu(d)/(2^d-1)^r, take the squarefree
indices q_j in increasing order, x_j=1/(2^{q_j}-1), a_j=mu(q_j).
The elementary estimate x_j<=2^{1-q_j} gives A<=2. Thus (1) has a completely
explicit bound using only the first N+1 squarefree indices. In particular,

    det(P_{s+i+j}) ~ (product_{j<=N}mu(q_j)) X^s Delta^2.

This does not assert nonvanishing at every shift, nor irrationality of P_2.

## Existing results consumed, not recredited

The literal ladder L_r=sum_d mu(d)/(2^{rd}-1)=2^{-r} already has a checked
separation theorem in MobiusMersenneLadderSeparation.lean. Its rank is one;
the present theorem concerns P_r. The all-base totient-kernel rank k^e+1
already has unconditional Lean support in AllBaseTotientKernel.lean.
The returned integral basis is a useful algebraic consequence: the integer
scalar reductions to the canonical rational basis make it a Z-basis, and
each noncanonical coordinate minus its scalar canonical image gives one
independent relation. Eliminating noncanonical coordinates proves completeness.
This adds no new rational-rank or parent-irrationality theorem.

The remaining parent step is still denominator compression for a linear form
isolating P_2. Infinite rank makes arbitrarily large blocks available but
does not give the required small primitive integer linear forms. The
rank-saturated Schur extraction already collapses to ordinary truncation;
repeating it after (1) does not improve that denominator obstruction.
