# First-contact valuation resonance and cumulative payment

Use the exact positive integral LCM coordinates

    rho_n=gcd(Lambda_n,a_n),  Lambda_{n+1}=Lambda_n a_n/rho_n,
    rho_n U_{n+1}=a_n U_n-Lambda_n,
    V_n=Lambda_n-(a_n-1)U_n,  M_{n+1}=M_n rho_n.

The following strengthens the Type B fresh-prime retirement theorem. It is an
ordinary integer proof, not a claim that the general Erdős 243 problem is solved.

## A source prime must be paid in one resonant step

Let j be fresh (rho_j=1) and p^e exactly divide a_j. Suppose t>j is the
first subsequent index with p dividing U_t. Then t>=j+2 and, at s=t-1,

    v_p(a_s)=v_p(Lambda_s)>=e,
    p^{v_p(Lambda_s)} divides rho_s.                         (1)

Moreover p does not divide either a_s/rho_s or Lambda_s/rho_s, and

    (a_s/rho_s) U_s = Lambda_s/rho_s (mod p).                (2)

Thus the first contact requires equality of valuations and cancellation of
the two residual units. A sum of many subthreshold reuse payments cannot
produce first contact, even when their total exceeds e.

Proof. Freshness gives p not dividing Lambda_j, so
U_{j+1}=a_j U_j-Lambda_j is a p-unit. At a first-contact step U_s is also
a p-unit. Put alpha=v_p(a_s), ell=v_p(Lambda_s)>=e and
beta=min(alpha,ell)=v_p(rho_s). Divide the step by rho_s. If alpha<ell,
its right side is a unit minus a multiple of p. If alpha>ell, it is a
multiple of p minus a unit. Both contradict p|U_{s+1}. Hence alpha=ell;
both residual coefficients are units and their cancellation is exactly (2).
This proves (1)--(2).

For any later contact p|U_T, apply (1) at the first contact before T.
It follows that p^e divides product_{j<s<T}rho_s. Consequently, if a_j|U_T,
then a_j|M_T. Distinct fresh source multipliers are pairwise coprime, so
products of distinct contacted source multipliers also divide M_T. The
returned cumulative retirement and disjoint-wall bounds follow, now with
a stronger local explanation of each first contact.

## Strict-rise log-log criterion

Assume the canonical orbit premises: V_n/U_n tends to zero, zero is eventually
absorbing, C_n=M_n U_n, log C_n=o(n), a_{n+1}/a_n^2 tends to one, and
log_2 log_2 D_n<=n+O(1). If for some delta in (0,1), every sufficiently
late strict rise satisfies

    -V_n <= (1-delta) log_2 log_2 max(4,U_n),                (3)

then the orbit terminates. Here is the complete CRT step in the returned proof.
Nontermination and integral V_n imply U_n tends to infinity. The count of
nonfresh steps is o(N), because 2^{count}<=M_N<=C_N. Given a large integer B,
take T=ceil((1+eta)B), with (1-delta)(1+2eta)<1. There are B fresh indices
below T whose multipliers m_0,...,m_{B-1} exceed B: the excluded initial
indices number O(log log B), and nonfresh indices number o(B). These m_r
are pairwise coprime. Write P=product m_r. Then

    U_T <= C_T < 2^T < B^B < P <= D_T,
    log_2 log_2(2P+B) <= (1+2eta)B

for large B. CRT gives x in [P,2P) with m_r|(x+r). Let t>T be the first
index with U_t>=x+B. The rise at n=t-1 is positive and, from
rho_n U_{n+1}=U_n-V_n with rho_n>=1, is at most -V_n. By (3) it is <B.
Thus U_n=x+r with 1<=r<B. Both U_n and Lambda_n are divisible by m_r,
so V_n is divisible by m_r. But 0<-V_n<B<m_r, a contradiction.

The canonical tail estimates yielding the premises are unchanged: the
quadratic growth hypothesis gives E_n/C_n->0 and C_{n+1}=C_n-E_n gives
subexponential C. Taking logarithms in a_{n+1}/a_n^2->1 gives the displayed
double-log bound for D. At consecutive zero states cancellation yields
a_{n+1}=a_n^2-a_n+1.

For A_n=product_{k<n}a_k, D_n=q A_n, and
Q_n=(A_n/a_n)(a_n^2/a_{n+1}-1), the exact tail identity is

    E_n+q Q_n = D_n(1/a_{n+1}-(a_n-1)sum_{k>=n+2}1/a_k).

Its right side tends to zero under quadratic growth (A_n=a_n^{1+o(1)}).
Dividing by M_n>=1 gives V_n+q Q_n/M_n->0. A finite upper limsup of Q_n/M_n
bounds the negative part of V_n, hence implies (3) and eventual recurrence.
These are conditional criteria: the required bound is not established for
every canonical orbit.

## Other return claims and the failed universal inference

In gcd-reduced coordinates u_n=C_n/gcd(C_n,D_n), with payment h_n, the exact
second-order relation is

    a_n^2 u_n+h_n h_{n+1}u_{n+2}=h_n(a_n+a_{n+1})u_{n+1}.

If h_n=h_{n+1}=1, multiply the relation modulo u_{n+1} by u_n to get
(a_n u_n)^2=-u_n u_{n+2}. Adjacent numerators are coprime, so this is a
unit square. Nonsquare defects force one of the adjacent payments; at most
twice the number of paid steps can be defects. Since gcd(C_n,D_n)<=C_n,
their density is zero under the same subexponential budget. Flat negative
runs give the square 1 and defeat a universal payment argument from this test.

The state-local log-log replacement is also false. For m>=2 set U=m^2+1,
a=U+m+1, Lambda=(a-1)U-m, V=-m. Both gcd(U,Lambda) and gcd(a,Lambda)
are one, and U'=U+m. Here |V|/U->0 but |V|/log log U->infinity.
This exact family cannot be promoted to a cofinal canonical orbit.

The new first-contact resonance is a necessary condition, not a frequency
theorem. A parent proof still needs sufficiently frequent contacts or a
large-jump obstruction. Neither the weighted real balance
(product rho)U_s/U_r=product(1-V_n/U_n) nor the new local resonance forces
that frequency. Three mechanisms were tested: short CRT crossings (conditional
closure), unit-square defects (flat-run obstruction), and valuation resonance
(stronger contact requirement). No unrestricted parent closure follows.
