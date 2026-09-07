# The filtered reciprocal-state calculation at arbitrary depth

This ordinary formal-power-series proof makes the all-depth source argument
directly available. The research packet already states the all-rank result;
the Type B return is a complete derivation of that existing ordinary theorem,
not a new solution of rational-base Lambert irrationality. The remaining Lean
boundary must be read from the exact source declarations, not inferred from
this note.

Work over A=Z[[q]]. Let H(X)=1+sum_{s>=1}a_s(q)X^s and

    W_n(t)=q^{(n+1)t} product_{r=1}^n H(q^r),
    D_j=product_{r=0}^{j-1}(I-q^r N),   (N f)_n=f_{n-1},
    E(n,j)=nj-j(j-1)/2.

If h_r=[X^r](H(X) mod q)^{-1}, with h_r=0 for r<0, then for n>=j,

    D_j W_n(t) in q^{E(n,j)} A,
    [q^{E(n,j)}]D_j W_n(t)=(-1)^j h_{j-t}.                 (1)

Here is a precise locally finite state proof. Define

    Phi e_0 = sum_{s>=1} a_s e_{s-1},
    Phi e_u = (q^u-1)e_{u-1}+q^u sum_{s>=1}a_s e_{u+s-1} (u>0).

Then

    D_j W_n(t)=q^{E(n,j)} sum_u (Phi^j e_t)_u W_{n-j}(u).   (2)

To verify induction, use r+E(n-1,r)=E(n,r) and
W_m(u)-W_{m-1}(u)=q^m sum_v(Phi e_u)_v W_{m-1}(v).
An individual transition can decrease a state by at most one. At depth j,
a path ending in state u never visits a state above max(t,u+j); consequently
there are only finitely many paths relevant to a bounded endpoint. Evaluation
has ord W_{n-j}(u)=(n-j+1)u, so only finitely many endpoints contribute to
any fixed q coefficient. These two bounds justify both the state powers and
evaluation of their sums; the assertion is not based merely on naming a
q-adic topology on an unspecified infinite matrix.

Modulo q, positive states move down by one with coefficient -1, and zero
emits the coefficients a_s(0). For c_{j,t}=(Phi_bar^j e_t)_0,

    c_{j+1,t}=-c_{j,t-1} (t>0),
    c_{j+1,0}=sum_{s=1}^{j+1} a_s(0)c_{j,s-1}.

The coefficient identity H_bar H_bar^{-1}=1 proves by induction
c_{j,t}=(-1)^j h_{j-t}. In (2) only state zero contributes at degree E(n,j).
This proves (1).

For the normalized Zudilin tail

    T_{n,t}=q^{(n+1)t}(q;q)_n^3(q^{t+1};q)_n/(q^{n+t+1};q)_{n+1},

take C_t=1/(1-q^{t+1}) and

    H_t(X)=(1-X)^3(1-q^t X)^2/((1-q^t X^2)(1-q^{t+1}X^2)).

Direct cancellation gives T_{n,t}=C_t W_n^{H_t}(t).
For t=0 the reciprocal reduction is (1+X)/(1-X)^4; for t>0 it is
1/(1-X)^3. Summing (1) over 0<=t<=j, using C_t(0)=1, gives

    D_j v_{j+l} = (-1)^j (j+1)^2(j+2)/2
                  q^{j(j+1)/2+jl} + higher powers.

Terms t>j have zero boundary coefficient. Interchanging the tail and the
finite backward difference is legitimate because ord T_{n,t}=(n+1)t.
The row operation is lower unitriangular and preserves determinants.
Among permutations sigma the cost sum_j j sigma(j) is uniquely minimized
by reversal. Its sign cancels product_j(-1)^j. Thus, for N>=1,

    ord det(v_{i+j}) = N(N-1)(2N-1)/6,
    leading coefficient = (N!)^2 (N+1)! / 2^N.

This completes the source calculation without an unproved limiting step.
It gives no extra denominator content at q=2/3 and no rational-base
irrationality theorem. The all-depth Lean entrywise leading-term bridge is
a formalization task; a paper proof cannot silently close that formal task.
