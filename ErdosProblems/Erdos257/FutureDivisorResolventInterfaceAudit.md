# The future-divisor resolvent and the missing strict entrance

Status: exact identities, an exact interface audit, and exact finite
counterexamples to weakened descent statements, 2026-08-20. The
saturated-socket descent is not proved or disproved when its full saturation
hypothesis is retained.

## 1. Definition and exact evaluation

Let \(A\) be the actual greedy support for \(1/21\), and put
\[
 D_R=A\cap\{2,\ldots,R\}.
\]
For \(c\geq1\), define
\[
 \nu_R(c)=\#\{d\in D_R:d\mid 2R+c\}.
\]
If \(\rho_R(d)\) is the least positive \(c\) for which \(d\mid2R+c\), then
\[
 \mathscr R_R(z)
 =\sum_{c\geq1}\nu_R(c)z^c
 =\sum_{d\in D_R}\frac{z^{\rho_R(d)}}{1-z^d}.       \tag{1}
\]
At \(z=1/2\), geometric summation gives
\[
 \boxed{\mathscr R_R(1/2)
 =\sum_{d\in D_R}\left\{\frac{4^R}{2^d-1}\right\}.} \tag{2}
\]
Thus the usual fractional mass is the discounted count of every divisor
pulse strictly after \(2R\).

The full formal series, unlike its value at \(1/2\), determines \(D_R\).
Suppose two subsets \(D,E\subseteq\{2,\ldots,R\}\) give the same coefficients
in (1), and write \(a_d={\bf1}_D(d)-{\bf1}_E(d)\). Then
\[
 \sum_{d\mid n}a_d=0\qquad(n>2R).                    \tag{3}
\]
For each \(m\leq R\), choose a prime \(p>R\) with \(mp>2R\). A divisor
\(d\leq R\) of \(mp\) cannot contain \(p\), so (3) gives
\(\sum_{d\mid m}a_d=0\). Induction on \(m\), or Möbius inversion, gives
\(a_m=0\) for every \(m\leq R\). The coefficient series is therefore a
lossless encoding of the finite divisor clocks. This injectivity does not
apply to the single scalar \(\mathscr R_R(1/2)\).

## 2. Transport and the forced-block cut

Let \(b_{R+1}={\bf1}_A(R+1)\), and put
\[
 a_R=\nu_R(1),\qquad b_R=\nu_R(2),\qquad p_R=2a_R+b_R.
\]
Moving the boundary from \(2R\) to \(2R+2\) deletes the first two
coefficients and shifts the others. If \(R+1\) is selected, its first pulse
after the new boundary occurs at offset \(R+1\). Hence
\[
 \boxed{\mathscr R_{R+1}(z)
 =z^{-2}\bigl(\mathscr R_R(z)-a_Rz-b_Rz^2\bigr)
 +b_{R+1}\frac{z^{R+1}}{1-z^{R+1}}.}                \tag{4}
\]
In particular,
\[
 \boxed{\mathscr R_{R+1}(1/2)
 =4\mathscr R_R(1/2)-p_R+
   \frac{b_{R+1}}{2^{R+1}-1}.}                       \tag{5}
\]

There is also an exact relation with the old-divisor charge
\[
 J_R=\sum_{R<n\leq2R}2^{2R-n}
       \sum_{\substack{d\in D_R\\d\mid n}}1.
\]
The intervals \(R<kd\leq2R\) and \(kd>2R\) partition all multiples of \(d\)
beyond \(R\). Therefore
\[
 \boxed{J_R+\mathscr R_R(1/2)
 =2^R\sum_{d\in D_R}
   \left\{\frac{2^R}{2^d-1}\right\}.}               \tag{6}
\]
Equations (2), (4), and (6) are exact.

## 3. What the \(3/7\) budget assumes

Let
\[
 S_R=\left\lfloor\frac{4^R}{21}\right\rfloor
 -\sum_{d\in D_R}
  \left\lfloor\frac{4^R}{2^d-1}\right\rfloor,
\]
and let \(r_R=1/21-\sum_{d\in D_R}w_d\). Expanding the floors gives
\[
 \boxed{S_R=4^Rr_R-\left\{\frac{4^R}{21}\right\}
       +\mathscr R_R(1/2).}                           \tag{7}
\]

Suppose \(R\) is at or beyond a final skip, so every later rank is selected,
and write
\[
 r_R=T_R+g,\qquad T_R=\sum_{n>R}w_n,\qquad g>0.
\]
The exact expansion
\[
 4^RT_R=2^R+\frac13+\varepsilon_R,\qquad
 \varepsilon_R=\sum_{k\geq3}
   \frac{2^{(2-k)R}}{2^k-1}>0                       \tag{8}
\]
and (7) imply, with \(e_R=S_R-2^R\),
\[
 \mathscr R_R(1/2)
 =e_R+\left\{\frac{4^R}{21}\right\}
 -\frac13-\varepsilon_R-4^Rg.                       \tag{9}
\]
If \(e_R=0\), nonnegativity of the left side forces
\(R\equiv2\pmod3\), and then
\[
 \mathscr R_R(1/2)
 =\frac37-\varepsilon_R-4^Rg
 <\frac37-\varepsilon_R.                            \tag{10}
\]
It follows that \(\nu_R(1)=0\) and \(\nu_R(2)\leq1\). Thus the \(3/7\)
budget and its sparse-pulse consequence are correct for a saturated row
after the final skip.

The same conclusion does not follow for a strict row. When \(e_R\geq1\),
the additional integer \(e_R\) remains in (9). It is the supercapacity
charge, and it is precisely the homogeneous mode which the fatal branch can
carry. Nor does (10) apply before the final skip: then \(r_R\) is not
\(T_R+g\), because the complete tail includes later omitted coins.

## 4. The saturated classifier misses one first-crossing branch

Put \(m_R=2^R-S_R\). The exact actual-prefix recurrences are
\[
 \begin{aligned}
 m_{R+1}&=4m_R+p_R+1-t_R, &&b_{R+1}=1,\\
 m_{R+1}&=4m_R-2^{R+1}+p_R-t_R, &&b_{R+1}=0,
 \end{aligned}                                      \tag{11}
\]
where \(t_R\in\{0,3\}\). Suppose \(m_R\geq0\) and \(m_{R+1}<0\), so this is
a first crossing from a closed row into strict supercapacity.

On a selected step, (11) forces
\[
 m_R=0,\qquad t_R=3,\qquad p_R\leq1.                 \tag{12}
\]
This is exactly the saturated sparse socket. On a skipped step, however,
the condition is only
\[
 4m_R+p_R-t_R<2^{R+1},                               \tag{13}
\]
which does not force \(m_R=0\) or a sparse pulse.

This distinction matters for the fatal branch. Eventual quotient/rational
alignment and eventual strict supercapacity are known, but the first
supercapacity crossing may occur earlier, at a real skipped rank, before the
alignment threshold. A final skip \(L\) is known to satisfy
\(S_L\geq2^L\); the strict possibility \(S_L>2^L\) has not been excluded.
If the first crossing occurs on a skipped step, there is no saturated
predecessor to which (10) can be applied. A strict final row also gives no
saturated socket at the final skip; its earlier crossing history is not
classified by the final-row inequality.

Consequently the saturated resolvent barrier does not cover the whole fatal
interface. The \(3/7\) budget covers the case \(S_L=2^L\). The sparse
saturation classifier covers selected first crossings. Neither covers a
strict final row reached through the skipped branch.

## 5. Why the ancestor hole does not yet descend

Assume that a final skip \(L=3a+2\) is saturated. The budget (10) forces
\(p_L\leq1\), so at least one of
\[
 a+1,\qquad2(a+1)                                    \tag{14}
\]
is absent from \(D_L\). This is an actual earlier greedy omission. It is not
another final skip, because \(L\) itself is a later omitted rank. At the
ancestor scale \(d<L\), the identity \(r_d=T_d+g\) used in (8)--(10) is
therefore unavailable.

Nor does a missing clock imply \(S_d=2^d\). Saturation is a global
subset-sum equation involving every selected rank up to \(d\). The inequality
\(\mathscr R_L(1/2)<3/7\) controls discounted future arrivals at \(2L\); it
supplies no equality for the quotient state at \(2d\).

Thus a minimal-socket argument currently lacks a map from the saturated
state at \(L\) to another state of the same class at \(d\). If recutting
means changing the support, one must prove that the new support is an actual
greedy prefix for \(1/21\), satisfies its saturated-row equation, and has the
required positive fatal tail. None follows from the ancestor hole alone.

## 6. Exact counterexamples to saturation-free descent

The saturation hypothesis cannot be discarded from a possible descent
theorem. Two actual-prefix rows give exact counterexamples.

At \(R=20\), one has \(R\equiv2\pmod3\),
\[
 \mathscr R_{20}(1/2)\approx0.387180,\qquad
 \nu_{20}(1)=0,\quad\nu_{20}(2)=1.
\]
Exact arithmetic proves
\[
 \mathscr R_{20}(1/2)+\frac1{7(2^{20}-1)}<\frac37,
\]
so it also lies below \(3/7-\varepsilon_{20}\). Of the ancestor pair
\(\{7,14\}\), rank \(14\) is missing. Nevertheless
\[
 \mathscr R_{14}(1/2)\approx0.614596>\frac37,\qquad
 \nu_{14}(2)=2.
\]

At \(R=56\), the resolvent is approximately \(0.248473\), its first two
coefficients vanish, and both ancestors \(19,38\) are missing. Their
resolvent values are approximately \(1.34679\) and \(1.60456\), respectively.
The rank \(38\) row is itself congruent to \(2\) modulo \(3\), but its
two-step pulse is \(5\).

All comparisons are exact in the script. Neither parent row is saturated:
their quotient excesses are \(-716470\) and \(-2213804584206166\). Hence
these examples do not disprove a descent theorem which uses exact saturation.
They show that low resolvent, the correct phase, sparse first coefficients,
and the forced ancestor hole do not by themselves propagate to a smaller
sparse resolvent row.

## 7. The strict layer and failure of restriction descent

For a strict row define
\[
 e_R=S_R-2^R\geq1,\qquad
 u_R=\mathscr R_R(1/2)-e_R.
\]
Equation (9) gives the exact strict-layer budget
\[
 u_R=
 \left\{\frac{4^R}{21}\right\}-\frac13
 -\varepsilon_R-4^Rg.                               \tag{15}
\]
Thus the fatal identity controls the shifted scalar \(u_R\), not the positive
resolvent itself. In the phase \(R\equiv2\pmod3\), it gives only
\[
 \mathscr R_R(1/2)<e_R+\frac37-\varepsilon_R.        \tag{16}
\]
For \(e_R\geq1\), (16) does not even force \(\nu_R(1)=0\). The sparse-pulse
deduction is specific to layer \(e_R=0\).

The transport laws expose the same cancellation. On a selected strict step,
\[
 \begin{aligned}
 e_{R+1}&=4e_R+t_R-p_R-1,\\
 \mathscr R_{R+1}(1/2)
   &=4\mathscr R_R(1/2)-p_R+\frac1{2^{R+1}-1},
 \end{aligned}
\]
and hence
\[
 \boxed{u_{R+1}
 =4u_R+1-t_R+\frac1{2^{R+1}-1}.}                    \tag{17}
\]
The divisor pulse \(p_R\) cancels. The shifted scalar again carries the
homogeneous base-four mode; retaining the labelled formal series does not
turn (17) into a scalar contraction.

There is also an exact obstruction to the most direct lexicographic descent
in the pair \((e_R,\mathscr R_R)\). Exhaustive meet-in-the-middle search over
all Boolean \(D\subseteq\{2,\ldots,R\}\) gives the following two models:
\[
 \begin{array}{c|c|c|c|c}
 R&D&e_R&p_R&\mathscr R_R(1/2)\\ \hline
 8&\{5,7\}&234&0&378/3937\\
 20&\{5,7,8,9,10,11,13,16,18\}&332107&1&
  1609958998816333043587/4158179019758771611065.
 \end{array}                                        \tag{18}
\]
In each row, \(e_R\) is the least nonnegative excess among every Boolean
support at that horizon. Both ranks are \(2\) modulo \(3\), both resolvents
lie below \(3/7-\varepsilon_R\), and both have the required ancestor hole.
Nevertheless restriction of the labelled clocks to every smaller boundary
\(K<R\) gives \(e_K<0\). There is no smaller nonnegative socket at all, at
an ancestor scale or otherwise.

These models agree with the actual \(1/21\) greedy support through rank
\(R-1\), and differ by changing the boundary decision at \(R\) to a skip.
They are therefore exact Boolean models of the skipped first-crossing
interface, not arbitrary sparse sets. The actual greedy orbit selects ranks
\(8\) and \(20\), so the models are not actual prefixes through \(R\).
They show that the labelled divisor clocks, exact quotient row, low
resolvent, sparse pulse, and minimal nonnegative layer do not force
restriction descent. Actual real complementarity at the changed boundary is
load-bearing.

A different recut could still change the support rather than restrict it.
Such a theorem must state the recut explicitly and prove anew its greedy
admissibility, quotient equation, and fatal-tail condition. The models in
(18) do not address a theorem with those additional conclusions.

## 8. Consequences for the proposed route

The future-divisor resolvent is a useful exact state. Its full coefficient
series is lossless, its transport is local, and (6) joins it to the preceding
forced block. The \(3/7\) calculation is also exact.

Two additional statements are required before minimal descent can address the
fatal branch:

1. exclude a strict entrance at the final skipped rank, or derive a separate
   resolvent inequality which controls the integer excess \(e_L\geq1\) in
   (9);
2. prove that exact saturation plus the low resolvent budget produces an
   ancestor-scale state satisfying a new saturated equation, rather than only
   an omitted ancestor.

Without the first statement the socket does not cover the pre-alignment
entrance. Without the second, minimality has no smaller object of the same
class to which it can be applied.

## 9. Reproduction

The script scripts/future_divisor_resolvent_descent_audit.py verifies the
identities and the two finite counterexamples. Its default command is

    python3 scripts/future_divisor_resolvent_descent_audit.py --depth 200

The identities and displayed counterexamples are exact. The absence of an
actual-prefix saturated row through rank \(200\), also reported by the script,
is only a finite computation.
