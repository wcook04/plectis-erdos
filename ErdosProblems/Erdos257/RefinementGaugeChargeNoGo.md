# Refinement destroys ungauged owner charges

Put

\[
 w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b,
 \qquad T_N=\left\lfloor\frac{2^N}{465}\right\rfloor. \tag{1}
\]

For a nonnegative atom coefficient word \(u=(u_d)\), define

\[
 P_N(u)=\sum_{d\le N}u_d,qquad
 Q_N(u)=T_N-\sum_{d\le N}u_d
       \left\lfloor\frac{2^N}{2^d-1}\right\rfloor. \tag{2}
\]

Let \(K_N\) be the value of \(Q_N\) for the ordinary primitive-cylinder
expansion of \(M(4,5)\).  A proposed ownership charge is

\[
 J_N^{(\lambda)}(u)=P_N(u)+\lambda\bigl(K_N-Q_N(u)\bigr), \tag{3}
\]

with \(\lambda=5\) suggested by the exact computation.  Even \(\lambda=1\)
would be sufficient for a linear quotient-defect bound.  This note shows
that no positive \(\lambda\) makes (3) monotone under the positive cylinder
refinements used by ownership-closed recuts.

## 1. The minimal exact drop

The cylinder refinement identity gives

\[
\begin{aligned}
 M(4,5)
 &=\frac{2^8-1}{2^4-1}\frac{2^{10}-1}{2^5-1}M(8,10)\\
 &=561M(8,10).                                    \tag{4}
\end{aligned}
\]

This is an exact positive ownership-preserving recoding.  The ordinary
primitive expansion of \(M(4,5)\) has its first atom at rank \(9\), with
coefficient one.  Hence, at horizon \(N=9\),

\[
 T_9=1,qquad P_9=1,qquad K_9=Q_9=0,              \tag{5}
\]

and therefore

\[
 J_9^{(\lambda)}=1.                               \tag{6}
\]

By contrast, the first primitive atom of \(M(8,10)\) has rank \(18\).
The coefficient \(561\) does not create any raw atom at or below rank
\(9\).  For the refined state,

\[
 P_9=0,qquad Q_9=T_9=1,                           \tag{7}
\]

so

\[
 J_9^{(\lambda)}=-\lambda.                        \tag{8}
\]

Thus the exact refinement (4) changes the charge by

\[
 \boxed{\Delta J_9^{(\lambda)}=-(\lambda+1).}      \tag{9}
\]

The drop is \(-2\) for the sufficient slope \(1\) and \(-6\) for the
empirically sharp slope \(5\).  This is the earliest possible failure:
for \(N<9\), both \(T_N\) and the primitive prefix of \(M(4,5)\) vanish.

The same obstruction is unbounded.  For every \(t\ge2\),

\[
 M(a,b)=
 \frac{2^{ta}-1}{2^a-1}\frac{2^{tb}-1}{2^b-1}M(ta,tb), \tag{10}
\]

so positive refinement can move the first raw head beyond any prescribed
fixed horizon while retaining exactly the same cylinder value.

## 2. Why the coefficient five is nevertheless real

The failure of (3) does not make the number five a numerical accident.  At
the fundamental horizon \(20=\operatorname{lcm}(4,5)\), the primitive
positive lattice points under \(4i+5j\le20\) give exactly the atoms

\[
 9,13,14,17,19.                                   \tag{11}
\]

Their count is five, while the raw binary carry is

\[
 K_{20}=1.                                        \tag{12}
\]

Hence the raw primitive state satisfies

\[
 P_{20}=5K_{20},                                  \tag{13}
\]

which is the exact equality observed for the real greedy word.  More
generally, at horizon \(20k\), the primitive boundary rays \(i=1\) or
\(j=1\) alone contain

\[
 (4k-1)+(5k-2)-1=9k-4\ge5k                       \tag{14}
\]

distinct primitive atoms.  The slope five therefore comes from the
fundamental primitive triangle and its boundary rays.

What fails is not the raw five-for-one geometry, but the attempt to measure
it by the ungauged front count (3) after arbitrary cylinder refinement.

## 3. Consequence for the \(1/465\) construction

Neither

\[
 P_N+(K_N-Q_N)                                    \tag{15}
\]

nor

\[
 P_N+5(K_N-Q_N)                                   \tag{16}
\]

is an ownership-local monotone on the positive cylinder cone.  Any viable
charge must assign latent credit to the refined cylinder in (4), and that
credit must be invariant under further replacements (10).  Equivalently,
the state must retain an anchor or height gauge; raw atom fronts alone are
not sufficient.

This theorem does not disprove the global inequalities \(P_N\ge Q_N\) or
\(P_N\ge5Q_N\) for the actual greedy orbit.  It rules out proving either by
an ungauged local monotonicity of (3).  The remaining viable route is an
anchored capacity charge which survives common refinement.

## 4. Exact audit

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/refinement_gauge_charge_nogo.py
```

The script checks the refinement coefficient, the two charge drops, the
minimality of rank \(9\), and the sharp primitive equality at rank \(20\)
using exact integer and rational arithmetic.
