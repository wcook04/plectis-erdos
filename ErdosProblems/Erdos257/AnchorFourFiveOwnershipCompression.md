# The first-generation four-pool theorem for \(M(4,5)\)

Put

\[
 w_r=\frac1{2^r-1},\qquad M(a,b)=w_aw_b.
\]

The corrected rank-\(29\) recut for

\[
 M(4,5)=\frac1{465}
\]

leaves twelve positive cylinder cohorts carrying a disjoint partition of
all sixteen physical sources in the first collision frontier.  This note
closes that entire frontier.  It is not a deeper digit scan: every operation
consumes whole current cohorts, and every new residual is certified in the
positive integer cylinder cone.

## 1. Ownership-closed recoding

A *cohort* is a positive integer combination of cylinders, equipped with
the set of physical sources whose full remaining mass it owns.  Cohorts in a
state have disjoint owner sets.  A recut may consume whole cohorts
\(X_1,\ldots,X_k\), emit distinct Boolean atoms, and install

\[
 H=X_1+\cdots+X_k-\sum_{r\in E}w_r              \tag{1}
\]

only when \(H>0\).  This preserves exact physical ownership.  Indeed, write
each \(w_r=(2^e-1)M(e,r)\), refine every cylinder in (1) to common
coordinate multiples, and use numerical positivity.  The resulting
coefficient is a positive integer.  Thus \(H\) is again a positive integer
cylinder cohort; no fractional packet reserve has been detached from its
source.

For a positive value \(X\), write

\[
 f(X)=\min\{r:w_r\le X\}.                         \tag{2}
\]

The exact script verifies both global fronts and the disjoint owner
partition after every recut.

## 2. Complete second-layer compression

Let \(Y\) be the corrected ownership-closed residual after emitting
\(w_{29}\).  Thus

\[
 f(Y)=35.
\]

Use the following untouched physical cohorts:

\[
\begin{aligned}
 C&=M(5,29),& A_3&=M(17,21),& B_3&=M(19,24),\\
 A_4&=M(21,25),& D&=M(25,29),& J&=M(24,29),\\
 L_i&=2^{4i}M(28,29)\quad(1\le i\le5).
\end{aligned}                                    \tag{3}
\]

The following is an exact ownership-closed schedule.  The number on the
left is the emitted atom; the expression on the right is the new cohort.

\[
\begin{array}{c|l|c}
\text{atom}&\text{new cohort}&\text{new front}\\ \hline
34&C_{34}=C-w_{34}&39\\
35&Y_1=Y-w_{35}&37\\
36&Z=Y_1+L_5-w_{36}&40\\
37&Q=Z+A_3+C_{34}+L_4-w_{37}&43\\
42&W=Q+B_3-w_{42}&44\\
43&V=W+L_3+A_4-w_{43}&47\\
47&V_1=V-w_{47}&49\\
48&X=V_1+L_2-w_{48}&55.
\end{array}                                      \tag{4}
\]

Every row is forced by the global greedy front.  Moreover, in each row
using more than one cohort, the displayed pool is inclusion-minimal: every
proper subpool is strictly smaller than the emitted weight.  Consequently
the nonlocal pool arities after the corrected rank-\(29\) state are

\[
 2,4,2,3,2,                                      \tag{5}
\]

and never exceed four.

The only unused equal-front sources can now be grouped as

\[
 G= L_1+J,qquad f(G)=52,                         \tag{6}
\]

while

\[
 f(D)=54,qquad f(X)=55.                          \tag{7}
\]

Hence all twelve rank-\(29\) cohorts, and all sixteen physical first-front
sources they own, have compressed to exactly three disjoint positive
cohorts with fronts

\[
 (52,54,55).                                      \tag{8}
\]

This is the first-generation four-pool theorem.  It closes the scheduling
question for the whole original collision frontier, rather than for a
chosen finite list of unlabelled residual values.

## 3. The synchronized-predecessor height lemma

There is a reusable recut at the next joint event.  In general, let \(U,V\)
be disjoint positive cylinder cohorts with

\[
 f(U)=f(V)=r.
\]

If, for some \(s>r\),

\[
 w_{r-1}+w_r+w_s
 \le U+V
 <w_{r-1}+w_r+w_{s-1},                            \tag{9}
\]

then the width-two ownership-closed recut emits \(w_{r-1}\) and \(w_r\)
and leaves a positive cylinder cohort of front \(s\):

\[
 H=U+V-w_{r-1}-w_r,qquad f(H)=s.                 \tag{10}
\]

This follows immediately from (9), while positivity in the cylinder cone
follows from the common-refinement argument of Section 1.  The point of the
lemma is scheduling: two individually later cohorts synthesize the missing
predecessor with pool width two, discharge their common head, and obtain the
certified height gain \(s-r\).

For the three cohorts in (8), direct single-cohort peeling gives

\[
\begin{aligned}
 G&=w_{52}+G_{77},& f(G_{77})&=77,\\
 D&=w_{54}+D_{79},& f(D_{79})&=79,                \tag{11}\\
 X&=w_{55}+w_{59}+w_{61}+w_{63}+w_{64}
      +w_{68}+w_{70}+w_{72}+w_{74}+X_{77},
 &&f(X_{77})=77.
\end{aligned}
\]

The two independently owned rank-\(77\) residuals satisfy the sharp
instance of (9)

\[
 w_{76}+w_{77}+w_{84}
 \le G_{77}+X_{77}
 <w_{76}+w_{77}+w_{83}.                            \tag{12}
\]

Neither cohort alone reaches \(w_{76}\).  Their width-two pool therefore
emits the missing predecessor \(w_{76}\), then \(w_{77}\), and leaves a
cohort of front \(84\).  Separately,

\[
 D_{79}=w_{79}+D_{83},qquad f(D_{83})=83.         \tag{13}
\]

After rank \(79\), the complete first-front ownership has therefore
contracted to two disjoint positive cohorts at fronts

\[
 (83,84).                                         \tag{14}
\]

The rank-\(76\) event is the smallest height margin in this generation: the
first recut leaves front \(77\), only one rank later.  It is not a zero
buffer.  The synchronized-predecessor lemma discharges that head in the same
width-two ownership pool and the residual jumps to front \(84\).

## 4. Exact Boolean conservation

The resulting Boolean prefix is

\[
\begin{aligned}
\mathcal P={}&\{9,13,14,17,19,21,22,23,24,25,28,29,34,35,36,37,\\
&42,43,47,48,52,54,55,59,61,63,64,68,70,72,74,76,77,79\}.
\end{aligned}                                    \tag{15}
\]

There are disjoint positive cylinder cohorts \(D_{83}\) and \(H_{84}\),
carrying a partition of all sixteen original physical owners, such that

\[
 M(4,5)=\sum_{r\in\mathcal P}w_r+D_{83}+H_{84},
 \qquad f(D_{83})=83,quad f(H_{84})=84.           \tag{16}
\]

Thus the corrected \(1/465\) construction survives its entire first
ownership generation with bounded pool width four.  This is not an
all-depth construction: the next theorem still has to show that later
generations admit a uniform recut bound.  What is now ruled out is a failure
caused by any physical source in the original first-collision frontier.

## 5. Exact audit

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_ownership_compression.py
```

The script checks exact rational conservation after every Boolean atom,
all inclusion-minimal pool inequalities, every stated front, and the
disjoint physical-owner partition.  No floating-point comparison is used.
