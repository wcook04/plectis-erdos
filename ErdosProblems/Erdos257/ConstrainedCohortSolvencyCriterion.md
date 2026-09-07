# Constrained cohort solvency and a scale-free counterexample

Write
\[
 w_n=\frac1{2^n-1},\qquad M(2,H)=\frac1{3(2^H-1)}.
\]
At height \(H\), the coefficient-six packet pair satisfies
\[
 6M(2,H)=2w_H.                                     \tag{1}
\]
Suppose this pair is kept protected, so ranks \(H\) and \(H+1\) cannot be
used by the external cohort.  This note gives an exact criterion for whether
an external value \(CM(2,H)\) retains the predecessor tax, and shows that the
criterion is not determined by normalized anchored load.

## 1. The exact constrained-greedy criterion

Let
\[
 \mathcal A_H=\mathbb N\setminus\{H,H+1\},\qquad
 Y=CM(2,H).
\]
Starting with \(R_0=Y\), define
\[
 R_n=\begin{cases}
 R_{n-1}-w_n,&n\in\mathcal A_H\text{ and }w_n\le R_{n-1},\\
 R_{n-1},&\text{otherwise}.
 \end{cases}                                      \tag{2}
\]
The limit \(\Delta_H(C)=\lim_nR_n\) exists.

The Mersenne weights satisfy
\[
 w_n>\sum_{m>n}w_m.                                \tag{3}
\]
Consequently the support selected by (2) is the largest permitted Boolean
subsum below \(Y\).  Indeed, at the first rank where another permitted
support differs from the greedy support, it cannot select a coin rejected by
the greedy rule; if it rejects a selected coin, (3) shows that every later
coin together has smaller value.  Therefore
\[
 \Delta_H(C)
 =\inf_{\substack{F\subseteq\mathcal A_H\\
                   \sum_{n\in F}w_n\le Y}}
   \left(Y-\sum_{n\in F}w_n\right).                \tag{4}
\]

Put \(\tau_H=M(H-1,H)=w_{H-1}-2w_H\).  Equations (1) and
(4) give the necessary and sufficient criterion
\[
 \boxed{\text{every permitted extraction retains the carry tax}
        \iff \Delta_H(C)\ge\tau_H.}                \tag{5}
\]
If \(\Delta_H(C)<\tau_H\), then a finite greedy prefix already has
remainder below \(\tau_H\), and its complete unresolved value lies in
\([2w_H,w_{H-1})\).

There is also a finite safe certificate.  If \(T_N=\sum_{n>N}w_n\), then
\[
 R_N>T_N+\tau_H                                    \tag{6}
\]
implies (5), since no continuation can remove more than \(T_N\).  The bound
\[
 T_N<\frac{2}{2^{N+1}-1}                           \tag{7}
\]
is sufficient for exact rational certificates.

## 2. Equal anchored load can have opposite solvency

The complete first-wave external coefficient has
\[
 \frac{1504}{2^{15}}=\frac{47}{1024}.
\]
Its height-15 cohort satisfies (6), as proved in
`FirstWaveZeroBufferSolvency.md`.

Keep the same normalized anchored load at height 12:
\[
 \frac{188}{2^{12}}=\frac{47}{1024}.               \tag{8}
\]
For
\[
 Y=188M(2,12),qquad
 F=\{7,8,9,10,11,14,16,17,21,22\},                 \tag{9}
\]
the set \(F\) avoids ranks 12 and 13, and exact arithmetic gives
\[
 0<Y-\sum_{n\in F}w_n
 =\frac{2688127220338038597838}
 {630826191904604658117352698501}
 <M(11,12).                                        \tag{10}
\]
Combining (1) and (10),
\[
 2w_{12}
 <194M(2,12)-\sum_{n\in F}w_n
 <w_{11}.                                          \tag{11}
\]
Thus the height-12 cohort reaches the fatal corridor after a finite permitted
Boolean extraction, whereas the height-15 cohort with exactly the same
anchored load retains the tax.

Equation (5) is an exact characterization, but its value is that it rejects
a plausible hereditary invariant: neither \(C/2^H\), the coefficient-six
pair, nor their combination determines whole-cohort solvency.  The absolute
Mersenne phase of the external coefficient relative to the forbidden ranks
is essential.  A successful induction must transport more than anchored
load; it must retain the constrained greedy phase or an equivalent
whole-cohort state.

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/constrained_cohort_solvency_criterion.py

to check (8)--(11) and the independent height-15 safe certificate.
