# Eight-step directed solvency fails at midpoint \(1298\)

For the exact real-greedy word \(b_n\) of \(1/465\), write

\[
 f_n=\sum_{d\mid n}b_d,\qquad s_n=f_n-b_n,
\]

and let \(Q_n\) be the quotient defect.  At a midpoint \(M\), define

\[
 D_0=-Q_M,\qquad
 D_i=2D_{i-1}+1-t_{M+i}+s_{M+i}.                  \tag{1}
\]

If

\[
 J_i=\sum_{j=1}^i(1-b_{M+j})2^{i-j},
\]

then direct induction gives

\[
 D_i=J_i-Q_{M+i}.                                 \tag{2}
\]

Thus directed payment by time \(i\) means \(D_i\geq0\).

The proposed uniform bound \(i\leq8\) is false.  The first counterexample
with \(M\geq20\) occurs at

\[
 M=1298,\qquad P_M=610,\qquad Q_M=2.              \tag{3}
\]

The exact eight-row orbit is

\[
\begin{array}{c|c|c|c|c|c|c|c}
i&n&b_n&t_n&f_n&s_n&Q_n&D_i\\ \hline
1&1299&1&1&1&0&4&-4\\
2&1300&1&1&7&6&2&-2\\
3&1301&1&0&1&0&3&-3\\
4&1302&1&0&4&3&2&-2\\
5&1303&1&0&1&0&3&-3\\
6&1304&1&0&3&2&3&-3\\
7&1305&1&0&5&4&1&-1\\
8&1306&0&0&0&0&2&-1
\end{array}                                             \tag{4}
\]

Here \(J_8=1<Q_{1306}=2\).  Payment still fails at offset \(9\), and first
occurs at offset \(10\):

\[
 J_{10}=5,\qquad Q_{1308}=3,\qquad D_{10}=2.       \tag{5}
\]

The obstruction is a byte-overflow pattern: seven selected ranks leave no
hole credit, the first hole supplies only one unit, and the following
selected rank doubles both sides before the second hole arrives.

## Exact growing-window criterion

There is an exact expression for the required window.  Fix \(M\), and for
\(i\leq M\) put

\[
 R_{M,i}=\sum_{j>i}2^{-j}
 \left(1-t_{M+j}+s^{(M)}_{M+j}\right),             \tag{6}
\]

where

\[
 s^{(M)}_n=\#\{d\leq M:b_d=1,\ d\mid n\}.
\]

For \(j\leq i\leq M\), every proper divisor of \(M+j\) is at most \(M\), so
\(s^{(M)}_{M+j}=s_{M+j}\).  Also

\[
 \sum_{j\geq1}2^{-j}t_{M+j}=\alpha_M,
\]

and, for every selected \(d\leq M\),

\[
 \sum_{\substack{j\geq1\\d\mid M+j}}2^{-j}
 =\frac{2^{M\bmod d}}{2^d-1}.
\]

Using the exact phase identity for \(Q_M\), these formulas give

\[
 \sum_{j\geq1}2^{-j}
 \left(1-t_{M+j}+s^{(M)}_{M+j}\right)
 =Q_M+1-y_M,                                      \tag{7}
\]

where \(y_M=2^Mr_M\).  Dividing the recurrence (1) by \(2^i\) now yields

\[
 \boxed{\frac{D_i}{2^i}=1-y_M-R_{M,i}.}            \tag{8}
\]

Consequently the minimal payment time is exactly the first cutoff \(i\) for
which

\[
 R_{M,i}\leq1-y_M.                                \tag{9}
\]

This identifies the obstruction to a growing-window theorem.  A bound in
terms of \(Q_M\) alone would have to control the real-greedy distance
\(1-y_M\), while the right side of (6) also retains the complete future
divisor-pulse schedule of the prefix.

This counterexample rules out a fixed eight-row theorem.  It also warns
against a payment window depending only on the current defect: exact
computation already exhibits payment delay \(18\) from a state with
\(Q_M=1\).  That observation is finite evidence, not an all-depth
counterexample to every function of \(Q_M\).  Any surviving theorem must
control the length and placement of the future hole word together with the
divisor pulses.

Run the exact audit with

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_eight_step_solvency_counterexample.py

The script certifies every real-greedy decision by an exact dyadic enclosure,
checks all midpoints \(20\leq M<1298\), verifies (2) row by row, and confirms
the first payment at offset \(10\).  No floating-point comparison is used.
