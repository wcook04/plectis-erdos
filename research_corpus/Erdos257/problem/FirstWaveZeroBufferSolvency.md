# The complete first wave excludes the isolated zero-buffer state

Write
\[
 w_n=\frac1{2^n-1},\qquad
 P(H,j)=2^jM(2,H)=\frac{2^j}{3(2^H-1)}.
\]
The first anchor-two decomposition of \(M(2,3)\) is
\[
 M(2,3)=w_5+1510M(2,15),
\]
and
\[
 1510=2^1+2^2+2^5+2^6+2^7+2^8+2^{10}.
\]
The two low packets form the exact zero-buffer pair
\[
 P(15,2)+P(15,1)=6M(2,15)=2w_{15}.                 \tag{1}
\]
Taken in isolation, (1) lies below \(w_{14}\) and cannot pay the
predecessor carry tax.  This section proves that the isolated state cannot be
obtained from the complete first wave while the two ranks in (1) are kept
unused.

## 1. The external first-wave value

The other five packets have total value
\[
 Y=(2^5+2^6+2^7+2^8+2^{10})M(2,15)
   =1504M(2,15).                                    \tag{2}
\]
Let \(F\subseteq\mathbb N\setminus\{15,16\}\) be any Boolean set for
which
\[
 \sum_{n\in F}w_n\leq Y.                           \tag{3}
\]
Then
\[
 \boxed{Y-\sum_{n\in F}w_n>M(14,15).}             \tag{4}
\]
Thus no positive rewrite of the external value can reduce its unresolved
part below the rank-15 predecessor tax while avoiding the two ranks occupied
by (1).

## 2. Proof of the solvency inequality

The Mersenne weights are strictly superincreasing in the reverse order:
\[
 w_n>\sum_{m>n}w_m.                                \tag{5}
\]
For example,
\[
 w_m=2^{-m}+\frac1{2^m(2^m-1)}
     <2^{-m}+2^{1-2m}.
\]
Summing over \(m>n\) gives a quantity less than
\(2^{-n}+\frac23,4^{-n}\), whereas
\(w_n>2^{-n}+4^{-n}\).  Equation (5) follows.

Consequently, the lexicographic greedy set is the largest Boolean subsum
below a fixed target, also when prescribed ranks are omitted.  Applying this
to \(Y\), with ranks 15 and 16 omitted, gives the exact decisions
\[
 F_0=\{7,8,9,10,11,14\}
\]
through rank 16.  The remaining value is
\[
 Y-\sum_{n\in F_0}w_n
 =\frac{508494094946}{25001218250357195}.           \tag{6}
\]
Every later rank is permitted.  Its complete capacity satisfies
\[
 \sum_{n\ge17}w_n
 <\frac{2}{131071}.                                \tag{7}
\]
Indeed, for \(n\ge17\), the factor \((1-2^{-n})^{-1}\) is less than
\((1-2^{-17})^{-1}\), and the dyadic tail sums to \(2^{-16}\).

Finally,
\[
 \frac{508494094946}{25001218250357195}
 -\frac{2}{131071}
 -M(14,15)
 =\frac{47228823157849}{9300666066109464255}>0.     \tag{8}
\]
Equations (5)--(8) prove (4).

Combining (1) and (4) gives
\[
 2w_{15}+\left(Y-\sum_{n\in F}w_n\right)
 >2w_{15}+M(14,15)=w_{14}.                         \tag{9}
\]
Hence the complete first wave always has enough external value for the
predecessor recut before the isolated rank-15 zero buffer can occur.

## 3. Scope

This is a schedule-independent theorem for the first height-15 cohort.  It
removes the literal \(P(15,2)+P(15,1)\) counterexample from the reachable
complete root state.  It does not yet prove the corresponding solvency
inequality for every later LCM-generated cohort.  The general statement is a
shifted achievement-capacity problem: the external complement of a protected
two-copy block must stay above the adjacent carry tax until one of the two
protected ranks is used.

## 4. Reproduction

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/first_wave_zero_buffer_solvency.py

The script checks all displayed rational identities, the exact greedy
decisions through rank 16, the tail bound, and the positive margin in (8).
