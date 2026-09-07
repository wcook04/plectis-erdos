# The totient (4/9) even-cylinder candidate

## Status

This note records an exact construction candidate and a finite exact audit.  It
does **not** prove an infinite Boolean Mersenne representation of (4/9), and
therefore does not solve Erdős 257.

## 1. A positive rational Lambert identity

The classical divisor identity

\[
  \sum_{d\mid m}\varphi(d)=m
\]

gives, by expanding every Mersenne denominator geometrically,

\[
  \sum_{n\ge 1}\frac{\varphi(n)}{2^{2n}-1}
  =\sum_{m\ge1}m,2^{-2m}
  =\frac{1/4}{(1-1/4)^2}
  =\frac49.                                      \tag{1}
\]

Thus the ordinary binary source coefficients for this rational target are

\[
  c_{2m}=m,\qquad c_{2m+1}=0.                    \tag{2}
\]

Let (t_n) be the binary digits of (4/9).  They repeat the word
(011100).  The raw carry

\[
  K_0=0,\qquad K_n=2K_{n-1}+t_n-c_n             \tag{3}
\]

has the exact period-six quasipolynomial

\[
\begin{aligned}
 K_{6j}&=j, &K_{6j+1}&=2j, &K_{6j+2}&=j,\\
 K_{6j+3}&=2j+1, &K_{6j+4}&=j+1, &K_{6j+5}&=2j+2.
\end{aligned}                                    \tag{4}
\]

For a Boolean prefix (b_1,\ldots,b_n), put

\[
 f_b(n)=\sum_{d\mid n}b_d,qquad
 Q_n=2Q_{n-1}+t_n-f_b(n).                        \tag{5}
\]

The finite corridor condition is (0\le Q_j\le K_j) at every processed
rank (j).

## 2. Exact two-step cylinder transport

Suppose that at an even rank (n) every endpoint (q=0,\ldots,K_n) has a
unique corridor word, and those words have the cylinder form

\[
  P\;\Vert\;\operatorname{bin}_{L}(A-q).         \tag{6}
\]

Assume also that the common prefix (P) contains every proper divisor needed
at ranks (n+1) and (n+2).  Write their state-independent proper-divisor
loads as (g_1,g_2), and set

\[
 c_1=t_{n+1}-g_1,qquad c_2=t_{n+2}-g_2,qquad
 C=2c_1+c_2.                                     \tag{7}
\]

The two appended Boolean bits encode a complete base-four digit
(v=2b_{n+1}+b_{n+2}\in\{0,1,2,3\}).  Hence

\[
  Q_{n+2}=4Q_n+C-v.                              \tag{8}
\]

If endpoint zero survives, its new suffix top is independent of the chosen
parent:

\[
  A'=4A+C.                                       \tag{9}
\]

Consequently the entire next endpoint family, when it is full, is exactly the
binary interval

\[
  [A'-K_{n+2},A'].                               \tag{10}
\]

Stripping the common leading bits of the two endpoints in (10) gives the next
cylinder without enumerating its (K_{n+2}+1) words.  The audit script checks
this compressed recurrence against the independent full-prefix dynamic
program through rank (300).

`TotientFourNinthsCylinderTransport.lean` now kernel-checks the affine
identities (8)--(9) and the exact divisor localization behind the
state-independent-load assumption.  For the odd row every positive proper
divisor is at most (m).  For the even row (2m+2), every positive proper
divisor is at most (m) except the single possible midpoint (m+1).  It also
formalizes the seam consumer: if the suffix width satisfies (L\le m-1), then
the common prefix at rank (2m) reaches through (m+1), so even that last
exception is fixed and both next-row loads are parent-independent.

## 3. What the finite computation establishes

The exact integer audit has been run through even horizon (10{,}000{,}000),
with an independent full-prefix cross-check through rank (500).
At every checked even rank:

1. every defect (0,\ldots,K_n) is represented;
2. the endpoint words form one cylinder of the form (6);
3. its common prefix contains all proper divisors needed by the next two rows;
4. the final suffix width is (21), and the largest suffix width encountered
   is (46), at rank (2{,}287{,}962).

The command is

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/totient_four_ninths_even_cylinder_audit.py --horizon 10000000 --crosscheck 500
```

This is exact finite evidence.  Increasing the horizon is not a proof.

## 4. The precise missing theorem

At an even rank (n=2m), all proper divisors of (n+1) lie at most
((n+1)/3), and every proper divisor of (n+2), except possibly (m+1),
lies at most ((n+2)/3).  Strict quotient superincrease therefore reduces
state dependence to one possible midpoint bit.

The all-depth construction would follow from the following statement.

> **Midpoint-seam exclusion.**  Along the globally reachable (4/9)
> cylinder, the integer interval ([A-K_{2m},A]) never crosses the binary
> boundary belonging to rank (m+1), after the finite initial ranks.

If that interval crosses the boundary, the midpoint divisor load changes once
across the endpoint family and the next two-step image has one missing integer.
This is the same full-ancestry seam phenomenon that survives in the (1/465)
quotient construction.  Period six, the linear corridor width, and local
divisor-count bounds do not by themselves exclude it.

If midpoint-seam exclusion is proved, (6)--(10) induct forever.  Compactness
then yields an infinite Boolean support (A\) with

\[
  \sum_{a\in A}\frac1{2^a-1}=\frac49,
\]

which would disprove Erdős 257.  Until that exclusion is proved, this remains
a construction candidate rather than a solution.

The same Lean module closes the final analytic consumer independently of the
cylinder induction: exact endpoint-zero finite quotient rows at every even
depth, with no nesting assumption, converge to (4/9) and put (4/9) in the
closed Mersenne achievement set.  Thus the surviving producer is now sharply
separated from both local divisor algebra and compactness: prove that the
reachable cylinders keep (L\le m-1), or otherwise exclude the ancestry seam
at rank (m+1).  Neither statement is currently proved.
