# Terminal coherence in the \(1/465\) quotient corridor

Status: exact theorem, 2026-08-21.  After one fixed corridor-valid prefix,
the two-sided corridor conditions at every intermediate rank follow from the
two-sided condition at the terminal rank alone.  Consequently the global
construction can be reduced to ordinary terminal quotient representations;
those representations need not be built recursively.

## 1. Recurrences

Let

\[
 t_n\in\{0,1\},\qquad
 f_b(n)=\sum_{d\mid n}b_d,
 \qquad
 Q_n=2Q_{n-1}+t_n-f_b(n),                         \tag{1}
\]

where \(b_d\in\{0,1\}\).  For the \(1/465\) source, put

\[
 K_n=\left\lfloor\frac n{20}\right\rfloor,
 \qquad
 r(n)=\#\{(i,j)\in\mathbb Z_{\geq1}^2:4i+5j=n\}.
\]

The source carry satisfies

\[
 K_n=2K_{n-1}+t_n-r(n).                            \tag{2}
\]

Thus the upper-corridor defect

\[
 E_n:=K_n-Q_n
\]

obeys the exact recurrence

\[
 E_n=2E_{n-1}+f_b(n)-r(n).                         \tag{3}
\]

## 2. Terminal nonnegativity forces all earlier nonnegativity

Since \(t_n\leq1\) and \(f_b(n)\geq0\), equation (1) gives

\[
 Q_n\leq2Q_{n-1}+1.
\]

Iteration from a rank \(j\) to a rank \(N\geq j\) gives

\[
 Q_N\leq2^{N-j}Q_j+\bigl(2^{N-j}-1\bigr).          \tag{4}
\]

Every \(Q_j\) is an integer.  If \(Q_j<0\), then the right side of (4) is
at most \(-1\), so \(Q_N<0\).  We have therefore proved:

> **Lower-coherence lemma.**  If \(Q_N\geq0\), then \(Q_j\geq0\) for every
> \(0\leq j\leq N\).

This part needs neither a cutoff nor a prescribed prefix.

## 3. An explicit upper-coherence cutoff

We first compare the maximum possible Boolean divisor load with \(r(n)\).
Write \(n=20k+a\), where \(0\leq a<20\).  Directly counting the admissible
values of \(j\) in \(4i+5j=n\) gives

\[
 r(n)\geq
 \begin{cases}
 k-1,&a=0,\\
 k,&1\leq a<20.
 \end{cases}
\]

Indeed, when \(a=0\), the values \(j=4,8,\ldots,4(k-1)\) work.  When
\(a>0\), take the least positive \(j_0\leq4\) congruent to \(a\pmod4\);
then \(5j_0\leq a+16\), so
\(j_0,j_0+4,\ldots,j_0+4(k-1)\) all give a positive integer \(i\).
Consequently

\[
 r(n)\geq\frac n{20}-1.                            \tag{5}
\]

The elementary divisor-pair bound gives

\[
 f_b(n)\leq\tau(n)\leq2\sqrt n.                   \tag{6}
\]

At \(n=1640\),

\[
 \frac n{20}-1=81>2\sqrt{1640};
\]

and the function \(n/20-1-2\sqrt n\) is increasing for \(n>400\).
Combining (5)--(6), we obtain the uniform estimate

\[
 f_b(n)\leq r(n)\qquad(n\geq1640).                 \tag{7}
\]

It follows from (3) and (7) that

\[
 E_n\leq2E_{n-1}qquad(n\geq1640).                 \tag{8}
\]

If an integer \(E_j\) is negative and every subsequent transition lies in
this range, (8) keeps it negative forever.  Hence:

> **Upper-coherence lemma.**  Let \(N\geq j\geq1639\).  If \(E_N\geq0\),
> then \(E_j\geq0\).

The index \(1639\) is the first possible starting rank here because its
first forward transition is rank \(1640\).

## 4. Terminal-to-full corridor theorem

Fix a Boolean word

\[
 a=(a_1,\ldots,a_{1638})
\]

that is already certified to satisfy

\[
 0\leq Q_j(a)\leq K_j\qquad(1\leq j\leq1638).      \tag{9}
\]

Let \(N\geq1638\), and let \(b=(b_1,\ldots,b_N)\) extend \(a\).  Then

\[
 \boxed{
 0\leq Q_N(b)\leq K_N
 \quad\Longrightarrow\quad
 0\leq Q_j(b)\leq K_j\quad(1\leq j\leq N).
 }                                                   \tag{10}
\]

The lower inequalities follow from the lower-coherence lemma.  The upper
inequalities through rank \(1638\) are (9), and all later ones follow from
the upper-coherence lemma applied backward from \(N\).  This proves (10).

One may instead fix a certified prefix through rank \(1640\), as in the
computational corridor certificates.  The statement above records the
earliest fixed-prefix boundary supplied by this estimate.

## 5. Exact terminal-representation reduction

Put

\[
 M_d=2^d-1,qquad
 q_{N,d}=\left\lfloor\frac{2^N}{M_d}\right\rfloor,
 \qquad
 H_N=\left\lfloor\frac{2^N}{465}\right\rfloor.
\]

The exact quotient identity is

\[
 Q_N(b)=H_N-\sum_{d=1}^N b_dq_{N,d}.               \tag{11}
\]

Therefore (10) has the following construction consequence.

> **Terminal-representation reduction.**  Fix one corridor-valid Boolean
> prefix \(a\) through rank \(1638\).  It suffices to prove that, for
> arbitrarily large \(N\), there are a Boolean extension
> \(b=(b_1,\ldots,b_N)\) of \(a\) and an integer \(q\in[0,K_N]\) such that
> \[
>  \sum_{d=1}^N b_dq_{N,d}=H_N-q.                  \tag{12}
> \]
> Every such terminal representation is automatically a complete corridor
> prefix.

Indeed, (11)--(12) give \(Q_N=q\), so (10) applies.  The complete corridor
prefixes form a finitely branching, prefix-closed tree.  If (12) is
solvable for arbitrarily large \(N\), that tree has vertices at arbitrarily
large depths; König's lemma supplies an infinite branch \(b_1,b_2,\ldots\).

Finally, along this branch,

\[
 \frac{H_N}{2^N}
 -\sum_{d=1}^N b_d\frac{q_{N,d}}{2^N}
 =\frac{Q_N}{2^N}\longrightarrow0.
\]

Replacing each \(q_{N,d}/2^N\) by \(1/M_d\) changes the finite sum by less
than \(N/2^N\).  Hence

\[
 \sum_{d\geq1}\frac{b_d}{2^d-1}=\frac1{465}.       \tag{13}
\]

Thus the remaining global problem may be attacked as a family of terminal
Boolean quotient-representation problems with one fixed prefix.  No
level-by-level corridor compatibility has to be imposed separately.
The finite-support exclusion proved in
`AnchorFourFiveCorridorCompatibility.md` then forces the resulting branch
to have infinite support.
