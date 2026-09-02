# The exact cylinder hidden in the source corridor

Status: exact finite recurrence and finite computation, 2026-08-21.  This
note derives a lossless compression of the Boolean-prefix dynamic program for
$x=1/465$.  It does not prove that the compressed recurrence remains valid
at every rank.

Let $t_n$ be the binary digits of $1/465$, let

\[
 K_n=\left\lfloor\frac n{20}\right\rfloor,
 \qquad
 f_b(n)=\sum_{d\mid n}b_d,
\]

and define

\[
 Q_0=0,
 \qquad
 Q_n=2Q_{n-1}+t_n-f_b(n).
 \tag{1}
\]

The full dynamic program retains a Boolean prefix
$(b_1,\ldots,b_n)$ precisely when
$0\leq Q_j\leq K_j$ for every $j\leq n$.  Prefixes with the same
terminal value are not identified.

## 1. Cylinder transition

Suppose that at depth $n$ there is one retained prefix $b^{(q)}$ for
each $q\in[0,K_n]\cap\mathbb Z$, and that these prefixes have the form

\[
 b^{(q)}=P\,\operatorname{bin}_L(A-q).             \tag{2}
\]

Here $P$ is a common prefix of length $p=n-L$, and
$0\leq A-K_n\leq A<2^L$.  Suppose in addition that

\[
 p\geq \left\lfloor\frac{n+1}{2}\right\rfloor.   \tag{3}
\]

Every proper divisor of $n+1$ then lies in $P$.  Hence

\[
 g=\sum_{\substack{d\mid n+1\\d<n+1}}b_d
\]

is independent of $q$.  Put $c=t_{n+1}-g$.  If $e\in\{0,1\}$ is
the new Boolean digit, the terminal defect is

\[
 q'=2q+c-e.                                        \tag{4}
\]

For consecutive $q$, the two values in (4) are disjoint and together
fill the integer interval

\[
 [c-1,\,2K_n+c]\cap\mathbb Z.                    \tag{5}
\]

Consequently the next endpoint set is exactly
$[0,K_{n+1}]\cap\mathbb Z$, with one prefix per endpoint, if and only if

\[
 c-1\leq0,
 \qquad
 2K_n+c\geq K_{n+1}.                              \tag{6}
\]

The first inequality is automatic because $c=t_{n+1}-g\leq1$.  The
second is the only endpoint-coverage inequality once the common-divisor
hypothesis (3) is available.

There is also an exact formula for the new prefix.  From (2) and (4),

\[
 2(A-q)+e=(2A+c)-q'.                               \tag{7}
\]

Thus the children again form a cylinder with unnormalised endpoint
$A'=2A+c$ and suffix width $L+1$.  Removing the common leading binary
digits of the interval

\[
 [A'-K_{n+1},A']                                   \tag{8}
\]

gives the maximal common prefix and the next normalised pair $(L',A')$.
Equations (4)--(8) are lossless; they do not merge different ancestors.

## 2. The one-bit seam in a prospective induction

The statement that depth-$n$ prefixes agree through
$\lfloor n/2\rfloor$ is not, by itself, enough to apply the transition.
At an odd depth $n=2s-1$, it gives agreement only through $s-1$, while
$s$ is a proper divisor of the next rank $2s$.  The coefficient in
(1) at rank $2s$ therefore reads the uncontrolled bit $b_s$.

An induction must instead prove agreement through
$\lceil n/2\rceil$, or supply a separate even-rank statement proving
that every surviving parent has the same $b_s$.  The finite dynamic
program does retain statewise divisor counts and is not invalidated by this
point.  The point concerns the proposed passage from the finite computation
to a scalar cylinder recurrence.

In the normalised cylinder, write

\[
 [A-K_n,A]=[2^{L-1}+\delta-K_n,2^{L-1}+\delta],
 \qquad 0\leq\delta<K_n.                           \tag{9}
\]

Before common digits are removed, the next displacement from $2^L$ is

\[
 \delta'=2\delta+c.                                \tag{10}
\]

If $0\leq\delta'<K_{n+1}$, no common digit is removed and the variable
suffix grows by one.  Otherwise common leading zeroes or ones are removed.
Thus an $O(\log n)$ suffix theorem reduces to excluding long runs of the
moving interval condition

\[
 0\leq2\delta+t_{n+1}-g<K_{n+1}.                  \tag{11}
\]

The corridor inequalities alone do not exclude such a run: the artificial
choice $c=0$, $\delta=0$ satisfies (11) indefinitely.  A proof must use
the fact that $g$ is the divisor count of the fixed source prefix, not
merely the bounds $0\leq g\leq\tau(n+1)-1$.

## 3. A backward certificate for the first seam

Suppose that the cylinder transition is valid through depth $2s-1$, but its
common prefix has length exactly $s-1$.  Let $P=(b_1,\ldots,b_{s-1})$ be
this common prefix.  At the most recent normalisation depth write

\[
 n_0=s-1+L_0,
 \qquad
 A_{n_0}=2^{L_0-1}+\delta_{n_0}.                 \tag{12}
\]

No common digit is extracted from depth $n_0+1$ through $2s-1$.  If the
even-seam hole at rank $2s$ is $z$, the same fixed-prefix recurrence gives

\[
 \delta_m=2\delta_{m-1}+t_m-g_P(m)
 \quad(n_0<m\leq2s),
 \qquad
 \delta_{2s}=z.                                   \tag{13}
\]

Define the quotient defect of the fixed prefix by

\[
 Q_m(P)=\left\lfloor\frac{2^m}{465}\right\rfloor
 -\sum_{d\leq s-1}b_d
  \left\lfloor\frac{2^m}{2^d-1}\right\rfloor.
 \tag{14}
\]

Because $n_0<2s$, every suffix rank $d\in[s,n_0]$ contributes the exact
power $2^{n_0-d}$ at horizon $n_0$.  The endpoint-zero member of the
cylinder then gives $Q_{n_0}(P)=A_{n_0}$.

Both $Q_m(P)$ and $\delta_m$ obey the recurrence in (13).  Their difference
doubles at each step.  Hence

\[
 \begin{aligned}
 Q_{2s}(P)-z
 &=2^{2s-n_0}\bigl(Q_{n_0}(P)-\delta_{n_0}\bigr)\\
 &=2^{s+1-L_0}2^{L_0-1}=2^s.
 \end{aligned}
\]

Thus every first internal seam hole has the exact backward certificate

\[
 \boxed{Q_{2s}(P)=2^s+z,
 \qquad 0\leq z\leq K_{2s}.}                     \tag{15}
\]

This condition concerns a globally corridor-admissible prefix $P$, rather
than an arbitrary divisor word.  It is necessary, not sufficient: the
equation does not encode the complete intervening cylinder.  An exact search
finds no such prefix for $s\leq1{,}500$, testing $56{,}999$ admissible
prefixes.  This remains finite evidence.

## 4. A seam hole cannot remain a bounded defect

There is an exact propagation law even after endpoint uniqueness is lost.
Let \(\mathcal F_{M-1}\) be any family of corridor-admissible prefixes at
depth \(M-1\), and suppose that all of them agree through
\(\lfloor M/3\rfloor\).  Every proper divisor of \(M\), other than the
possible divisor \(M/2\), lies in this common prefix.  Put

\[
 a_M=t_M-
 \sum_{\substack{d\mid M\\d<M/2}}b_d,
 \qquad
 h_M(w)=
 \begin{cases}
 b_{M/2}(w),&2\mid M,\\
 0,&2\nmid M.
 \end{cases}                                      \tag{16}
\]

If \(w\) has endpoint \(q\), its two children have endpoints

\[
 I_M(w)=
 \{2q+a_M-h_M(w)-1,\ 2q+a_M-h_M(w)\}.            \tag{17}
\]

The next endpoint family is obtained by taking the union of these pairs and
intersecting it with \([0,K_M]\).  Formula (17) remains valid when several
prefixes have the same endpoint.

Now partition \(\mathcal F_{M-1}\) into two ancestry classes, left and
right, whose endpoint sets are separated.  Let \(q_L\) be the largest left
endpoint, let \(q_R\) be the smallest right endpoint, and let

\[
 u=q_R-q_L-1\geq1                                  \tag{18}
\]

be the number of missing endpoints between them.  Among prefixes at the
boundary endpoints, let \(H_L\) and \(H_R\) be the sets of possible values
of \(h_M\).  Before corridor truncation, the largest left descendant and
the smallest right descendant are respectively

\[
 R_L=2q_L+a_M-\min H_L,
 \qquad
 L_R=2q_R+a_M-\max H_R-1.                         \tag{19}
\]

If both ancestry classes still meet the corridor and remain separated
internally, their new gap has the exact size

\[
 \boxed{u'=L_R-R_L-1
 =2u+\min H_L-\max H_R.}                          \tag{20}
\]

Otherwise one of the two ancestry classes has no corridor-admissible child.
Indeed, all left descendants are at most \(R_L\), all right descendants are
at least \(L_R\), and \(R_L<L_R\).  Thus truncation can move the separating
gap through a corridor boundary only by deleting the ancestry class on that
side.

At an odd rank, (20) gives \(u'=2u\).  At an even rank it gives

\[
 2u-1\leq u'\leq2u+1.                             \tag{21}
\]

In particular, a nonempty internal gap never heals.  The possible
state-dependent half-bit can shrink the naively doubled gap by at most one;
endpoint multiplicity does not change this conclusion.

Apply this to a first one-point seam hole at rank \(2s\).  Its surviving
prefixes split canonically into descendants of the endpoints to the left and
right of the hole.  Write \(G_r\) for their gap at rank \(2s+2r\), as long
as both classes survive.  The transition to the intervening odd rank doubles
the gap, and the following even transition can reduce that doubled value by
at most one.  Hence

\[
 G_0=1,
 \qquad
 G_{r+1}\geq4G_r-1,
 \qquad
 G_r\geq\frac{2\cdot4^r+1}{3}.                   \tag{22}
\]

This estimate needs no new common-bit extraction.  The common prefix through
\(s-1\) already present at the seam controls every divisor below the half-bit
for all target ranks \(M\leq3s-3\), because then
\(\lfloor M/3\rfloor\leq s-1\).

An internal seam hole requires \(K_{2s}\geq2\), so \(s\geq20\).  Take
\(r=\lceil\log_4s\rceil\).  Then \(2r\leq s-3\), so the preceding
propagation law is available through rank \(2s+2r\).  If both ancestry
classes still survived there, (22) would give

\[
 G_r\geq\frac{2s+1}{3}
 >K_{2s+2r}-1,
\]

which is impossible for an internal gap in \([0,K_{2s+2r}]\).  Therefore,
within at most \(2\lceil\log_4s\rceil\) further ranks, every admissible
prefix from at least one side of the first hole is extinct.

This rules out a hole-tolerant induction in which a seam defect remains a
bounded puncture of an otherwise full endpoint interval.  It does not rule
out an infinite path: the ancestry class on the other side may continue.
After the forced one-sided collapse, a proof still needs a mechanism that
selects or controls the surviving class.

## 5. Finite anchors do not bound the runs

The divisor-count interpretation of $g$ does not give a uniform run bound
when only a fixed finite part of the prefix is prescribed.  More precisely,
fix a length $L$, a depth $D$, and arbitrary prescribed bits
$a_1,\ldots,a_D$.  There is a Boolean prefix extending these bits and a rank
$N>D$ for which the displacement recurrence

\[
 \delta_{N+j}=2\delta_{N+j-1}+t_{N+j}-g_{N+j}
 \tag{23}
\]

has the constant solution $\delta_{N+j}=C$ for every $1\leq j\leq L$,
with $0<C<K_{N+j}$.

To see this, take $N\equiv0$ modulo
$\operatorname{lcm}(1,\ldots,\max(D,20))$.  If

\[
 a(j)=\sum_{\substack{d\mid j\\d\leq D}}a_d,
\]

choose $C\geq\max(1,\max_{1\leq j\leq L}a(j))$.  For each $j$, choose
$C+t_j-a(j)$ new pairwise distinct primes $p_{j,k}>\max(D,L)$, and impose

\[
 N\equiv-j\pmod {p_{j,k}}.                        \tag{24}
\]

The Chinese remainder theorem is applicable because the new primes are
pairwise distinct and coprime to the initial modulus.  Taking a sufficiently
large solution makes every $p_{j,k}$ smaller than $N$.  Select precisely the
prescribed indices $d\leq D$ with $a_d=1$ and all the primes $p_{j,k}$;
set every other bit through $N$ to zero.  Since $p_{j,k}>L$, a prime assigned
to row $j$ divides none of the other $N+i$, $1\leq i\leq L$.  Consequently

\[
 g_{N+j}=a(j)+C+t_j-a(j)=C+t_{N+j},               \tag{25}
\]

where the final equality uses the period $20$ of the target digits.
Equation (23) now fixes $C$.  Increasing the chosen CRT solution also gives
$C<K_{N+j}$ throughout the block.

This construction is local.  It does not assert that the manufactured prefix
satisfies the corridor at every earlier rank.  It proves that period-$20$
target digits, genuine divisor ancestry, and any fixed collection of forced
prefix bits cannot by themselves bound the length of a non-extraction run.
An all-depth proof must use the complete earlier corridor history.

## 6. Finite audit

The full-prefix program and the compressed recurrence agree exactly through
rank $10{,}000$.  A separate compressed run through rank $10{,}000{,}000$
finds no endpoint, uniqueness, cylinder, or ancestry failure.  At the final
rank it has $500{,}001$ endpoints, variable suffix width $23$, and common
prefix length $9{,}999{,}977$.  The maximum suffix width in this run is
$45$, first reached at rank $9{,}947{,}025$.  The longest run with no new
common digit extracted has length $25$, from rank $9{,}947{,}001$ through
$9{,}947{,}025$.

These are finite computations.  In particular, the observed logarithmic
suffix size is not proved for all ranks.  The ten-million-rank computation
also disproves the earlier finite conjecture that every non-extraction run
has length at most twenty.

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_source_corridor_cylinder_audit.py --horizon 100000 --full-crosscheck 3000
```

for the default reproducible check.  The larger computation reported above
uses `--horizon 10000000 --full-crosscheck 10000`.
