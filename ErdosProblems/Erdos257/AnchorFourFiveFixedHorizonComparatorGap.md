# Anchor \(M(4,5)\): fixed-horizon comparator gaps

## Status

This note proves an exact comparator theorem for the proposed fixed-horizon
quotient representations.  It does **not** prove that the required
representations exist.  Its consequence is that, if the consecutive target
integers are representable, their representing words automatically have a
common prefix reaching to within \(O(\log N)\) of the half-rank seam.

For \(1\le d\le N\), put

\[
q_{N,d}:=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor
       =\sum_{r=1}^{\lfloor N/d\rfloor}2^{N-rd},
\]

and define the strict dominance gap

\[
G_{N,d}:=q_{N,d}-\sum_{a=d+1}^{N}q_{N,a}.
\]

The intended targets are

\[
H_N-e,\qquad H_N:=\left\lfloor\frac{2^N}{465}\right\rfloor,
\qquad 0\le e\le K_N:=\left\lfloor\frac N{20}\right\rfloor.
\]

## First-difference comparator

Suppose two Boolean words \(b,b'\in\{0,1\}^N\) represent integers \(x,x'\):

\[
x=\sum_{d=1}^{N}b_dq_{N,d},\qquad
x'=\sum_{d=1}^{N}b'_dq_{N,d}.
\]

If \(d\) is their first differing rank, then

\[
|x-x'|\ge G_{N,d}.
\]

Indeed, the contribution at rank \(d\) has magnitude \(q_{N,d}\), while all
later contributions can cancel at most \(\sum_{a>d}q_{N,a}\).
Consequently, if every integer \(H_N-e\), \(0\le e\le K_N\), has a Boolean
\(q_{N,d}\)-representation, then all those representing words have the same
bit at every rank \(d\) for which

\[
G_{N,d}>K_N.
\]

This conclusion does not require choosing among multiple representations.
In fact the quotient weights are superincreasing, so representations are
unique: the same first-difference argument applies because \(G_{N,d}>0\).

The gaps are nonincreasing with the rank.  More precisely,

\[
G_{N,d}-G_{N,d+1}=q_{N,d}-2q_{N,d+1}\ge0.
\]

The last inequality follows from

\[
\frac{2^N}{2^d-1}>
2\frac{2^N}{2^{d+1}-1},
\]

and taking floors.  Together with \(G_{N,N}=1\), this also proves
\(G_{N,d}>0\) for every \(d\).  Thus one gap estimate at rank \(d\) controls
the entire prefix through rank \(d\).

## Exact gaps next to the half-rank seam

### Even horizon

Let \(N=2M\), and write \(d=M-j>N/3\).  Since only the first two geometric
terms occur in \(q_{N,d}\),

\[
q_{2M,M-j}=2^{M+j}+4^j.
\]

The sum of all first terms in the later weights is \(2^{M+j}-1\).  Among the
later weights, the second terms occur for \(d<a\le M\), and their sum is

\[
1+4+\cdots+4^{j-1}=\frac{4^j-1}{3}.
\]

Therefore

\[
\boxed{G_{2M,M-j}=\frac{2\cdot4^j+4}{3}}.
\]

### Odd horizon

Let \(N=2M+1\), again with \(d=M-j>N/3\).  Now

\[
q_{2M+1,M-j}=2^{M+1+j}+2\cdot4^j,
\]

and the later second terms sum to

\[
2(1+4+\cdots+4^{j-1})=\frac{2(4^j-1)}{3}.
\]

Hence

\[
\boxed{G_{2M+1,M-j}=\frac{4\cdot4^j+5}{3}}.
\]

## Common-prefix consequence

Choose \(j\) with \(M-j>N/3\) and with the appropriate displayed gap larger
than \(K_N\).  If all \(K_N+1\) consecutive targets \(H_N-e\) are Boolean
representable, then their unique representing words share every bit through
rank \(M-j\).  The number of ranks left uncontrolled before the half-rank
seam is therefore \(O(\log K_N)=O(\log N)\), not a positive proportion of
the horizon.

Above the half-rank seam there is an exact binary completion mechanism:
for \(d>M\),

\[
q_{N,d}=2^{N-d}.
\]

Thus the upper-half weights represent every integer from \(0\) through
\(2^{N-M}-1\).  Fixed-horizon representability is consequently a cylinder
placement problem: a lower-half prefix must leave each of the consecutive
residuals inside that complete binary interval.  The comparator theorem says
that any successful placement is forced to have the quantitative common
prefix above.

## Remaining boundary

The positive product identity

\[
H_N-K_N=\sum_d c_dq_{N,d}
\]

does not by itself supply the needed Boolean representation: its primitive
pair multiplicities \(c_d\) can exceed \(1\).  The unresolved step is to
prove, or disprove, that every \(H_N-e\) for \(0\le e\le K_N\) lies in the
Boolean achievement set of the quotient weights, eventually in \(N\).  The
results above prove the desired prefix coherence conditionally on that
existence statement; they do not establish it.
