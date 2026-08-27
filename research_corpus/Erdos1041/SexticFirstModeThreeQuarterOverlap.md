# The sextic first-mode overlap reaches three quarters

Status: complete homogeneous tangent-model theorem with exact replay and
focused Lean formalization, 2026-08-25. It strengthens the previous rational
threshold from \(4/5\) to \(3/4\). The remaining mixed atlas and nonlinear
actual-polynomial transfer are still open.

Write the paired ray model as

\[
R(t)=(t-t^5)a+(t^2-t^4)b-t^6,
\qquad 0\le t\le1.
\]

The adjacent first-mode selector gives \(a\le-A/2\), while \(b\le B\) and
\(B\le1\). Under

\[
3B\le4A,
\]

the worst normalized ray is

\[
-{3\over8}(t-t^5)+(t^2-t^4)-t^6
=-{t\over8}P(t),
\]

where

\[
P(t)=8t^5-3t^4+8t^3-8t+3.
\]

For \(0\le t\le1/2\), substituting \(x=2t\) gives the degree-five Bernstein
controls

\[
3,\quad {11\over5},\quad {7\over5},\quad {7\over10},
\quad {13\over80},\quad {1\over16},
\]

all positive. For \(1/2\le t\le1\), put \(x=2t-1\). Then

\[
16P(t)=4x^5+17x^4+44x^3+70x^2-8x+1,
\]

and

\[
70x^2-8x+1=70\left(x-{2\over35}\right)^2+{27\over35}>0.
\]

Thus both selected complete rays are nonpositive whenever
\(|E_1|/|E_2|\ge3/4\).

The joining chord remains strict. At chord scale \(u\le1/16\), the two
second-mode terms together cost at most \(Au/6\), the fifth-mode term costs
\(Au/16\), and the cubic and sextic budgets cost \(Au/8\) each. Their total is
\(23Au/48<Au/2\), leaving the strict margin \(Au/48\).

This removes the computational adversary at ratio about \(0.7975\) and shrinks
the unresolved normalized mixed annulus from \(|E_1|/|E_2|<4/5\) to
\(|E_1|/|E_2|<3/4\). It does not construct the remaining finite atlas, perform
the nonlinear transfer, or solve unrestricted Erdős #1041.
