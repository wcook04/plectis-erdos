# Complete origin spokes fail in a genuinely mixed sextic family

This is a sharp architectural obstruction inside the remaining sextic
first/second-mode band.  It shows that positive-radius truncation is not merely
needed at the pure cubic face or at (E_1=0).

Let (0\le\lambda\le1/4), choose first-mode phase (5\pi/6), and choose
second-mode phase (13\pi/12).  On the six sixth-root directions, the paired
tangent-ray model

\[
R_j(t)=(t-t^5)A_j+(t^2-t^4)B_j-t^6
\]

has projection tables

\[
A_j={\sqrt3\lambda\over2}(-1,-1,0,1,1,0)
\]

and

\[
B_j=\left(
-{\sqrt2(\sqrt3+1)\over4},
{\sqrt2\over2},
{\sqrt2(\sqrt3-1)\over4},
-{\sqrt2(\sqrt3+1)\over4},
{\sqrt2\over2},
{\sqrt2(\sqrt3-1)\over4}
\right).                                                    \tag{1}
\]

Four rays escape explicitly:

\[
R_1(1/2)>0,\qquad R_2(1/4)>0,
\qquad R_4(1/2)>0,\qquad R_5(1/4)>0.        \tag{2}
\]

For the first inequality the worst case is \(\lambda=1/4\), where

\[
256R_1(1/2)=24\sqrt2-15\sqrt3-4>0.
\]

For directions 2 and 5, the first-mode projection is zero and the positive
second-mode germ dominates (t^6) at (t=1/4).  Direction 4 has both
nonnegative first-mode and positive second-mode contributions at (t=1/2).

Thus only directions 0 and 3 can possibly carry complete safe origin rays,
and they are antipodal.  Every adjacent or gap-two pair contains one of the
four escaping directions.  Consequently no two complete sixth-root spokes
can be shortened by a non-antipodal joining chord in this family.

## The obstruction is repaired exactly by truncation

At the endpoint \(\lambda=1/4\), take the adjacent pair of directions 0 and 1
and truncate both spokes at radius \(r=2/3\).  Direction 0 is nonpositive on
the whole unit ray because both of its low-mode projections are negative.
For direction 1, the elementary radical bounds

\[
 \sqrt3\ge {5\over3},\qquad \sqrt2\le {3\over2}
\]

give, for \(2/3\le t\le1\),

\[
R_1(t)\le-{5\over24}(t-t^5)+{3\over4}(t^2-t^4)-t^6
        =-{t\over24}Q(t),
\]

where

\[
Q(t)=24t^5-5t^4+18t^3-18t+5.
\]

Writing \(v=3t-2\ge0\) produces the coefficient-positive identity

\[
81Q(t)=8v^5+75v^4+334v^3+844v^2+642v+41>0.       \tag{3}
\]

It remains to control the joining chord

\[
z(u)={2\over3}\left((1-u)+u e^{\pi i/3}\right),\qquad 0\le u\le1.
\]

Substitution into the exact paired tangent polynomial gives a degree-six real
polynomial.  Its degree-six Bernstein controls are

\[
\begin{aligned}
c_0&=-{180\sqrt2+256+195\sqrt3+180\sqrt6\over2916},\\
c_1&={-276\sqrt6-235\sqrt3-128+132\sqrt2\over2916},\\
c_2&={-1752\sqrt6-1375\sqrt3+640+1536\sqrt2\over14580},\\
c_3&={-1872\sqrt6-1455\sqrt3+1280+1872\sqrt2\over14580},\\
c_4&={-1644\sqrt6-1375\sqrt3+640+1860\sqrt2\over14580},\\
c_5&={-204\sqrt6-235\sqrt3-128+348\sqrt2\over2916},\\
c_6&={-195\sqrt3-256+360\sqrt2\over2916}.
\end{aligned}                                                   \tag{4}
\]

The same rational radical bounds, together with
\(\sqrt6=\sqrt2\sqrt3>7/3\), put every \(c_j\) below \(-1/1000\).
Since the Bernstein basis is nonnegative and sums to one, the complete chord
is at most \(-1/1000\).  Equations (3)--(4) therefore prove an exact truncated
connector for this configuration.

The result is sharper than a no-go: complete origin spokes fail, but the
rational radius \(2/3\) succeeds.  Thus positive truncation is both genuinely
necessary and concretely sufficient here.  Any global mixed-band argument
must retain radius as a live selector variable.

This does **not** prove the full sextic tangent model or Erdős #1041.  It closes
one explicit genuinely mixed configuration and rules out one tempting global
architecture.  The remaining task is to turn this local strict certificate
and its symmetry orbit into finite parameter neighborhoods covering the
moderate mixed band.

The computation first isolated the boundary phases, ratio interval, and the
rational truncation radius.  Exact radical inequalities, the Bernstein
identity, and the Lean kernel are the proof.
