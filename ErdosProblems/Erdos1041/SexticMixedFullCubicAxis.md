# Two adjacent tiles cover the full cubic axis

Fix the open mixed coefficient cell

\[
|A-A_0|\le10^{-4},\qquad |B-B_0|\le10^{-4}.
\]

The previous tile uses adjacent directions \((0,1)\), radius \(2/3\), and
works for every \(c\ge-10^{-4}\).  The reflected adjacent pair \((5,0)\), at
the same radius, supplies the missing lower range.

For its chord

\[
\widetilde z(u)={2\over3}((1-u)e^{-\pi i/3}+u),
\]

the exact degree-six Bernstein controls of the non-cubic endpoint model are

\[
\begin{aligned}
&-{ -45\sqrt6+45\sqrt2+64\over729},\\
&-{ -144\sqrt6+256+161\sqrt3+960\sqrt2\over5832},\\
&-{ -640-108\sqrt6+645\sqrt3+3396\sqrt2\over14580},\\
&-{ -2560+1455\sqrt3+7488\sqrt2\over29160},\\
&-{ -320+54\sqrt6+365\sqrt3+1698\sqrt2\over7290},\\
&-{256+144\sqrt6+309\sqrt3+960\sqrt2\over5832},\\
&-{180\sqrt2+256+195\sqrt3+180\sqrt6\over2916}.
\end{aligned}
\]

Every control is below \(-10^{-3}\).  A coefficient perturbation costs at
most \(4\times10^{-4}\), leaving \(-3/5000\).  The reflected cubic shape lies
in \([-1,0]\), so every \(c\le10^{-4}\) costs at most another \(10^{-4}\).

The reflected ray in direction 5 has the explicit endpoint-model margin

\[
H_{A_0,B_0}(t e^{-\pi i/3})\le-{107\over5832},
\qquad 2/3\le t\le1,
\]

and the cubic vanishes there.  Direction 0 is the already sign-stable ray.
Thus the reflected tile is strict throughout \(c\le10^{-4}\).

The two cubic ranges overlap:

\[
[-10^{-4},\infty)\ \cup\ (-\infty,10^{-4}]=\mathbb R.
\]

Therefore every real tangent-cubic coefficient over the whole open
\((A,B)\) cell admits one of the two adjacent radius-\(2/3\) connectors.
Lean checks the complex identities, seven Bernstein bounds, reflected ray
margin, cubic sign, perturbation transfer, and final exhaustive disjunction.

This removes the cubic coordinate completely at one genuine mixed cell.  It
does not yet cover the remaining compact \((A,B)\) section or perform the
nonlinear actual-polynomial transfer, so Erdős #1041 remains open.
