# A kernel-checked compactness bound for the normalized cubic coordinate

Write \(\Delta=s^6\), let \(\rho^4=|E_2|\), and suppose the anisotropic
cubic cone has been exited through the second mode:

\[
|E_2|\ge {3s^4\over2048}.
\]

Then the rational comparison

\[
\left({25\over128}\right)^4<{3\over2048}
\]

gives \(\rho\ge25s/128\).  Radial energy gives
\(|E_3|^2\le12s^6\), hence \(|E_3|\le(7/2)s^3\).  Therefore

\[
{|E_3|\over\rho^3}\le470.
\]

Lean checks this with rational inequalities only.  The sharp calibration
from these two input inequalities is
\(\sqrt{12}(2048/3)^{3/4}\approx462.65\), so 470 loses less than 1.6%.
This theorem makes the remaining normalized
mixed sextic atlas literally bounded; it does not construct that atlas.
