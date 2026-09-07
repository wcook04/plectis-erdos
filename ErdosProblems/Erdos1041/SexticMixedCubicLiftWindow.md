# A one-sided cubic lift—and an exact obstruction to an arbitrary lift

The open mixed coefficient cell does extend in the tangent-cubic direction,
but not symmetrically.

For

\[
M_{A,B,c}(z)=H_{A,B}(z)+\Re(ci z^3),
\]

the cubic vanishes on both sixth-root ray directions used by the radius-
\(2/3\) connector.  On its joining chord

\[
z(u)={2\over3}((1-u)+u e^{\pi i/3}),
\]

one has

\[
\Im z(u)^3={4\sqrt3\over9}u(1-u)\in[0,1],
\qquad \Re(ci z(u)^3)=-c\Im z(u)^3.               \tag{1}
\]

The coefficient-ball theorem bounds the non-cubic chord by \(-3/5000\).
Thus every \(c\ge-1/10000\) adds at most \(1/10000\), leaving the chord
strictly below zero; both ray tails are unchanged.  Consequently

\[
|A-A_0|,|B-B_0|\le10^{-4},\qquad c\ge-10^{-4}    \tag{2}
\]

is a certified half-infinite atlas tile with one fixed adjacent pair and one
fixed rational radius.

The missing lower half-line is not an artifact of the proof.  At the exact
endpoint and \(c=-2\), the chosen chord is positive at its midpoint:

\[
M_{A_0,B_0,-2}(z(1/2))
 ={ -6\sqrt6+2+6\sqrt2+7\sqrt3\over54}>0.         \tag{3}
\]

The antipodal chord cannot repair it, because at its endpoint the cubic
vanishes and

\[
M_{A_0,B_0,-2}(-z(1))
 ={ -256+195\sqrt3+360\sqrt2\over2916}>0.         \tag{4}
\]

So the pure-second-mode theorem “choose a chord or its antipode for every
cubic coefficient” genuinely fails once the first mode is present.  The
correct mixed atlas must stratify or change its pair/radius as the cubic
coordinate crosses the lower boundary.

Lean checks (1), the half-line connector (2), both exact radical identities
(3)--(4), and their positivity.  This is still a homogeneous tangent-model
result, not the full finite atlas or Erdős #1041.
