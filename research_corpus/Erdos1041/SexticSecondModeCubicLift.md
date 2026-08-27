# The second-mode phase circle is stable under every tangent cubic

Consider

\[
H_{B,c}(z)=\operatorname{Re}(Bz^2+ic z^3-z^6),
\qquad |B|=1,\ c\in\mathbb R.
\]

The existing phase-circle theorem supplies, for every phase of (B), an
adjacent sixth-root chord on which the even model

\[
H_{B,0}(z)=\operatorname{Re}(Bz^2-z^6)
\]

is nonpositive, together with its two safe outward rays.

Write the canonical adjacent chord as

\[
z(t)=r\left((1-t)+t e^{\pi i/3}\right),\qquad0\le t\le1.
\]

Direct expansion gives the exact identity

\[
\operatorname{Im}z(t)^3
=\frac{3\sqrt3}{2}r^3t(1-t)\ge0.                 \tag{1}
\]

Hence the cubic contribution on this entire chord has one sign:

\[
\operatorname{Re}(ic z(t)^3)
=-c\operatorname{Im}z(t)^3.                              \tag{2}
\]

If (c\ge0), the original chord remains safe.  If (c\le0), replace it by
its antipodal chord.  The even model is unchanged under (z\mapsto-z),
whereas the cubic contribution reverses sign.  Thus one of the two antipodal
chords is nonpositive for every real (c).  On sixth-root rays (z^3) is
real, so the tangent cubic vanishes identically and the original radial-tail
certificate is unchanged.

Therefore the complete pure second-mode phase circle lifts to **arbitrary
tangent cubic amplitude**.  In normalized tangent coordinates, the whole
plane (E_1=0), (|E_2|=1), (E_3\in i\mathbb R) is closed by the same
canonical radius and an antipodal sign choice.  The previously proved bound
\(|E_3|/\rho^3\le470) is needed only for genuinely mixed (E_1\ne0)
stability, not on the base second-mode plane itself.

This does not yet give a uniform neighborhood in (E_1), because antipodal
reflection also reverses the first-mode term.  The exact next obligation is
to spend the phase-circle/null-box margins against that reversed linear term,
uniformly for \(|E_1|/|E_2|<4/5\).
