# Point separation does not force critical-value separation

Let
\[
 p(z)=z^4-\frac{z^3}{262144}-2z^2+\frac{3z}{262144}+\frac12,
 \qquad t=\frac{3}{1048576}.
\]
Then
\[
 p'(z)=4(z+1)(z-t)(z-1),
\]
so the critical points are exactly \(-1,t,1\). Direct rational evaluation
gives opposite signs at the endpoints of each of
\[
 (-3/2,-5/4),\quad(-3/4,-1/2),\quad(1/2,3/4),\quad(5/4,3/2).
\]
The intermediate value theorem therefore supplies four distinct real roots,
one in each interval. Since \(p\) has degree four, these exhaust its complex
roots. In their increasing order with the three critical points, every
successive gap is strictly greater than \(1/4\); hence every pair among the
seven points is more than \(1/4\) apart.

Nevertheless,
\[
 |p(1)-p(-1)|=\frac1{65536}
   <\frac3{65536}=3\left(\frac{1/4}{4}\right)^4.
\]
The two values are distinct. The value at \(t\) is greater than \(1/2\), while
the values at \(\pm1\) are negative, so all three critical values are distinct.
Thus pairwise separation of the complete root and critical-point
configuration by \(\varepsilon\) does not imply
\[
 |p(c)-p(d)|\ge(n-1)(\varepsilon/4)^n
\]
for distinct critical points.

This failure is not repaired by changing the positive constant. For
\[
 p_s(z)=z^4-\frac43sz^3-2z^2+4sz+\frac12,
 \qquad 0<s\le\frac1{64},
\]
one has \(p_s'(z)=4(z+1)(z-s)(z-1)\). The same four root intervals and the
same \(1/4\) point-separation margin persist, whereas
\[
 |p_s(1)-p_s(-1)|=\frac{16s}{3}\longrightarrow0.
\]

This counterexample does not affect the paper's conditional
critical-value-separation theorem. That theorem assumes a quantitative gap
between normalized critical values directly. It only rules out deriving that
hypothesis from root and critical-point separation alone.

The arithmetic was independently checked with exact rational operations in
`work/erdos_release_readiness_r8_20260908/returned_authoring_r11/review_1041_geometry_r13/exact_counterexample_check.json`.
The accompanying returned Lean candidate remains unrun.
