# Reserve-lineage tax solvency does not survive the handoff

Put
\[
 w_n=\frac1{2^n-1},\qquad
 \lambda_r=2^{2-r},\qquad
 g(r)=\frac{3w_r}{\lambda_r}.
\]
This note tests a global reserve-lineage proposal.  One complete anchor-two
component is kept dormant while its siblings are unfolded and normalized;
the remaining leading child is then chosen as the next reservoir.  The
aggregate carry-tax estimate is strong enough: from rank five onward, even
the minimal reservoir dominates the carry-value increase of the entire
formally unfolded sibling tree under the \(31/60\) load contraction.  But
this does not produce a fair lineage.  The selected child can jump to the
right of an unprocessed sibling, and the sibling can consume the child's
whole value to reconstruct an earlier atom with no tax surplus.

This is a different obstruction from the length of an occupied predecessor
run.  The problem occurs before a funded carry is requested: tax-only
accounting treats value needed for future atoms as if it were free bank.

## 1. A carry-potential identity

Assign a visible atom \(w_s\) the shadow mass \(\lambda_s\).  Then
\[
  w_s=\frac{g(s)}3\lambda_s,                       \tag{1}
\]
where \(g(s)\) is strictly decreasing and
\[
  g(s)>\frac34.                                    \tag{2}
\]
Binary carrying preserves total shadow mass.  If a finite multiset of raw
fronts of total mass \(L\) is normalized to distinct fronts, all at ranks at
least \(h\), its complete carry tax is the increase in visible atom value.
Equations (1)--(2) give
\[
  \mathcal T
  <\frac{g(h)-3/4}{3}L.                            \tag{3}
\]
The same inequality holds uniformly for finite truncations of an infinite
front tree.

## 2. The \(31/60\) tree has a solvent tax budget

Let a dormant reservoir have front rank \(r\), mass \(\lambda_r\), and
value \(X\).  Its distortion is greater than one, so its reserve satisfies
\[
  X-w_r>\frac{1-g(r)}3\lambda_r.                   \tag{4}
\]
Suppose the active siblings have total load \(E<\lambda_r\), and every
opening passes less than
\[
  \rho=\frac{31}{60}
\]
of its input load to its children.  The total shadow mass of all fronts in
the formally unfolded sibling tree is less than
\[
  \frac{E}{1-\rho}<\frac{60}{29}\lambda_r.         \tag{5}
\]
Including the reservoir's own visible front gives total mass below
\[
  \left(1+\frac{60}{29}\right)\lambda_r
  =\frac{89}{29}\lambda_r
  <4\lambda_r=\lambda_{r-2}.                       \tag{6}
\]
Consequently its binary normalization cannot reach a rank earlier than
\(r-1\).  Applying (3) with \(h=r-1\), its total carry tax is less than
\[
 \frac{89}{29}\frac{g(r-1)-3/4}{3}\lambda_r.      \tag{7}
\]

For every \(r\ge5\), one has the exact inequality
\[
 \boxed{
  \frac{89}{29}\left(g(r-1)-\frac34\right)
  <1-g(r).}                                        \tag{8}
\]
To verify it, put \(y=2^{r-2}\ge8\).  After clearing positive
denominators, (8) becomes
\[
  232y^2-1416y+383>0.
\]
It is positive at \(y=8\) and strictly increasing thereafter.  Equations
(4), (7), and (8) prove:

> The minimal rank-\(r\) reservoir value dominates the aggregate carry tax
> of its own front and the complete formal sibling tree, uniformly for
> \(r\ge5\).

Thus neither LCM height nor the sum of future carry taxes is the missing
quantitative obstruction.

## 3. Exact failure of the leading-child handoff

Tax solvency is not lineage solvency.  Consider the two height-fifteen
packets
\[
  A=P(15,2)=4M(2,15),\qquad E=P(15,1)=2M(2,15).    \tag{9}
\]
They occur as literal siblings in the first anchor-two root wave.  If
\(A\) is the dormant reservoir, opening it gives
\[
  A=w_{15}+P(15,0).                                \tag{10}
\]
The only residual child \(R=P(15,0)\) is necessarily the next lineage
choice.  But its front is rank 17, while the unprocessed sibling \(E\) has
front rank 16.  The proposed leading-child handoff has moved behind its own
sibling.

More seriously,
\[
 \boxed{E+R=w_{15}},                               \tag{11}
\]
and
\[
  A+E=2w_{15}<w_{14}.                              \tag{12}
\]
The post-opening load is only
\[
  \frac12\lambda_{15}+\frac14\lambda_{15}
  =\frac34\lambda_{15},                            \tag{13}
\]
so no load-level rank-fifteen challenger is present.  Nevertheless the
sibling and the selected child use their entire scalar value to reconstruct
the already visible atom.  There is zero remaining predecessor tax.

This is a reachable root subcohort, although the other five first-wave
packets can rescue it when the complete cohort is pooled.  Hence (9)--(13)
do not prove that the full root rewrite fails.  They do prove that a
one-reservoir lineage cannot be justified by the uniform tax estimate:
the value counted in (4) is also the value from which future atoms must be
built.

There is a scheduling dichotomy.  Handing off immediately gives (11).
Waiting until the sibling's formal positive rewrite tree is completely
processed gives no finite handoff time, because every anchored opening has
a strictly positive residual.  Dovetailing the old sibling with the new
reservoir abandons the one-lineage invariant and returns to a global
multi-cohort ownership problem.

Therefore the \(31/60\) contraction proves aggregate tax solvency but not a
fair schedule with vanishing reserve.  Any viable reservoir theorem must
pool complete sibling value at each handoff, not merely bound its future
carry taxes or follow one leading child.

## 4. Reproduction

The companion exact-arithmetic script checks (8)--(13) and the tax-bound
constants through rank 500:

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/reserve_lineage_tax_budget_nogo.py
