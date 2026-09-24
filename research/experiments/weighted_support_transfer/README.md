<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# When does the weighted-support test apply?

The [#257 short paper](../../../docs/papers/full-text/erdos-257-mersenne-support-subseries.md#res:weighted-support)
proves a sufficient condition for irrationality of
$X_A(b)=\sum_{a\in A}(b^a-1)^{-1}$. Its dyadic example shows why ordinary
reciprocal summability is too restrictive. This exercise changes the
example's growth rate and asks you to decide what the theorem still proves.
It uses an ordinary calculation from the paper; the two supports below are
not themselves formalised in Lean or claimed as new results.

For each $k\ge1$, choose a positive integer $r_k$ and include the numbers
$2^k m$ with $m$ odd and $1\le m\le2^{r_k}$. Call their union $A$. Different
$k$ give disjoint layers. If $S_r$ is the sum of $1/m$ over odd
$m\le2^r$, the paper proves $r/4\le S_r\le r$ for $r\ge2$. Thus

$$
\sum_{a\in A}\frac1a=\sum_{k\ge1}\frac{S_{r_k}}{2^k},
\qquad
W_{b,\{2\}}(A)=\sum_{k\ge1}\frac{S_{r_k}}{b^{2^k}-1}.
$$

## Make the decision

Set $r_k=\lceil 2^{2^k}/k\rceil$. Does the displayed weighted sum converge
at base $2$? At base $3$? What can the theorem say about $X_B(b)$ for every
infinite subset $B\subseteq A$ at those bases? Repeat with
$r_k=\lceil 2^{2^k}/k^2\rceil$. In either case, does
$\sum_{a\in A}1/a$ converge? Decide what failure of the base-two weighted
test would mean before reading the answer.

## Check your reasoning

The bounds on $S_r$ make each weighted term comparable to
$r_k/(b^{2^k}-1)$. At base $2$, the first choice therefore behaves like
$1/k$, so its weighted sum diverges. At base $3$, its term is bounded by a
constant times $(2/3)^{2^k}/k$ plus a summable rounding term. That sum
converges, as do the weighted sums at all larger integer bases. The
fixed-base theorem applies to every infinite $B\subseteq A$ at each
$b\ge3$. Failure of this $P=\{2\}$ test at base $2$ supplies no rationality
verdict there; another argument or a different finite prime set might apply.

With $k^2$ in the denominator, the binary weighted terms behave like
$1/k^2$, so the binary test converges. The theorem's binary clause then
covers every integer base $b\ge2$ and every infinite subset of $A$. Both
supports have divergent ordinary reciprocal sum: the lower bound
$S_{r_k}/2^k\ge r_k/(4\cdot2^k)$ grows without bound. No huge support needs
to be enumerated to make any of these decisions.

The paper's simpler example takes $r_k=2^k$. Compare its proof with these
two choices, the [exact Lean statement](../../../lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean#L75)
and the [reproduction route](../../../docs/REPRODUCIBILITY.md). The Lean
proof checks the conditional weighted theorem, not this parameter choice.
A failed sufficient condition never proves rationality; irrationality for
*every* infinite support in Erdős #257 remains open. A corrected bound, a
useful variation, or an earlier reference can be returned through the
[contributor guide](../../../CONTRIBUTING.md) with credit.
