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
$b\ge3$. At base $2$, no fixed finite prime set gives a weighted witness
for the whole of $A$. This support is the host $A(2,r)$ of (1) below. If
$2\in P$, its comparison series at base $2$ is
$\sum_k r_k/(2^{2^k}-1)$, which behaves like $\sum_k1/k$; if $2\notin P$,
it is $\sum_k r_k/2^k$, whose terms tend to infinity. This failure of the
test gives no rationality verdict: another argument may still prove
irrationality, and a thinner infinite subset may admit a weighted witness.

With $k^2$ in the denominator, the binary weighted terms behave like
$1/k^2$, so the binary test converges. The theorem's binary clause then
covers every integer base $b\ge2$ and every infinite subset of $A$. Both
supports have divergent ordinary reciprocal sum: the lower bound
$S_{r_k}/2^k\ge r_k/(4\cdot2^k)$ grows without bound. No huge support needs
to be enumerated to make any of these decisions.

## A host that needs every chosen prime

The dyadic example above uses the prime $2$. A different layer construction
can require several primes together. The following is an AI-assisted ordinary
proof about the weighted criterion; this particular construction has not been
formalised in Lean or independently assessed for novelty.

Let $F$ be a finite nonempty set of primes, put $D=\prod_{p\in F}p$, and
choose positive integers $r_k$. Define

$$
A(D,r)=\{D^km:k\ge1,\ 1\le m\le2^{r_k},\ \gcd(m,D)=1\}.
$$

For a fixed finite prime set $P$, write $g=\prod_{p\in F\cap P}p$, with
$g=1$ when the intersection is empty. At each integer base $b\ge2$,

$$
W_{b,P}(A(D,r))<\infty
\quad\Longleftrightarrow\quad
\sum_{k\ge1}\left(\frac{g}{D}\right)^k
       \frac{r_k}{b^{g^k}-1}<\infty. \tag{1}
$$

To see this, the $k$th layer has $v_p(D^km)=k$ for every $p\in F$, so the
layers are disjoint. Its prime part is $h_P(D^km)=g^ku$ for some positive
integer $u$. The identity

$$
\frac{xu}{b^{xu}-1}
=\frac{x}{b^x-1}\,
  \frac{u}{1+b^x+\cdots+b^{(u-1)x}}
\le\frac{x}{b^x-1}
$$

and $\sum_{m\le2^r}1/m\le2r$ give an upper bound of twice the $k$th term
in (1). For the lower bound, set $Q=\prod_{p\in F\cup P}p$ and keep only
$m\equiv1\pmod Q$. These cofactors avoid all primes in $F\cup P$, hence
$h_P(D^km)=g^k$. Their reciprocal sum up to $2^r$ is at least $c_Qr$
for a constant $c_Q>0$ independent of $r\ge1$: the terms $1+jQ$ bound it
below by $H_{\lfloor(2^r-1)/Q\rfloor+1}/Q$, which grows linearly in $r$;
the finitely many smaller $r$ have a positive lower bound after reducing
$c_Q$. This gives the other half of (1). Constants depend on the fixed
prime sets; (1) makes no uniform claim as $P$ grows.

Now set $R=D/\min F$ and $r_k=D^k2^{R^k}$. For the resulting host $A_F$,

$$
W_{2,P}(A_F)<\infty\quad\Longleftrightarrow\quad F\subseteq P.
$$

When $P$ contains $F$, we have $g=D$ and the terms in (1) are
$D^k2^{R^k}/(2^{D^k}-1)$. Since $R\le D/2$, these are bounded by
$2D^k2^{-D^k/2}$, a summable sequence. If $P$ omits a prime of $F$,
then $g$ is a proper divisor of $D$ and $g\le R$. The terms in (1) are
$g^k2^{R^k}/(2^{g^k}-1)>g^k$, so the series diverges. Extra primes outside
$F$ cannot change that conclusion. Restricting the ordinary reciprocal
sum to cofactors $m\equiv1\pmod D$ shows that each layer contributes at
least $c_Dr_k/D^k=c_D2^{R^k}$; thus $\sum_{a\in A_F}1/a$ diverges.

For example, $F=\{2,3\}$ gives $D=6$, $R=3$, and
$r_k=6^k2^{3^k}$. At base two the whole host has a finite weighted mass
exactly for prime sets containing both $2$ and $3$. The checked binary
weighted-support theorem therefore proves that every infinite subset of this
host has an irrational support series at every integer base $b\ge2$.
This is a statement about this sufficient criterion on the whole host:
a thinner subset may admit a simpler witness, and failure of the criterion
does not imply rationality. Witness minimality can also change with the base;
for this two-prime host, $P=\{3\}$ works at every base $b>2$.

The paper's simpler example takes $r_k=2^k$. Compare its proof with these
two choices, the [exact Lean statement](../../../lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean#L75)
and the [reproduction route](../../../docs/REPRODUCIBILITY.md). The Lean
proof checks the conditional weighted theorem, not this parameter choice.
A failed sufficient condition never proves rationality; irrationality for
*every* infinite support in Erdős #257 remains open. A corrected bound, a
useful variation, or an earlier reference can be returned through the
[contributor guide](../../../CONTRIBUTING.md) with credit.
