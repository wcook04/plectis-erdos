# Fourier-magnitude no-go for pinned rational membership

Let

\[
  \mathcal A=\left\{\sum_{n\geq1}\frac{b_n}{2^n-1}:b_n\in\{0,1\}\right\}.
\]

[`FairCodingFourierDecay.md`](FairCodingFourierDecay.md) identifies the
Fourier transform of its indicator and proves an all-scale polynomial decay
bound.  The interval audit at
[`scripts/fair_coding_fourier_decay_audit.py`](scripts/fair_coding_fourier_decay_audit.py)
also finds strong, but decaying, LCM resonance.  This note states the exact
limit of any route which uses only the magnitude of that transform.

## Translation-blindness theorem

> **Theorem.** Let \(K\subset\mathbb R\) be a nonempty compact measurable
> set and let \(q\in\mathbb R\).  There are translates \(K+t_1\) and
> \(K+t_0\) such that
> \[
>   q\in K+t_1,\qquad q\notin K+t_0,
> \]
> while
> \[
>   \left|\widehat{\mathbf 1_{K+t_1}}(\xi)\right|
>   =\left|\widehat{\mathbf 1_{K+t_0}}(\xi)\right|
>   =\left|\widehat{\mathbf 1_K}(\xi)\right|
> \]
> for every real \(\xi\).

Choose \(x\in K\) and put \(t_1=q-x\).  Then \(q\in K+t_1\).  Since
\(K\) is bounded, choose \(y\notin K\) and put \(t_0=q-y\); then
\(q\notin K+t_0\).  Translation gives

\[
  \widehat{\mathbf 1_{K+t}}(\xi)
  =e^{-2\pi i\xi t}\widehat{\mathbf 1_K}(\xi),
\]

so all three magnitudes agree.

Consequently, no criterion whose complete input is
\(\lvert\widehat{\mathbf 1_K}\rvert\)—including decay exponents, absolute
LCM resonance sizes, or the absolute zero set—can by itself decide whether a
pinned rational belongs to a set.  Such data does not retain the set's
location.  This is a mechanism no-go, not a claim that phase-sensitive
Fourier analysis of the specifically anchored set \(\mathcal A\) is
impossible.

## Exact zero-set classification

For the Mersenne achievement set,

\[
  \widehat{\mathbf1_{\mathcal A}}(\xi)
  =e^{-\pi i\xi E}\prod_{n\geq1}
    \cos\!\left(\frac{\pi\xi}{2^n-1}\right).
\]

Its real zero set is exactly

\[
  \boxed{\{(2k+1)/2:k\in\mathbb Z\}}.                       \tag{1}
\]

Indeed, a single factor vanishes only when

\[
  \xi=\frac{(2k+1)(2^n-1)}2,
\]

which is an odd half-integer; conversely the \(n=1\) factor vanishes at
every odd half-integer.  If \(\xi\) is not an odd half-integer, every factor
is nonzero.  For sufficiently large \(n\) the factors are positive, and

\[
  0\leq1-\cos\!\left(\frac{\pi\xi}{2^n-1}\right)
  \leq \frac{\pi^2\xi^2}{2(2^n-1)^2}.
\]

The right-hand side is summable, so the positive tail product is nonzero;
the finite prefix is also nonzero.  This proves (1).  In particular, the
apparently Mersenne-indexed zero families are redundant specializations of
the first coin's half-integer lattice.  A search for additional exact
Fourier zeros is therefore closed completely.

## Consequence for computation

The rigorous LCM experiment remains useful as a stress test for the decay
theorem: exact prefix alignment can lift the transform by dozens of bits,
yet it does not create a nondecaying subsequence.  It cannot be promoted into
a rational-membership certificate from magnitudes alone.  Any continuing
Fourier route must instead retain phase and prove a target-specific signed
inversion or local lower bound at the rational.  The existing
\(O(|\xi|^{-1/3})\) absolute bound is not integrable and supplies no such
pointwise lower bound.

This no-go does not decide Erdős 257, rational membership in \(\mathcal A\),
or the phase-sensitive route.  It decisively closes the structurally weaker
Fourier-magnitude and extra-zero mechanisms, preventing further resonance
horizon scans from being counted as progress.

## Consequence decisions

- `FairCodingFourierDecay.md`: verified as the analytic and computational
  input; its corrected claim boundary already agrees with this no-go.
- Rational-membership and universal Erdős 257 claims: verified unchanged.
- Phase-sensitive Fourier inversion: deliberately left open; this theorem
  eliminates magnitude-only consumers, not anchored complex Fourier data.
- Research-packet and public theorem projections: deferred until the result
  is Lean-formalized or changes a rational-membership conclusion.
- Generic consequence-map matches on `prod_` and `mathbf1_`: outside scope;
  they are lexical collisions with unrelated products and indicators.
