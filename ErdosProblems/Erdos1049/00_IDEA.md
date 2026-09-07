# The mathematical idea and the short-paper decision

## What has actually improved

The R6 short note is already a coherent eleven-page mathematical note. The rational-base theorem is first, the cancelled denominator cost is visible, and the exact Hankel order has a Gram proof. Repeating the R5 restructuring would create churn rather than progress. This return makes a small revision to that note and supplies a separate mathematical dossier.

The most economical addition is a quantitative consequence of the existing source forms:

\[
\mu_{\rm irr}(F((a/b)^r))\le
\frac{1-\log b/\log a}{\theta^*-\log b/\log a},\qquad r\ge1.
\]

The parameter region is exactly the live region. The bound is uniform in the positive power, although approximation constants and starting denominators need not be. For the title's family the displayed bound is below 301. This is not a new irrational base. It is a more complete extraction from the same construction.

The ordinary measure argument already appears in the supplied long record's proof of `res:archcap`. Zudilin's 2004 result is itself an integer-base irrationality-exponent theorem, and his 2016 paper announces quantitative rational-base extensions. The new contribution of this corollary relative to the live short note is therefore the explicit rational-base expression, its source coefficient estimate and the power-uniform conclusion, not a new general method or a certified priority claim.

This is the appropriate use of Tao's results-to-effort advice: extract a natural consequence that costs about a page, rather than require each reader to reconstruct it. Conversely, the more substantial Hankel work below should not be added to an eleven-page note merely because it was obtained during the same review. Tao's discussion supports that distinction, not indiscriminate accumulation. Source: *Maximising the results-to-effort ratio*, 12 February 2010, expanded 20 July 2019.

## The independent idea worth remembering

For positive moments supported on a geometric progression,

\[
v_m=\sum_{k\ge0}a_kq^{(m+1)k},\qquad0<q<1,
\]

the Hankel determinant has an exact expansion as a Schur partition sum. The empty partition is the unique least-order configuration. The other partitions give the finite-q correction. This places the formal theorem and analytic estimates in the same representation instead of treating them as unrelated calculations.

The Schur measure and its Cauchy normalisation are classical; Okounkov's *Infinite wedge and random partitions*, §2.1, is a direct antecedent. The mathematical work here is the exact atom-weight perturbation for these determinants, the domination estimate allowing quantitative expansion, and the consequences of that expansion for the literal 2016 rows.

A particularly compact conclusion is the stability theorem. Suppose positive weights have the form

\[
a_k=p(k)+O(\rho^{-k}),\quad
\widetilde a_k=p(k)+O(\rho^{-k}),\qquad \rho>1,
\]

with the same polynomial part. Then

\[
\frac{V_N(a)}{V_N(\widetilde a)}
=\left(\prod_{k\ge0}\frac{a_k}{\widetilde a_k}\right)
(1+O(e^{-cN})).
\]

In generating-function language: when the only singular contribution in a disc larger than the unit disc is a finite pole at 1, its polar part controls every algebraic determinant correction. The analytic remainder affects only a positive multiplicative constant. This mechanism is independent of the irrationality benchmark.

The hypotheses have a useful falsifying example. Adding \(\varepsilon/(1+w)\) preserves the polar part at 1 and keeps the coefficients positive for \(0<\varepsilon<1\), but changes the determinant by an exponential factor. Equality near one point is not a substitute for the larger-disc hypothesis.

For the actual cubic weights, the calculation yields

\[
V_N=K(q)C_Nq^{B_N}(q;q)_\infty^{2N}N^{-8F(1/q)}
\left(1+\frac{11F(1/q)^2-7F(1/q)}N+O_q(N^{-2})\right).
\]

The cancellation producing the correction is informative. The weighted Lambert series \(T(q)=\sum j q^j/(1-q^j)\) occurs both in the second polar derivative of the atom generating function and in the expected partition size. Its two contributions cancel. This is not obtained by differentiating the MacMahon normaliser indiscriminately: an independent marking variable is needed to select partition size rather than the varying Schur alphabet.

This revisits the deferred R3 leading asymptotic with an exact representation, a quantitative proof, a further derivative and regression checks. The result remains an ordinary candidate requiring adjudication. The next step is not to promote the old claim on the strength of repetition.

## What the remaining arithmetic question teaches

The finite quantitative selector theorem already exists in the live Lean corpus. The short note still states a weaker qualitative form. The patch exposes the conditional version and the actual sufficient inequality:

\[
2^M>Qk\left(\left\lfloor nT/D\right\rfloor+1\right).
\]

The same primitive source family must supply the image size \(Q\), conditional exact multiplicity \(k\), and real remainder span \(T\). The raw positive hypergeometric remainder is not the primitive remainder span. Polynomial rank is not real nonvanishing. A generic finite theorem does not provide its source-specific hypotheses.

The thin-strip lemma adds a geometric diagnostic. If points in one lattice coset of index \(I\) have first-coordinate width \(W\) and error width \(\delta\), then \(2W\delta<I\) forces them to be collinear. In the local-divisor regime, a putatively useful narrow modular bin may therefore be one-dimensional rather than a small two-dimensional cloud. A successful estimate must control occupancy along rational directions. This is not a no-go for close points on such a line.

The lacunary countermodel identifies a different boundary. Real remainders can tend to zero even while two-adic precision exponentially exceeds coefficient height, provided the next height jumps to a much larger scale. Its nonzero adjacent determinant is explicit. The regular-scale assumption in the R4 theorem is doing mathematical work; cofinal selection cannot be rejected merely by citing an all-large-index obstruction.

## Disposition

The twelve-page preview is a surgical revision of the live note, not a competing paper. Its title, flagship theorem, original labels and public pin are preserved. The optional measure corollary has a complete ordinary proof. The larger Hankel stability argument, the new polar coefficient, the geometric lemma and the lacunary countermodel stay in the dossier.

The strongest source-specific open task remains a conditional concentration estimate for primitive real remainders in the wide family. This return has not supplied it. It has identified a more informative geometric quantity to record and prevented the regular-scale obstruction from being applied outside its hypotheses.
