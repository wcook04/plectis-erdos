# The idea and the result

The round-5 construction rationalised a dyadic sum by sparse pairs and repair buffers. Its entropy estimate showed that corrections of size at most `(log n)^α` need order `N/log log N` available sites to encode an interval. The leading constant and the effect of cumulative congruences were unresolved.

The replacement is single-site residue feedback. At site `n_j`, require the new cumulative correction to be divisible by the modulus at the **next** site. This selects a residue class for the current digit. Every residue class has a common interval of achievable remainders when successive digit intervals overlap. The cumulative sum may depend on previous digits; independence is unnecessary. No separate buffer or companion digit is required.

The ordinary proof attains the entropy bound, including its constant. With amplitude exponent α, arithmetic modulus exponent β, and support budget δ, it gives

\[
\dim_H\mathcal E_{\alpha,M}(\delta)
=\min\{1,(\alpha-\beta)\delta/\log2\}.
\]

At `δ = log 2/(α−β)` the correction values contain an interval. Below that threshold the rationalisable inputs have dimension strictly below one, even when their supports are chosen individually. Cumulative congruences incur no additional leading-order cost beyond the restricted digit alphabet.

For every fixed congruence simultaneously, choose a slowly growing divisibility chain with β=0. The threshold is `log 2/α`. For the actual prime gaps, the construction preserves an arbitrary finite prefix, coefficient and reconstructed-position congruences, PNT-scale cumulative growth for `0<α≤1`, and the previously obtained bounded block-test laws for block length `o(log log X)`. It does not prove a new distribution law for the primes, nor a lower bound for the circular-arc deficiency.

## What belongs in the short note now

The live polynomial calculation already has its complete telescope on page one. Keep it. The stronger **landed** sparse proposition belongs immediately after the elementary bounded rationalisation. Its proof should display the pair total, weighted identity and continuation overlap before naming formal infrastructure. The edits do this without importing the new sharp theorem into the registered note.

The first theorem, `res:lcmdiagonal`, should be proved directly from

\[
T_{N+h}-T_N=2^N(2^h-1)T_0-z_{N,h},\qquad z_{N,h}\in\mathbb Z.
\]

The current forward reference to the much later classifier reverses the reader's dependency order. The direct proof also explains why later recurrence criteria collapse to the same arithmetic condition.

The new sharp theorem belongs in its own proof memorandum until reviewed. After that review, it would justify a construction-and-obstruction research paper. It is not evidence for raising the parent-problem status or replacing a registered Palomar entry today.

## Failures that became useful

**Making the bounded alphabet sparse.** The number of prefixes is subexponential at zero-density support, so an interval cannot be encoded. The variable alphabet repairs exactly this information deficit.

**Using one unconstrained digit instead of the pair.** A freely chosen digit changes the cumulative residue. Feedback permits that dependence and constrains the next digit; common interval overlap prevents the arithmetic restriction from exhausting the real-valued control.

**Using only the current modulus.** That does not guarantee the cumulative congruence at intermediate indices where the modulus increases. The corrected construction repairs the next support site's modulus and uses a divisibility chain in between.

**Equating dimension one with interval filling.** Dimension one alone would not rationalise every real input. The interval at the critical constant is established separately by the overlap construction.

**Counting only one fixed support.** That leaves target-adaptive supports unaddressed. The entropy proof counts both their locations and their digits. Location entropy is lower order at the relevant sparsity scale.

**Treating generic irrationality as positive-density dispersion.** The sparse binary irrational example in the earlier record remains a counterexample. The prime-specific lower-bound criterion is sufficient, not equivalent to irrationality.

## Transfer within the corpus

The achievement-set viewpoint from #257 supplies the interval-versus-gap geometry. The #269 residue/coboundary split identifies a finite residue while leaving the integer transfer uncontrolled. The present lemma adds a common controlled continuation interval for every residue state, in a setting where the coefficients are freely selectable. It is a possible abstract interface for other constructions; the prescribed arithmetic coefficients in #269 do not automatically satisfy it.

The mathematical distinction to retain is between (a) an invariant one can preserve while choosing coefficients and (b) an estimate for the actual prime coefficients. The first is advanced here; the second still needs a producer exceeding the finite-tail error budget.
