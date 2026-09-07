# The failures as a structural map

The purpose is to separate hypotheses, not to accumulate warnings that “local arguments fail”. Each row names a model, the information it preserves, and an inference it disproves. A synthetic model should not be advertised as an orbit counterexample; a genuine weighted orbit should not be advertised as a unit-fraction counterexample.

## 1. The information hierarchy

The relevant data come in distinct layers:

1. A positive integer numerator and a small relative decrement.
2. Exact transport by a denominator state.
3. The LCM update, overlap factor, and persistent old divisors.
4. Integrality of the numerator coefficient in `a_n U_n-U_(n+1)=b_n L_n`.
5. The exact unit coefficient `b_n=1`.
6. Synchronisation of denominator size, divisor activation and the actual record sources.

The final two are not consequences of the preceding layers. The adaptive prime construction in `01_research_note.md`, Theorem 5, preserves the first four, even with positive reduced terms and a rational sum, while allowing the quotient in layer 4 and the scale in layer 6 to vary.

## 2. Named separating examples

| Example or theorem | What it preserves | What it defeats | Information still absent |
|---|---|---|---|
| Scalar `C_n=n^2+1`, `E_n=-(2n+1)` | Positive integrality, normalised vanishing, subexponential numerator growth, finite square mass | A conclusion based only on these scalar estimates | Exact denominator transport; the word `0,0,2 mod 5` is impossible in the exact system |
| r4 arbitrary-envelope avoidance walk | Increasing states, coprimality with every selected modulus, gaps below any chosen unbounded envelope | A coefficient-free, scale-free small-rise extension of the bounded-rise barrier | Exact orbit realisation and canonical modulus timing; the family depends on the envelope |
| r6 adaptive prime realisation | Exact rational tails of sum one, positive proper reduced terms, all-fresh primitive states, normalised vanishing, weighted critical rate, arbitrarily slowly unbounded errors | The assertion that exact arithmetic realisability and freshness repair the preceding countermodel | The coefficient is not identically one; denominator representatives can be arbitrarily large |
| r6 overlap series `(n+1)/2^(n+2)` | Exact LCM transport, rational sum one, every actual jump equal to one | Replacing raw error or mixed charge by actual-jump excess when centring is removed | Normalised vanishing; raw overlap cost is large |
| r5 unit-numerator `U=1`, `V=-1`, `rho=2` | Exact rational series, bounded height, bounded negative error | Inferring zero error from bounded height alone | Normalised vanishing; the bare denominator ratio tends to `1/2`, not one |
| r5 positive-coefficient `(1,3)` cycle | Rational sum, bounded height, no overlap, positive coefficients from a finite alphabet | Inferring stationarity from bounded height and freshness | Normalised vanishing |
| r5 coefficient old-divisor example | Exact positive coefficient system and permanent freshness after the initial step | Transporting the unit-numerator coprimality theorem verbatim to coefficients | Unit forcing; jump divisibility still survives |
| r6 doubling-height telescoping system | Exact positive rational tails and permanent freshness | Using an integrable weight to force bounded height | Divergence of the weight integral |
| r6 smooth weight `sin^2(pi t)+exp(-t^2)` | Strict positivity, smoothness, divergent integral | Dropping monotonicity of the weight | A comparison between the continuous height integral and the sampled integer states |
| Pure-square cancellation examples in the supplied record | Quadratic-character compatibility | Estimating cancellation size from square classes alone | Valuation magnitude and exact transport |
| Arbitrarily long finite constant-error prefixes | Each tested finite constraint, followed by later termination | Inferring one infinite nonterminal orbit from long prefixes | A compatible infinite construction with every limiting hypothesis |
| #249 synthetic factor-ideal pulse | Exact coboundary identities, all named factor ideals, bounded states/letters, every finite shift-linear observation | An endpoint argument depending only on those linear observations | Actual totient forcing; nonlinear observations are not covered by the theorem |

## 3. A reusable proof architecture

First-crossing arguments separate *supply*, *local obstruction* and *accounting*.

**Supply.** Infinite fresh records provide an infinite pairwise-coprime family because each old multiplier enters every future LCM. A finite family then gives a CRT progression. The existing `LcmRecordCrossing.exists_crt_covering_progression` already proves the latter finite construction. These two assertions should not be merged into an opaque “supply lemma”.

**Local obstruction.** At a fresh step, every divisor of both source and clearance divides the actual jump. A covered source cannot produce a positive jump smaller than its assigned divisor. The coefficient disappears modulo the divisor; unit-numerator coprimality is unnecessary for this implication.

**Accounting.** A height is charged at its unique first crossing, not at every recrossing. The fresh step pays through jump excess. An overlap step pays through new record height, dominated by raw error after a finite threshold. This is why no monotonicity of the orbit and no centring hypothesis is needed in the new theorem. Monotonicity of the *weight* is a separate, essential assumption.

This resembles a deterministic level-crossing or layer-cake argument: integrate over heights after assigning each height to its first hitting step. There is no probability assumption or asserted martingale theorem. CRT supplies the periodic set of test heights.

## 4. The construction tests the proof's blind spot

The inverse construction solves two different constraints in sequence:

\[
a\equiv vU^{-1}\pmod L,
\qquad b=(aU-v)/L>0.
\]

The congruence makes the quotient integral. Dirichlet provides arbitrarily large representatives, and their size enforces positivity, prime freshness, tail contraction and any required sparsity. The quotient is then whatever the construction needs. A proof that keeps only divisibility has forgotten whether that quotient was one.

This does not establish that every successful proof of #243 must explicitly mention `b=1`. A different invariant might encode the same restriction indirectly. It does establish that a proposed collection of hypotheses preserved by Theorem 5 cannot imply the desired universal stationarity theorem for the larger coefficient class.

## 5. The productive questions

The canonical target remains

\[
\exists B\ge0:\qquad
\liminf_{X\to\infty}\frac1X
\sum_{\substack{n\in\mathcal R\\U_n\le X}}(-V_n-B)_+=0.
\]

The arithmetic already forces positive linear excess on a nonterminal canonical orbit. The new results do not prove the displayed estimate. They show what an argument for it must distinguish.

The most useful next experiment is to retain the exact quotient-one equation at exceptional record sources, rather than weaken it to congruence, and seek a quantitative restriction on how those sources can align with the activated old moduli. Another focused question asks whether a finite positive coefficient alphabet, together with normalised vanishing, still permits an infinite nonterminal orbit; the r5 cycle fails vanishing and the r6 construction uses unbounded coefficients. Neither decides that question. A third asks what changes when the denominator primes must lie on a prescribed near-quadratic scale; Dirichlet without a quantitative bound deliberately supplies no such control.

These are research questions, not additional obligations already solved by a finite verifier.
