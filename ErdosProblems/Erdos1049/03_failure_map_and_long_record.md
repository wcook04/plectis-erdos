# What the failures establish, and where the records should change

## A structural map

The following are distinct implications. A route crosses a boundary only by supplying the information named in the final column.

| Available information | What it proves | What it does not prove | Stronger information needed |
|---|---|---|---|
| Integral polynomial coefficients after cyclotomic cancellation | Denominators at a rational base are cleared by the cancelled degree | Optimality among other constructions, or the endpoint 3/2 | A new admissible rate or a different arithmetic mechanism |
| Unique formal least-order Gram tuple | Exact formal Hankel order and leading coefficient | Fixed-q asymptotics | Positive representation and a convergent bound for all nonminimal tuples |
| Same generating-function polar part at 1 | Polynomial part of atom coefficients, provided other boundary singularities are excluded | Stability if another unit-circle singularity remains | Analytic continuation of the remainder to a disc larger than one |
| Primitive row divisibility and modular image collapse | Nontrivial modular collisions, with separate integer noncollapse input | A small nonzero real error | Conditional exact multiplicity and a sufficiently short primitive real range |
| Global selector span and row counts | A global sufficient binning test | Conditional concentration inside selected fibres | Fibrewise ranges or a large restricted selector family, with rigorous counts |
| Two-adic precision exceeding coefficient height | A constraint on determinants using those rows | A universal obstruction independent of successive scales | Actual cross-index height control; regular-scale hypotheses cannot be omitted |
| A narrow bin in a high-index lattice | Collinearity when its shear-area bound is below the index | Absence of close distinct real errors along the line | Rational-direction occupancy and spacing information |

The appropriate falsifying examples are retained, not described as failed research clutter. Multiplication by `(1-q)^(N^3)` separates formal order from fixed-q decay. Multiplication by an evaluation-kernel factor separates functional rank from special-value nonvanishing. The alternating atom perturbation in dossier §4 separates a pole at 1 from a larger-disc analytic hypothesis. The lacunary sequence in §8 separates large local precision from a regular-scale determinant obstruction.

## Concrete new countermodel

With `d_n = 4^n`, the primitive pairs

\[
Q_n=9^{d_n},\qquad P_n=\sum_{j\le n}2^{d_j}9^{d_n-d_j}
\]

have nonzero real errors tending to zero for the separately defined real lacunary sum, while their two-adic errors have valuation `4*d_n`. The adjacent determinant is exactly

\[
P_{n+1}Q_n-P_nQ_{n+1}=Q_n2^{4d_n}\ne0.
\]

This is the strongest falsification to preserve when explaining the regular-scale theorem. It does not concern the actual Lambert source family. It shows exactly which quantifier would make a purported generalisation false.

## Long-record lag: locations in the supplied `02_long_record.tex`

The long record is an older rendered/source snapshot and is not being patched. Line numbers below refer to that uploaded TeX, not the current public branch. The instructions distinguish propagation from new mathematics.

**Opening comparison, around line 268.** The older sentence presenting the Bundschuh–Väänänen threshold as the strongest explicit number conflicts with the later rational-base theorem. Propagate the already accepted R5 source-comparison wording. Do not claim this is a newly found R6 mathematical error.

**Rational-base theorem and its applications.** Insert the optional measure corollary after the corresponding positive-power application, not in the general obstruction section. Preserve the original theorem and the external attribution. The generic measure argument already appears in the proof of `res:archcap`, lines 952–982. Link to or consolidate that argument rather than count its reuse as another theorem.

**`res:archcap`, beginning around line 922.** Keep the distinction between a degree upper bound and an actual degree asymptotic. Keep the full base-uniform hypotheses. When the R4 regular-scale local-height obstruction is incorporated, place the new lacunary countermodel immediately after it, with separate real and two-adic definitions. Do not append it as an objection to the valid base-uniform polynomial cap.

**`res:zudilin-sharp-qorder`, around line 1237, and `res:allrowinitial`, around line 1267.** Keep the all-depth associated-grade proof and its formal source links. The short Gram proof can precede it as an explanation. A future accepted Schur/stability module belongs after the positive-moment representation of the 2016 rows, not after the 2004 divisibility proof. The new module must state the literal normalisation (dossier (5.1)) before using any asymptotic.

**`res:boundedfibre`, around line 1792.** The existing qualitative version lags the checked conditional finite-bin theorem. Propagate the short-note replacement and the unchanged-pin locator to `QuantitativeSelectorEscape.lean`. State the exact source-dependent cardinality and range obligations. The finite wrapper produces neither source rows nor the real bin estimates.

**`prob:kernel`, around line 2314, and `eq:negative-margin`, around line 2522.** Preserve the distinction between the strong all-large-n producer specification and the cofinal sequence sufficient for irrationality. Propagate the earlier scalar-versus-height–error correction: a negative height–error exponent is not required merely to obtain nonzero integral scalar forms tending to zero. Do not quietly weaken a named producer; state the weaker consumer separately.

**`res:nomahler`, around line 2541.** The long record still carries an older simultaneous-base formulation. The R5 live note's single-base literature correction should propagate. The mixed-dilation/differential result is a separate advisory claim and must not be promoted by changing the attribution of the known theorem.

**`app:index`, around line 2635.** Regenerate only after mathematical source reconciliation. New candidate files in this return are not checked entries. The already checked quantitative selector wrapper is not rendered unverified by its historical review-environment header.

## Authored corpus destinations

The `reasoning-parts/erdos1049/family_catalogue.tex` entry for “Four jet collision” is the appropriate family-map consumer of the sharpened finite-bin statement. Its “Height and pade arithmetic” and “Scalar content no go” entries should retain the separation between local index and real error. These are navigation updates after acceptance, not authority for the new results.

The detailed new geometric-moment material is best kept in one source-facing module with this order: exact moment definition; positivity; Schur identity; domination; stability; polar derivatives; determinant correction. The general stability theorem should not be hidden inside a numerical experiment page. Its hypotheses are useful independently of this problem.

## The next actual source experiment

Choose one declared primitive source family and one modulus before computing. Record the real interval method and precision budget. For each modular signature, record the number of selectors or a rigorously described subfamily, its exact-value multiplicity bound, its certified real span, and the affine rank of narrow occupied bins. If the thin-strip inequality forces rank one, record the primitive integer direction and occupancy along it.

Sampling a few bins gives finite evidence only. Floating-point equality is not exact multiplicity. An observed near collision is not certified nonvanishing. A full-span obstruction is not a proof that every conditional fibre lacks a useful subfamily. These distinctions are the mathematical content of the proposed experiment, not mere reporting requirements.
