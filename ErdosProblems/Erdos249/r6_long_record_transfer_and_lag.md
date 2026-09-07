# Long-record destinations and specific lag

Authority: the round-six live note and source slice. The long record and authored parts are the reported-prior assembly. This file identifies destinations; it does not modify that assembly.

## Existing status contradiction that must be repaired

### `a249_front.tex`, `defn:apfde`, subsection “Survivor 4: depth-locked full-depth escape”

The paragraph following the definition says the predicate may be strictly stronger than irrationality and cites a docstring saying necessity is unknown. That is contradicted by live `res:fulldepth` and `FullDepthRayAmplifier.lean`.

The replacement mathematical content is:

> For each fixed d≥1 and N≥0, existence of a full-depth certificate at a positive multiple of d is equivalent to Δ_d(N) being nonintegral. One nonintegral seed supplies certificates in every sufficiently late adjacent pair of multiplier indices. Universal supply over d,N is equivalent to irrationality of S. The existence of those seeds is the unsupplied arithmetic condition.

Preserve the definition and its existing consumer. Replace the “possibly strictly stronger / not known necessary” discussion with the current equivalence. Do not reclassify finite seeds as universal supply.

### `a249_invent.tex`, “Route 4: depth-locked full-depth escape”, `prop:route4`

The one-sided metric inequality in `prop:route4` remains valid. Retain it. Immediately afterwards, insert the live nonintegral-seed equivalence and its recurrence proof from `res:fulldepth`.

The later paragraph beginning “Which technique family fits” calls subword complexity the required route and describes one technique as the only available machine. That characterisation is superseded by the elementary phase recurrence. The exact missing fact is a seed for every d,N, or equivalently the canonical gap for every c,v. Keep historical discussion explicitly historical; do not describe a particular unproved method as logically necessary.

## Where the new mathematical proof belongs after review

### Kernel algebra: after the existing kernel-basis discussion

Anchor: `a249_front.tex`, `prop:rank` and `prop:period-not-rank`. Preserve both statements. Add a new authored part `a249_polynomial_kernel.tex`, with proposed labels:

* `thm:totient-kernel-polynomial-ideal`;
* `lem:affine-totient-open-box`;
* `thm:affine-totient-algebraic-stability`;
* `cor:totient-kernel-product-ranks`;
* `prop:affine-totient-subspace-arrangement`.

Source: Sections 1–3 of `research/ordinary_proofs.tex`, particularly `thm:kernel-algebra`, `lem:box`, `thm:stable`, `cor:hilbert` and `eq:arrangement`.

These are ordinary proof candidates. Their relation to prior linear results must be explicit. Do not append “Lean” to the completeness theorem because the dyadic identity candidate compiles later. Identity verification and ideal completeness are different statements.

The general ideal-intersection formula is a useful destination for the earlier affine-signature theorem. It subsumes a polynomial relation problem; the old linear theorem remains a readable corollary. The compiled periodic and Boolean helpers retain their narrower statuses.

### Dilated residue values: extend the existing dyadic classification section

Anchor: `a249_extensions.tex`, `thm:dyadic-classification`, `cor:dyadic-relations`, `cor:joint-independence`, and `prop:allbase-observable`.

The existing `cor:joint-independence` varies dyadic resolution at denominator base two. The new theorem varies both resolution and the exponent of a common base. Do not replace the old corollary with an apparently identical statement and call it new. Add proposed labels:

* `thm:joint-dilated-dyadic-observables`;
* `lem:finite-dilation-pulse-isolation`;
* `cor:two-parameter-residue-independence`;
* `prop:finite-linear-form-pulse-bound`.

Source: Section 4 of the research memorandum, including `thm:joint`, `lem:dilation`, `cor:grid`, `eq:lower-linear`. Keep m≥3 for least residues, b≥2 integer, finite distinct positive exponents, and rational observables. The dyadic modulus k=1 case is rational and must remain included as the trivial boundary. The arbitrary-modulus statement covers least residues; no general all-modulus mixed-observable classification is claimed.

The finite witness data belong beside this proposition, with the full exact receipt. Do not report their tiny symbolic lower bounds as a uniform irrationality measure.

### Stronger rational-control obstruction: keep distinct controls separate

Anchor: `a249_extensions.tex`, `thm:parity-perturbed-control` inside `ssec:rankupper-retired`.

After the checked control, append the ordinary corollary that its nonproportional affine sections are algebraically independent over Q(n), since the error from φ is bounded. Proposed label: `cor:rational-control-algebraic-independence`.

Then add the separate o(n) branch-unlabelled control, proposed label `prop:unlabelled-dyadic-branch-control`, followed by a reference to the already checked `one_prime_law_and_little_o_forces_totient` in `PrefixValuationAndControlRigidity.lean`.

Do not conflate the two examples. Rational sum is proved for the first. The quadratic branch identity is proved for the second. No single control is asserted to have both sets of properties, and neither is asserted to satisfy the exact labelled prime laws.

### The bounded-to-unbounded transition

Anchor: `a249_extensions.tex`, after `prop:allbase-observable` and `prop:composite-centres`; cross-reference the canonical endpoint in `a249_p5.tex`, “What is open, stated exactly”.

Add the short comparison `0 < S−A_m ≤ (m+1)2^(−m)` and the explanation that the pulse centre depends on the modulus and coefficient bounds. Attach the existing `termwise_dyadic_window_vacuous` inequality. These identify the lost uniformity without claiming that all weighted-window cancellation is impossible.

No old failed route should be described as newly closed merely because this comparison is now better explained.

## Records that should stay intact

`a249_front.tex`, `thm:rankonefloor`: retain the exact positive-quotient family, unique minimiser and false 1/15 comparison. The current candidate work does not extend this family.

`a249_newdecls.tex`, `rank-one-subrank`: attach a cross-reference to the current rank-uniform Hankel result in the live frontier card. The old fixed-rank statement is a weaker antecedent, not the present open task. Keep the reduced-denominator estimate as the unsupplied arithmetic link.

`a249_extensions.tex`, `ssec:cf-record`: retain the distinct comparisons q≥2^39989 and q>10^12038, along with the computation receipt and its evidence band. The current review did not rerun that computation.

`a249_invent.tex`, `thm:lacunary`, and the later normal prime-locking construction: preserve the strongest available falsifier for generic prime sampling. The new density lemma concerns integers in affine progressions; it supplies no estimate for the specific prime-aligned orbit of S.

The authored long record was not mutated. Any transfer should retain its ordinary/candidate label until independently checked and, separately, registered by the desk.
