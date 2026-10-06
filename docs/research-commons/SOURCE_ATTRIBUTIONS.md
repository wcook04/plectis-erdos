<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Source attributions

_Generated from the authored source registry; do not hand-edit._

This index shows which public sources informed which papers, problems, Lean-facing records, and implemented changes. Source credit does not establish proof, novelty, endorsement, peer review, or complete historical coverage.

Private correspondence appears only under a neutral anonymous identity until public naming is confirmed. Its email, mailbox location, message text, and private evidence remain outside this repository.

## Coverage and anonymous implementation credits

The registry contains `312` curated sources across `24` registered papers and `1903` Lean library files.

Source review states: `bibliography_only`: `97`; `existing_source_closure`: `31`; `external_claim_unverified`: `1`; `implemented_advice`: `5`; `source_verified`: `178`.

Bibliography coverage records attribution already present in the corpus. A `bibliography_only` record still needs direct source-passage verification; a completed lexical review does not certify a source-to-theorem correspondence.

Implemented advice from private correspondence. The [credit ledger](CREDIT_LEDGER.md) gives each entry's date, what changed and whether the person has been named:

- [Listing each checked result, with a cheap way to check it](#source-correspondence-001) — Implemented advice to classify each selected result, expose exact statements, proof provenance, novelty status, sorry count, axiom budget, and boundaries in formalization.yaml, and to provide a cheap Comparator inspection route with an altered-statement rejection fixture. The current public surface has evolved beyond the original interface count; the durable implementation is the manifest-plus-Comparator pattern and its explicit scope ceiling.
- [Leading the #249 paper with its exact theorem](#source-correspondence-002) — Implemented advice to lead with the exact finite-level rank and basis, give the CRT/Dirichlet-style independence mechanism, compare the result precisely with Allouche–Shallit, Coons, Martin, and adjacent k-kernel literature, and link a minimal Lean entry. The paper states the exact rank k^e+1 and basis, records that Coons already proved non-k-regularity and Martin supplies a broader external affine-independence antecedent while the public Lean proof establishes all-base independence separately, and keeps the unbounded #249 irrationality endpoint open. No proof verification, novelty judgment, or progress-on-parent-problem judgment is attributed to the correspondent.
- [Earlier work on the #1049 Lambert value](#source-correspondence-003) — Implemented a received pointer by comparing the cited q-Apéry construction with the #1049 rational-base programme. The public source closure verifies that the paper targets the same Lambert value, identifies the q-WZ operator and the integer-base denominator-clearing boundary, and credits both published authors in the ordinary literature row. The local Lean module separately proves that Van Assche’s different moving diagonal has a nonzero n=0 residual for the cited operator. This correspondence row credits only the private prior-art pointer; it does not claim the correspondent checked the comparison, calculations, Lean, or #1049 mathematics.
- [Writing for a first-time reader](#source-correspondence-004) — Implemented advice on exposition received about the #243 note: replace private names for ordinary objects with the mathematics they denote, inline notation that is used once, and say how restrictive a conditional hypothesis is. The eight short and eight long problem papers were rewritten under these rules and merged on 18 September 2026. The #243 note now names the Chinese remainder theorem where that is the tool and gives examples of what its bounded-increment hypothesis covers, and the public writing skill and short-paper contract now require plain names, notation only where it helps, and an explanation of restrictive hypotheses. No mathematical review, verification or endorsement of any paper is attributed to the correspondent.
- [Showing where methods and ideas come from](#source-correspondence-005) — Implemented advice received in reply to a letter about one of the eight problems: the main objection to AI-assisted mathematics is how rarely it shows where its methods and ideas come from. A prior-art literature review was then run for each of the eight problems, and pull requests #180 and #181 added point-of-use attribution and corrected locators to all eight short papers and long records. No mathematical review, verification or endorsement of any paper is attributed to the correspondent.

- Unmatched citation keys: `0`
- Bibliography entries awaiting curated links: `119`
- Lean candidates awaiting review: `827` (`3` direct URL/DOI/arXiv rows; `1678` surname/key rows; categories may overlap).

## Browse by problem

- **Erdős #1041**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates), [Listing each checked result, with a cheap way to check it](#source-correspondence-001), [Writing for a first-time reader](#source-correspondence-004), [Showing where methods and ideas come from](#source-correspondence-005), [Degree-seven total-variation counterexample for polynomial lemniscates](#source-erdos1041-ani-degree-seven-candidate-counterexample), [Independent check of candidate degree-seven counterexample](#source-erdos1041-morluto-independent-check), [Quartic case of Erdős #1041](#source-erdos1041-pendyala-quartic), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [A Markov-type inequality for arbitrary plane continua](#source-eremenko-2007-markov-type-inequality-plane-continua), [An extremal problem for polynomials](#source-eremenko-lempert-1994-extremal-problem-for-polynomials), [Comb functions](#source-eremenko-yuditskii-2012-comb-functions), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [The maximal length of the Erdős–Herzog–Piranian lemniscate in high…](#source-source-0e12f93aeac487), [Lemniscates and inequalities for the logarithmic capacities of cont…](#source-source-2a86f52125aec0), [Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zu…](#source-source-2ec6bf87654604), [Bad Polynomials for Newton's Method](#source-source-318ee5e7cf6d74), [The area of polynomial images and preimages](#source-source-40bc4064b92788), [Three refinements for the lemniscate-path programme](#source-source-45037c29c04bed), [Length functions of lemniscates](#source-source-57fe330e419648), [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff), [Critical points and values of complex polynomials](#source-source-7ac8693558c1a2), [On the length of lemniscates](#source-source-7f1f2a3fd9238c), [A bound for Smale's mean value conjecture for complex polynomials](#source-source-818467bc1cb170), [Shortest paths in polynomial lemniscate sublevel sets and a problem…](#source-source-8710374c3e8c9f), [The arc length of the lemniscate |p(z)|=1](#source-source-89b9a294db76bb), [Computing the Newtonian Graph](#source-source-92b0dfb67f5009), [A Degree-Four Lemniscate Path Theorem](#source-source-951f70d8dfc418), [Number of Components of Polynomial Lemniscates: A Problem of Erdős,…](#source-source-97b4e6a82335a7), [Two-dimensional shapes and lemniscates](#source-source-9e37cc2fe7db3e), [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec), [Inequalities for critical values of polynomials](#source-source-b10b965e63a00d), [Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichun…](#source-source-b4b0f2811b1d2d), [Some inequalities for polynomials and rational functions associated…](#source-source-dcbe400c96be59), [Four-point distortion theorem for complex polynomials](#source-source-f0af8e6f36727f), [A Short Path Joining Two Zeros Inside a Polynomial Lemniscate](#source-source-f300911fb03a5c)
- **Erdős #1049**: [Listing each checked result, with a cheap way to check it](#source-correspondence-001), [Earlier work on the #1049 Lambert value](#source-correspondence-003), [Writing for a first-time reader](#source-correspondence-004), [Showing where methods and ideas come from](#source-correspondence-005), [Retrieval of Chowla 1947 original scan](#source-erdos1049-bloom-chowla-scan-retrieval), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #1049](#source-formal-conjectures-adapter-problem-1049), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [A problem about Mahler functions](#source-source-0a6b8c93371570), [Stieltjes moment sequences of polynomials](#source-source-0f46dee5024c66), [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [À propos de la série ∑\_{n≥1} x^n/(q^n−1)](#source-source-169c3d67838965), [On a permutation group related to ζ(2)](#source-source-176d35cb60b651), [On the non-quadraticity of values of the q-exponential function and…](#source-source-22ef36d016ca81), [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62), [On powers of Stieltjes moment sequences, II](#source-source-2a10c7287879c3), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [A determinant identity for moments of orthogonal polynomials that i…](#source-source-3479bad7869d7c), [Common Factors in Fraction-Free Matrix Decompositions](#source-source-39e4fc546549fd), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [Lattice paths and branched continued fractions: An infinite sequenc…](#source-source-490b1875016ea4), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Calculation of Gauss Quadrature Rules](#source-source-53a2a9c4a9e7c2), [NIST Digital Library of Mathematical Functions, Eq. 17.2.37](#source-source-5857f9959e7529), [On an incomplete argument of Erdős on the irrationality of Lambert…](#source-source-5911448b65fdf9), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [On the irrationality of ∑ 1/(q^n+r)](#source-source-62f9190aeb7d34), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [Arithmetical functions and irrationality of Lambert series](#source-source-6cfe654e650970), [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b), [Smith normal form in combinatorics](#source-source-91756d895a28a8), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Zero Coefficients of Rational Power Series and Rational Lambert Series](#source-source-aa2d5c249362f1), [On the irrationality of generalized q-logarithm](#source-source-ae9859af28fdcd), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [Continued-fraction characterization of Stieltjes moment sequences w…](#source-source-c61a0cf3f328ce), [Irrationality proof of certain Lambert series using little q-Jacobi…](#source-source-ca19e504149107), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94), [Some New Applications of the Subspace Theorem](#source-source-corvaja-zannier-2002-subspace), [FormalConjectures.ErdosProblems.1049](#source-source-d7a43109c64c0c), [Log-convex and Stieltjes moment sequences](#source-source-e535117ac620e6), [Arithmetical investigations of a certain infinite product](#source-source-e553241a97e580), [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f), [A further improvement of the quantitative Subspace Theorem](#source-source-evertse-ferretti-2013-author2012), [Remarks on irrationality of q-harmonic series](#source-source-f1c687cb5e9ae4), [A determinantal approach to irrationality](#source-source-f67bf9959aa230), [Rational approximations to a q-analogue of π and some other q-series](#source-source-f9fd9214c9ef11), [Christoffel transform and multiple orthogonal polynomials](#source-source-kozhan-vaktnas-2407-13946v1), [Multivariate Rogers-Szego polynomials and flags in finite vector sp…](#source-source-vinroot-2010-multivariate-rogers-szego), [A determinantal approach to irrationality (arXiv v2)](#source-source-zudilin-determinantal-1507-05697v2)
- **Erdős #243**: [Listing each checked result, with a cheap way to check it](#source-correspondence-001), [Writing for a first-time reader](#source-correspondence-004), [Showing where methods and ideas come from](#source-correspondence-005), [Koizumi pseudo-greedy equivalence and computation pointer](#source-erdos243-kovac-koizumi-pointer), [Rational-tail deterministic pair recurrence and open-boundary reduc…](#source-erdos243-tao-tail-pair-recurrence), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Irrationality exponents of certain fast converging series of ration…](#source-source-0f03e2dab0b8c2), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [FormalConjectures.ErdosProblems.243](#source-source-1713b9ad6350bd), [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641), [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62), [Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partia…](#source-source-2a3af2a360bb15), [A theorem on irrationality of infinite series and applications](#source-source-318b37ba5af2eb), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [On the irrationality of polynomial Cantor series](#source-source-77ddbf43e364f7), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Irrationality of the reciprocal sum of doubly exponential sequences](#source-source-86d1745e2d139b), [Chebotarëv and his density theorem](#source-source-abedb02f9939e5), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [{Digital Library of Mathematical Functions}, {Section} 5.11(iii): R…](#source-source-b95bf142df7fb5), [Irrationality Criteria for Series by Erdős and Straus](#source-source-c6e97d89c9fa5f), [On the rationality of Cantor and Ahmes series](#source-source-cbaba7aeeb0f71), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f), [Erdős #243: working report](#source-source-ee991edd431d57)
- **Erdős #249**: [Listing each checked result, with a cheap way to check it](#source-correspondence-001), [Leading the #249 paper with its exact theorem](#source-correspondence-002), [Writing for a first-time reader](#source-correspondence-004), [Showing where methods and ideas come from](#source-correspondence-005), [Möbius-transform identity for the binary totient constant](#source-erdos249-fan-mobius-transform), [Irrationality of the n=2^m sparse totient subseries](#source-erdos249-rafik-sparse-power-two-subseries), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #249](#source-formal-conjectures-adapter-problem-249), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891), [Erdős–Gál lacunary-series law of the iterated logarithm (two-part s…](#source-proposed-direct-7f278004ad452a), [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c), [Note on normal numbers](#source-proposed-direct-f7f90747134dba), [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da), [On asymptotic distributions of arithmetical functions](#source-source-0e9b7210b29d99), [On the set of partial sums of an infinite series](#source-source-0ecb074e507b86), [Answer to An infinite sum based on the mod-parity of Euler's totien…](#source-source-0f61ad0796acdf), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Simultaneous inequalities among values of the Euler phi-function](#source-source-11b46a0435368f), [A survey of gcd-sum functions](#source-source-22ce74d28ddb49), [Regular sequences and the joint spectral radius](#source-source-296ff41148fff7), [On a curious property of vulgar fractions](#source-source-2aa4970cfda278), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [On the law of the iterated logarithm. I](#source-source-39690ee8e07b0c), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [A dynamical proof of the van der Corput inequality](#source-source-3d300ccd5e4cbb), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [The ring of k -regular sequences](#source-source-5752bb5009e4de), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Integer sequences and periodic points](#source-source-5cac1ad51acb12), [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [Modular functions and transcendence questions](#source-source-6346eeeac5036d), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [How to prove that a sequence is not automatic](#source-source-6b460d123159d9), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [Comment and formula added to OEIS A256936 (revisions 28 and 31)](#source-source-71037224a1dd7c), [(Non)automaticity of number theoretic functions](#source-source-741da55b02c5a9), [On the complexity of algebraic numbers I. Expansions in integer bases](#source-source-7c8ba4ea6eea79), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [The Lambert series factorization theorem](#source-source-8935df46fb4693), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [Comment on Erdős Problem #249](#source-source-99c2f3cb190b95), [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81), [Multiplicative functions and k-automatic sequences](#source-source-a0d109b4492fba), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [Transcendence of generating functions whose coefficients are multip…](#source-source-b791f5b49e0da6), [Smooth numbers: computational number theory and beyond](#source-source-bc5d16b84e62c7), [The Fourier transform of functions of the greatest common divisor](#source-source-c786f202d47318), [(Non)Automaticity of number theoretic functions (arXiv v3)](#source-source-coons-nonautomaticity-0810-3709v3), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [On the binary digits of the Erdős--Borwein constant](#source-source-eca9e699590922), [Uber die asymptotische Verteilung reeller Zahlen mod 1](#source-source-eeff3fa685af8a), [Sparse Polynomial-Weighted Expansions](#source-source-f4ad17717c8fd4), [Cyclotomic completions of polynomial rings](#source-source-habiro-2004-cyclotomic)
- **Erdős #251**: [Listing each checked result, with a cheap way to check it](#source-correspondence-001), [Writing for a first-time reader](#source-correspondence-004), [Showing where methods and ideas come from](#source-correspondence-005), [Schlage-Puchta Theorem 2 literature pointer](#source-erdos251-alfaiz-schlage-puchta-pointer), [Counterexample to Erdős variable-denominator expectation](#source-erdos251-kovac-variable-denominator-counterexample), [Conditional #251 proof under Kuperberg Conjecture 1.3 and Lean form…](#source-erdos251-land-conditional-proof-lean), [Prime-gap summation-by-parts equivalence and conditional route](#source-erdos251-tao-prime-gap-equivalence), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #251](#source-formal-conjectures-adapter-problem-251), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Multiplicative Number Theory I: Classical Theory](#source-source-0aca0e5e4e03c0), [On the Erdős problem #251](#source-source-0ec7ca07508557), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Beweis eines Satzes von Tschebyschef](#source-source-20c650f8cf3744), [Erdős Problems discussion thread #251](#source-source-21738452dcb95c), [On the largest prime factors of n and n+1](#source-source-27575f46a101c1), [Multigeometric sequences and Cantorvals](#source-source-2b0038d2c239f5), [Sur certaines séries à valeur irrationnelle](#source-source-2ee394177d0f38), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [Sums of singular series along arithmetic progressions and with smoo…](#source-source-450aed97015b8f), [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Continued Fractions](#source-source-5ee5f85bd606ee), [Subsum sets: intervals, Cantor sets, and Cantorvals](#source-source-63a234b13e4427), [Small gaps between primes](#source-source-6564b203677735), [On Kakeya Conditions for Achievement Sets](#source-source-6d8837bbc174ce), [Achievement sets -- current results and open problems](#source-source-77333436a9e579), [Achievable Cantorvals almost without reversed Kakeya conditions](#source-source-779915b8355ac1), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Sums of singular series with large sets and the tail of the distrib…](#source-source-811205223e0788), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3), [Variants of the Selberg sieve, and bounded intervals containing man…](#source-source-91aa380a16dba9), [Local gap statistics, telescoping, and normality](#source-source-9a38b2d8b0dada), [Ford circles, continued fractions, and best approximation of the se…](#source-source-9b23918ce33c38), [FormalConjectures.ErdosProblems.251](#source-source-b202a3f125817d), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [More on Kakeya Conditions for Achievement Sets](#source-source-b46f8a083b4271), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001), [Bounded gaps between primes](#source-source-c32d672658410d), [The Poisson Tail Conjecture for primes in short intervals](#source-source-c9b987093aaf4e), [On a new condition implying that an achievement set is a Cantorval…](#source-source-ce27d27dd5ec77), [Long gaps between primes](#source-source-d3995db1508bc9), [The irrationality of some number theoretical series](#source-source-d471eacdba0f87), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [Partitions with prescribed sum of reciprocals: asymptotic bounds](#source-source-dbbc7de069eeee), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f), [A conditional proof of the irrationality of ∑\_{n≥1} p\_n 2^{−n} unde…](#source-source-f42f9e04743a4c), [Generalized bases for the real numbers](#source-source-fb4194cadb150b)
- **Erdős #257**: [Listing each checked result, with a cheap way to check it](#source-correspondence-001), [Writing for a first-time reader](#source-correspondence-004), [Showing where methods and ideas come from](#source-correspondence-005), [Earlier variants, interval-filling negative variant, and fat-Cantor…](#source-erdos257-kovac-context-bundle), [Older Erdős and Borwein attribution for even/odd supports](#source-erdos257-kovac-older-special-case-attribution), [Period-two Lambert theorem applied to even and odd supports](#source-erdos257-tang-tachiya-period-two), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #257](#source-formal-conjectures-adapter-problem-257), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Diophantine Problems for q-Zeta Values](#source-proposed-direct-0ef4f73f93ceed), [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [Divisor-bounded multiplicative functions in short intervals](#source-proposed-direct-6c67db53ef5f8c), [The critical-window profile for d\_k in short intervals](#source-proposed-direct-6f90767d1d01dd), [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da), [On the set of partial sums of an infinite series](#source-source-0ecb074e507b86), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [On a curious property of vulgar fractions](#source-source-2aa4970cfda278), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [Some problems and results on the irrationality of the sum of infini…](#source-source-43a734be32736f), [FormalConjectures.ErdosProblems.257](#source-source-4bb571f8383293), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [The ring of k -regular sequences](#source-source-5752bb5009e4de), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [Modular functions and transcendence questions](#source-source-6346eeeac5036d), [Subsum sets: intervals, Cantor sets, and Cantorvals](#source-source-63a234b13e4427), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Über beliebige Teilsummen absolut konvergenter Reihen](#source-source-691e9cc3c46273), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [(Non)automaticity of number theoretic functions](#source-source-741da55b02c5a9), [Achievement sets -- current results and open problems](#source-source-77333436a9e579), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3), [The Lambert series factorization theorem](#source-source-8935df46fb4693), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [Irrationality of Lambert series associated with a periodic sequence](#source-source-9ce84321e202f1), [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94), [Some New Applications of the Subspace Theorem](#source-source-corvaja-zannier-2002-subspace), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [On the binary digits of the Erdős--Borwein constant](#source-source-eca9e699590922), [The logarithmic endpoint fails under arithmetic sampling](#source-source-endpoint2026-logarithmic-repair), [A further improvement of the quantitative Subspace Theorem](#source-source-evertse-ferretti-2013-author2012), [Sparse Polynomial-Weighted Expansions](#source-source-f4ad17717c8fd4), [Linear independence of certain Lambert series](#source-source-f6ee6890db85d9)
- **Erdős #269**: [Listing each checked result, with a cheap way to check it](#source-correspondence-001), [Writing for a first-time reader](#source-correspondence-004), [Showing where methods and ideas come from](#source-correspondence-005), [Infinite-prime-set irrationality proof and correction chain](#source-erdos269-fan-infinite-p-proof-repair), [Two-prime Hecke–Mahler factorisation and transcendence disclosure](#source-erdos269-fan-two-prime-disclosure), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [The Prime Number Theorem](#source-source-06457731c60720), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [On the irrationality of Cantor and Ahmes series](#source-source-1a7535a5e17a8c), [Comment on Erdős Problem #269](#source-source-21cdeefea4c8ec), [Letter to the Editor](#source-source-22aba734190d65), [Transcendence of Hecke–Mahler Series](#source-source-29bdada58b414a), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Sur le développement en fraction continue d'un nombre choisi au hasard](#source-source-5270112e32002d), [FormalConjectures.ErdosProblems.269](#source-source-573a79feb36d47), [Continued Fractions](#source-source-5ee5f85bd606ee), [On the set of points of convergence of a lacunary trigonometric ser…](#source-source-62ee65065db497), [Strongly complete sets and a conjecture of Erdős](#source-source-71fb76f6e1363b), [On the irrationality of polynomial Cantor series](#source-source-77ddbf43e364f7), [On the number of positive integers ≤ x and free of prime factors \> y](#source-source-78565c625f0ea3), [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](#source-source-7a9657920d576b), [On the complexity of algebraic numbers I. Expansions in integer bases](#source-source-7c8ba4ea6eea79), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Smith normal form in combinatorics](#source-source-91756d895a28a8), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [On the arithmetic properties of complex values of Hecke-Mahler seri…](#source-source-9c2776b87b1155), [On integers generated by a finite number of fixed primes](#source-source-ab6d6d6b890f57), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [Transcendence and continued fraction expansion of values of Hecke--…](#source-source-b9d7160919621f), [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380), [Irrationality Criteria for Series by Erdős and Straus](#source-source-c6e97d89c9fa5f), [A new proof of Nishioka's theorem in Mahler's method](#source-source-e7f2f796dbcdb6), [Mahler's method in several variables and finite automata](#source-source-eaeb7980382323), [Arithmetic properties of certain functions in several variables III](#source-source-fcf73a15ff9c7c)
- **Erdős #68**: [Listing each checked result, with a cheap way to check it](#source-correspondence-001), [Writing for a first-time reader](#source-correspondence-004), [Showing where methods and ideas come from](#source-correspondence-005), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #68](#source-formal-conjectures-adapter-problem-68), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [On the sequence $n!$ mod $p$](#source-source-02fc1f0e6f0418), [Lower bounds for some value sets over finite fields: incidence geom…](#source-source-04603f785c9e7f), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674), [An improved point-line incidence bound over arbitrary fields](#source-source-29cbac966b8b76), [On equal products of consecutive integers](#source-source-3068a3586a5e8b), [Character sums and congruences with n!](#source-source-34b520c561ee3c), [Factorial residues modulo a prime: beyond the square-root bound](#source-source-365c2b5cf46ebe), [On the greatest and least prime factors of n!+1](#source-source-3fb9e4907eec24), [Some problems and results on the irrationality of the sum of infini…](#source-source-43a734be32736f), [On the irrationality of certain 2-adic zeta values](#source-source-5122572a1e7312), [On the largest prime divisor of n!+1](#source-source-57adfd0cdcd8c2), [Prime divisors of shifted factorials](#source-source-5f85fb0bd75b8b), [A geometric proof that e is irrational and a new measure of its irr…](#source-source-6a5bf83735fdef), [Distribution of factorials modulo $p$](#source-source-724fef812699b7), [The product of consecutive integers is never a power](#source-source-7d923cace5602a), [Über die einfachen Zahlensysteme](#source-source-8ac37c92429a46), [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [On the irrationality of certain p-adic zeta values](#source-source-b3b7518e07e159), [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5), [On Equal Products of Consecutive Integers](#source-source-b6d577df139d85), [On the irrationality of factorial series](#source-source-c835bc94aad831), [On the greatest and least prime factors of n!+1 , II](#source-source-d1710db60eae06), [Representations of Real Numbers by Infinite Series](#source-source-e13ecb7c94852a), [On the largest prime factor of n!+2^n−1](#source-source-e66e0693f05f0a), [Rational numbers with odd greedy expansion of fixed length](#source-source-ef6233b59b95cb), [Additive congruences with factorials modulo a prime](#source-source-f1a42898642b5f), [NIST Digital Library of Mathematical Functions, §1.12(ii) Convergents](#source-source-f213b302ada43a), [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](#source-source-fb64da05c3acc7)

<details>
<summary>Browse alphabetically by author or public identity</summary>


- **A mathematician (name withheld pending confirmation)**: [Listing each checked result, with a cheap way to check it](#source-correspondence-001), [Leading the #249 paper with its exact theorem](#source-correspondence-002), [Earlier work on the #1049 Lambert value](#source-correspondence-003), [Writing for a first-time reader](#source-correspondence-004), [Showing where methods and ideas come from](#source-correspondence-005)
- **A. Anandkumar**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **A. Baanen**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **A. Eldar**: [Comment and formula added to OEIS A256936 (revisions 28 and 31)](#source-source-71037224a1dd7c)
- **A. Eremenko**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates), [A Markov-type inequality for arbitrary plane continua](#source-eremenko-2007-markov-type-inequality-plane-continua), [An extremal problem for polynomials](#source-eremenko-lempert-1994-extremal-problem-for-polynomials), [Comb functions](#source-eremenko-yuditskii-2012-comb-functions), [On the length of lemniscates](#source-source-7f1f2a3fd9238c)
- **A. Granville**: [Smooth numbers: computational number theory and beyond](#source-source-bc5d16b84e62c7), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31)
- **A. Gu**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **A. Hildebrand**: [On the number of positive integers ≤ x and free of prime factors \> y](#source-source-78565c625f0ea3)
- **A. J. van der Poorten**: [Integer sequences and periodic points](#source-source-5cac1ad51acb12), [Arithmetic properties of certain functions in several variables III](#source-source-fcf73a15ff9c7c)
- **A. Koutsoukou-Argyraki**: [Irrationality Criteria for Series by Erdős and Straus](#source-source-c6e97d89c9fa5f)
- **A. M. Swope**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **A. Sannai**: [Lean Atlas: An Integrated Proof Environment for Scalable Human--AI…](#source-source-ae32306341559a)
- **A. Ya. Khinchin**: [Continued Fractions](#source-source-5ee5f85bd606ee)
- **A. Yokoi**: [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62)
- **Aaroosh Ramadorai**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Abbas Mehrabian**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Abigail See**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Adam Zsolt Wagner**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Advisory Group on Mathematics and Artificial Intelligence at IAS**: [Responsible Release of AI-Generated Mathematics](#source-agmai-20260929-responsible-release)
- **Alain Togbé**: [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380)
- **Alan D. Sokal**: [Lattice paths and branched continued fractions: An infinite sequenc…](#source-source-490b1875016ea4), [Continued-fraction characterization of Stieltjes moment sequences w…](#source-source-c61a0cf3f328ce)
- **Alessandro Languasco**: [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380)
- **Alex Davies**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Alex Rice**: [Sárközy's theorem for P-intersective polynomials](#source-source-rice-pintersective-1111-6559)
- **Alex Zhindon-Romero**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Alexander Fryntov**: [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec)
- **Alexander Novikov**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Alexander P. Mangerel**: [Divisor-bounded multiplicative functions in short intervals](#source-proposed-direct-6c67db53ef5f8c)
- **Alfaiz**: [Schlage-Puchta Theorem 2 literature pointer](#source-erdos251-alfaiz-schlage-puchta-pointer)
- **Amal Gueroudji**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Amy Xin**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Andrew Scoones**: [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](#source-source-7a9657920d576b)
- **Antonio Lobaccaro**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Artemii Remizov**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Arthur H. Copeland**: [Note on normal numbers](#source-proposed-direct-f7f90747134dba)
- **Aruna Das**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Asgar Jamneshan**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Association for Computing Machinery**: [Association for Computing Machinery](#source-source-ce5fddc99aff3f)
- **B. Adamczewski**: [A problem about Mahler functions](#source-source-0a6b8c93371570), [On the complexity of algebraic numbers I. Expansions in integer bases](#source-source-7c8ba4ea6eea79)
- **B. Gin-ge Chen**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **B. Green**: [Long gaps between primes](#source-source-d3995db1508bc9)
- **B. Miranda**: [Pantograph: A Machine-to-Machine Interaction Interface for Advanced…](#source-source-9a04cbea11fd0b)
- **B. Yanahama**: [Lean Atlas: An Integrated Proof Environment for Scalable Human--AI…](#source-source-ae32306341559a)
- **Banks, William D.**: [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5)
- **Bao-Xuan Zhu**: [Lattice paths and branched continued fractions: An infinite sequenc…](#source-source-490b1875016ea4), [Log-convex and Stieltjes moment sequences](#source-source-e535117ac620e6)
- **Barrodale, I.**: [On Equal Products of Consecutive Integers](#source-source-b6d577df139d85)
- **Bartoszewicz, Artur**: [Multigeometric sequences and Cantorvals](#source-source-2b0038d2c239f5)
- **Ben Antieau**: [Fast math/slow math](#source-ai-essay-antieau-20260915-fast-math-slow-math)
- **Benjamin Burns**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Bhawesh Mishra**: [Polynomials consisting of quadratic factors with roots modulo any p…](#source-source-mishra-quadratic-2102-08379)
- **Bin Dong**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Boris Adamczewski**: [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c), [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082), [A new proof of Nishioka's theorem in Mahler's method](#source-source-e7f2f796dbcdb6), [Mahler's method in several variables and finite automata](#source-source-eaeb7980382323)
- **Borislav Kozlovskii**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Boshi Wang**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Botao Yu**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Brian Etz**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Bryan Dai**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Bryna Kra**: [Deep theorems were scarce and difficult and so became an effective…](#source-ai-essay-kra-20260913-deep-theorems)
- **C. Badea**: [A theorem on irrationality of infinite series and applications](#source-source-318b37ba5af2eb)
- **C. Barrett**: [Pantograph: A Machine-to-Machine Interaction Interface for Advanced…](#source-source-9a04cbea11fd0b)
- **C. E. Brown**: [Agent Hunt: Bounty Based Collaborative Autoformalization With LLM A…](#source-source-ae5cc4ddfa6af5)
- **C. J. Bishop**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates)
- **C. Kaliszyk**: [Agent Hunt: Bounty Based Collaborative Autoformalization With LLM A…](#source-source-ae5cc4ddfa6af5)
- **C. Krattenthaler**: [On the non-quadraticity of values of the q-exponential function and…](#source-source-22ef36d016ca81)
- **C. L. Stewart**: [On the greatest and least prime factors of n!+1 , II](#source-source-d1710db60eae06)
- **C. Lupu**: [On the irrationality of certain p-adic zeta values](#source-source-b3b7518e07e159)
- **C. Pomerance**: [On the largest prime factors of n and n+1](#source-source-27575f46a101c1), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31)
- **C. Ryan Vinroot**: [Multivariate Rogers-Szego polynomials and flags in finite vector sp…](#source-source-vinroot-2010-multivariate-rogers-szego)
- **C. Smet**: [Irrationality proof of certain Lambert series using little q-Jacobi…](#source-source-ca19e504149107)
- **C. Sun**: [Pantograph: A Machine-to-Machine Interaction Interface for Advanced…](#source-source-9a04cbea11fd0b)
- **C. Viola**: [On a permutation group related to ζ(2)](#source-source-176d35cb60b651)
- **Cameron L. Stewart**: [On the greatest and least prime factors of n!+1](#source-source-3fb9e4907eec24)
- **Carl Schildkraut**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Carlo Pagano**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **ChatGPT 5.4 Pro (orchestrated by V. Kovač)**: [On the Erdős problem #251](#source-source-0ec7ca07508557)
- **Chen Wei**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Cheng-Chiang Tsai**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Chenkai Kuang**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Chenyi Li**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **Christian Berg**: [On powers of Stieltjes moment sequences, II](#source-source-2a10c7287879c3)
- **Christian Krattenthaler**: [A determinant identity for moments of orthogonal polynomials that i…](#source-source-3479bad7869d7c)
- **Christoph Koutschan**: [Common Factors in Fraction-Free Matrix Decompositions](#source-source-39e4fc546549fd)
- **Christoph Thiele**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Chuqin Geng**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Clemens Müllner**: [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082)
- **Colin Faverjon**: [A new proof of Nishioka's theorem in Mahler's method](#source-source-e7f2f796dbcdb6), [Mahler's method in several variables and finite automata](#source-source-eaeb7980382323)
- **D. Duverney**: [À propos de la série ∑\_{n≥1} x^n/(q^n−1)](#source-source-169c3d67838965), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe)
- **D. Khavinson**: [Two-dimensional shapes and lemniscates](#source-source-9e37cc2fe7db3e)
- **D. Kozen**: [Computing the Newtonian Graph](#source-source-92b0dfb67f5009)
- **D. P. Anderson**: [BOINC: A Platform for Volunteer Computing](#source-source-967c9acd787096)
- **D. Schmersau**: [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0)
- **D. Smertnig**: [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63)
- **D. Testa**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **D. Zeilberger**: [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b)
- **Daniel Adu-Ampratwum**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Daniel Duverney**: [Irrationality exponents of certain fast converging series of ration…](#source-source-0f03e2dab0b8c2), [Arithmetical functions and irrationality of Lambert series](#source-source-6cfe654e650970)
- **Daniel Jarka**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Daniel Litt**: [A beginning for mathematics](#source-ai-essay-litt-20260913-a-beginning-for-mathematics)
- **Daniel Rosendo**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **David J. Jeffrey**: [Common Factors in Fraction-Free Matrix Decompositions](#source-source-39e4fc546549fd)
- **David Tischler**: [Critical points and values of complex polynomials](#source-source-7ac8693558c1a2)
- **Dawsen Hwang**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Demis Hassabis**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Dimitris Koukoulopoulos**: [A CERN for AI-assisted science?](#source-ai-essay-koukoulopoulos-20260917-cern-for-ai-science)
- **Dongruo An**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **E. Crane**: [The area of polynomial images and preimages](#source-source-40bc4064b92788)
- **E. G. Straus**: [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f)
- **Earl T. Barr**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Edward Crane**: [A bound for Smale's mean value conjecture for complex polynomials](#source-source-818467bc1cb170)
- **Edward van de Meent**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Emad Shihab**: [Synergizing LLMs and Knowledge Graphs: A Novel Approach to Software…](#source-arxiv-2412-03815)
- **Emilien Dupont**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Erdős, Paul**: [The product of consecutive integers is never a power](#source-source-7d923cace5602a)
- **Eric Leonen**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Erick Wong**: [Answer to An infinite sum based on the mod-parity of Euler's totien…](#source-source-0f61ad0796acdf)
- **Evan Wang**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Evan Zheran Liu**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Evgenia Karunus**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **F. Herzog**: [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff)
- **F. Luca**: [Character sums and congruences with n!](#source-source-34b520c561ee3c), [Prime divisors of shifted factorials](#source-source-5f85fb0bd75b8b), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44)
- **F. W. J. Olver et al. (eds.)**: [NIST Digital Library of Mathematical Functions, Eq. 17.2.37](#source-source-5857f9959e7529)
- **Fanjin Zhang**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Federico Pasqualotto**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Federico Pellarin**: [On the arithmetic properties of complex values of Hecke-Mahler seri…](#source-source-9c2776b87b1155)
- **Fedor Nazarov**: [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec)
- **Fellows of the Royal Society**: [Open Letter to Sir Paul Nurse, President of the Royal Society](#source-open-letter-royal-society-fellows-20260917)
- **Fields Medallists**: [A severe misalignment of AI in mathematics](#source-ai-essay-fields-medallists-20260911-severe-misalignment)
- **Filipczak, Ma{\\l}gorzata**: [Multigeometric sequences and Cantorvals](#source-source-2b0038d2c239f5)
- **Florian Luca**: [Transcendence of Hecke–Mahler Series](#source-source-29bdada58b414a), [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](#source-source-7a9657920d576b), [Irrationality of Lambert series associated with a periodic sequence](#source-source-9ce84321e202f1), [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380), [On the largest prime factor of n!+2^n−1](#source-source-e66e0693f05f0a), [Linear independence of certain Lambert series](#source-source-f6ee6890db85d9), [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](#source-source-fb64da05c3acc7)
- **Floris van Doorn**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Francisco J. R. Ruiz**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Frazier N. Baker**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **G. Cantor**: [Über die einfachen Zahlensysteme](#source-source-8ac37c92429a46)
- **G. Everest**: [Integer sequences and periodic points](#source-source-5cac1ad51acb12)
- **G. Piranian**: [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff)
- **G. Pólya**: [Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zu…](#source-source-2ec6bf87654604)
- **G. Rhin**: [On a permutation group related to ζ(2)](#source-source-176d35cb60b651)
- **Garrett Bingham**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Gene H. Golub**: [Calculation of Gauss Quadrature Rules](#source-source-53a2a9c4a9e7c2)
- **George Holland**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Giovanni Inchiostro**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **GitHub**: [Preventing pwn requests](#source-source-9ef9271dbecbce)
- **Glyn Harman**: [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001)
- **Golnaz Ghiasi**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Google DeepMind**: [formal-conjectures](#source-source-5edeb2408c36bd)
- **Grant Sanderson**: [If math is more than proof, we need to better celebrate the rest of it](#source-ai-essay-sanderson-20260918-more-than-proof)
- **Great Internet Mersenne Prime Search**: [GIMPS](#source-source-cc1c19967d418f)
- **Grebennikov, Alexandr**: [On the sequence $n!$ mod $p$](#source-source-02fc1f0e6f0418)
- **Greg Martin**: [Simultaneous inequalities among values of the Euler phi-function](#source-source-11b46a0435368f)
- **Guoxiong Gao**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **G{\\l}\\k{a}b, Szymon**: [Achievement sets -- current results and open problems](#source-source-77333436a9e579)
- **H. G. Meijer**: [On integers generated by a finite number of fixed primes](#source-source-ab6d6d6b890f57)
- **H. Kreidler**: [A dynamical proof of the van der Corput inequality](#source-source-3d300ccd5e4cbb)
- **H. L. Montgomery**: [The Prime Number Theorem](#source-source-06457731c60720), [Multiplicative Number Theory I: Classical Theory](#source-source-0aca0e5e4e03c0)
- **H. S. Shapiro**: [Two-dimensional shapes and lemniscates](#source-source-9e37cc2fe7db3e)
- **H. W. Lenstra, Jr.**: [Chebotarëv and his density theorem](#source-source-abedb02f9939e5)
- **Hajime Kaneko**: [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9)
- **Han Wang**: [Sparse Polynomial-Weighted Expansions](#source-source-f4ad17717c8fd4)
- **Hangrui Bi**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Hans Hornich**: [Über beliebige Teilsummen absolut konvergenter Reihen](#source-source-691e9cc3c46273)
- **Hanzhao Lin**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Hao-An Wu**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Heng-Tze Cheng**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Henry Cohn**: [The technical debt of AI-generated mathematics](#source-ai-essay-cohn-20260915-technical-debt)
- **Henry Yuen**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Hu, Xiyu**: [Lower bounds for some value sets over finite fields: incidence geom…](#source-source-04603f785c9e7f)
- **Huan Sun**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Huyile Liang**: [Stieltjes moment sequences of polynomials](#source-source-0f46dee5024c66)
- **Hyunwoo Choi**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **I. E. Shparlinski**: [Character sums and congruences with n!](#source-source-34b520c561ee3c), [Prime divisors of shifted factorials](#source-source-5f85fb0bd75b8b)
- **I. J. Schoenberg**: [On asymptotic distributions of arithmetical functions](#source-source-0e9b7210b29d99)
- **I. O. Bado**: [Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partia…](#source-source-2a3af2a360bb15)
- **I. Rivin**: [Zero Coefficients of Rational Power Series and Rational Lambert Series](#source-source-aa2d5c249362f1)
- **I. Rochev**: [On the non-quadraticity of values of the q-exponential function and…](#source-source-22ef36d016ca81)
- **I. S. Gal**: [On the law of the iterated logarithm. I](#source-source-39690ee8e07b0c)
- **I. Schoenberg**: [Uber die asymptotische Verteilung reeller Zahlen mod 1](#source-source-eeff3fa685af8a)
- **I. Short**: [Ford circles, continued fractions, and best approximation of the se…](#source-source-9b23918ce33c38)
- **Iekata Shiokawa**: [Irrationality exponents of certain fast converging series of ration…](#source-source-0f03e2dab0b8c2)
- **Igor E. Shparlinski**: [On the largest prime factor of n!+2^n−1](#source-source-e66e0693f05f0a), [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](#source-source-fb64da05c3acc7)
- **Imaan Sidhu**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Issai Schur**: [Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichun…](#source-source-b4b0f2811b1d2d)
- **István S. Gál**: [Erdős–Gál lacunary-series law of the iterated logarithm (two-part s…](#source-proposed-direct-7f278004ad452a)
- **Ivo Petrov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **J. A. Fridy**: [Generalized bases for the real numbers](#source-source-fb4194cadb150b)
- **J. Asher**: [LeanExplore: A Search Engine for Lean 4 Declarations](#source-source-608828559136f9)
- **J. Avigad**: [LeanArchitect: Automating Blueprint Generation for Humans and AI](#source-source-80c9ae60b7f7be)
- **J. Bell**: [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63)
- **J. Commelin**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **J. Coussement**: [Irrationality proof of certain Lambert series using little q-Jacobi…](#source-source-ca19e504149107)
- **J. Farey**: [On a curious property of vulgar fractions](#source-source-2aa4970cfda278)
- **J. Galambos**: [Representations of Real Numbers by Infinite Series](#source-source-e13ecb7c94852a)
- **J. H. Loxton**: [Arithmetic properties of certain functions in several variables III](#source-source-fcf73a15ff9c7c)
- **J. Hančl**: [On the irrationality of Cantor and Ahmes series](#source-source-1a7535a5e17a8c), [On the irrationality of factorial series](#source-source-c835bc94aad831)
- **J. Kang**: [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674)
- **J. Koizumi**: [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62), [Irrationality of the reciprocal sum of doubly exponential sequences](#source-source-86d1745e2d139b)
- **J. Land**: [A conditional proof of the irrationality of ∑\_{n≥1} p\_n 2^{−n} unde…](#source-source-f42f9e04743a4c)
- **J. Louwsma**: [Rational numbers with odd greedy expansion of fixed length](#source-source-ef6233b59b95cb)
- **J. M. Campbell**: [On the binary digits of the Erdős--Borwein constant](#source-source-eca9e699590922)
- **J. Martino**: [Rational numbers with odd greedy expansion of fixed length](#source-source-ef6233b59b95cb)
- **J. Maynard**: [Small gaps between primes](#source-source-6564b203677735), [Long gaps between primes](#source-source-d3995db1508bc9)
- **J. P. Bell**: [A problem about Mahler functions](#source-source-0a6b8c93371570)
- **J. Shallit**: [The ring of k -regular sequences](#source-source-5752bb5009e4de)
- **J. Sprang**: [On the irrationality of certain p-adic zeta values](#source-source-b3b7518e07e159)
- **J. Teräväinen**: [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2)
- **J. Urban**: [Agent Hunt: Bounty Based Collaborative Autoformalization With LLM A…](#source-source-ae5cc4ddfa6af5)
- **J. Vandehey**: [On an incomplete argument of Erdős on the irrationality of Lambert…](#source-source-5911448b65fdf9)
- **J.-C. Schlage-Puchta**: [The irrationality of some number theoretical series](#source-source-d471eacdba0f87)
- **J.-P. Allouche**: [The ring of k -regular sequences](#source-source-5752bb5009e4de)
- **Jaehyeon Seo**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **James Sundstrom**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **James Walrad**: [Continued-fraction characterization of Stieltjes moment sequences w…](#source-source-c61a0cf3f328ce)
- **James Worrell**: [Transcendence of Hecke–Mahler Series](#source-source-29bdada58b414a), [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](#source-source-7a9657920d576b)
- **Jan-Hendrik Evertse**: [A further improvement of the quantitative Subspace Theorem](#source-source-evertse-ferretti-2013-author2012)
- **Jarod Alper**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Jaroslav Hančl**: [On the irrationality of polynomial Cantor series](#source-source-77ddbf43e364f7)
- **Jason P. Bell**: [Transcendence of generating functions whose coefficients are multip…](#source-source-b791f5b49e0da6)
- **Jasper Dekoninck**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Jasper Mulder-Sohn**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Jean-Paul Allouche**: [How to prove that a sequence is not automatic](#source-source-6b460d123159d9)
- **Jeffrey Remmel**: [Stieltjes moment sequences of polynomials](#source-source-0f46dee5024c66)
- **Jeffrey Shallit**: [How to prove that a sequence is not automatic](#source-source-6b460d123159d9)
- **Jeremiah Alonzo**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Jeremy Tan**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Jha, Abhishek**: [The Poisson Tail Conjecture for primes in short intervals](#source-source-c9b987093aaf4e)
- **Jialiang Sun**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Jian Song**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Jiang Hu**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **Jiedong Jiang**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Jiening Siow**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Jim Portegies**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Jingda Xu**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Jiwon Kang**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **Joel Land**: [Erdős Problems discussion thread #251](#source-source-21738452dcb95c)
- **Johan Land**: [Conditional #251 proof under Kuperberg Conjecture 1.3 and Lean form…](#source-erdos251-land-conditional-proof-lean)
- **Johannes Middeke**: [Common Factors in Fraction-Free Matrix Decompositions](#source-source-39e4fc546549fd)
- **John H. Welsch**: [Calculation of Gauss Quadrature Rules](#source-source-53a2a9c4a9e7c2)
- **Jonas Henkel**: [The Mathematician's Assistant: Integrating AI into Research Practice](#source-source-0d338bb41b8987)
- **Jonathan N. Lee**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Jonathan Sondow**: [A geometric proof that e is irrational and a new measure of its irr…](#source-source-6a5bf83735fdef)
- **Joni Teräväinen**: [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404)
- **Joonkyung Lee**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Joris Roos**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Joël Ouaknine**: [Transcendence of Hecke–Mahler Series](#source-source-29bdada58b414a), [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](#source-source-7a9657920d576b)
- **Juanzi Li**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Julio C. Pardo**: [Additive congruences with factorials modulo a prime](#source-source-f1a42898642b5f)
- **Junehyuk Jung**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Junjie Wang**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Junsu Kim**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **János Pintz**: [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001)
- **K. Barreto**: [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674)
- **K. Ford**: [Long gaps between primes](#source-source-d3995db1508bc9)
- **K. Lazebnik**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates)
- **K. Postelmans**: [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f)
- **K. Ramachandran**: [Number of Components of Polynomial Lemniscates: A Problem of Erdős,…](#source-source-97b4e6a82335a7)
- **K. Stefánsson**: [Computing the Newtonian Graph](#source-source-92b0dfb67f5009)
- **K. Väänänen**: [On the non-quadraticity of values of the q-exponential function and…](#source-source-22ef36d016ca81), [Arithmetical investigations of a certain infinite product](#source-source-e553241a97e580), [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f)
- **K. Yang**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **Kaisa Matomäki**: [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404)
- **Kaiying Hou**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Kaloyan Tsvetkov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Kazuo Habiro**: [Cyclotomic completions of polynomial rings](#source-source-habiro-2004-cyclotomic)
- **Kevin Barreto**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **Klurman, Oleksiy**: [Distribution of factorials modulo $p$](#source-source-724fef812699b7)
- **Koray Kavukcuoglu**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Kristian Minchev**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Kunal Marwaha**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Kuperberg, Vivian**: [Sums of singular series along arithmetic progressions and with smoo…](#source-source-450aed97015b8f)
- **L. Aniva**: [Pantograph: A Machine-to-Machine Interaction Interface for Advanced…](#source-source-9a04cbea11fd0b)
- **L. Lai**: [On the irrationality of certain 2-adic zeta values](#source-source-5122572a1e7312), [On the largest prime divisor of n!+1](#source-source-57adfd0cdcd8c2), [On the irrationality of certain p-adic zeta values](#source-source-b3b7518e07e159)
- **L. Lempert**: [An extremal problem for polynomials](#source-eremenko-lempert-1994-extremal-problem-for-polynomials)
- **L. Toth**: [A survey of gcd-sum functions](#source-source-22ce74d28ddb49)
- **Lars Becker**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Lean FRO**: [Comparator](#source-software-comparator-statement-checker)
- **Lean Project.**: [Lean Language Reference](#source-source-bae14c21d3e920)
- **Lean community**: [Contributing to mathlib](#source-source-c29036ef9c4da8)
- **Lean contributors**: [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1)
- **Lei Hou**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Leo Diedering**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Leonardo Lobaccaro**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Leonardo de Moura**: [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3)
- **Luca Matone**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Luca, Florian**: [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5)
- **Luke Alexander**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Luke Zerrer**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Lyuba Konova**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **M. Coons**: [Regular sequences and the joint spectral radius](#source-source-296ff41148fff7), [(Non)automaticity of number theoretic functions](#source-source-741da55b02c5a9)
- **M. D. Schmidt**: [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c)
- **M. Kripner**: [OpenProver: Agentic and Interactive Theorem Proving with Lean 4](#source-source-d31e3bc51f2784)
- **M. Laurent**: [Transcendence and continued fraction expansion of values of Hecke--…](#source-source-b9d7160919621f)
- **M. Merca**: [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [The Lambert series factorization theorem](#source-source-8935df46fb4693)
- **M. Pawan Kumar**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **M. R. Ballard**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **M. Rothgang**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **M. Stern**: [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81)
- **M. Straka**: [OpenProver: Agentic and Interactive Theorem Proving with Lean 4](#source-source-d31e3bc51f2784)
- **M. Z. Garaev**: [Character sums and congruences with n!](#source-source-34b520c561ee3c)
- **Macleod, R. A.**: [On Equal Products of Consecutive Integers](#source-source-b6d577df139d85)
- **Maksym Radziwiłł**: [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404)
- **Marchwicki, Jacek**: [On Kakeya Conditions for Achievement Sets](#source-source-6d8837bbc174ce)
- **Marcus Vaktnäs**: [Christoffel transform and multiple orthogonal polynomials](#source-source-kozhan-vaktnas-2407-13946v1)
- **Maria Drencheva**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Mark Harman**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Martin Höst**: [Guidelines for Conducting and Reporting Case Study Research in Soft…](#source-source-25efc27ed2130d)
- **Martin Vechev**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Marvin Eisenberger**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **María Inés de Frutos-Fernández**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Matej Balog**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Mathias Pétréolle**: [Lattice paths and branched continued fractions: An infinite sequenc…](#source-source-490b1875016ea4)
- **Melinda Yuan**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Michael Coons**: [Transcendence of generating functions whose coefficients are multip…](#source-source-b791f5b49e0da6), [(Non)Automaticity of number theoretic functions (arXiv v3)](#source-source-coons-nonautomaticity-0810-3709v3)
- **Michael Drmota**: [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082)
- **Michael Rothgang**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Milen Shumanov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Mingyi Xue**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Miroslav Marinov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Miska, Piotr**: [On Kakeya Conditions for Achievement Sets](#source-source-6d8837bbc174ce), [More on Kakeya Conditions for Achievement Sets](#source-source-b46f8a083b4271)
- **Mislav Balunovic**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Moubariz Z. Garaev**: [Additive congruences with factorials modulo a prime](#source-source-f1a42898642b5f), [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](#source-source-fb64da05c3acc7)
- **Munsch, Marc**: [Distribution of factorials modulo $p$](#source-source-724fef812699b7)
- **Muzammil Shahbaz**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **N. Edeko**: [A dynamical proof of the van der Corput inequality](#source-source-3d300ccd5e4cbb)
- **N. Peng**: [The Network Structure of Mathlib](#source-source-81b67bfd835ac9)
- **NISO**: [CRediT: Contributor Roles Taxonomy](#source-source-d517c8a2d6f84d)
- **National Academies of Sciences, Engineering, and Medicine**: [Reproducibility and Replicability in Science](#source-source-011f43e5a781d7)
- **National Aeronautics and Space Administration**: [Software Assurance and Software Safety Standard](#source-source-278e74bfddddf0)
- **National Information Standards Organization.**: [Reproducibility Badging and Definitions](#source-source-f2a047037bae55)
- **National Institute of Standards**: [National Institute of Standards and Technology](#source-source-e6716218a1ac07)
- **National Institute of Standards and Technology**: [Secure Hash Standard](#source-source-f6e839bcb8a60f)
- **Nguyen Xuan Tho**: [On equal products of consecutive integers](#source-source-3068a3586a5e8b)
- **Ngân Vũ**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Nigamaa Nayakanti**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Nils Bruin**: [Transcendence of generating functions whose coefficients are multip…](#source-source-b791f5b49e0da6)
- **Nowakowski, Piotr**: [On a new condition implying that an achievement set is a Cantorval…](#source-source-ce27d27dd5ec77)
- **Object Management Group.**: [Structured Assurance Case Metamodel (SACM)](#source-source-463b7e9f7264b1)
- **Olga S. Kuznetsova**: [Length functions of lemniscates](#source-source-57fe330e419648)
- **P. B. Borwein**: [On the irrationality of ∑ 1/(q^n+r)](#source-source-62f9190aeb7d34), [On the irrationality of certain series](#source-source-96aef073e2ea33)
- **P. Borwein**: [The arc length of the lemniscate |p(z)|=1](#source-source-89b9a294db76bb)
- **P. Bundschuh**: [Arithmetical investigations of a certain infinite product](#source-source-e553241a97e580), [Rational approximations to a q-analogue of π and some other q-series](#source-source-f9fd9214c9ef11)
- **P. Ebenfelt**: [Two-dimensional shapes and lemniscates](#source-source-9e37cc2fe7db3e)
- **P. Erdos**: [On the law of the iterated logarithm. I](#source-source-39690ee8e07b0c)
- **P. Erdős**: [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Beweis eines Satzes von Tschebyschef](#source-source-20c650f8cf3744), [Letter to the Editor](#source-source-22aba734190d65), [On the largest prime factors of n and n+1](#source-source-27575f46a101c1), [Sur certaines séries à valeur irrationnelle](#source-source-2ee394177d0f38), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff), [On the set of points of convergence of a lacunary trigonometric ser…](#source-source-62ee65065db497), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f)
- **P. Lévy**: [Sur le développement en fraction continue d'un nombre choisi au hasard](#source-source-5270112e32002d)
- **P. Massot**: [leanblueprint](#source-source-944a1a754b1f3a)
- **P. Monticone**: [LeanArchitect: Automating Blueprint Generation for Humans and AI](#source-source-80c9ae60b7f7be)
- **P. Shafto**: [The Network Structure of Mathlib](#source-source-81b67bfd835ac9)
- **P. Song**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **P. Stevenhagen**: [Chebotarëv and his density theorem](#source-source-abedb02f9939e5)
- **P. White with Claude (Anthropic)**: [Erdős #243: working report](#source-source-ee991edd431d57)
- **P. Yuan**: [On the rationality of Cantor and Ahmes series](#source-source-cbaba7aeeb0f71)
- **P. Yuditskii**: [Comb functions](#source-eremenko-yuditskii-2012-comb-functions)
- **Palomar Registry**: [About Palomar](#source-source-9733ab875d6048)
- **Paul Erdős**: [Erdős–Gál lacunary-series law of the iterated logarithm (two-part s…](#source-proposed-direct-7f278004ad452a), [Note on normal numbers](#source-proposed-direct-f7f90747134dba), [On the greatest and least prime factors of n!+1](#source-source-3fb9e4907eec24), [Some problems and results on the irrationality of the sum of infini…](#source-source-43a734be32736f)
- **Pavol Kebis**: [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](#source-source-7a9657920d576b)
- **Peihao Wu**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Per Runeson**: [Guidelines for Conducting and Reporting Case Study Research in Soft…](#source-source-25efc27ed2130d)
- **Phil McMinn**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Pieter Moree**: [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380)
- **Pietro Corvaja**: [Some New Applications of the Subspace Theorem](#source-source-corvaja-zannier-2002-subspace)
- **Pietro Monticone**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Plectis working note**: [The logarithmic endpoint fails under arithmetic sampling](#source-source-endpoint2026-logarithmic-repair)
- **Po-Sen Huang**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Polymath Project**: [General polymath rules](#source-source-af9e99293e9dd0)
- **Prasanna Balaprakash**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Priyamvad Srivastav**: [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891)
- **Prus-Wi\\'sniowski, Franciszek**: [Achievement sets -- current results and open problems](#source-source-77333436a9e579), [Achievable Cantorvals almost without reversed Kakeya conditions](#source-source-779915b8355ac1), [More on Kakeya Conditions for Achievement Sets](#source-source-b46f8a083b4271)
- **Ptak, Jolanta**: [Achievable Cantorvals almost without reversed Kakeya conditions](#source-source-779915b8355ac1), [More on Kakeya Conditions for Achievement Sets](#source-source-b46f8a083b4271)
- **Pushmeet Kohli**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Q. Tang**: [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641)
- **Qianheng Zhang**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Quanyu Tang**: [Period-two Lambert theorem applied to even and odd supports](#source-erdos257-tang-tachiya-period-two)
- **Quoc V. Le**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **R. Balasubramanian**: [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891)
- **R. C. Baker**: [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001)
- **R. C. Vaughan**: [The Prime Number Theorem](#source-source-06457731c60720), [Multiplicative Number Theory I: Classical Theory](#source-source-0aca0e5e4e03c0)
- **R. Chalamala**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **R. Crandall**: [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da)
- **R. L. Graham**: [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88)
- **R. Nagel**: [A dynamical proof of the van der Corput inequality](#source-source-3d300ccd5e4cbb)
- **R. P. Stanley**: [Smith normal form in combinatorics](#source-source-91756d895a28a8)
- **R. Prenger**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **R. Tijdeman**: [On the irrationality of Cantor and Ahmes series](#source-source-1a7535a5e17a8c), [On the irrationality of factorial series](#source-source-c835bc94aad831), [On the rationality of Cantor and Ahmes series](#source-source-cbaba7aeeb0f71)
- **Rafael Ferreira da Silva**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Rajula Srivastava**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Raymond Provost**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Reem Yassawi**: [How to prove that a sequence is not automatic](#source-source-6b460d123159d9)
- **Renan Souza**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Robert Rosenthal**: [The File Drawer Problem and Tolerance for Null Results](#source-source-7aa96129ebb643)
- **Robert Tijdeman**: [On the irrationality of polynomial Cantor series](#source-source-77ddbf43e364f7), [On integers generated by a finite number of fixed primes](#source-source-ab6d6d6b890f57)
- **Roberto Ferretti**: [A further improvement of the quantitative Subspace Theorem](#source-source-evertse-ferretti-2013-author2012)
- **RomanLeLan**: [Retrieval of Chowla 1947 original scan](#source-erdos1049-bloom-chowla-scan-retrieval)
- **Rostyslav Kozhan**: [Christoffel transform and multiple orthogonal polynomials](#source-source-kozhan-vaktnas-2407-13946v1)
- **Ruey-An Shiu**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **S. Fan**: [Comment on Erdős Problem #269](#source-source-21cdeefea4c8ec), [Comment on Erdős Problem #249](#source-source-99c2f3cb190b95)
- **S. Ghosh**: [Number of Components of Polynomial Lemniscates: A Problem of Erdős,…](#source-source-97b4e6a82335a7)
- **S. Godil**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **S. J. Taylor**: [On the set of points of convergence of a lacunary trigonometric ser…](#source-source-62ee65065db497)
- **S. Kakeya**: [On the set of partial sums of an infinite series](#source-source-0ecb074e507b86)
- **S. Konyagin**: [Long gaps between primes](#source-source-d3995db1508bc9)
- **S. Koyejo**: [Pantograph: A Machine-to-Machine Interaction Interface for Advanced…](#source-source-9a04cbea11fd0b)
- **S. Ringer**: [Local gap statistics, telescoping, and normality](#source-source-9a38b2d8b0dada)
- **S. Severini**: [The Network Structure of Mathlib](#source-source-81b67bfd835ac9)
- **S. Sutherland**: [Bad Polynomials for Newton's Method](#source-source-318ee5e7cf6d74)
- **S. Welleck**: [LeanArchitect: Automating Blueprint Generation for Humans and AI](#source-source-80c9ae60b7f7be)
- **S. Yu**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **S. Zhang**: [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674)
- **S.-h. Kim**: [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674)
- **SCSC Assurance Case Working Group**: [Goal Structuring Notation Community Standard, Version 3](#source-source-6dbbb774ff928e)
- **SCSC Assurance Case Working Group (ACWG).**: [Goal Structuring Notation Community Standard, Version 3](#source-source-bd5fabd398bdfa)
- **Sagdeev, Arsenii**: [On the sequence $n!$ mod $p$](#source-source-02fc1f0e6f0418)
- **Sainan Zheng**: [Stieltjes moment sequences of polynomials](#source-source-0f46dee5024c66)
- **Samuel Abedu**: [Synergizing LLMs and Knowledge Graphs: A Novel Approach to Software…](#source-arxiv-2412-03815)
- **Sang-hyun Kim**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **SayedHassan Khatoonabadi**: [Synergizing LLMs and Knowledge Graphs: A Novel Approach to Software…](#source-arxiv-2412-03815)
- **Sebastian Nowozin**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Sebastian Ullrich**: [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3)
- **Selfridge, John L.**: [The product of consecutive integers is never a power](#source-source-7d923cace5602a)
- **Semchankau, Aliaksei**: [On the sequence $n!$ mod $p$](#source-source-02fc1f0e6f0418)
- **Sergei Gukov**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Sergey Shirobokov**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Shengtong Zhang**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **Shijie Chen**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Shin Yoo**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Shparlinski, Igor E.**: [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5)
- **Shuze Chen**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Simon Kurgan**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Song Gao**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Sophie Szeto**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Soroosh Yazdani**: [Multiplicative functions and k-automatic sequences](#source-source-a0d109b4492fba)
- **Steve Fan**: [Möbius-transform identity for the binary totient constant](#source-erdos249-fan-mobius-transform), [Infinite-prime-set irrationality proof and correction chain](#source-erdos269-fan-infinite-p-proof-repair), [Two-prime Hecke–Mahler factorisation and transcendence disclosure](#source-erdos269-fan-two-prime-disclosure), [Strongly complete sets and a conjecture of Erdős](#source-source-71fb76f6e1363b)
- **Stevens, Sophie**: [An improved point-line incidence bound over arbitrary fields](#source-source-29cbac966b8b76)
- **Stichtenoth, Henning**: [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5)
- **Sumit Giri**: [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891)
- **Sunny Hu**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Swarat Chaudhuri**: [AlphaEvolve: A coding agent for scientific and algorithmic discovery](#source-source-cf94fac28d0ff1)
- **Szabolcs Marka**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Szymonik, Emilia**: [Multigeometric sequences and Cantorvals](#source-source-2b0038d2c239f5)
- **Sébastien Gouëzel**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **T. Amdeberhan**: [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b)
- **T. M. Apostol**: [Introduction to Analytic Number Theory](#source-source-99385343e032a3)
- **T. Matala-aho**: [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f)
- **T. Tao**: [The maximal length of the Erdős–Herzog–Piranian lemniscate in high…](#source-source-0e12f93aeac487), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Mathematics in the age of AI](#source-source-75e79d15dfab15), [Long gaps between primes](#source-source-d3995db1508bc9)
- **T. Ward**: [Integer sequences and periodic points](#source-source-5cac1ad51acb12)
- **T. Zhu**: [LeanArchitect: Automating Blueprint Generation for Humans and AI](#source-source-80c9ae60b7f7be)
- **Takeshi Kurosawa**: [Irrationality exponents of certain fast converging series of ration…](#source-source-0f03e2dab0b8c2)
- **Talia Ringer**: [Becoming a benchmark](#source-ai-essay-ringer-20260917-becoming-a-benchmark)
- **Tasmin Chu**: [The AI dissenter viewpoint](#source-ai-essay-chu-20260809-ai-dissenter-viewpoint)
- **Technology**: [National Institute of Standards and Technology](#source-source-e6716218a1ac07)
- **Terence Tao**: [Mining open problems](#source-ai-essay-tao-20260908-mining-open-problems), [Rational-tail deterministic pair recurrence and open-boundary reduc…](#source-erdos243-tao-tail-pair-recurrence), [Prime-gap summation-by-parts equivalence and conditional route](#source-erdos251-tao-prime-gap-equivalence), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [Erdős Problems discussion thread #251](#source-source-21738452dcb95c), [AI contributions to Erdős problems](#source-source-e99ce64694b554)
- **Thai Hoang Lê**: [Intersective polynomials and the primes](#source-source-le-intersective-0910-1880)
- **Thang Luong**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **The Formal Conjectures Authors**: [Formal Conjectures compatibility surface for Erdős #1049](#source-formal-conjectures-adapter-problem-1049), [Formal Conjectures compatibility surface for Erdős #249](#source-formal-conjectures-adapter-problem-249), [Formal Conjectures compatibility surface for Erdős #251](#source-formal-conjectures-adapter-problem-251), [Formal Conjectures compatibility surface for Erdős #257](#source-formal-conjectures-adapter-problem-257), [Formal Conjectures compatibility surface for Erdős #68](#source-formal-conjectures-adapter-problem-68), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [FormalConjectures.ErdosProblems.243](#source-source-1713b9ad6350bd), [FormalConjectures.ErdosProblems.257](#source-source-4bb571f8383293), [FormalConjectures.ErdosProblems.269](#source-source-573a79feb36d47), [FormalConjectures.ErdosProblems.251](#source-source-b202a3f125817d), [FormalConjectures.ErdosProblems.1049](#source-source-d7a43109c64c0c)
- **The mathlib Community**: [mathlib4](#source-mathlib4-pin-5e932f97), [The Lean mathematical library](#source-source-d8b2a7c411bc2d)
- **Thomas Bloom**: [Retrieval of Chowla 1947 original scan](#source-erdos1049-bloom-chowla-scan-retrieval), [Infinite-prime-set irrationality proof and correction chain](#source-erdos269-fan-infinite-p-proof-repair)
- **Thomas F. Bloom**: [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Erdős Problems discussion thread #251](#source-source-21738452dcb95c)
- **Thomas F. Bloom (site editor)**: [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context)
- **Tianyi Peng**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Timothy Poteet**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Tony Feng**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Tonći Crmarić**: [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb)
- **Trieu H. Trinh**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Trieu Trinh**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Umberto Zannier**: [Some New Applications of the Subspace Theorem](#source-source-corvaja-zannier-2002-subspace)
- **Unknown**: [NIST Digital Library of Mathematical Functions, §1.12(ii) Convergents](#source-source-f213b302ada43a)
- **V. Kovač**: [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3)
- **V. Kuperberg**: [Sums of singular series with large sets and the tail of the distrib…](#source-source-811205223e0788)
- **V. N. Dubinin**: [Lemniscates and inequalities for the logarithmic capacities of cont…](#source-source-2a86f52125aec0), [Some inequalities for polynomials and rational functions associated…](#source-source-dcbe400c96be59)
- **V. S. Pendyala**: [Shortest paths in polynomial lemniscate sublevel sets and a problem…](#source-source-8710374c3e8c9f), [A Degree-Four Lemniscate Path Theorem](#source-source-951f70d8dfc418)
- **Vasilevskii, Aliaksei**: [On the sequence $n!$ mod $p$](#source-source-02fc1f0e6f0418)
- **Vasily Ilin**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Venkata Pendyala**: [Quartic case of Erdős #1041](#source-erdos1041-pendyala-quartic)
- **Vishal Dey**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Vjekoslav Kovač**: [Koizumi pseudo-greedy equivalence and computation pointer](#source-erdos243-kovac-koizumi-pointer), [Counterexample to Erdős variable-denominator expectation](#source-erdos251-kovac-variable-denominator-counterexample), [Earlier variants, interval-filling negative variant, and fat-Cantor…](#source-erdos257-kovac-context-bundle), [Older Erdős and Borwein attribution for even/odd supports](#source-erdos257-kovac-older-special-case-attribution), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **Vladimir G. Tkachev**: [Length functions of lemniscates](#source-source-57fe330e419648)
- **Vladimir N. Dubinin**: [Inequalities for critical values of polynomials](#source-source-b10b965e63a00d), [Four-point distortion theorem for complex polynomials](#source-source-f0af8e6f36727f)
- **W. Hayman**: [On the length of lemniscates](#source-source-7f1f2a3fd9238c)
- **W. Koepf**: [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0)
- **W. Li**: [Irrationality Criteria for Series by Erdős and Straus](#source-source-c6e97d89c9fa5f)
- **W. R. Alford**: [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31)
- **W. Schramm**: [The Fourier transform of functions of the greatest common divisor](#source-source-c786f202d47318)
- **W. T. Gowers**: [Why I didn't sign the Fields medallists' letter](#source-ai-essay-gowers-20260917-why-i-didnt-sign)
- **W. Van Assche**: [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94)
- **W. Zudilin**: [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [On the non-quadraticity of values of the q-exponential function and…](#source-source-22ef36d016ca81), [On the irrationality of generalized q-logarithm](#source-source-ae9859af28fdcd), [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f), [Remarks on irrationality of q-harmonic series](#source-source-f1c687cb5e9ae4), [A determinantal approach to irrationality](#source-source-f67bf9959aa230), [Rational approximations to a q-analogue of π and some other q-series](#source-source-f9fd9214c9ef11)
- **W. van Doorn**: [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3)
- **Wadim Zudilin**: [Diophantine Problems for q-Zeta Values](#source-proposed-direct-0ef4f73f93ceed), [A determinantal approach to irrationality (arXiv v2)](#source-source-zudilin-determinantal-1507-05697v2)
- **Wei-Yuan Li**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Wenjie Ma**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Will Cook (coverage audit author)**: [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary)
- **Woong Shin**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **X. Li**: [The Network Structure of Mathlib](#source-source-81b67bfd835ac9)
- **Xia Ning**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Xiaomeng Yang**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Xiaoyang Lu**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Xiyu Hu**: [Factorial residues modulo a prime: beyond the square-root bound](#source-source-365c2b5cf46ebe)
- **Xuhui Huang**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Xujie Si**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Y. Bugeaud**: [On the complexity of algebraic numbers I. Expansions in integer bases](#source-source-7c8ba4ea6eea79), [Transcendence and continued fraction expansion of values of Hecke--…](#source-source-b9d7160919621f)
- **Y. Li**: [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641)
- **Y. Puri**: [Integer sequences and periodic points](#source-source-5cac1ad51acb12)
- **Y. Tachiya**: [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44)
- **Y. Zhang**: [Bounded gaps between primes](#source-source-c32d672658410d)
- **YaGuang Li**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yann Bugeaud**: [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c)
- **Yi Tay**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yi Wang**: [Log-convex and Stieltjes moment sequences](#source-source-e535117ac620e6)
- **Yifei Li**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Yohei Tachiya**: [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9), [Irrationality of Lambert series associated with a periodic sequence](#source-source-9ce84321e202f1), [Linear independence of certain Lambert series](#source-source-f6ee6890db85d9)
- **Youngbeom Jin**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Youyuan Zhang**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Yu Su**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Yu-Chen Sun**: [The critical-window profile for d\_k in short intervals](#source-proposed-direct-6f90767d1d01dd)
- **Yu-Sheng Shih**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Yu. V. Nesterenko**: [Modular functions and transcendence questions](#source-source-6346eeeac5036d)
- **Yuan Liu**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yuri Chervonyi**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yuta Suzuki**: [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9)
- **Yuting Ning**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Yutong Wang**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Z. Nitecki**: [Subsum sets: intervals, Cantor sets, and Cantorvals](#source-source-63a234b13e4427)
- **Zaiwen Wen**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **Zeming Sun**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Zeraoulia Rafik**: [Irrationality of the n=2^m sparse totient subseries](#source-erdos249-rafik-sparse-power-two-subseries)
- **Zeyi Liao**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Zhaoyu Li**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Zichen Lai**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **Zijun Yao**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Ziru Chen**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Zitong Lu**: [ScienceAgentBench: Toward Rigorous Assessment of Language Agents fo…](#source-source-05a4915b796443)
- **Zsuzsa Marka**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **ammkrn**: [nanoda\_lib](#source-software-nanoda-lib-independent-lean-checker)
- **ani (forum handle)**: [Degree-seven total-variation counterexample for polynomial lemniscates](#source-erdos1041-ani-degree-seven-candidate-counterexample)
- **de Zeeuw, Frank**: [An improved point-line incidence bound over arbitrary fields](#source-source-29cbac966b8b76)
- **morluto**: [Independent check of candidate degree-seven counterexample](#source-erdos1041-morluto-independent-check)
- **shtuka**: [A Short Path Joining Two Zeros Inside a Polynomial Lemniscate](#source-source-f300911fb03a5c)
- **van Doorn, Wouter**: [Partitions with prescribed sum of reciprocals: asymptotic bounds](#source-source-dbbc7de069eeee)
- **{D. H. J. Polymath}**: [Variants of the Selberg sieve, and bounded intervals containing man…](#source-source-91aa380a16dba9)
- **{Plectis revision research draft}**: [Three refinements for the lemniscate-path programme](#source-source-45037c29c04bed)
- **{{National Institute of Standards and Technology}}**: [{Digital Library of Mathematical Functions}, {Section} 5.11(iii): R…](#source-source-b95bf142df7fb5)

</details>

## Sources and exact uses

<a id="source-agmai-20260929-responsible-release"></a>

### [Responsible Release of AI-Generated Mathematics](https://agmai.org/general-sep29/)

- Source id: `agmai\_20260929\_responsible\_release`
- Author or public identity: Advisory Group on Mathematics and Artificial Intelligence at IAS
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Dated recommendations motivating technical release practices and the distinction between inspection and human understanding. Not endorsement or evidence that this project fulfils laboratory-scale obligations.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1104-L1110) — lines `1104–1110`; excerpt `sha256:0a56177bf9ee04c7eb8c56e6cdf4582861b8073e14f40dffc4804702603020b0`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:653](../../paper/systems/claim-faithful-publication-systems-paper.tex#L653-L653), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:660](../../paper/systems/claim-faithful-publication-systems-paper.tex#L660-L660)

<a id="source-ai-essay-antieau-20260915-fast-math-slow-math"></a>

### [Fast math/slow math](https://antieau.github.io/2026/09/15/fast-math-slow-math.html)

- Source id: `ai\_essay\_antieau\_20260915\_fast\_math\_slow\_math`
- Author or public identity: Ben Antieau
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1350-L1351) — lines `1350–1351`; excerpt `sha256:e6c89924a4cd473044338ab4fc20aab3daf6d1b197c0f08b9472a7eb66e2f7cd`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1055](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1055-L1055)

<a id="source-ai-essay-chu-20260809-ai-dissenter-viewpoint"></a>

### [The AI dissenter viewpoint](https://proofsandprompts.com/2026/08/09/the-ai-dissenter-viewpoint/)

- Source id: `ai\_essay\_chu\_20260809\_ai\_dissenter\_viewpoint`
- Author or public identity: Tasmin Chu
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1332-L1336) — lines `1332–1336`; excerpt `sha256:5136e66cbb7aa726a4eba02e1ee74ebc36796ad2770d611cf4e96b785da6ef25`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1055](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1055-L1055)

<a id="source-ai-essay-cohn-20260915-technical-debt"></a>

### [The technical debt of AI-generated mathematics](https://terrytao.wordpress.com/2026/09/15/the-technical-debt-of-ai-generated-mathematics/)

- Source id: `ai\_essay\_cohn\_20260915\_technical\_debt`
- Author or public identity: Henry Cohn
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1088-L1092) — lines `1088–1092`; excerpt `sha256:1f3c81b19f794be86d53650e08f9626446c906889d77d4da17985117e7947f30`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1054](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1054-L1054)

<a id="source-ai-essay-fields-medallists-20260911-severe-misalignment"></a>

### [A severe misalignment of AI in mathematics](https://terrytao.wordpress.com/2026/09/11/a-severe-misalignment-of-ai-in-mathematics/)

- Source id: `ai\_essay\_fields\_medallists\_20260911\_severe\_misalignment`
- Author or public identity: Fields Medallists
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1095-L1100) — lines `1095–1100`; excerpt `sha256:553ba84c17dccb37ab70dd4506f101c56d8b207258ef5f556721aa2d84a92767`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1055](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1055-L1055)

<a id="source-ai-essay-gowers-20260917-why-i-didnt-sign"></a>

### [Why I didn't sign the Fields medallists' letter](https://gowers.wordpress.com/2026/09/17/why-i-didnt-sign-the-fields-medallists-letter/)

- Source id: `ai\_essay\_gowers\_20260917\_why\_i\_didnt\_sign`
- Author or public identity: W. T. Gowers
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1342-L1346) — lines `1342–1346`; excerpt `sha256:30a6ad65c6c978c4097cc16f982b354864ca71e82129c8fa9065966a7a99cbc7`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1055](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1055-L1055)

<a id="source-ai-essay-koukoulopoulos-20260917-cern-for-ai-science"></a>

### [A CERN for AI-assisted science?](https://terrytao.wordpress.com/2026/09/17/a-cern-for-ai-assisted-science/)

- Source id: `ai\_essay\_koukoulopoulos\_20260917\_cern\_for\_ai\_science`
- Author or public identity: Dimitris Koukoulopoulos
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1346-L1350) — lines `1346–1350`; excerpt `sha256:b315d91d429f123ac74c77414dc4454141f8d52412fece95c0b8c814e70403ab`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1055](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1055-L1055)

<a id="source-ai-essay-kra-20260913-deep-theorems"></a>

### [Deep theorems were scarce and difficult and so became an effective mechanism to identify deep thought. AI has broken this system](https://terrytao.wordpress.com/2026/09/13/deep-theorems-were-scarce-and-difficult-and-so-became-an-effective-mechanism-to-identify-deep-thought-ai-has-broken-this-system/)

- Source id: `ai\_essay\_kra\_20260913\_deep\_theorems`
- Author or public identity: Bryna Kra
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1083-L1088) — lines `1083–1088`; excerpt `sha256:e61243701770aa4a88c533a5d157859a8aa852eed7eaa9c15ea1f717f235830c`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1054](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1054-L1054)

<a id="source-ai-essay-litt-20260913-a-beginning-for-mathematics"></a>

### [A beginning for mathematics](https://www.daniellitt.com/blog/2026/9/13/a-beginning-for-mathematics/)

- Source id: `ai\_essay\_litt\_20260913\_a\_beginning\_for\_mathematics`
- Author or public identity: Daniel Litt
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1329-L1332) — lines `1329–1332`; excerpt `sha256:ee9093a8c86cbeb2eb9fab28c7202c32fd65ef7cfab1714fde3545451c0fb674`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1054](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1054-L1054)

<a id="source-ai-essay-ringer-20260917-becoming-a-benchmark"></a>

### [Becoming a benchmark](https://terrytao.wordpress.com/2026/09/17/becoming-a-benchmark/)

- Source id: `ai\_essay\_ringer\_20260917\_becoming\_a\_benchmark`
- Author or public identity: Talia Ringer
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1201-L1205) — lines `1201–1205`; excerpt `sha256:92b92f334ac258aae259af8de72a10cc1aa303685716b7dbf5e840cead2d885c`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1055](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1055-L1055)

<a id="source-ai-essay-sanderson-20260918-more-than-proof"></a>

### [If math is more than proof, we need to better celebrate the rest of it](https://terrytao.wordpress.com/2026/09/18/if-math-is-more-than-proof-we-need-to-better-celebrate-the-rest-of-it/)

- Source id: `ai\_essay\_sanderson\_20260918\_more\_than\_proof`
- Author or public identity: Grant Sanderson
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1100-L1104) — lines `1100–1104`; excerpt `sha256:a1bece4a654c92fc6c6c1c2396621144c9c8eb394e2c5b5ec7d7bfc65fb34896`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1054](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1054-L1054)

<a id="source-ai-essay-tao-20260908-mining-open-problems"></a>

### [Mining open problems](https://mathstodon.xyz/@tao/117237320796901560)

- Source id: `ai\_essay\_tao\_20260908\_mining\_open\_problems`
- Author or public identity: Terence Tao
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1092-L1095) — lines `1092–1095`; excerpt `sha256:96881ad1e94a3efbaf8da36596bf04f78b3013bdcaa5fe8fb4f4e218e14bf4c0`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1054](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1054-L1054)

<a id="source-arxiv-2309-05942"></a>

### [End-to-End Testing of Open-Source Hardware Documentation Developed in Large Collaborations](https://arxiv.org/abs/2309.05942)

- Source id: `arxiv\_2309\_05942`
- Author or public identity: Melinda Yuan, Aruna Das, Sunny Hu, Aaroosh Ramadorai, Imaan Sidhu, Luke Zerrer, Jeremiah Alonzo, Daniel Jarka, Antonio Lobaccaro, Leonardo Lobaccaro, Raymond Provost, Alex Zhindon-Romero, Luca Matone, Szabolcs Marka, Zsuzsa Marka
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Methodological precedent for testing documentation by outsider task completion: two student teams worked through old timing-hardware documentation. This hardware case supplies no evaluation result for the present mathematical repository.
- Source verification: `source\_verified` — Primary source bibliographic metadata and cited methodological passages verified; no local performance or evaluation claim.
- Local mapping: `not recorded`

Exact source locations:

- [Sections End-to-End Exercise (including Method), Student Recommendations, and Discussion and Additional Recommendations. Two student teams worked through timing-hardware documentation; task and survey evidence, not evaluation of this mathematical repository.](https://arxiv.org/abs/2309.05942v1)

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1050](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1050-L1050)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:1253](../../paper/systems/open-source-mathematics-strategy.tex#L1253-L1253)

<a id="source-arxiv-2412-03815"></a>

### [Synergizing LLMs and Knowledge Graphs: A Novel Approach to Software Repository-Related Question Answering](https://arxiv.org/abs/2412.03815)

- Source id: `arxiv\_2412\_03815`
- Author or public identity: Samuel Abedu, SayedHassan Khatoonabadi, Emad Shihab
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Empirical comparison for repository knowledge-graph question answering. Evaluation covers selected Git metadata questions and user tasks; it excludes source-level program analysis and does not validate this repository.
- Source verification: `source\_verified` — Primary source bibliographic metadata and cited methodological passages verified; no local performance or evaluation claim.
- Local mapping: `not recorded`

Exact source locations:

- [arXiv:2412.03815v2, Introduction and Approach; Evaluation Setup; Results RQ3/RQ4; Threats to Validity and Conclusion. Graph schema covers Users, Commits, Issues and Files and excludes source-level program-analysis edges.](https://arxiv.org/abs/2412.03815)
- [Versioned source archive, docs/introduction.tex, lines 7–13 (navigation\_locator).](https://arxiv.org/src/2412.03815v2)
- [Versioned source archive, docs/introduction.tex, lines 10–13 (contribution).](https://arxiv.org/src/2412.03815v2)
- [Versioned source archive, docs/approach.tex, lines 60–74 (contribution).](https://arxiv.org/src/2412.03815v2)
- [Versioned source archive, docs/evaluation.tex, lines 5–45 (method).](https://arxiv.org/src/2412.03815v2)
- [Versioned source archive, docs/introduction.tex, lines 12–18 (method).](https://arxiv.org/src/2412.03815v2)
- [Versioned source archive, docs/abstract.tex, lines 2–2 (evaluation).](https://arxiv.org/src/2412.03815v2)
- [Versioned source archive, docs/results/RQ3.tex, lines 101–125 (evaluation).](https://arxiv.org/src/2412.03815v2)
- [Versioned source archive, docs/results/RQ4.tex, lines 7–23 (evaluation).](https://arxiv.org/src/2412.03815v2)
- [Versioned source archive, docs/threats\_validity.tex, lines 5–18 (limitations\_boundary).](https://arxiv.org/src/2412.03815v2)
- [Versioned source archive, docs/conclusion.tex, lines 3–4 (limitations\_boundary).](https://arxiv.org/src/2412.03815v2)

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1045](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1045-L1045)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:507](../../paper/systems/cold-clone-to-proof-receipt.tex#L507-L507)

<a id="source-arxiv-2509-13978"></a>

### [LLM Agents for Interactive Workflow Provenance: Reference Architecture and Evaluation Methodology](https://arxiv.org/abs/2509.13978)

- Source id: `arxiv\_2509\_13978`
- Author or public identity: Renan Souza, Timothy Poteet, Brian Etz, Daniel Rosendo, Amal Gueroudji, Woong Shin, Prasanna Balaprakash, Rafael Ferreira da Silva
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Background and methodological comparison: workflow-provenance dimensions, reference architecture, and bounded evaluation; does not establish kernel verdicts or research-claim authority.
- Source verification: `source\_verified` — Primary source bibliographic metadata and cited methodological passages verified; no local performance or evaluation claim.
- Local mapping: `not recorded`

Exact source locations:

- [arXiv:2509.13978v2, Background and Related Work: Data Analysis via Workflow Provenance; LLM-powered Provenance Agent Evaluation Methodology; LLM-powered Provenance Agent for Workflow Data Analysis; Experimental Evaluation and Conclusions. Workflow provenance dimensions, modular query architecture and bounded LLM-judge evaluation.](https://arxiv.org/abs/2509.13978)
- [Versioned source archive, sections/background.tex, lines 5–15 (navigation\_locator).](https://arxiv.org/src/2509.13978v2)
- [Versioned source archive, sections/intro.tex, lines 9–20 (contribution).](https://arxiv.org/src/2509.13978v2)
- [Versioned source archive, sections/framework.tex, lines 12–17 (method).](https://arxiv.org/src/2509.13978v2)
- [Versioned source archive, sections/framework.tex, lines 32–63 (method).](https://arxiv.org/src/2509.13978v2)
- [Versioned source archive, sections/method.tex, lines 20–50 (method).](https://arxiv.org/src/2509.13978v2)
- [Versioned source archive, sections/evaluation.tex, lines 8–32 (evaluation).](https://arxiv.org/src/2509.13978v2)
- [Versioned source archive, sections/llm\_evaluation.tex, lines 65–80 (evaluation).](https://arxiv.org/src/2509.13978v2)
- [Versioned source archive, sections/method.tex, lines 43–46 (limitations\_boundary).](https://arxiv.org/src/2509.13978v2)
- [Versioned source archive, sections/llm\_evaluation.tex, lines 56–61 (limitations\_boundary).](https://arxiv.org/src/2509.13978v2)
- [Versioned source archive, sections/conclusion.tex, lines 1–3 (limitations\_boundary).](https://arxiv.org/src/2509.13978v2)

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1053](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1053-L1053)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:393](../../paper/systems/cold-clone-to-proof-receipt.tex#L393-L393)

<a id="source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates"></a>

### [On the shapes of rational lemniscates](https://arxiv.org/abs/2407.14610)

- Source id: `bishop\_eremenko\_lazebnik\_2025\_shapes\_of\_rational\_lemniscates`
- Author or public identity: C. J. Bishop, A. Eremenko, K. Lazebnik
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Lemniscate-graph description with four-valent vertices at simple critical points (Definition 1.2, Proposition 2.4), used in the saddle-block diagnosis.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Definition 1.2 (lemniscate graph, every vertex of even degree at least four) and Proposition 2.4 (every rational lemniscate is a lemniscate graph with vertices at the critical points on the level set); Corollary 1.6 (a lemniscate graph is realised by a polynomial lemniscate up to a homeomorphism of the plane exactly when it is the boundary of its unbounded face). Numbering checked against arXiv v3.](https://arxiv.org/abs/2407.14610)
- [Definition 1.2 and Proposition 2.4](https://doi.org/10.1007/s00039-025-00704-2)
- [Definition 1.2 and Proposition 2.4; Corollary 1.6](https://doi.org/10.1007/s00039-025-00704-2)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1220-L1226) — lines `1220–1226`; excerpt `sha256:bfae70e92b17ff0eb46d5a89787ab01a60a09ee1c2fa3385ddf8b2ff8854f038`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5482-L5488) — lines `5482–5488`; excerpt `sha256:26d60d27d7d495f7259334fef196a51735ac5030652cb8728846fed7b1146393`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5432-L5438) — lines `5432–5438`; excerpt `sha256:26d60d27d7d495f7259334fef196a51735ac5030652cb8728846fed7b1146393`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1071](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1071-L1071)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4419](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4419-L4419), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4422](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4422-L4422), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4490](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4490-L4490), [cite at paper/reasoning-parts/erdos1041/core.tex:4369](../../paper/reasoning-parts/erdos1041/core.tex#L4369-L4369), [cite at paper/reasoning-parts/erdos1041/core.tex:4372](../../paper/reasoning-parts/erdos1041/core.tex#L4372-L4372), [cite at paper/reasoning-parts/erdos1041/core.tex:4440](../../paper/reasoning-parts/erdos1041/core.tex#L4440-L4440)

<a id="source-correspondence-001"></a>

### Listing each checked result, with a cheap way to check it

- Source id: `correspondence-001`
- Author or public identity: A mathematician (name withheld pending confirmation)
- Kind: `correspondence`
- Received: `2026-08-06`; naming: Name withheld until they confirm. [Credit ledger entry](CREDIT_LEDGER.md#credit-correspondence-001)
- Problems: #68, #243, #249, #251, #257, #269, #1041, #1049
- Relationship and boundary: Implemented advice to classify each selected result, expose exact statements, proof provenance, novelty status, sorry count, axiom budget, and boundaries in formalization.yaml, and to provide a cheap Comparator inspection route with an altered-statement rejection fixture. The current public surface has evolved beyond the original interface count; the durable implementation is the manifest-plus-Comparator pattern and its explicit scope ceiling.
- Source verification: `implemented\_advice` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- Private correspondence retained by maintainer; identity withheld pending confirmation.

Public implementation or evidence coordinates:

- [formalization.yaml](../../formalization.yaml#L1-L60) — lines `1–60`; excerpt `sha256:301b260737a1b5176e64724b27eb990eaeda45fba3a6cb92b482ca3bfe6bfd0f`
- [verification/comparator.json](../../verification/comparator.json#L1-L40) — lines `1–40`; excerpt `sha256:8b08466c661aa5a0f1977d62d091fd0a355dd90ba5d7d74a51ca6c578639737f`
- [verification/comparator-negative-mismatch.json](../../verification/comparator-negative-mismatch.json#L1-L13) — lines `1–13`; excerpt `sha256:43aca5f4da7f5f42baf826e53324c045e4fa11acd20ffd1743609e20b5084157`
- [docs/EXTERNAL\_VERIFICATION.md](../../docs/EXTERNAL_VERIFICATION.md#L4-L14) — lines `4–14`; excerpt `sha256:841f2dd16d4a52b7d08408468dd3f4f231b7d8aeb174d9ffad383abbde1acfe9`

<a id="source-correspondence-002"></a>

### Leading the #249 paper with its exact theorem

- Source id: `correspondence-002`
- Author or public identity: A mathematician (name withheld pending confirmation)
- Kind: `correspondence`
- Received: `2026-08-06`; naming: Name withheld until they confirm. [Credit ledger entry](CREDIT_LEDGER.md#credit-correspondence-002)
- Problems: #249
- Relationship and boundary: Implemented advice to lead with the exact finite-level rank and basis, give the CRT/Dirichlet-style independence mechanism, compare the result precisely with Allouche–Shallit, Coons, Martin, and adjacent k-kernel literature, and link a minimal Lean entry. The paper states the exact rank k^e+1 and basis, records that Coons already proved non-k-regularity and Martin supplies a broader external affine-independence antecedent while the public Lean proof establishes all-base independence separately, and keeps the unbounded #249 irrationality endpoint open. No proof verification, novelty judgment, or progress-on-parent-problem judgment is attributed to the correspondent.
- Source verification: `implemented\_advice` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- Private correspondence retained by maintainer; identity withheld pending confirmation.

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L22-L24) — lines `22–24`; excerpt `sha256:88b60a7e65dd8caa239cb470e4423911058629e75c0bb69c7656677329f9429a`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L79-L79) — lines `79–79`; excerpt `sha256:b6ce0fb599e9bf02898ae89ea89e3bf47a7a31efcaab7ffbe2a9e2aaaae8ab8c`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L78-L78) — lines `78–78`; excerpt `sha256:c1960cd50c0146b008839691c83ef53220ec6bdf251ce3c02d30ff006670e01a`
- [lean/Erdos249257/TotientMahlerDefect.lean](../../lean/Erdos249257/TotientMahlerDefect.lean#L935-L1145) — lines `935–1145`; excerpt `sha256:e4bbeef9407526e58653fc7ed307d51530c41af7bd6d225f36388486dc845a6e`
- [formalization.yaml](../../formalization.yaml#L159-L216) — lines `159–216`; excerpt `sha256:b323e9a098414f61b29469d542453a446713a6650efbe384accb4d657f9a1e7e`
- [docs/EXTERNAL\_VERIFICATION.md](../../docs/EXTERNAL_VERIFICATION.md#L534-L544) — lines `534–544`; excerpt `sha256:cb49ade0a57a20d0355d24a8ebc443b2be0b82e0f3c2bdd61f361abe2913a17b`

<a id="source-correspondence-003"></a>

### Earlier work on the #1049 Lambert value

- Source id: `correspondence-003`
- Author or public identity: A mathematician (name withheld pending confirmation)
- Kind: `correspondence`
- Received: `2026-08-05`; naming: Name withheld until they confirm. [Credit ledger entry](CREDIT_LEDGER.md#credit-correspondence-003)
- Problems: #1049
- Relationship and boundary: Implemented a received pointer by comparing the cited q-Apéry construction with the #1049 rational-base programme. The public source closure verifies that the paper targets the same Lambert value, identifies the q-WZ operator and the integer-base denominator-clearing boundary, and credits both published authors in the ordinary literature row. The local Lean module separately proves that Van Assche’s different moving diagonal has a nonzero n=0 residual for the cited operator. This correspondence row credits only the private prior-art pointer; it does not claim the correspondent checked the comparison, calculations, Lean, or #1049 mathematics.
- Source verification: `implemented\_advice` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- Private correspondence retained by maintainer; identity withheld pending confirmation.

Public implementation or evidence coordinates:

- [docs/primary-sources/reciprocal-tail/amdeberhan-zeilberger-1998-q-apery-source-closure.md](../../docs/primary-sources/reciprocal-tail/amdeberhan-zeilberger-1998-q-apery-source-closure.md#L1-L41) — lines `1–41`; excerpt `sha256:2dd1c6e867a779af56358ca64dc97076e8c0c4f4fe8db1128aed5624673e206b`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L878-L878) — lines `878–878`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L389-L393) — lines `389–393`; excerpt `sha256:c9f8d191bbf7d39a3e75436d9d7036604d3f396d1223d6f8d505668cafc4971e`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L1-L100) — lines `1–100`; excerpt `sha256:2869c3db2da5857a4c9fc56be272d52f5a7b1242f3633bd8ed0b01f0da016724`

<a id="source-correspondence-004"></a>

### Writing for a first-time reader

- Source id: `correspondence-004`
- Author or public identity: A mathematician (name withheld pending confirmation)
- Kind: `correspondence`
- Received: `2026-09-17`; naming: Name withheld until they confirm. [Credit ledger entry](CREDIT_LEDGER.md#credit-correspondence-004)
- Problems: #68, #243, #249, #251, #257, #269, #1041, #1049
- Relationship and boundary: Implemented advice on exposition received about the #243 note: replace private names for ordinary objects with the mathematics they denote, inline notation that is used once, and say how restrictive a conditional hypothesis is. The eight short and eight long problem papers were rewritten under these rules and merged on 18 September 2026. The #243 note now names the Chinese remainder theorem where that is the tool and gives examples of what its bounded-increment hypothesis covers, and the public writing skill and short-paper contract now require plain names, notation only where it helps, and an explanation of restrictive hypotheses. No mathematical review, verification or endorsement of any paper is attributed to the correspondent.
- Source verification: `implemented\_advice` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- Private correspondence retained by maintainer; identity withheld pending confirmation.

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L608-L608) — lines `608–608`; excerpt `sha256:4fccb25970fe4d947353fbb0ac94e7491bdd3e9ff10f3d53ddab5ffa734e53e8`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L719-L741) — lines `719–741`; excerpt `sha256:66aefd687af9eeb0fd368920f79b4a003fe1b1cfb714d090e0bc71e7608e8010`
- [skills/public-mathematical-writing/SKILL.md](../../skills/public-mathematical-writing/SKILL.md#L204-L215) — lines `204–215`; excerpt `sha256:e0e13da38d38e09f8750613516947c6ecc6895f947339efa10f17e32951fe324`
- [docs/papers/SHORT\_PAPER\_CONTRACT.md](../../docs/papers/SHORT_PAPER_CONTRACT.md#L15-L15) — lines `15–15`; excerpt `sha256:43ae7aa3892935664831547944b3b27f554b3fd290c430f00cc870396a0f8a9e`
- [docs/papers/SHORT\_PAPER\_CONTRACT.md](../../docs/papers/SHORT_PAPER_CONTRACT.md#L23-L23) — lines `23–23`; excerpt `sha256:ff5754db474f064134ae8227c14f4824529f41415521823ca5a324a5154ab45c`

<a id="source-correspondence-005"></a>

### Showing where methods and ideas come from

- Source id: `correspondence-005`
- Author or public identity: A mathematician (name withheld pending confirmation)
- Kind: `correspondence`
- Received: `2026-09-15`; naming: Name withheld until they confirm. [Credit ledger entry](CREDIT_LEDGER.md#credit-correspondence-005)
- Problems: #68, #243, #249, #251, #257, #269, #1041, #1049
- Relationship and boundary: Implemented advice received in reply to a letter about one of the eight problems: the main objection to AI-assisted mathematics is how rarely it shows where its methods and ideas come from. A prior-art literature review was then run for each of the eight problems, and pull requests #180 and #181 added point-of-use attribution and corrected locators to all eight short papers and long records. No mathematical review, verification or endorsement of any paper is attributed to the correspondent.
- Source verification: `implemented\_advice` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- Private correspondence retained by maintainer; identity withheld pending confirmation.

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L68-L73) — lines `68–73`; excerpt `sha256:1ab1c0d45ed163c3d6109bb69e7ef350daad697816ad030e33bac851a4b79ca4`
- [docs/papers/SHORT\_PAPER\_CONTRACT.md](../../docs/papers/SHORT_PAPER_CONTRACT.md#L19-L19) — lines `19–19`; excerpt `sha256:25842c87b62e2854557a2e4add69568a3d3398b523afd982a2f0348cca448abf`

<a id="source-erdos1041-ani-degree-seven-candidate-counterexample"></a>

### [Degree-seven total-variation counterexample for polynomial lemniscates](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-8861)

- Source id: `erdos1041\_ani\_degree\_seven\_candidate\_counterexample`
- Author or public identity: ani (forum handle)
- Kind: `website\_contribution`
- Problems: #1041
- Relationship and boundary: Ani publicly posted the explicit degree-seven construction and linked manuscript. The post states that the counterexample was found with the help of GPT-6 ("With the help of GPT 6, I find a counterexample in degree 7"). This repository credits that construction to ani and formalises one explicit instance in Lean: all seven roots lie in the open unit disc and every continuous root-to-root path inside the strict unit lemniscate has total variation greater than two. The checked theorem refutes the universal total-variation formulation. It does not formalise the manuscript's full small-parameter family or adjudicate correspondence with the historical curve-length question.
- Source verification: `source\_verified` — The public source identity, ani attribution and correspondence to the linked local Lean declarations are verified. Lean's kernel checks the local explicit-instance and universal-negation theorems. This does not independently validate the manuscript's full family, establish novelty or priority, or settle the historical curve-length correspondence.
- Local mapping: `exact\_authored\_attribution` — The public forum post owns finder credit; the linked local Lean declarations own the repository's checked total-variation refutation.

Exact source locations:

- [Comment posted 7 Sep 2026 by ani; exact HTML element permalink #post-8861](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-8861)
- [Public Overleaf project title \`1041counterexample\`; main.tex viewed 2026-09-12; no \\author command between title/date and document body](https://www.overleaf.com/read/ctmqrqwthkcn#bf8155)
- [Theorem 1.1 and equations (1.1)–(1.2): one-parameter monic degree-7 family; all seven simple zeros have modulus rho=1-s^16\<1; every joining path has length \>2+(alpha/2)s^2](https://www.overleaf.com/read/ctmqrqwthkcn#bf8155)

Public implementation or evidence coordinates:

- [lean/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean](../../lean/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean#L3-L13) — lines `3–13`; excerpt `sha256:0dc7be32db4ccb96eb5a7cc2b22e956f6422aea7ec5706b6217b0a15925b86eb`
- [lean/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean](../../lean/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean#L23-L40) — lines `23–40`; excerpt `sha256:de7c9f67adba5db7a57c763684b751678c107891d725c6a4a3296b34acb2b7c2`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1157-L1159) — lines `1157–1159`; excerpt `sha256:4e4234729ca246120c50642f617d7062a456fa5a1f0900f82ed49b3a7e16a132`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1000](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1000-L1000), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1057](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1057-L1057)

<a id="source-erdos1041-morluto-independent-check"></a>

### [Independent check of candidate degree-seven counterexample](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-8925)

- Source id: `erdos1041\_morluto\_independent\_check`
- Author or public identity: morluto
- Kind: `website\_contribution`
- Problems: #1041
- Relationship and boundary: Forum statement that the degree-seven counterexample seems valid. No proof details or independent artifact are linked, so this is corroboration only. The repository's checked status rests on its Lean formalisation of ani's construction, not on this comment.
- Source verification: `external\_claim\_unverified` — The public comment identity is verified. The comment supplies no independently checkable proof artifact and neither adds to nor changes the repository's Lean-checked total-variation status.
- Local mapping: `external\_corroboration\_only` — No proof artifact is attached to the comment; it is recorded as public corroboration, not as the local proof authority.

Exact source locations:

- [Comment posted 9 Sep 2026 by morluto; exact HTML element permalink #post-8925](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-8925)

<a id="source-erdos1041-pendyala-quartic"></a>

### [Quartic case of Erdős #1041](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-7175)

- Source id: `erdos1041\_pendyala\_quartic`
- Author or public identity: Venkata Pendyala
- Kind: `website\_contribution`
- Problems: #1041
- Relationship and boundary: Author announces degree-four theorem, arXiv:2606.24875, and Aristotle-assisted Lean verification. Quartic partial result only; formal files were not linked in the comment.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `related\_topic\_only` — Current frontier is the same problem family; no precise local theorem/passage consuming Pendyala’s quartic result was identified in this pass.

Exact source locations:

- [Comment posted 24 Jun 2026 by Venkata Pendyala; exact HTML element permalink #post-7175](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-7175)

<a id="source-erdos1049-bloom-chowla-scan-retrieval"></a>

### [Retrieval of Chowla 1947 original scan](https://www.erdosproblems.com/forum/thread/1049?order=oldest#post-5356)

- Source id: `erdos1049\_bloom\_chowla\_scan\_retrieval`
- Author or public identity: RomanLeLan, Thomas Bloom
- Kind: `website\_contribution`
- Problems: #1049
- Relationship and boundary: Provenance/retrieval credit: RomanLeLan requests the source, Bloom locates the Internet Archive scan at p.187. Mathematical credit remains Chowla; current source closure supplies theorem boundary.
- Source verification: `existing\_source\_closure` — A current authored local source-closure already verifies the original literature relation. This does not automatically verify a forum contributor’s independent formulation.
- Local mapping: `source\_retrieval\_provenance` — Local source closure verifies Chowla’s source; the forum exchange earns retrieval credit, not mathematical authorship or implementation credit.

Exact source locations:

- [Comment posted 13 Apr 2026 by RomanLeLan; exact HTML element permalink #post-5356](https://www.erdosproblems.com/forum/thread/1049?order=oldest#post-5356)
- [Comment posted 13 Apr 2026 by Thomas Bloom; exact HTML element permalink #post-5357](https://www.erdosproblems.com/forum/thread/1049?order=oldest#post-5357)

Public implementation or evidence coordinates:

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L78-L82) — lines `78–82`; excerpt `sha256:c2864518e4865dd44a4a7f0e412686c80f1580a48114e8077d016e2b7ddcb64b`
- [docs/primary-sources/reciprocal-tail/chowla-1947-source-closure.md](../../docs/primary-sources/reciprocal-tail/chowla-1947-source-closure.md#L1-L1) — lines `1–1`; excerpt `sha256:e84a307e279c842107b65ddf94e864ecb813914844df302a5f2c28509b7ee1db`

<a id="source-erdos243-kovac-koizumi-pointer"></a>

### [Koizumi pseudo-greedy equivalence and computation pointer](https://www.erdosproblems.com/forum/thread/243?order=oldest#post-439)

- Source id: `erdos243\_kovac\_koizumi\_pointer`
- Author or public identity: Vjekoslav Kovač
- Kind: `website\_contribution`
- Problems: #243
- Relationship and boundary: Identifies Koizumi arXiv:2504.05933 as prior art for the recurrence and conditional pseudo-greedy termination equivalence; pointer/attribution contribution, not an independent theorem.
- Source verification: `existing\_source\_closure` — A current authored local source-closure already verifies the original literature relation. This does not automatically verify a forum contributor’s independent formulation.
- Local mapping: `source\_provenance\_correspondence` — Kovač’s pointer identifies the Koizumi source that has an exact local source closure; the forum post itself is not a proof input.

Exact source locations:

- [Comment posted 11 Sep 2025 by Vjekoslav Kovač; exact HTML element permalink #post-439](https://www.erdosproblems.com/forum/thread/243?order=oldest#post-439)

Public implementation or evidence coordinates:

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L272-L282) — lines `272–282`; excerpt `sha256:9ec6b8b09de1bfee382a968ad6339f9789fe914f34ddd80289565b2b929a0fc7`
- [docs/primary-sources/reciprocal-tail/koizumi-2026-source-closure.md](../../docs/primary-sources/reciprocal-tail/koizumi-2026-source-closure.md#L1-L1) — lines `1–1`; excerpt `sha256:6126bfd0669f6bbbaf09f65bc95f02fb185baddaac42274887a3cba79bdb3118`

<a id="source-erdos243-tao-tail-pair-recurrence"></a>

### [Rational-tail deterministic pair recurrence and open-boundary reduction](https://www.erdosproblems.com/forum/thread/243?order=oldest#post-438)

- Source id: `erdos243\_tao\_tail\_pair\_recurrence`
- Author or public identity: Terence Tao
- Kind: `website\_contribution`
- Problems: #243
- Relationship and boundary: Discussion derivation of the rational-tail pair recurrence; post-459 concedes essentially all observations are already in Koizumi, so credit is disclosure/exposition and not priority over Koizumi.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `related\_topic\_only` — Local Koizumi passage concerns the same recurrence family but does not evidence Tao attribution or adopt Tao’s forum derivation.

Exact source locations:

- [Comment posted 11 Sep 2025 by Terence Tao; exact HTML element permalink #post-438](https://www.erdosproblems.com/forum/thread/243?order=oldest#post-438)
- [Comment posted 11 Sep 2025 by Terence Tao; exact HTML element permalink #post-459](https://www.erdosproblems.com/forum/thread/243?order=oldest#post-459)

<a id="source-erdos249-fan-mobius-transform"></a>

### [Möbius-transform identity for the binary totient constant](https://www.erdosproblems.com/forum/thread/249?order=oldest#post-6489)

- Source id: `erdos249\_fan\_mobius\_transform`
- Author or public identity: Steve Fan
- Kind: `website\_contribution`
- Problems: #249
- Relationship and boundary: Exact identity Σφ(n)/2^n = 1/2 + Σμ(n)/(2^n−1)^2 from φ=μ\*id. Coordinate change only; no irrationality conclusion.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `unmapped\_external\_coordinate\_identity` — No exact local passage/declaration adopting Fan’s displayed Möbius identity was found.

Exact source locations:

- [Comment posted 16 May 2026 by Steve Fan; exact HTML element permalink #post-6489](https://www.erdosproblems.com/forum/thread/249?order=oldest#post-6489)

<a id="source-erdos249-rafik-sparse-power-two-subseries"></a>

### [Irrationality of the n=2^m sparse totient subseries](https://www.erdosproblems.com/forum/thread/249?order=oldest#post-6476)

- Source id: `erdos249\_rafik\_sparse\_power\_two\_subseries`
- Author or public identity: Zeraoulia Rafik
- Kind: `website\_contribution`
- Problems: #249
- Relationship and boundary: Exact elementary proof that the restricted power-of-two-index subseries has a non-eventually-periodic binary expansion. This is a special subseries and does not decide the full #249 constant.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `unmapped\_external\_result` — No exact local passage or Lean declaration adopting this sparse-subseries result was found.

Exact source locations:

- [Comment posted 15 May 2026 by Zeraoulia Rafik; exact HTML element permalink #post-6476](https://www.erdosproblems.com/forum/thread/249?order=oldest#post-6476)

<a id="source-erdos251-alfaiz-schlage-puchta-pointer"></a>

### [Schlage-Puchta Theorem 2 literature pointer](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-5404)

- Source id: `erdos251\_alfaiz\_schlage\_puchta\_pointer`
- Author or public identity: Alfaiz
- Kind: `website\_contribution`
- Problems: #251
- Relationship and boundary: Bibliographic pointer to arXiv:1105.1451, Theorem 2, as related. Exact theorem-to-target comparison remains unaudited.
- Source verification: `bibliography\_only` — Identity or relevance lead recorded without theorem-level verification.
- Local mapping: `bibliographic\_lead\_only` — No audited source closure or exact local use found.

Exact source locations:

- [Comment posted 15 Apr 2026 by Alfaiz; exact HTML element permalink #post-5404](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-5404)

<a id="source-erdos251-kovac-variable-denominator-counterexample"></a>

### [Counterexample to Erdős variable-denominator expectation](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-5416)

- Source id: `erdos251\_kovac\_variable\_denominator\_counterexample`
- Author or public identity: Vjekoslav Kovač
- Kind: `website\_contribution`
- Problems: #251
- Relationship and boundary: Telescoping construction refuting the adjacent g\_n=o(p\_n) expectation; Nat Sothanaphan reports a standard check found no issue. It does not bear on the fixed dyadic target. The comment attributes the telescoping countermodel mechanism to Kovač’s public counterexample discussion; this is lineage/comparison, not a claim that the local theorem reproduces all of that contribution.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_authored\_attribution` — PRIOR\_ART explicitly credits Kovač’s Theorem 1 and states its boundary; no Lean implementation claimed.

Exact source locations:

- [Comment posted 15 Apr 2026 by Vjekoslav Kovač; exact HTML element permalink #post-5416](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-5416)
- [Comment posted 15 Apr 2026 by Nat Sothanaphan; exact HTML element permalink #post-5428](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-5428)

Public implementation or evidence coordinates:

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L286-L290) — lines `286–290`; excerpt `sha256:0f62f937441a579688654793f759c8d3a907ac15bb22aa83897d45df1462216a`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L27-L30) — lines `27–30`; excerpt `sha256:1fdbe78f7474100bd312810adac9f1ef95fe6de93652e252348899dffa4e15c6`

<a id="source-erdos251-land-conditional-proof-lean"></a>

### [Conditional #251 proof under Kuperberg Conjecture 1.3 and Lean formalization](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-8820)

- Source id: `erdos251\_land\_conditional\_proof\_lean`
- Author or public identity: Johan Land
- Kind: `website\_contribution`
- Problems: #251
- Relationship and boundary: Very recent author claim and GitHub formalization. Conditional on a uniform Hardy–Littlewood prime-tuples conjecture; repo and assumption bridge were not independently checked in this scout.
- Source verification: `bibliography\_only` — Identity or relevance lead recorded without theorem-level verification.
- Local mapping: `external\_claim\_only` — No local adoption or audit found.

Exact source locations:

- [Comment posted 6 Sep 2026 by Johan Land; exact HTML element permalink #post-8820](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-8820)
- [Comment posted 6 Sep 2026 by Johan Land; exact HTML element permalink #post-8823](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-8823)

<a id="source-erdos251-tao-prime-gap-equivalence"></a>

### [Prime-gap summation-by-parts equivalence and conditional route](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-926)

- Source id: `erdos251\_tao\_prime\_gap\_equivalence`
- Author or public identity: Terence Tao
- Kind: `website\_contribution`
- Problems: #251
- Relationship and boundary: Exact summation-by-parts equivalence with Σ(p\_{n+1}−p\_n)/2^n, followed by a heuristic conditional prime-tuples/entropy route. Equivalence is exact; suggested route is not a theorem.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_mathematical\_correspondence` — Paper explicitly attributes the already-known summation-by-parts identity to Tao’s 7 Oct 2025 forum comment; Lean lines 138–172 implement the finite prime-gap identity, while adapter lines 390–421 prove the zero-based infinite identity/equivalence.

Exact source locations:

- [Comment posted 7 Oct 2025 by Terence Tao; exact HTML element permalink #post-926](https://www.erdosproblems.com/forum/thread/251?order=oldest#post-926)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L435-L435) — lines `435–435`; excerpt `sha256:564fef3b1c83b587c34b3db58f1f89d199d9b9f7fccafdea2fbbe0766f05f34a`
- [lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean](../../lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L138-L172) — lines `138–172`; excerpt `sha256:df88134179386f6161b138662a0cf1e7faf8a0ff67d5a839a7ac4608d03ad1c2`
- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L404-L435) — lines `404–435`; excerpt `sha256:912d421ce3a607706d9b45fcb033ab97d4d81f834be36a029c3407aca9e05ae8`

<a id="source-erdos257-kovac-context-bundle"></a>

### [Earlier variants, interval-filling negative variant, and fat-Cantor boundary](https://www.erdosproblems.com/forum/thread/257?order=oldest#post-2)

- Source id: `erdos257\_kovac\_context\_bundle`
- Author or public identity: Vjekoslav Kovač
- Kind: `website\_contribution`
- Problems: #257
- Relationship and boundary: Source-linked synthesis distinguishing multi-base interval filling, fixed-base positive measure, and the lack of a rational-point theorem. Maps to Kovač–Tao and Boes–Darst–Erdős; does not solve #257.
- Source verification: `existing\_source\_closure` — A current authored local source-closure already verifies the original literature relation. This does not automatically verify a forum contributor’s independent formulation.
- Local mapping: `related\_source\_family` — Local source closure verifies Kovač–Tao’s paper; it does not make the forum synthesis an implementation input.

Exact source locations:

- [Comment posted 9 Aug 2025 by Vjekoslav Kovač; exact HTML element permalink #post-2](https://www.erdosproblems.com/forum/thread/257?order=oldest#post-2)
- [Comment posted 25 Aug 2025 by Vjekoslav Kovač; exact HTML element permalink #post-208](https://www.erdosproblems.com/forum/thread/257?order=oldest#post-208)

Public implementation or evidence coordinates:

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L156-L160) — lines `156–160`; excerpt `sha256:badb6c16b351f142047e83c1c8631e63319c82edabf1973f16a616deead6f4d6`
- [docs/primary-sources/reciprocal-tail/kovac-tao-2025-source-closure.md](../../docs/primary-sources/reciprocal-tail/kovac-tao-2025-source-closure.md#L1-L1) — lines `1–1`; excerpt `sha256:afa5eea7ce02b26464e36300842105a356651d8f78c7fafa103c54075c0b9979`

<a id="source-erdos257-kovac-older-special-case-attribution"></a>

### [Older Erdős and Borwein attribution for even/odd supports](https://www.erdosproblems.com/forum/thread/257?order=oldest#post-332)

- Source id: `erdos257\_kovac\_older\_special\_case\_attribution`
- Author or public identity: Vjekoslav Kovač
- Kind: `website\_contribution`
- Problems: #257
- Relationship and boundary: Attributes even support to Erdős 1948 at base q² and odd support to Borwein 1991 by algebraic rewrite. Corrects priority/context for Tang’s Tachiya application.
- Source verification: `existing\_source\_closure` — A current authored local source-closure already verifies the original literature relation. This does not automatically verify a forum contributor’s independent formulation.
- Local mapping: `source\_provenance\_correspondence` — Local closures cover Erdős/Borwein sources; the forum priority correction is not itself a proof input.

Exact source locations:

- [Comment posted 5 Sep 2025 by Vjekoslav Kovač; exact HTML element permalink #post-332](https://www.erdosproblems.com/forum/thread/257?order=oldest#post-332)

Public implementation or evidence coordinates:

- [docs/primary-sources/totient-kernel/erdos-1948-lambert-source-closure.md](../../docs/primary-sources/totient-kernel/erdos-1948-lambert-source-closure.md#L1-L1) — lines `1–1`; excerpt `sha256:15d4e4847c661dbad3433bbb57367700e448f59ce576437f988dc0d04eb98762`
- [docs/primary-sources/reciprocal-tail/borwein-1991-qn-r-source-closure.md](../../docs/primary-sources/reciprocal-tail/borwein-1991-qn-r-source-closure.md#L1-L1) — lines `1–1`; excerpt `sha256:588b231fb7c44e99046d30f840d6eb897e87b715544cff4b2864b476aea9fc7b`

<a id="source-erdos257-tang-tachiya-period-two"></a>

### [Period-two Lambert theorem applied to even and odd supports](https://www.erdosproblems.com/forum/thread/257?order=oldest#post-330)

- Source id: `erdos257\_tang\_tachiya\_period\_two`
- Author or public identity: Quanyu Tang
- Kind: `website\_contribution`
- Problems: #257
- Relationship and boundary: Correct application of Tachiya Theorem 1 to even/odd support; later discussion notes those two cases already follow from older Erdős/Borwein work. Special supports only.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `unmapped\_external\_specialization` — No exact local passage adopting Tang’s forum specialization found.

Exact source locations:

- [Comment posted 5 Sep 2025 by Quanyu Tang; exact HTML element permalink #post-330](https://www.erdosproblems.com/forum/thread/257?order=oldest#post-330)

<a id="source-erdos269-fan-infinite-p-proof-repair"></a>

### [Infinite-prime-set irrationality proof and correction chain](https://www.erdosproblems.com/forum/thread/269?order=oldest#post-1000)

- Source id: `erdos269\_fan\_infinite\_p\_proof\_repair`
- Author or public identity: Steve Fan, Thomas Bloom
- Kind: `website\_contribution`
- Problems: #269
- Relationship and boundary: Proof for infinite P with an earlier false growth assertion identified by Bloom and edited by Fan; addresses only infinite P, which Erdős called a simple exercise, not finite-P #269.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `related\_topic\_only` — Finite-P local programme does not consume this infinite-P exercise proof.

Exact source locations:

- [Comment posted 11 Oct 2025 by Steve Fan; exact HTML element permalink #post-1000](https://www.erdosproblems.com/forum/thread/269?order=oldest#post-1000)
- [Comment posted 11 Oct 2025 by Thomas Bloom; exact HTML element permalink #post-1002](https://www.erdosproblems.com/forum/thread/269?order=oldest#post-1002)
- [Comment posted 11 Oct 2025 by Steve Fan; exact HTML element permalink #post-1013](https://www.erdosproblems.com/forum/thread/269?order=oldest#post-1013)

<a id="source-erdos269-fan-two-prime-disclosure"></a>

### [Two-prime Hecke–Mahler factorisation and transcendence disclosure](https://www.erdosproblems.com/forum/thread/269?order=oldest#post-7218)

- Source id: `erdos269\_fan\_two\_prime\_disclosure`
- Author or public identity: Steve Fan
- Kind: `website\_contribution`
- Problems: #269
- Relationship and boundary: Earlier public disclosure of the two-channel factorisation and transcendence conclusion; current PRIOR\_ART explicitly disclaims priority for the later note.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_authored\_attribution` — PRIOR\_ART explicitly records Fan’s earlier public disclosure and the later note’s nonpriority boundary.

Exact source locations:

- [Comment posted 26 Jun 2026 by Steve Fan; exact HTML element permalink #post-7218](https://www.erdosproblems.com/forum/thread/269?order=oldest#post-7218)
- [Comment posted 26 Jun 2026 by Steve Fan; exact HTML element permalink #post-7229](https://www.erdosproblems.com/forum/thread/269?order=oldest#post-7229)

Public implementation or evidence coordinates:

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L330-L346) — lines `330–346`; excerpt `sha256:f4d1278504a386c4d49236ab4efd039ef5ddd233f5bae878c29728b527bd5417`

<a id="source-erdos-problems-catalog-eight-problem-context"></a>

### [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257, 269, 1041, and 1049](https://www.erdosproblems.com/68)

- Source id: `erdos\_problems\_catalog\_eight\_problem\_context`
- Author or public identity: Thomas F. Bloom (site editor), Thomas F. Bloom
- Kind: `catalogue`
- Problems: #68, #243, #249, #251, #257, #269, #1041, #1049
- Relationship and boundary: Dated catalogue record of the problem and its status.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `catalog\_context\_only` — PRIOR\_ART names the catalogue only for numbering/status context; no mathematical result imported.

Exact source locations:

- [Catalogue problem page #68; fetched 2026-09-12](https://www.erdosproblems.com/68)
- [Catalogue problem page #243; fetched 2026-09-12](https://www.erdosproblems.com/243)
- [Catalogue problem page #249; fetched 2026-09-12](https://www.erdosproblems.com/249)
- [Catalogue problem page #251; fetched 2026-09-12](https://www.erdosproblems.com/251)
- [Catalogue problem page #257; fetched 2026-09-12](https://www.erdosproblems.com/257)
- [Catalogue problem page #269; fetched 2026-09-12](https://www.erdosproblems.com/269)
- [Catalogue problem page #1041; fetched 2026-09-12](https://www.erdosproblems.com/1041)
- [Catalogue problem page #1049; fetched 2026-09-12](https://www.erdosproblems.com/1049)
- [Reference and role retained from the attached paper; not independently reread in full in this revision.](https://www.erdosproblems.com/68)
- [Dated catalogue observation only.](https://www.erdosproblems.com/243)
- [Catalogue and numbering, not proof or an exhaustive novelty search.](https://www.erdosproblems.com/269)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://www.erdosproblems.com/1049)

Public implementation or evidence coordinates:

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L13-L14) — lines `13–14`; excerpt `sha256:aa0115edbe0e59ed8b451f14efbc32d972ac7de0a6a72dd7f26064aeb1e64466`
- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5438-L5449) — lines `5438–5449`; excerpt `sha256:f4a1bd463f398d1bcf67d88f273df4a9fc0dc2d42efadf85db1519f432cadfb5`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L564-L568) — lines `564–568`; excerpt `sha256:791153345d44da2ba3bf2e7cd8c560cfe40cee7e061723be8a58fff4aa7c68f9`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3155-L3159) — lines `3155–3159`; excerpt `sha256:fd3671803715497848f50b7e406b351a3c0b3100358db5c0e7912563aefc2384`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1453-L1456) — lines `1453–1456`; excerpt `sha256:4d4235c9f8595425346cd8f2ad0afc169ccb1bbc0fba3996d6af5ec8a919f0f7`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4150-L4153) — lines `4150–4153`; excerpt `sha256:1dca12f343679fed7cbdd1c9c2c6875092a3fc3a72e5f2d5a7e3c53e88c81bad`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L834-L836) — lines `834–836`; excerpt `sha256:005880e8a0c24af82bd80baf86e412679544e057c8fc1dd3cb8974df9821931f`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3071-L3073) — lines `3071–3073`; excerpt `sha256:005880e8a0c24af82bd80baf86e412679544e057c8fc1dd3cb8974df9821931f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4425-L4428) — lines `4425–4428`; excerpt `sha256:537273daefc24b11ce4957528c7e9ccf4d6f1dded43341bd70c16ddf413cbaec`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1036-L1039) — lines `1036–1039`; excerpt `sha256:1f96b54624b74012e10f2b0eb737b72d04c0a867978035159fb1c8d591f76534`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1161-L1163) — lines `1161–1163`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5392-L5394) — lines `5392–5394`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1298-L1302) — lines `1298–1302`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5318-L5322) — lines `5318–5322`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1671-L1676) — lines `1671–1676`; excerpt `sha256:bb8050123710e542e010c55df517209f1e56e938a1655ebb63df13ec2e2c8c44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5342-L5344) — lines `5342–5344`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L48-L48) — lines `48–48`; excerpt `sha256:39b01ef53f651e61857928eaa6e3fcd4e9d3905f467040c640112f06aed89e75`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5287-L5291) — lines `5287–5291`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L32-L32) — lines `32–32`; excerpt `sha256:8b3731b52bf9c49e062c5c9c515a019161fd4e93d201621c6c7b6b38d14ec5cc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L32-L32) — lines `32–32`; excerpt `sha256:8b3731b52bf9c49e062c5c9c515a019161fd4e93d201621c6c7b6b38d14ec5cc`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4111-L4114) — lines `4111–4114`; excerpt `sha256:1dca12f343679fed7cbdd1c9c2c6875092a3fc3a72e5f2d5a7e3c53e88c81bad`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:291771799f1e1c8a9a0b43391570fd9b02e3836c3944d9938c7a8118de5e6afb`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:291771799f1e1c8a9a0b43391570fd9b02e3836c3944d9938c7a8118de5e6afb`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3029-L3031) — lines `3029–3031`; excerpt `sha256:005880e8a0c24af82bd80baf86e412679544e057c8fc1dd3cb8974df9821931f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:d538a4c45ccfa82fa63fdd158d662620db6780ba048b39e23d15f5c6393443b8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:d538a4c45ccfa82fa63fdd158d662620db6780ba048b39e23d15f5c6393443b8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:d538a4c45ccfa82fa63fdd158d662620db6780ba048b39e23d15f5c6393443b8`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4367-L4370) — lines `4367–4370`; excerpt `sha256:537273daefc24b11ce4957528c7e9ccf4d6f1dded43341bd70c16ddf413cbaec`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L61-L61) — lines `61–61`; excerpt `sha256:a70f5c34effd84c3fbdebb08f7c02886f19fea4ea5a96f7f4cadf1eef3d5c97b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L61-L61) — lines `61–61`; excerpt `sha256:a70f5c34effd84c3fbdebb08f7c02886f19fea4ea5a96f7f4cadf1eef3d5c97b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L61-L61) — lines `61–61`; excerpt `sha256:a70f5c34effd84c3fbdebb08f7c02886f19fea4ea5a96f7f4cadf1eef3d5c97b`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3120-L3124) — lines `3120–3124`; excerpt `sha256:fd3671803715497848f50b7e406b351a3c0b3100358db5c0e7912563aefc2384`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L28-L28) — lines `28–28`; excerpt `sha256:170789f848d7f281c8706ecc14826b85c56cbb95549d73fab6df1df6b540b6d0`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5318-L5322) — lines `5318–5322`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5287-L5291) — lines `5287–5291`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1149-L1153) — lines `1149–1153`; excerpt `sha256:33dec8bc1acd3ac4b9b6a3607c65aa0df85e610d6c5b426244f817177fde3b78`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1068-L1071) — lines `1068–1071`; excerpt `sha256:78a4c894e36fc15f59c4cdc58d03271ad69a3f67a8366ca747b59cae0138bb2e`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:108](../../paper/systems/claim-faithful-publication-systems-paper.tex#L108-L108), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:813](../../paper/systems/claim-faithful-publication-systems-paper.tex#L813-L813), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1000](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1000-L1000), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1052](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1052-L1052), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1057](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1057-L1057)
- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:73](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L73-L73)
- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1251](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1251-L1251)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:71](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L71-L71)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:804](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L804-L804)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1019](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1019-L1019)
- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:49](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L49-L49)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:98](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L98-L98), [cite at paper/reasoning-parts/erdos1041/core.tex:48](../../paper/reasoning-parts/erdos1041/core.tex#L48-L48)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:63](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L63-L63), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5074](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5074-L5074), [cite at paper/reasoning-parts/erdos1049/core.tex:32](../../paper/reasoning-parts/erdos1049/core.tex#L32-L32), [cite at paper/reasoning-parts/erdos1049/core.tex:5043](../../paper/reasoning-parts/erdos1049/core.tex#L5043-L5043)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:77](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L77-L77), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:876](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L876-L876), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3751](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3751-L3751), [cite at paper/reasoning-parts/erdos243/core.tex:38](../../paper/reasoning-parts/erdos243/core.tex#L38-L38), [cite at paper/reasoning-parts/erdos243/core.tex:837](../../paper/reasoning-parts/erdos243/core.tex#L837-L837), [cite at paper/reasoning-parts/erdos243/core.tex:3712](../../paper/reasoning-parts/erdos243/core.tex#L3712-L3712)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:197](../../paper/archive/erdos249-257-main-paper.tex#L197-L197), [cite at paper/archive/erdos249-257-main-paper.tex:4521](../../paper/archive/erdos249-257-main-paper.tex#L4521-L4521)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:71](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L71-L71), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2129](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2129-L2129), [cite at paper/reasoning-parts/erdos251/core.tex:29](../../paper/reasoning-parts/erdos251/core.tex#L29-L29), [cite at paper/reasoning-parts/erdos251/core.tex:2087](../../paper/reasoning-parts/erdos251/core.tex#L2087-L2087)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:119](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L119-L119), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3866](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3866-L3866), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3884](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3884-L3884), [cite at paper/reasoning-parts/erdos269/core.tex:61](../../paper/reasoning-parts/erdos269/core.tex#L61-L61), [cite at paper/reasoning-parts/erdos269/core.tex:3808](../../paper/reasoning-parts/erdos269/core.tex#L3808-L3808), [cite at paper/reasoning-parts/erdos269/core.tex:3826](../../paper/reasoning-parts/erdos269/core.tex#L3826-L3826)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:63](../../paper/68/erdos68-factorial-reasoning-surface.tex#L63-L63), [cite at paper/reasoning-parts/erdos68/core.tex:28](../../paper/reasoning-parts/erdos68/core.tex#L28-L28)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:571](../../paper/systems/open-source-mathematics-strategy.tex#L571-L571), [cite at paper/systems/open-source-mathematics-strategy.tex:789](../../paper/systems/open-source-mathematics-strategy.tex#L789-L789)

<a id="source-eremenko-2007-markov-type-inequality-plane-continua"></a>

### [A Markov-type inequality for arbitrary plane continua](https://arxiv.org/abs/math/0606745)

- Source id: `eremenko\_2007\_markov\_type\_inequality\_plane\_continua`
- Author or public identity: A. Eremenko
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Restatement, with equality cases, of the Eremenko–Lempert bound (Theorem A).
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Theorem A (arXiv p. 2) states the sharp bound sup |f'| \<= 2^(1/d-1) d^2 on a connected sublevel set {|f| \<= 1} of a monic degree-d polynomial, conjectured by Erdos and proved by Eremenko and Lempert, with equality exactly for c^(-d) T\_d(2^(1/d-1) c z + b), |c| = 1; Theorem 2 (p. 3) gives the capacity form for a component of the sublevel set.](https://arxiv.org/abs/math/0606745)
- [Theorem A](https://doi.org/10.1090/S0002-9939-06-08640-0)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1214-L1220) — lines `1214–1220`; excerpt `sha256:9b66ac2741824a4fb126ce6c85cdddc7806daa4534b4f393e06ebf1a210dbd9c`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5476-L5482) — lines `5476–5482`; excerpt `sha256:23a731c181be1a3d3f4f814b84774f68a8a5b6bcebb7b8717ac21e9917899da5`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5426-L5432) — lines `5426–5432`; excerpt `sha256:23a731c181be1a3d3f4f814b84774f68a8a5b6bcebb7b8717ac21e9917899da5`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1123](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1123-L1123)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2367](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2367-L2367), [cite at paper/reasoning-parts/erdos1041/core.tex:2317](../../paper/reasoning-parts/erdos1041/core.tex#L2317-L2317)

<a id="source-eremenko-lempert-1994-extremal-problem-for-polynomials"></a>

### [An extremal problem for polynomials](https://doi.org/10.1090/S0002-9939-1994-1207536-1)

- Source id: `eremenko\_lempert\_1994\_extremal\_problem\_for\_polynomials`
- Author or public identity: A. Eremenko, L. Lempert
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Sharp derivative bound on a connected sublevel set of a monic polynomial (Theorem 1).
- Source verification: `source\_verified` — The cited passages (Theorem 1 (was a plain citation); Theorem 1 (replaces 'cited here through its restatement as Theorem A')) were checked against the journal (PAMS reprint scan with text layer) copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1 (was a plain citation)](https://doi.org/10.1090/S0002-9939-1994-1207536-1)
- [Theorem 1 (replaces 'cited here through its restatement as Theorem A')](https://doi.org/10.1090/S0002-9939-1994-1207536-1)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1209-L1214) — lines `1209–1214`; excerpt `sha256:a3161ac11344fd8199bdbbb63800da9443a64e2a1d3fdd2007366848b954d26f`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5471-L5476) — lines `5471–5476`; excerpt `sha256:2ca5100ac1e4e768257b05ac88a40e2a04ae625930bbba2c8e7c147703d176a6`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5421-L5426) — lines `5421–5426`; excerpt `sha256:2ca5100ac1e4e768257b05ac88a40e2a04ae625930bbba2c8e7c147703d176a6`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1122](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1122-L1122)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2365](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2365-L2365), [cite at paper/reasoning-parts/erdos1041/core.tex:2315](../../paper/reasoning-parts/erdos1041/core.tex#L2315-L2315)

<a id="source-eremenko-yuditskii-2012-comb-functions"></a>

### [Comb functions](https://arxiv.org/abs/1109.1464)

- Source id: `eremenko\_yuditskii\_2012\_comb\_functions`
- Author or public identity: A. Eremenko, P. Yuditskii
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Critical-sequence description of real polynomials (Theorem 1), background for the collinear theorem.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Section 1 (arXiv v1 pp. 1-2) recalls the equioscillation characterisation of the monic polynomial of least deviation from zero on a compact subset of the real line; Theorem 1 (p. 5) shows that a real polynomial with real zeros is determined by its critical sequence up to a real affine change of variable z -\> az+b with a \> 0.](https://arxiv.org/abs/1109.1464)
- [Theorem 1](https://doi.org/10.1090/conm/578/11472)
- [§1](https://doi.org/10.1090/conm/578/11472)
- [Theorem 1; §1](https://doi.org/10.1090/conm/578/11472)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1205-L1209) — lines `1205–1209`; excerpt `sha256:97ed6ed938a762a7aa078c24d5e27afbbef833b6e4baddc2c4ebde5eff3f4607`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5467-L5471) — lines `5467–5471`; excerpt `sha256:42b99f9986d17fa7c89618f299bdc5940ef3f67b0a8129937e2dcd5521a15379`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5417-L5421) — lines `5417–5421`; excerpt `sha256:42b99f9986d17fa7c89618f299bdc5940ef3f67b0a8129937e2dcd5521a15379`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:908](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L908-L908)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2350](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2350-L2350), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2358](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2358-L2358), [cite at paper/reasoning-parts/erdos1041/core.tex:2300](../../paper/reasoning-parts/erdos1041/core.tex#L2300-L2300), [cite at paper/reasoning-parts/erdos1041/core.tex:2308](../../paper/reasoning-parts/erdos1041/core.tex#L2308-L2308)

<a id="source-formal-conjectures-adapter-problem-1049"></a>

### [Formal Conjectures compatibility surface for Erdős #1049](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

- Source id: `formal\_conjectures\_adapter\_problem\_1049`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #1049
- Relationship and boundary: Adapter proves the exact upstream integer-base statement form from the local Erdős-1948 theorem.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_local\_compatibility\_implementation` — Exact local adapter declaration range; no claim of upstream adoption.

Exact source locations:

- [Adapter docstring records upstream comparison pin 398958d3964d738886bd24433918c365df4a2aab; exact target identity varies by block](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

Public implementation or evidence coordinates:

- [research/adapters/FormalConjecturesAdapter.lean](../../research/adapters/FormalConjecturesAdapter.lean#L95-L108) — lines `95–108`; excerpt `sha256:6103702256378b99f284f4867d0c51dd9dd0c5c5e808b1d22f64210a0dbd2253`

<a id="source-formal-conjectures-adapter-problem-249"></a>

### [Formal Conjectures compatibility surface for Erdős #249](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

- Source id: `formal\_conjectures\_adapter\_problem\_249`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #249
- Relationship and boundary: Local variants expose dyadic totient kernel rank/basis over an upstream-shaped namespace; not an upstream accepted result.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_local\_compatibility\_implementation` — Exact local adapter declaration range; no claim of upstream adoption.

Exact source locations:

- [Adapter docstring records upstream comparison pin 398958d3964d738886bd24433918c365df4a2aab; exact target identity varies by block](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

Public implementation or evidence coordinates:

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L284-L302) — lines `284–302`; excerpt `sha256:12a5b1f7563cefb7d10a26be861ae84e01bcba9b150a9655b9c3e2aabd93108b`

<a id="source-formal-conjectures-adapter-problem-251"></a>

### [Formal Conjectures compatibility surface for Erdős #251](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

- Source id: `formal\_conjectures\_adapter\_problem\_251`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #251
- Relationship and boundary: Local variant implements the exact zero-based prime-gap identity and transfer over upstream-owned primeGap vocabulary.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_local\_compatibility\_implementation` — Exact local adapter declaration range; no claim of upstream adoption.

Exact source locations:

- [Adapter docstring records upstream comparison pin 398958d3964d738886bd24433918c365df4a2aab; exact target identity varies by block](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

Public implementation or evidence coordinates:

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L376-L440) — lines `376–440`; excerpt `sha256:4db989ccba90a32a255fe9bd93b65967fa391e1cf1c9974d07cfa64d5d0e92c8`

<a id="source-formal-conjectures-adapter-problem-257"></a>

### [Formal Conjectures compatibility surface for Erdős #257](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

- Source id: `formal\_conjectures\_adapter\_problem\_257`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #257
- Relationship and boundary: Local variant implements finite-period noncollapse over upstream-shaped vocabulary; universal #257 remains open.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_local\_compatibility\_implementation` — Exact local adapter declaration range; no claim of upstream adoption.

Exact source locations:

- [Adapter docstring records upstream comparison pin 398958d3964d738886bd24433918c365df4a2aab; exact target identity varies by block](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

Public implementation or evidence coordinates:

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L356-L374) — lines `356–374`; excerpt `sha256:7ff63cde13f349a5f42b41b5bbc6f9160c468a7a7ae2a92d8cd54b5d8afc85d6`

<a id="source-formal-conjectures-adapter-problem-68"></a>

### [Formal Conjectures compatibility surface for Erdős #68](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

- Source id: `formal\_conjectures\_adapter\_problem\_68`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #68
- Relationship and boundary: Local variant restates the upstream-shaped shifted series and proves the cofinal divisibility-miss equivalence; proposed/support vocabulary, not evidence the upstream file accepted it.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_local\_compatibility\_implementation` — Exact local adapter declaration range; no claim of upstream adoption.

Exact source locations:

- [Adapter docstring records upstream comparison pin 398958d3964d738886bd24433918c365df4a2aab; exact target identity varies by block](https://github.com/google-deepmind/formal-conjectures/tree/398958d3964d738886bd24433918c365df4a2aab/FormalConjectures/ErdosProblems)

Public implementation or evidence coordinates:

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L485-L518) — lines `485–518`; excerpt `sha256:5bd0c8f1316751bbcc0c8dd95f60449cc49b395f5984c254b1db288a24fda020`

<a id="source-formal-conjectures-eight-problem-coverage-boundary"></a>

### [Formal Conjectures coverage boundary across the eight-problem corpus](https://github.com/google-deepmind/formal-conjectures)

- Source id: `formal\_conjectures\_eight\_problem\_coverage\_boundary`
- Author or public identity: The Formal Conjectures Authors, Will Cook (coverage audit author)
- Kind: `software`
- Problems: #68, #243, #249, #251, #257, #269, #1041, #1049
- Relationship and boundary: Direct paper citations exist for #243, #251, #269, #1049. Local compatibility declarations exist for #68, #249, #251, #257, #1049. For #1041, the local fcLength definition explicitly restates the Formal Conjectures Hausdorff path-image-length vocabulary; the case study records the merged upstream statement correction and external proof link. This is statement reuse and contribution provenance, not independent mathematical review or recorded human review of correspondence with the 1958 wording.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `coverage\_audit` — Derived from exact cited paths and adapter declarations.

Exact source locations:

- [Repository-level formal statement corpus](https://github.com/google-deepmind/formal-conjectures)
- [Merged #1041 statement correction and external proof link; current public case-study provenance.](https://github.com/google-deepmind/formal-conjectures/blob/a01ad23474c14781e4f16f48f6e5a430895e10a0/FormalConjectures/ErdosProblems/1041.lean)

Public implementation or evidence coordinates:

- [research/adapters/FormalConjecturesAdapter.lean](../../research/adapters/FormalConjecturesAdapter.lean#L10-L42) — lines `10–42`; excerpt `sha256:a09ac08e4260951af6627cc74ccc029207e6497eb1840a65bda22888010525ed`
- [lakefile.toml](../../lakefile.toml#L67-L79) — lines `67–79`; excerpt `sha256:831b7c7270f57c8606e4effd1314f87cfd4b9ad0eee57b89a546b5457b16aa78`
- [lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean](../../lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L390-L390) — lines `390–390`; excerpt `sha256:cbe13cbf9d5041738aecdb7bbe0abff35d2f946ed3567c4098ec6ce11c206613`
- [docs/case-studies/formal-conjectures-1041.md](../../docs/case-studies/formal-conjectures-1041.md#L12-L12) — lines `12–12`; excerpt `sha256:92f1c74787cba286feffec250ded2fbf4944d6ac40f80c655b6b9370623f920c`
- [docs/case-studies/formal-conjectures-1041.md](../../docs/case-studies/formal-conjectures-1041.md#L74-L74) — lines `74–74`; excerpt `sha256:630e2b08b1fc43aaea823cabc9d314e0e96ad4d7a5d571d1203febbcb140df69`

<a id="source-lean4-toolchain-v4-29-1"></a>

### [Lean 4 theorem prover](https://lean-lang.org/papers/system.pdf)

- Source id: `lean4\_toolchain\_v4\_29\_1`
- Author or public identity: Leonardo de Moura, Sebastian Ullrich, Lean contributors
- Kind: `software`
- Problems: #68, #243, #249, #251, #257, #269, #1041, #1049
- Relationship and boundary: Proof-checking infrastructure used across the complete Lean corpus; software/tool attribution, not mathematical authorship.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_pinned\_dependency` — Exact toolchain pin and CFF reference located.

Exact source locations:

- [Toolchain version leanprover/lean4:v4.29.1](https://github.com/leanprover/lean4/releases/tag/v4.29.1)
- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://doi.org/10.1007/978-3-030-79876-5_37)

Public implementation or evidence coordinates:

- [lean-toolchain](../../lean-toolchain#L1-L1) — lines `1–1`; excerpt `sha256:7dc000621e0046d1aada809e2b7177e64454645cf4c741e9daaf79c99ec2e7a2`
- [CITATION.cff](../../CITATION.cff#L168-L182) — lines `168–182`; excerpt `sha256:20ed248984e0372fbfcc616d3d61f895f70cb37bf9a5e14498b7618a6f5f137b`

<a id="source-mathlib4-pin-5e932f97"></a>

### [mathlib4](https://github.com/leanprover-community/mathlib4/tree/5e932f97dd25535344f80f9dd8da3aab83df0fe6)

- Source id: `mathlib4\_pin\_5e932f97`
- Author or public identity: The mathlib Community
- Kind: `software`
- Problems: #68, #243, #249, #251, #257, #269, #1041, #1049
- Relationship and boundary: Library dependency used by every problem’s Lean source; infrastructure attribution only.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_pinned\_dependency` — Exact manifest revision, Lake requirement, and CFF software credit located.

Exact source locations:

- [lake-manifest.json exact rev 5e932f97dd25535344f80f9dd8da3aab83df0fe6](https://github.com/leanprover-community/mathlib4/tree/5e932f97dd25535344f80f9dd8da3aab83df0fe6)

Public implementation or evidence coordinates:

- [lakefile.toml](../../lakefile.toml#L32-L35) — lines `32–35`; excerpt `sha256:e23a1b4c89226a64e814575fe11c1cf7df1ba9a52561da8d51c246412e7a4f1a`
- [lake-manifest.json](../../lake-manifest.json#L5-L15) — lines `5–15`; excerpt `sha256:b0f750acfc6ef6e2955d978ed32fc02884e8fa180faa9f99bc1ec15ba856defc`
- [CITATION.cff](../../CITATION.cff#L183-L187) — lines `183–187`; excerpt `sha256:b732cf902522394d45614cbb39c73530e2cde6315917ace5f34708b2e268bdb8`

<a id="source-open-letter-royal-society-fellows-20260917"></a>

### [Open Letter to Sir Paul Nurse, President of the Royal Society](https://proofsandprompts.com/2026/09/17/open-letter-to-sir-paul-nurse-president-of-the-royal-society/)

- Source id: `open\_letter\_royal\_society\_fellows\_20260917`
- Author or public identity: Fellows of the Royal Society
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1336-L1342) — lines `1336–1342`; excerpt `sha256:ddd868bf0de48975e181eeb67636c48b7e6b2302a12ac524c3140adace3bd8e3`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1055](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1055-L1055)

<a id="source-proposed-direct-0ef4f73f93ceed"></a>

### [Diophantine Problems for q-Zeta Values](https://www.mathnet.ru/eng/mzm674)

- Source id: `proposed-direct-0ef4f73f93ceed`
- Author or public identity: Wadim Zudilin
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Source of the published 2002 irrationality-measure bound for the q-zeta/Erdős–Borwein value. The manuscript uses the numerical exponent only to show it does not close the local budget.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `not recorded`

Exact source locations:

- [Mathematical Notes 72:6 (2002), 858–862; English DOI 10.1023/A:1021450231834.](https://www.mathnet.ru/eng/mzm674)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L976-L976) — lines `976–976`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1278-L1278) — lines `1278–1278`; excerpt `sha256:603c399e18eec54e4b76bcb455d51b93adf56ce7a26e699ca50aa8527aaa25fa`

<a id="source-proposed-direct-329775d58148a9"></a>

### [Refinements of Erdős's irrationality criterion for certain sparse infinite series](https://arxiv.org/abs/2601.20743)

- Source id: `proposed-direct-329775d58148a9`
- Author or public identity: Hajime Kaneko, Yuta Suzuki, Yohei Tachiya
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Sparse-coefficient criteria compared with the divisor-incidence coefficients; the support-counting conditions fail here and the remote tail differs from the full scaled tail.
- Source verification: `existing\_source\_closure` — The complete bound preprint was read and its pages were checked as images; the source closure records the locators and the counting-hypothesis boundary. This does not certify the paper's mathematics or imply that the note adopts its criteria.
- Local mapping: `not recorded`

Exact source locations:

- [Primary public record metadata verified 2026-09-12.](https://arxiv.org/abs/2601.20743)
- [- \*\*Bound publication identity:\*\* arXiv:2601.20743v1, dated 28 January 2026;](https://arxiv.org/abs/2601.20743)
- [- \*\*Averaged-tail mechanism:\*\* PDF p. 3, equation (1.7), defines](https://arxiv.org/abs/2601.20743)
- [- \*\*Counting hypotheses:\*\* condition (iii) of Theorem 1 (PDF p. 3) and](https://arxiv.org/abs/2601.20743)
- [Theorem 1(iii), p. 3, and Theorem 3(iv), p. 5](https://arxiv.org/abs/2601.20743v1)
- [(1.7), Theorem 1, p. 3; Theorem 3, p. 5; Lemma 1, pp. 6–7; Lemma 2, pp. 7–8 (v1).](https://arxiv.org/pdf/2601.20743v1)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1213-L1213) — lines `1213–1213`; excerpt `sha256:bd3042b8bb213124b09edd0ae290bc793d67b690b4f3eaa43e75f1389ed209f9`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L333-L333) — lines `333–333`; excerpt `sha256:b9b62910f98767af0487515614b98abc215e43ea91b2eca81896345e82d5ba47`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1648-L1652) — lines `1648–1652`; excerpt `sha256:1d98da1cc9acba9dff63b689605b7402eee23c5f2cea8e887c7c18989b40d0d1`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L520-L520) — lines `520–520`; excerpt `sha256:1ed1ce69c8bf73f3362ff5a2aca04fe7d02e4cc4dbe0784bc0f09ca0a22ad778`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9641-L9650) — lines `9641–9650`; excerpt `sha256:29419ac25750a3ca44cb2c1c49ac4bd44f6206b9eff9cc840572a0d12a962f43`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9441-L9450) — lines `9441–9450`; excerpt `sha256:29419ac25750a3ca44cb2c1c49ac4bd44f6206b9eff9cc840572a0d12a962f43`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:464](../../paper/249/erdos-249-binary-totient-series.tex#L464-L464)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:333](../../paper/257/erdos-257-mersenne-support-subseries.tex#L333-L333)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:690](../../paper/249/erdos249-totient-reasoning-surface.tex#L690-L690), [cite at paper/249/erdos249-totient-reasoning-surface.tex:696](../../paper/249/erdos249-totient-reasoning-surface.tex#L696-L696), [cite at paper/249/erdos249-totient-reasoning-surface.tex:698](../../paper/249/erdos249-totient-reasoning-surface.tex#L698-L698), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:498](../../paper/reasoning-parts/erdos249/a249_front.tex#L498-L498), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:504](../../paper/reasoning-parts/erdos249/a249_front.tex#L504-L504), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:506](../../paper/reasoning-parts/erdos249/a249_front.tex#L506-L506)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:720](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L720-L720), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:520](../../paper/reasoning-parts/erdos257/a257_front.tex#L520-L520)

<a id="source-proposed-direct-4e797194f74404"></a>

### [Shifted multiplicative-function correlation program named in the #249 reasoning surface](https://arxiv.org/abs/1501.04585)

- Source id: `proposed-direct-4e797194f74404`
- Author or public identity: Kaisa Matomäki, Maksym Radziwiłł, Terence Tao, Joni Teräväinen
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: This is a public program/context row because the manuscript collectively names three strands rather than asserting one theorem from one paper. The linked primary records identify the named strands: Matomäki–Radziwiłł short intervals, Tao two-point logarithmic Chowla/Elliott, and Tao–Teräväinen odd-order logarithmic Chowla. The manuscript says these results are averaged and do not supply its pointwise input.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `named\_literature\_program\_context`

Exact source locations:

- [Primary public publication record.](https://arxiv.org/abs/1501.04585)
- [Theorem 1, pp. 1-2 (arXiv v4)](https://doi.org/10.4007/annals.2016.183.3.6)
- [Theorems 1.2-1.3, pp. 2 and 5 (arXiv v4)](https://doi.org/10.1017/fmp.2016.6)
- [Theorem 1.1, p. 2 (arXiv v1)](https://doi.org/10.5802/jtnb.1062)
- [Theorem 1, pp. 1-2](https://doi.org/10.4007/annals.2016.183.3.6)
- [Short-interval multiplicative averages; distinguish interval and fine-residue assertions.](https://arxiv.org/abs/1501.04585v4)
- [Logarithmically averaged two-point statements; do not substitute ordinary or pointwise estimates.](https://arxiv.org/abs/1509.05422v4)
- [Odd-order logarithmically averaged correlation statements.](https://arxiv.org/abs/1710.02112v1)
- [Inherited long-paper background record; not newly audited.](https://doi.org/10.4007/annals.2016.183.3.6)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L8250-L8250) — lines `8250–8250`; excerpt `sha256:bad452dab3a80d026ba2b9d6aca2caf78d90b3a49add7f6d1955eef4c220342f`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10363-L10369) — lines `10363–10369`; excerpt `sha256:f37eea22c3c2e50c9106c29e8480d8c2ab20d0f3f59a7faec27317f14c9ea473`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10171-L10177) — lines `10171–10177`; excerpt `sha256:f37eea22c3c2e50c9106c29e8480d8c2ab20d0f3f59a7faec27317f14c9ea473`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10369-L10375) — lines `10369–10375`; excerpt `sha256:e35aaa04403be003a4b96499d83a53616643be3a1bc6ec591562551be6db9bf5`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10177-L10183) — lines `10177–10183`; excerpt `sha256:e35aaa04403be003a4b96499d83a53616643be3a1bc6ec591562551be6db9bf5`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10375-L10382) — lines `10375–10382`; excerpt `sha256:4ca7b4c0db1de3a40807dc6214421cb78ee688d52511a96a2204550ee24c19a4`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10183-L10190) — lines `10183–10190`; excerpt `sha256:4ca7b4c0db1de3a40807dc6214421cb78ee688d52511a96a2204550ee24c19a4`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9688-L9693) — lines `9688–9693`; excerpt `sha256:0b4989fd169ff765ea3d5b38ef8e6aea0f4cd59a60283d86861edd55ca023917`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9488-L9493) — lines `9488–9493`; excerpt `sha256:0b4989fd169ff765ea3d5b38ef8e6aea0f4cd59a60283d86861edd55ca023917`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8442](../../paper/249/erdos249-totient-reasoning-surface.tex#L8442-L8442), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8445](../../paper/249/erdos249-totient-reasoning-surface.tex#L8445-L8445), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8447](../../paper/249/erdos249-totient-reasoning-surface.tex#L8447-L8447), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8250](../../paper/reasoning-parts/erdos249/a249_front.tex#L8250-L8250), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8253](../../paper/reasoning-parts/erdos249/a249_front.tex#L8253-L8253), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8255](../../paper/reasoning-parts/erdos249/a249_front.tex#L8255-L8255)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:8096](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L8096-L8096), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7896](../../paper/reasoning-parts/erdos257/a257_front.tex#L7896-L7896)

<a id="source-proposed-direct-595203db1f6891"></a>

### [On correlations of certain multiplicative functions](https://arxiv.org/abs/1511.02221)

- Source id: `proposed-direct-595203db1f6891`
- Author or public identity: R. Balasubramanian, Sumit Giri, Priyamvad Srivastav
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Context for uniform shifted-correlation estimates; the manuscript explicitly says it does not supply the needed anti-concentration.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `direct\_prose\_source\_absent\_from\_refined\_literature`

Exact source locations:

- [Primary public record metadata verified 2026-09-12.](https://arxiv.org/abs/1511.02221)
- [Theorem 2.2, p. 2 (arXiv v3)](https://doi.org/10.1016/j.jnt.2016.10.001)
- [Theorem 2.2](https://doi.org/10.1016/j.jnt.2016.10.001)
- [Shifted-convolution asymptotics. The citation key records a preprint-era year, not the publication year.](https://arxiv.org/abs/1511.02221v3)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L92-L92) — lines `92–92`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L907-L913) — lines `907–913`; excerpt `sha256:a8cf6f2cdc8cb0b26a0a37cb8141e5828d7e67bf0a8de5e636412840e1a2f1b7`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10337-L10343) — lines `10337–10343`; excerpt `sha256:1e409fb0093faa23ebcc4e5651da0b5eac48a708ad25c90724afa7a140769712`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10145-L10151) — lines `10145–10151`; excerpt `sha256:1e409fb0093faa23ebcc4e5651da0b5eac48a708ad25c90724afa7a140769712`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:844](../../paper/249/erdos-249-binary-totient-series.tex#L844-L844)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:10188](../../paper/249/erdos249-totient-reasoning-surface.tex#L10188-L10188), [cite at paper/249/erdos249-totient-reasoning-surface.tex:10190](../../paper/249/erdos249-totient-reasoning-surface.tex#L10190-L10190), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9996](../../paper/reasoning-parts/erdos249/a249_front.tex#L9996-L9996), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9998](../../paper/reasoning-parts/erdos249/a249_front.tex#L9998-L9998)

<a id="source-proposed-direct-6c67db53ef5f8c"></a>

### [Divisor-bounded multiplicative functions in short intervals](https://arxiv.org/abs/2108.11401)

- Source id: `proposed-direct-6c67db53ef5f8c`
- Author or public identity: Alexander P. Mangerel
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Short-interval context; the manuscript explicitly records why it does not directly supply the selected-trajectory weighted estimate.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `direct\_prose\_source\_absent\_from\_refined\_literature`

Exact source locations:

- [Primary public record metadata verified 2026-09-12.](https://arxiv.org/abs/2108.11401)
- [Theorem 1.7, p. 7, and Corollary 1.8, pp. 7-8](https://doi.org/10.1007/s40687-023-00376-0)
- [Attached full text catalogued; existing long-paper scale comparison retained, not independently re-proved.](https://doi.org/10.1007/s40687-023-00376-0)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L7896-L7896) — lines `7896–7896`; excerpt `sha256:d50e57ea55fd331cc5fcd2f60b7cbbe4f74bdfad5ed5d507e3e2607f34a7aae6`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9693-L9697) — lines `9693–9697`; excerpt `sha256:c5c4489e4688d8773d399bf748456a2ae9b05460c54f6faafd532fa836da5957`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9493-L9497) — lines `9493–9497`; excerpt `sha256:c5c4489e4688d8773d399bf748456a2ae9b05460c54f6faafd532fa836da5957`

Paper citation usages:

- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:8098](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L8098-L8098), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7898](../../paper/reasoning-parts/erdos257/a257_front.tex#L7898-L7898)

<a id="source-proposed-direct-6f90767d1d01dd"></a>

### [The critical-window profile for d\_k in short intervals](https://arxiv.org/abs/2401.08432v3)

- Source id: `proposed-direct-6f90767d1d01dd`
- Author or public identity: Yu-Chen Sun
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Short-interval context; the manuscript explicitly records why it does not directly supply the selected-trajectory weighted estimate.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `direct\_prose\_source\_absent\_from\_refined\_literature`

Exact source locations:

- [Primary public record metadata verified 2026-09-12.](https://arxiv.org/abs/2401.08432v3)
- [Theorem 1.1 and Corollary 1.2, p. 3](https://arxiv.org/abs/2401.08432v3)
- [Attached v3 full text catalogued; existing almost-all versus orbit comparison retained, not independently re-proved.](https://arxiv.org/pdf/2401.08432v3)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L7896-L7896) — lines `7896–7896`; excerpt `sha256:d50e57ea55fd331cc5fcd2f60b7cbbe4f74bdfad5ed5d507e3e2607f34a7aae6`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9697-L9701) — lines `9697–9701`; excerpt `sha256:6d0851d07c69f2ae700a812b4b5fc31762d09234debac02cca0ca4ff63212261`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9497-L9501) — lines `9497–9501`; excerpt `sha256:6d0851d07c69f2ae700a812b4b5fc31762d09234debac02cca0ca4ff63212261`

Paper citation usages:

- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:8100](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L8100-L8100), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7900](../../paper/reasoning-parts/erdos257/a257_front.tex#L7900-L7900)

<a id="source-proposed-direct-7f278004ad452a"></a>

### [Erdős–Gál lacunary-series law of the iterated logarithm (two-part source context)](https://users.renyi.hu/~p_erdos/1955-06.pdf)

- Source id: `proposed-direct-7f278004ad452a`
- Author or public identity: Paul Erdős, István S. Gál
- Kind: `literature`
- Problems: #249
- Relationship and boundary: The prose names the Erdős–Gál law rather than one part. The two primary papers “On the law of the iterated logarithm I” and “II” are linked as the source series; the local use is heuristic calibration, not an input to a proof.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `named\_literature\_program\_context`

Exact source locations:

- [Primary public publication record.](https://users.renyi.hu/~p_erdos/1955-06.pdf)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7973-L7973) — lines `7973–7973`; excerpt `sha256:df8b5a08361a8b2709dbfbc190e9e72f41b2ef5c5874a6274b6c15c70054b621`

<a id="source-proposed-direct-d4ac203509248c"></a>

### [Adamczewski–Bugeaud subword-complexity method context](https://annals.math.princeton.edu/2007/165-2/p04)

- Source id: `proposed-direct-d4ac203509248c`
- Author or public identity: Boris Adamczewski, Yann Bugeaud
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Program/context identity for the method named in prose. The linked primary paper is “On the complexity of algebraic numbers I. Expansions in integer bases”; the local paragraph invokes its algebraicity-conditioned digit-complexity method and explicitly says the hypothesis is unavailable for S.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `named\_literature\_program\_context`

Exact source locations:

- [Primary public publication record.](https://annals.math.princeton.edu/2007/165-2/p04)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L8424-L8424) — lines `8424–8424`; excerpt `sha256:be78c26f277d33338d36a1396ef173f2016a8d8cd7654b87697206f4f4ceb081`

<a id="source-proposed-direct-f7f90747134dba"></a>

### [Note on normal numbers](https://doi.org/10.1090/S0002-9904-1946-08657-7)

- Source id: `proposed-direct-f7f90747134dba`
- Author or public identity: Arthur H. Copeland, Paul Erdős
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Classical constructed-normal-number context. The prose uses it as a contrast for the lack of digit control at prime positions of the explicit target constant.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `not recorded`

Exact source locations:

- [Primary public publication record.](https://doi.org/10.1090/S0002-9904-1946-08657-7)

<a id="source-software-comparator-statement-checker"></a>

### [Comparator](https://github.com/leanprover/comparator)

- Source id: `software\_comparator\_statement\_checker`
- Author or public identity: Lean FRO
- Kind: `software`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1143-L1146) — lines `1143–1146`; excerpt `sha256:a0dabd3a68ddafea15a4462241af10cb793e90e59c6324a84b883eac434e638d`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:293](../../paper/systems/claim-faithful-publication-systems-paper.tex#L293-L293), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1041](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1041-L1041)

<a id="source-software-nanoda-lib-independent-lean-checker"></a>

### [nanoda\_lib](https://github.com/ammkrn/nanoda_lib)

- Source id: `software\_nanoda\_lib\_independent\_lean\_checker`
- Author or public identity: ammkrn
- Kind: `software`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1146-L1149) — lines `1146–1149`; excerpt `sha256:decf3e535ef53dc9a412ddb4ade7e5eae7af85a715a810421802b58ffa0eec49`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:293](../../paper/systems/claim-faithful-publication-systems-paper.tex#L293-L293), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1041](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1041-L1041)

<a id="source-source-011f43e5a781d7"></a>

### [Reproducibility and Replicability in Science](https://doi.org/10.17226/25303)

- Source id: `source-011f43e5a781d7`
- Author or public identity: National Academies of Sciences, Engineering, and Medicine
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1312-L1318) — lines `1312–1318`; excerpt `sha256:f06c40636e471872b987aaee6322971311baed24c1120af1f18cddd808e50e98`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:394](../../docs/papers/mirror/plectis-public-system.tex#L394-L394), [cite at docs/papers/mirror/plectis-public-system.tex:397](../../docs/papers/mirror/plectis-public-system.tex#L397-L397)

<a id="source-source-02fc1f0e6f0418"></a>

### [On the sequence $n!$ mod $p$](https://ems.press/content/serial-article-files/47109)

- Source id: `source-02fc1f0e6f0418`
- Author or public identity: Grebennikov, Alexandr, Sagdeev, Arsenii, Semchankau, Aliaksei, Vasilevskii, Aliaksei
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Primary journal PDF: title page, introduction and precise theorem/corollary statements on pp. 637–639. Later algebraic-geometric proof not independently audited.
- Local mapping: `not recorded`

Exact source locations:

- [Primary journal PDF: title page, introduction and precise theorem/corollary statements on pp. 637–639. Later algebraic-geometric proof not independently audited.](https://ems.press/content/serial-article-files/47109)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3255-L3259) — lines `3255–3259`; excerpt `sha256:bddcb7495409ba674f37573e14998a223896847e01c9d7d112a430f0cca41d03`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3220-L3224) — lines `3220–3224`; excerpt `sha256:bddcb7495409ba674f37573e14998a223896847e01c9d7d112a430f0cca41d03`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1981](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1981-L1981), [cite at paper/reasoning-parts/erdos68/core.tex:1946](../../paper/reasoning-parts/erdos68/core.tex#L1946-L1946)

<a id="source-source-04603f785c9e7f"></a>

### [Lower bounds for some value sets over finite fields: incidence geometry and {Bourgain}'s group expansion theorem](https://arxiv.org/abs/2609.05652v1)

- Source id: `source-04603f785c9e7f`
- Author or public identity: Hu, Xiyu
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Primary arXiv HTML: Sections 2–3 including all of the proof of Theorem 3.1; other applications not independently checked.
- Local mapping: `not recorded`

Exact source locations:

- [Primary arXiv HTML: Sections 2–3 including all of the proof of Theorem 3.1; other applications not independently checked.](https://arxiv.org/abs/2609.05652v1)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3243-L3247) — lines `3243–3247`; excerpt `sha256:a14aa06f222d10c851dd2bfa10beea5352390803145dcffcbdd0759d84e41498`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3208-L3212) — lines `3208–3212`; excerpt `sha256:a14aa06f222d10c851dd2bfa10beea5352390803145dcffcbdd0759d84e41498`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1991](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1991-L1991), [cite at paper/reasoning-parts/erdos68/core.tex:1956](../../paper/reasoning-parts/erdos68/core.tex#L1956-L1956)

<a id="source-source-05a4915b796443"></a>

### [ScienceAgentBench: Toward Rigorous Assessment of Language Agents for Data-Driven Scientific Discovery](https://arxiv.org/html/2410.05080v2)

- Source id: `source-05a4915b796443`
- Author or public identity: Ziru Chen, Shijie Chen, Yuting Ning, Qianheng Zhang, Boshi Wang, Botao Yu, Yifei Li, Zeyi Liao, Chen Wei, Zitong Lu, Vishal Dey, Mingyi Xue, Frazier N. Baker, Benjamin Burns, Daniel Adu-Ampratwum, Xuhui Huang, Xia Ning, Song Gao, Yu Su, Huan Sun
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: The round-7 research-commons note uses the paper’s task construction and grading design as evaluation prior art; the benchmark’s results are not local mathematical-reading measurements.
- Source verification: `source\_verified` — Only the round-7 README passage at lines 59–62 is source-verified against arXiv:2410.05080v2 §§2.1–2.3 and 4.1. No model score transfer, full-paper audit, or claim of local performance.
- Local mapping: `bounded\_round7\_source\_use` — Version-2 methods and evaluation passages checked for the round-7 README design choice.

Exact source locations:

- [§2.1 Problem Formulation, §2.2 Data Collection, §2.3 Evaluation, §4.1 Main Results: publication-derived scientific coding tasks, self-contained Python outputs, task-specific execution grading and cost accounting.](https://arxiv.org/html/2410.05080v2)

Public implementation or evidence coordinates:

- [docs/research-commons/rounds/round7/README.md](../../docs/research-commons/rounds/round7/README.md#L65-L68) — lines `65–68`; excerpt `sha256:92b7b9cc64a1acc947637d28189aed2eaf7a81277bae40c024328d6a919e0414`

<a id="source-source-06457731c60720"></a>

### [The Prime Number Theorem](https://doi.org/10.1017/CBO9780511618314.008)

- Source id: `source-06457731c60720`
- Author or public identity: H. L. Montgomery, R. C. Vaughan
- Kind: `literature`
- Problems: #269
- Relationship and boundary: General textbook reference for lcm(1,…,N) and ψ(N), beside Apostol.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Background in the extended inventory; not an input to the elementary fixed-prime geometry.](https://doi.org/10.1017/cbo9780511618314.008)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4453-L4456) — lines `4453–4456`; excerpt `sha256:0db3df8cac9eaa008e4ba1fc69bf370097ffa91fb0e512033da28a1cab6e2dbc`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4395-L4398) — lines `4395–4398`; excerpt `sha256:0db3df8cac9eaa008e4ba1fc69bf370097ffa91fb0e512033da28a1cab6e2dbc`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L318-L318) — lines `318–318`; excerpt `sha256:a48dbfded735816b42a100262684c9bca03496f8812e5b3646266716ccf5cc33`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:376](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L376-L376), [cite at paper/reasoning-parts/erdos269/core.tex:318](../../paper/reasoning-parts/erdos269/core.tex#L318-L318)

<a id="source-source-07d2ca69e611b7"></a>

### [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](https://doi.org/10.48550/arXiv.2508.21593)

- Source id: `source-07d2ca69e611b7`
- Author or public identity: A. Baanen, M. R. Ballard, J. Commelin, B. Gin-ge Chen, M. Rothgang, D. Testa
- Kind: `software`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L723-L728) — lines `723–728`; excerpt `sha256:361c5b2fa1f2778906e262b1d0e58a126d4e7d28ea4d10e58c4b3607ef4706e2`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1040](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1040-L1040)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:517](../../paper/systems/cold-clone-to-proof-receipt.tex#L517-L517)

<a id="source-source-0a6b8c93371570"></a>

### [A problem about Mahler functions](https://arxiv.org/abs/1303.2019)

- Source id: `source-0a6b8c93371570`
- Author or public identity: B. Adamczewski, J. P. Bell
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Two-base Mahler rationality theorem (Theorem 1.1 of arXiv v1) used in the simultaneous-system proposition.
- Source verification: `source\_verified` — The cited passages (Thm. 1.1, p. 6) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Thm. 1.1, p. 6](https://arxiv.org/abs/1303.2019v1)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://arxiv.org/abs/1303.2019v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5257-L5266) — lines `5257–5266`; excerpt `sha256:559ea13819baf75b04cc9d7303f6c7c0c031c962cc19c07bc95ad20eac0a8832`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5226-L5235) — lines `5226–5235`; excerpt `sha256:559ea13819baf75b04cc9d7303f6c7c0c031c962cc19c07bc95ad20eac0a8832`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4708-L4708) — lines `4708–4708`; excerpt `sha256:255e468ab972fcdcc21a815a58d107099746c2882b841d319f2239751a44e4fe`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4739](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4739-L4739), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5132](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5132-L5132), [cite at paper/reasoning-parts/erdos1049/core.tex:4708](../../paper/reasoning-parts/erdos1049/core.tex#L4708-L4708), [cite at paper/reasoning-parts/erdos1049/core.tex:5101](../../paper/reasoning-parts/erdos1049/core.tex#L5101-L5101)

<a id="source-source-0aca0e5e4e03c0"></a>

### [Multiplicative Number Theory I: Classical Theory](https://doi.org/10.1017/CBO9780511618314)

- Source id: `source-0aca0e5e4e03c0`
- Author or public identity: H. L. Montgomery, R. C. Vaughan
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Standard prime-growth input p\_n ~ n log n (Chapter 6) where the papers use it.
- Source verification: `source\_verified` — The cited passages (Chapter 6 (three new citations: bounded perturbation, PNT scope, first moment); Chapter 6 (PNT scope, Corollary 6.5, state compression)) were checked against the author-hosted Chapter 6 only copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Chapter 6 (three new citations: bounded perturbation, PNT scope, first moment)](https://doi.org/10.1017/CBO9780511618314)
- [Chapter 6 (PNT scope, Corollary 6.5, state compression)](https://doi.org/10.1017/CBO9780511618314)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L830-L832) — lines `830–832`; excerpt `sha256:d266a1d3a0fa072bc043987dc7748df23076e1f5a520e7d5041e49ad2509fad6`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2582-L2582) — lines `2582–2582`; excerpt `sha256:19cfb014840fa377aa38df9849019ad015dd70327f7bf8e708af471ac52e8466`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2540-L2540) — lines `2540–2540`; excerpt `sha256:19cfb014840fa377aa38df9849019ad015dd70327f7bf8e708af471ac52e8466`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3061-L3063) — lines `3061–3063`; excerpt `sha256:b7e63e9f291863fbd6b9fd3c4dc4951de337b3fe54505a8871c92d96d21d90a9`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3019-L3021) — lines `3019–3021`; excerpt `sha256:b7e63e9f291863fbd6b9fd3c4dc4951de337b3fe54505a8871c92d96d21d90a9`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:469](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L469-L469)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:795](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L795-L795), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1564](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1564-L1564), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1633](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1633-L1633), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2284](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2284-L2284), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2582](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2582-L2582), [cite at paper/reasoning-parts/erdos251/core.tex:753](../../paper/reasoning-parts/erdos251/core.tex#L753-L753), [cite at paper/reasoning-parts/erdos251/core.tex:1522](../../paper/reasoning-parts/erdos251/core.tex#L1522-L1522), [cite at paper/reasoning-parts/erdos251/core.tex:1591](../../paper/reasoning-parts/erdos251/core.tex#L1591-L1591), [cite at paper/reasoning-parts/erdos251/core.tex:2242](../../paper/reasoning-parts/erdos251/core.tex#L2242-L2242), [cite at paper/reasoning-parts/erdos251/core.tex:2540](../../paper/reasoning-parts/erdos251/core.tex#L2540-L2540)

<a id="source-source-0d338bb41b8987"></a>

### [The Mathematician's Assistant: Integrating AI into Research Practice](https://arxiv.org/abs/2508.20236)

- Source id: `source-0d338bb41b8987`
- Author or public identity: Jonas Henkel
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by both public systems papers as prior work (August 2025) for cross-model verification on the Open Proof Corpus self-grading finding, the model-as-instrument authorship rule, and the tool-acknowledgement norm; an untested single-author framework for one mathematician at a chat window.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1722-L1727) — lines `1722–1727`; excerpt `sha256:6ab1870a7b04b9f3cc30d59640dcc05a0b6fcd49f9ea44245ecb129aba0f4c4e`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1050](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1050-L1050)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:779](../../paper/systems/open-source-mathematics-strategy.tex#L779-L779), [cite at paper/systems/open-source-mathematics-strategy.tex:1018](../../paper/systems/open-source-mathematics-strategy.tex#L1018-L1018)

<a id="source-source-0dd4239a1d50da"></a>

### [The googol-th bit of the Erdős--Borwein constant](https://math.colgate.edu/~integers/m23/m23.pdf)

- Source id: `source-0dd4239a1d50da`
- Author or public identity: R. Crandall
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. Direct literature attribution. The paper is INTEGERS 12 (2012), article A23, pp. 811–840; the local prose points specifically to section 7.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5397-L5406) — lines `5397–5406`; excerpt `sha256:94ae85ad39b40622ea590cddfc409ecb93f19d077df9ec9c6ab543560d0d1a1a`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L976-L976) — lines `976–976`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2239](../../paper/archive/erdos249-257-main-paper.tex#L2239-L2239)

<a id="source-source-0e12f93aeac487"></a>

### [The maximal length of the Erdős–Herzog–Piranian lemniscate in high degree](https://arxiv.org/abs/2512.12455)

- Source id: `source-0e12f93aeac487`
- Author or public identity: T. Tao
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Resolution of the Erdős #114 level-curve length problem for large degree, cited as context.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Main Theorem 1 proves successively sharper bounds and, in part (iv), the EHP extremal statement for all sufficiently large degrees, with equality characterization.](https://arxiv.org/abs/2512.12455)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5463-L5467) — lines `5463–5467`; excerpt `sha256:7968722d9338768846f85bc2ef2063b55804e78527ad41a2e77023c434d04535`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5413-L5417) — lines `5413–5417`; excerpt `sha256:7968722d9338768846f85bc2ef2063b55804e78527ad41a2e77023c434d04535`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1643-L1643) — lines `1643–1643`; excerpt `sha256:adaee106fc9f14bfa32c5f6ab3ba20afe848ed080f83389485ba7fbd8b3be932`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1693](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1693-L1693), [cite at paper/reasoning-parts/erdos1041/core.tex:1643](../../paper/reasoning-parts/erdos1041/core.tex#L1643-L1643)

<a id="source-source-0e9b7210b29d99"></a>

### On asymptotic distributions of arithmetical functions

- Source id: `source-0e9b7210b29d99`
- Author or public identity: I. J. Schoenberg
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Framework for asymptotic distribution functions, cited beside the 1928 paper that carries the continuity statement.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10353-L10357) — lines `10353–10357`; excerpt `sha256:2ffe3c91d993950605f8bf070b0a5a11ffc1f8ef39055137701039e8577a8e67`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10161-L10165) — lines `10161–10165`; excerpt `sha256:2ffe3c91d993950605f8bf070b0a5a11ffc1f8ef39055137701039e8577a8e67`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8285](../../paper/249/erdos249-totient-reasoning-surface.tex#L8285-L8285), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8093](../../paper/reasoning-parts/erdos249/a249_front.tex#L8093-L8093)

<a id="source-source-0ec7ca07508557"></a>

### [On the Erdős problem #251](https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf)

- Source id: `source-0ec7ca07508557`
- Author or public identity: ChatGPT 5.4 Pro (orchestrated by V. Kovač)
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Public note of 15 April 2026, printed as by ChatGPT 5.4 Pro orchestrated by Vjeko Kovač, refuting Erdős's variable-denominator expectation.
- Source verification: `source\_verified` — The cited passages (plain citation; Theorem 1 and proof, pp. 1-2 (two citations)) were checked against the hosted note, 2 pp. copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [plain citation](https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf)
- [Theorem 1 and proof, pp. 1-2 (two citations)](https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L541-L544) — lines `541–544`; excerpt `sha256:de76425fbfedc49c7c1333d6ff6b6755d0f608d87b83bcebc6b9c6d27c0db50d`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3075-L3077) — lines `3075–3077`; excerpt `sha256:1565fef6512ed60adfcce853ce390a078eea05be1ecd50bcf8d12b0b2b596645`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3033-L3035) — lines `3033–3035`; excerpt `sha256:1565fef6512ed60adfcce853ce390a078eea05be1ecd50bcf8d12b0b2b596645`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L501-L501) — lines `501–501`; excerpt `sha256:f0be293a894eaec58b1c7ed38efb4953996ef87f9ac22c7627561bf7e65657c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L501-L501) — lines `501–501`; excerpt `sha256:f0be293a894eaec58b1c7ed38efb4953996ef87f9ac22c7627561bf7e65657c8`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:543](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L543-L543), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1937](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1937-L1937), [cite at paper/reasoning-parts/erdos251/core.tex:501](../../paper/reasoning-parts/erdos251/core.tex#L501-L501), [cite at paper/reasoning-parts/erdos251/core.tex:1895](../../paper/reasoning-parts/erdos251/core.tex#L1895-L1895)

<a id="source-source-0ecb074e507b86"></a>

### [On the set of partial sums of an infinite series](https://doi.org/10.11429/ptmps1907.7.14_250)

- Source id: `source-0ecb074e507b86`
- Author or public identity: S. Kakeya
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5332-L5335) — lines `5332–5335`; excerpt `sha256:888488ef48fd0e622a7a10d9a3365f11c2438983c6865da31232ee81ad07c437`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1209-L1209) — lines `1209–1209`; excerpt `sha256:2f13d854d17862e3e84cfe8260e36f3e508b7165189455204d23c133aeac237e`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:5068](../../paper/archive/erdos249-257-main-paper.tex#L5068-L5068), [cite at paper/archive/erdos249-257-main-paper.tex:5108](../../paper/archive/erdos249-257-main-paper.tex#L5108-L5108)

<a id="source-source-0f03e2dab0b8c2"></a>

### [Irrationality exponents of certain fast converging series of rational numbers](https://danielduverney.fr/documents/theorie-des-nombres/Tsukuba.pdf)

- Source id: `source-0f03e2dab0b8c2`
- Author or public identity: Daniel Duverney, Takeshi Kurosawa, Iekata Shiokawa
- Kind: `literature`
- Problems: #243
- Relationship and boundary: Full text of the specified source object/passage was read; this is not independent refereeing of the complete article.
- Source verification: `source\_verified` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 1, author-version p. 2, (1.2)–(1.4)](https://danielduverney.fr/documents/theorie-des-nombres/Tsukuba.pdf)
- [Proof, §3, pp. 6–9](https://danielduverney.fr/documents/theorie-des-nombres/Tsukuba.pdf)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1466-L1472) — lines `1466–1472`; excerpt `sha256:c6ad3b74ba433b2451bb8a22ac558445aec5cb56ecfef0b9118236d8dbc841ac`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4168-L4174) — lines `4168–4174`; excerpt `sha256:c6ad3b74ba433b2451bb8a22ac558445aec5cb56ecfef0b9118236d8dbc841ac`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4129-L4135) — lines `4129–4135`; excerpt `sha256:c6ad3b74ba433b2451bb8a22ac558445aec5cb56ecfef0b9118236d8dbc841ac`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1010](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1010-L1010)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:938](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L938-L938), [cite at paper/reasoning-parts/erdos243/core.tex:899](../../paper/reasoning-parts/erdos243/core.tex#L899-L899)

<a id="source-source-0f1a3708d62674"></a>

### [Irrationality of rapidly converging series: a problem of Erdős and Graham](https://arxiv.org/abs/2601.21442v3)

- Source id: `source-0f1a3708d62674`
- Author or public identity: K. Barreto, J. Kang, S.-h. Kim, V. Kovač, S. Zhang
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Consecutive-product and weighted rapid-growth criteria (Theorems 2–3) and the cleared-tail construction (Lemma 8, Proposition 12), compared with the growth of n!−1.
- Source verification: `source\_verified` — The cited passages (Thms. 2-3 and Rem. 4, pp. 2-5; Lem. 8, p. 6; Proposition 12, pp. 9-12) were checked against the arXiv v3 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Thms. 2-3 and Rem. 4, pp. 2-5](https://arxiv.org/abs/2601.21442v3)
- [Lem. 8, p. 6](https://arxiv.org/abs/2601.21442v3)
- [Proposition 12, pp. 9-12](https://arxiv.org/abs/2601.21442v3)
- [Reference and role retained from the attached paper; not independently reread in full in this revision.](https://arxiv.org/abs/2601.21442v3)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3195-L3199) — lines `3195–3199`; excerpt `sha256:de382823fb7376836cf48c1a4705162b30877bceecea105e5ba9fd991dc8dcc9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3160-L3164) — lines `3160–3164`; excerpt `sha256:de382823fb7376836cf48c1a4705162b30877bceecea105e5ba9fd991dc8dcc9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2164-L2164) — lines `2164–2164`; excerpt `sha256:c6c8cf9b68fb541c95c305abe93492fb959422799957e770844d1c594c99ab29`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2164-L2164) — lines `2164–2164`; excerpt `sha256:c6c8cf9b68fb541c95c305abe93492fb959422799957e770844d1c594c99ab29`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2164-L2164) — lines `2164–2164`; excerpt `sha256:c6c8cf9b68fb541c95c305abe93492fb959422799957e770844d1c594c99ab29`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2199](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2199-L2199), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2609](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2609-L2609), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2622](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2622-L2622), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2624](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2624-L2624), [cite at paper/reasoning-parts/erdos68/core.tex:2164](../../paper/reasoning-parts/erdos68/core.tex#L2164-L2164), [cite at paper/reasoning-parts/erdos68/core.tex:2574](../../paper/reasoning-parts/erdos68/core.tex#L2574-L2574), [cite at paper/reasoning-parts/erdos68/core.tex:2587](../../paper/reasoning-parts/erdos68/core.tex#L2587-L2587), [cite at paper/reasoning-parts/erdos68/core.tex:2589](../../paper/reasoning-parts/erdos68/core.tex#L2589-L2589)

<a id="source-source-0f46dee5024c66"></a>

### [Stieltjes moment sequences of polynomials](https://arxiv.org/abs/1710.05795v1)

- Source id: `source-0f46dee5024c66`
- Author or public identity: Huyile Liang, Jeffrey Remmel, Sainan Zheng
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Possible sufficient mechanism for coefficientwise Hankel positivity, not a theorem about the present moving diagonal.
- Source verification: `source\_verified` — Full-text Section 2, including the tridiagonal production-matrix sufficient conditions. Selected section, not an assertion of reading every page.
- Local mapping: `not recorded`

Exact source locations:

- [Full-text Section 2, including the tridiagonal production-matrix sufficient conditions. Selected section, not an assertion of reading every page.](https://arxiv.org/abs/1710.05795v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5377-L5380) — lines `5377–5380`; excerpt `sha256:e321a18827767ed58cdd1dd982eeeb9a39803cd37871901a8449163cbd346499`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5346-L5349) — lines `5346–5349`; excerpt `sha256:e321a18827767ed58cdd1dd982eeeb9a39803cd37871901a8449163cbd346499`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2929](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2929-L2929), [cite at paper/reasoning-parts/erdos1049/core.tex:2898](../../paper/reasoning-parts/erdos1049/core.tex#L2898-L2898)

<a id="source-source-0f61ad0796acdf"></a>

### [Answer to An infinite sum based on the mod-parity of Euler's totient function](https://math.stackexchange.com/a/1211557)

- Source id: `source-0f61ad0796acdf`
- Author or public identity: Erick Wong
- Kind: `website\_contribution`
- Problems: #249
- Relationship and boundary: Public Mathematics Stack Exchange answer of 29 March 2015 proving the matched-base residue case, credited before the base-two theorem.
- Source verification: `source\_verified` — Primary accepted answer and public author identity read and checked. This is a public web contribution; no separate publication or broader priority claim is asserted.
- Local mapping: `not recorded`

Exact source locations:

- [Accepted answer, 29 March 2015: opening statement for every integer k\>2; paragraphs 2–3 establish infinitely many zero and nonzero base-k digits; paragraphs 4–5 give the eventual-periodicity contradiction.](https://math.stackexchange.com/a/1211557)
- [Earlier irrationality with modulus equal to the base; distinguish from fixing base 2.](https://math.stackexchange.com/a/1211557)

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L888-L892) — lines `888–892`; excerpt `sha256:117bd3171f2e021774f4f9022ede7b0664bac13a6e9e4ac082ac520ce020f436`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10268-L10272) — lines `10268–10272`; excerpt `sha256:fb74fd71f49bc3b483f5ac1feed5de8f28b2cb86a5c35567b0628c644acf4527`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10076-L10080) — lines `10076–10080`; excerpt `sha256:fb74fd71f49bc3b483f5ac1feed5de8f28b2cb86a5c35567b0628c644acf4527`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:469](../../paper/249/erdos-249-binary-totient-series.tex#L469-L469)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:702](../../paper/249/erdos249-totient-reasoning-surface.tex#L702-L702), [cite at paper/249/erdos249-totient-reasoning-surface.tex:10176](../../paper/249/erdos249-totient-reasoning-surface.tex#L10176-L10176), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:510](../../paper/reasoning-parts/erdos249/a249_front.tex#L510-L510), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9984](../../paper/reasoning-parts/erdos249/a249_front.tex#L9984-L9984)

<a id="source-source-10545f868b3e88"></a>

### [Old and New Problems and Results in Combinatorial Number Theory](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)

- Source id: `source-10545f868b3e88`
- Author or public identity: P. Erdős, R. L. Graham
- Kind: `literature`
- Problems: #243, #249, #251, #257, #269
- Relationship and boundary: Historical statement of the problem and of the complementary largest-prime-factor indicator.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Mathématique\*, Université de Genève, 1980, 128 printed pages.](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [and size 5,253,644 bytes. PDF pages 1–124 correspond to the monograph's](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [printed pages 3–128 after the cover and contents leaves.](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [printed pp. 60–66 were manually checked against the page images because](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [1. \*\*Section 7 identification (printed p. 60; PDF p. 56).\*\* The source](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [a general irrationality theorem.](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [2. \*\*Divisor and totient full-support boundary (printed p. 61; PDF p. 57).](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [3. \*\*Full-support Mersenne identity (printed p. 62; PDF p. 58).\*\* The source](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [4. \*\*Squarefree reciprocal question (printed p. 63; PDF p. 59).\*\* The](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [questions. This is an explicit open boundary, not a theorem.](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [5. \*\*Adjacent LCM-denominator result (printed p. 65; PDF p. 61).\*\* For a set](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [6. \*\*Section boundary (printed p. 66; PDF p. 62).\*\* The source moves from](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [these irrationality questions to its Diophantine Problems section; the](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [boundaries at the printed pages above. No novelty or priority claim is](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [names, Comparator theorem names, Palomar verdicts, finite totient-kernel](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [full-support identity on printed p. 62 and the open boundaries on printed pp.](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [p. 65](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)
- [Historical problem statement, p. 64.](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5312-L5315) — lines `5312–5315`; excerpt `sha256:89ad0eb6d9dac773cb478c008d67b4ac6ad8b50cdf587f23feda6a8d1825acf6`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1423-L1427) — lines `1423–1427`; excerpt `sha256:8d04873393ce01957978e7bf822e3411f2a23947e1a44f04f81a2db2f17c6332`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4109-L4113) — lines `4109–4113`; excerpt `sha256:8d04873393ce01957978e7bf822e3411f2a23947e1a44f04f81a2db2f17c6332`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L904-L907) — lines `904–907`; excerpt `sha256:e79adb56b67cd11616132762fbeadb6b20811b0217440e25c49e7a4f695da264`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L810-L812) — lines `810–812`; excerpt `sha256:22cefc7058ffe04e57c206b77700b9b9eb94a7db94b2cb2d8367e3e36b8da144`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3031-L3033) — lines `3031–3033`; excerpt `sha256:44c67147da17a5a42fe794398401c5f1d3beb10fb6f1b30933e004aa1a164fd5`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4416-L4419) — lines `4416–4419`; excerpt `sha256:8466f5a9dd4ced1a4f291d5d67e847f3b2fca1cf34f259ca712ff23fe61bbc42`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1027-L1030) — lines `1027–1030`; excerpt `sha256:8466f5a9dd4ced1a4f291d5d67e847f3b2fca1cf34f259ca712ff23fe61bbc42`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4070-L4074) — lines `4070–4074`; excerpt `sha256:8d04873393ce01957978e7bf822e3411f2a23947e1a44f04f81a2db2f17c6332`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2989-L2991) — lines `2989–2991`; excerpt `sha256:44c67147da17a5a42fe794398401c5f1d3beb10fb6f1b30933e004aa1a164fd5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L30-L30) — lines `30–30`; excerpt `sha256:9ac9f5c746a4ed69413e2f364cc0753ee3aa969eb39b5d87a0c1c8e8d6797e46`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4358-L4361) — lines `4358–4361`; excerpt `sha256:8466f5a9dd4ced1a4f291d5d67e847f3b2fca1cf34f259ca712ff23fe61bbc42`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L60-L60) — lines `60–60`; excerpt `sha256:89b37a0d3340796c5590d761a39d83444f6987ea56bf2f2eaf180f3f1f9e9178`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10290-L10294) — lines `10290–10294`; excerpt `sha256:727de5144fdf771c479a2e03e7b875cffecf9400543450974b25f25aced90f03`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10098-L10102) — lines `10098–10102`; excerpt `sha256:727de5144fdf771c479a2e03e7b875cffecf9400543450974b25f25aced90f03`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1115-L1119) — lines `1115–1119`; excerpt `sha256:cf7b027cd3e9245f607b100b8d844bf31558425e35d45828ba319ee30f657f6b`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1057](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1057-L1057)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:69](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L69-L69)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:144](../../paper/249/erdos-249-binary-totient-series.tex#L144-L144)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:52](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L52-L52)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:105](../../paper/269/erdos-269-three-prime-running-lcm.tex#L105-L105)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:75](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L75-L75), [cite at paper/reasoning-parts/erdos243/core.tex:36](../../paper/reasoning-parts/erdos243/core.tex#L36-L36)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:193](../../paper/archive/erdos249-257-main-paper.tex#L193-L193), [cite at paper/archive/erdos249-257-main-paper.tex:194](../../paper/archive/erdos249-257-main-paper.tex#L194-L194)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:284](../../paper/249/erdos249-totient-reasoning-surface.tex#L284-L284), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:92](../../paper/reasoning-parts/erdos249/a249_front.tex#L92-L92)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:72](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L72-L72), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:565](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L565-L565), [cite at paper/reasoning-parts/erdos251/core.tex:30](../../paper/reasoning-parts/erdos251/core.tex#L30-L30), [cite at paper/reasoning-parts/erdos251/core.tex:523](../../paper/reasoning-parts/erdos251/core.tex#L523-L523)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:118](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L118-L118), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3912](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3912-L3912), [cite at paper/reasoning-parts/erdos269/core.tex:60](../../paper/reasoning-parts/erdos269/core.tex#L60-L60), [cite at paper/reasoning-parts/erdos269/core.tex:3854](../../paper/reasoning-parts/erdos269/core.tex#L3854-L3854)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:72](../../paper/synthesis/optimal-sparse-perturbations.tex#L72-L72), [cite at paper/synthesis/optimal-sparse-perturbations.tex:852](../../paper/synthesis/optimal-sparse-perturbations.tex#L852-L852)

<a id="source-source-11b46a0435368f"></a>

### [Simultaneous inequalities among values of the Euler phi-function](https://arxiv.org/abs/math/0603053)

- Source id: `source-11b46a0435368f`
- Author or public identity: Greg Martin
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Separation theorem (Theorem 1) implying linear independence of the totient along pairwise nonproportional affine forms; the papers' own independence proof is a separate CRT-Dirichlet argument.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [eight pages were read. PDF pp. 1, 2, and 8 were also visually checked; the](https://arxiv.org/abs/math/0603053)
- [- \*\*Scope and main theorem:\*\* PDF p. 1 gives the title, author, abstract, and](https://arxiv.org/abs/math/0603053)
- [the start of Theorem 1. PDF p. 2 completes Theorem 1: for positive integer](https://arxiv.org/abs/math/0603053)
- [- \*\*Corollaries:\*\* PDF p. 2 states Corollary 2 for arbitrary strict-order](https://arxiv.org/abs/math/0603053)
- [patterns among consecutive φ-values. PDF pp. 2–3 state Corollary 3 for](https://arxiv.org/abs/math/0603053)
- [comparisons of two nonproportional affine forms and complete Corollary 4,](https://arxiv.org/abs/math/0603053)
- [which transfers Theorem 1 and Corollaries 2–3 from φ to σ. The proof of](https://arxiv.org/abs/math/0603053)
- [Corollary 4 gives the product lower bound and the reversed ordering used](https://arxiv.org/abs/math/0603053)
- [- \*\*Proof architecture:\*\* PDF pp. 3–7 contain the proof and its gcd and](https://arxiv.org/abs/math/0603053)
- [density lemmas, including Lemmas 5 and 6 on p. 4 and the subsequent](https://arxiv.org/abs/math/0603053)
- [- \*\*Bibliographic boundary:\*\* PDF p. 8 contains the references and the](https://arxiv.org/abs/math/0603053)
- [makes no claim that it proves the release's finite dyadic theorem.](https://arxiv.org/abs/math/0603053)
- [The full PDF (pp. 1–8) was checked for the release's theorem names, Lean](https://arxiv.org/abs/math/0603053)
- [Theorem 1 and Corollaries 2–4, while pp. 3–7 contain only Martin's](https://arxiv.org/abs/math/0603053)
- [source supplies comparison input but not the release's finite-base theorem,](https://arxiv.org/abs/math/0603053)
- [formal proof, or endpoint solution. PDF p. 8's bibliography and author block](https://arxiv.org/abs/math/0603053)
- [nonproportional affine forms to Martin's Theorem 1.](https://arxiv.org/abs/math/0603053)
- [φ-to-σ transfer in Corollary 4.](https://arxiv.org/abs/math/0603053)
- [independence theorem.](https://arxiv.org/abs/math/0603053)
- [Martin directly states the release's linear-independence theorem. The](https://arxiv.org/abs/math/0603053)
- [positive-density comparison theorem for nonproportional affine φ-progressions](https://arxiv.org/abs/math/0603053)
- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://arxiv.org/abs/math/0603053)
- [Theorem 1, pp. 1-2](https://arxiv.org/abs/math/0603053v1)
- [Theorem 1](https://arxiv.org/abs/math/0603053v1)
- [Theorem 1, pp. 1–2; proof, pp. 5–8](https://arxiv.org/pdf/math/0603053v1)

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L884-L888) — lines `884–888`; excerpt `sha256:5c07b90db96e384410ed6cbfa6f0a0260dd341520e919d4e5654581d25bb3b5c`
- [lean/Erdos249257/AllBaseTotientKernel.lean](../../lean/Erdos249257/AllBaseTotientKernel.lean#L4-L61) — lines `4–61`; excerpt `sha256:a7583f78b57fbb25305024044671d8303e0dfd61da003f0de23f3c82ca558fb4`
- [lean/Erdos249257/AllBaseTotientKernel.lean](../../lean/Erdos249257/AllBaseTotientKernel.lean#L642-L644) — lines `642–644`; excerpt `sha256:f2847f43a004d01715e61f5510732df2e0014e197cb1796803035180a98f88f6`
- [lean/Erdos249257/TotientKernelConditional.lean](../../lean/Erdos249257/TotientKernelConditional.lean#L5-L18) — lines `5–18`; excerpt `sha256:bb1cbd9adcabf879040179a1dda4145da0903770eb95510584365a88131340ba`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L99-L99) — lines `99–99`; excerpt `sha256:0b9c9251af21e6eeb9177cb4f168d77d98fe8e2be6e6f70f8029efd8b0ef9375`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10264-L10268) — lines `10264–10268`; excerpt `sha256:c97e654465265fb62b6de801d7921a842ace01171d8790c26144b859fefa809c`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10072-L10076) — lines `10072–10076`; excerpt `sha256:c97e654465265fb62b6de801d7921a842ace01171d8790c26144b859fefa809c`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:990](../../paper/systems/claim-faithful-publication-systems-paper.tex#L990-L990), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1056](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1056-L1056)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:124](../../paper/249/erdos-249-binary-totient-series.tex#L124-L124), [cite at paper/249/erdos-249-binary-totient-series.tex:178](../../paper/249/erdos-249-binary-totient-series.tex#L178-L178), [cite at paper/249/erdos-249-binary-totient-series.tex:524](../../paper/249/erdos-249-binary-totient-series.tex#L524-L524)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:291](../../paper/249/erdos249-totient-reasoning-surface.tex#L291-L291), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7006](../../paper/249/erdos249-totient-reasoning-surface.tex#L7006-L7006), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7111](../../paper/249/erdos249-totient-reasoning-surface.tex#L7111-L7111), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:99](../../paper/reasoning-parts/erdos249/a249_front.tex#L99-L99), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6814](../../paper/reasoning-parts/erdos249/a249_front.tex#L6814-L6814), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6919](../../paper/reasoning-parts/erdos249/a249_front.tex#L6919-L6919)

<a id="source-source-120bebce1ffe8c"></a>

### [Heine's basic transform and a permutation group for q-harmonic series](https://geodesic.mathdoc.fr/articles/10.4064/aa111-2-4/)

- Source id: `source-120bebce1ffe8c`
- Author or public identity: W. Zudilin
- Kind: `literature`
- Problems: #1049, #257
- Relationship and boundary: Primary source of the linear forms, Lemma 7 with display (23), the direction (14, 12, 14; 27), the thirteen intervals and the constants C\_1 and C\_0 used by the #1049 rational-base theorem. The tracked source closure records the printed locators, the integer-base hypothesis of every stated result, and the attribution ceiling; the rational specialisation is argued in the notes. Primary metadata titles it “Heine’s basic transform and a permutation group for q-harmonic series”; the manuscript’s shorthand “erratum” should not replace that publication identity. The comments explicitly identify Zudilin’s 2004 Heine/q-harmonic paper, printed formulas, lemmas, section, and theorem used by the rational-base contour comparison. Analytic steps are expressly not formalized. Adjacent/source-independent arithmetic comparison to the Heine–Zudilin construction; the comments do not claim the analytic source theorem is formalized.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Reading status: complete publisher PDF read from rendered pages; printed pp. 153–164 are PDF pp. 1–12.](https://doi.org/10.4064/aa111-2-4)
- [Lemma 7, display (23), printed p. 161: the polynomial inclusion used before the integer evaluation (24).](https://doi.org/10.4064/aa111-2-4)
- [Section 5, (24)–(26), printed pp. 161–162: direction (14, 12, 14; 27), C\_1 = 545.5, C\_0 = 221.30008816..., the thirteen intervals, and Theorem 1's bound.](https://doi.org/10.4064/aa111-2-4)
- [Thm. 1, p. 154](https://doi.org/10.4064/aa111-2-4)
- [Sec. 2, p. 154; Thm. 1](https://doi.org/10.4064/aa111-2-4)
- [Lemmas 1--2, p. 155 (also 'p. 155', 'Sec. 3, p. 155')](https://doi.org/10.4064/aa111-2-4)
- [p. 156 and (8)--(11), pp. 156--157](https://doi.org/10.4064/aa111-2-4)
- [p. 157](https://doi.org/10.4064/aa111-2-4)
- [pp. 156--161; Sec. 4, pp. 159--161; Secs. 3--5](https://doi.org/10.4064/aa111-2-4)
- [p. 161; p. 161, (23)](https://doi.org/10.4064/aa111-2-4)
- [Sec. 5, p. 161; \\S5 / Sec. 5, pp. 161--162; pp. 161--162; Thm. 1, p. 154; Secs. 4--5, pp. 159--162](https://doi.org/10.4064/aa111-2-4)
- [p. 162; Lemma 2, p. 155, and (26), p. 162](https://doi.org/10.4064/aa111-2-4)
- [Theorem 1, p. 154 (two places); remark at the end of Section 3, p. 159](https://doi.org/10.4064/aa111-2-4)
- [Theorem 1, p. 154; final remark of Section 3, p. 159.](https://doi.org/10.4064/aa111-2-4)
- [Full publisher text, especially Lemma 7 (23), p. 161; (24) and direction/constants, p. 162; remainder normalisation, pp. 156--157.](https://geodesic.mathdoc.fr/articles/10.4064/aa111-2-4/)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1271-L1277) — lines `1271–1277`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5205-L5211) — lines `5205–5211`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5174-L5180) — lines `5174–5180`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38) — lines `38–38`; excerpt `sha256:e6675f6b5abec078209b885874c1e1fc5f3a512534f81e8d5d37122583fa90fa`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L976-L976) — lines `976–976`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1278-L1278) — lines `1278–1278`; excerpt `sha256:603c399e18eec54e4b76bcb455d51b93adf56ce7a26e699ca50aa8527aaa25fa`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L8-L36) — lines `8–36`; excerpt `sha256:580a0329d38f93ac21807ae3e4b5576bc7cc0a60f32dc890b169224bff93a983`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L121-L143) — lines `121–143`; excerpt `sha256:9cbb2521fc20ab9b5f2b1ef19d400d7a4706ab42e437b60f3d445f245666ebab`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L312-L317) — lines `312–317`; excerpt `sha256:9d8f3b2b1f69665003c2e2e1011aa3ab2153e1279df369928b397383f2c62c70`
- [lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean](../../lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L8-L15) — lines `8–15`; excerpt `sha256:944f0e0e804396ce17b086bb0755d7c33ca82e608e624be2a2542fcd18124e82`
- [lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean](../../lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L72-L79) — lines `72–79`; excerpt `sha256:519814e5b5744e92c8a9dc9ac2c0c0fd009c2f4c5e71df7e3e2af9a3034f730a`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9676-L9682) — lines `9676–9682`; excerpt `sha256:b26157f8e2462fe6a9cb317178ca1aa00c80c57d6b9c2a7ae528d32e670113ad`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9476-L9482) — lines `9476–9482`; excerpt `sha256:b26157f8e2462fe6a9cb317178ca1aa00c80c57d6b9c2a7ae528d32e670113ad`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:119](../../paper/1049/erdos-1049-rational-base-lambert.tex#L119-L119), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:658](../../paper/1049/erdos-1049-rational-base-lambert.tex#L658-L658), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:661](../../paper/1049/erdos-1049-rational-base-lambert.tex#L661-L661), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:715](../../paper/1049/erdos-1049-rational-base-lambert.tex#L715-L715), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:746](../../paper/1049/erdos-1049-rational-base-lambert.tex#L746-L746), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:758](../../paper/1049/erdos-1049-rational-base-lambert.tex#L758-L758), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:768](../../paper/1049/erdos-1049-rational-base-lambert.tex#L768-L768), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:774](../../paper/1049/erdos-1049-rational-base-lambert.tex#L774-L774), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:870](../../paper/1049/erdos-1049-rational-base-lambert.tex#L870-L870), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:978](../../paper/1049/erdos-1049-rational-base-lambert.tex#L978-L978), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1073](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1073-L1073)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:69](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L69-L69), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:183](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L183-L183), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:215](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L215-L215), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:226](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L226-L226), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:260](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L260-L260), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:282](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L282-L282), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:307](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L307-L307), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:321](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L321-L321), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:324](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L324-L324), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:357](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L357-L357), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:508](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L508-L508), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:543](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L543-L544), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:867](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L867-L867), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:880](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L880-L880), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1169](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1169-L1169), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1178](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1178-L1178), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1309](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1309-L1309), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3302](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3302-L3302), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3458](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3458-L3458), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3802](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3802-L3802), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5020](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5020-L5020), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5062](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5062-L5062), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5103](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5103-L5103), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5104](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5104-L5104), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5109](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5109-L5109), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5256](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5256-L5256), [cite at paper/reasoning-parts/erdos1049/core.tex:38](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38), [cite at paper/reasoning-parts/erdos1049/core.tex:152](../../paper/reasoning-parts/erdos1049/core.tex#L152-L152), [cite at paper/reasoning-parts/erdos1049/core.tex:184](../../paper/reasoning-parts/erdos1049/core.tex#L184-L184), [cite at paper/reasoning-parts/erdos1049/core.tex:195](../../paper/reasoning-parts/erdos1049/core.tex#L195-L195), [cite at paper/reasoning-parts/erdos1049/core.tex:229](../../paper/reasoning-parts/erdos1049/core.tex#L229-L229), [cite at paper/reasoning-parts/erdos1049/core.tex:251](../../paper/reasoning-parts/erdos1049/core.tex#L251-L251), [cite at paper/reasoning-parts/erdos1049/core.tex:276](../../paper/reasoning-parts/erdos1049/core.tex#L276-L276), [cite at paper/reasoning-parts/erdos1049/core.tex:290](../../paper/reasoning-parts/erdos1049/core.tex#L290-L290), [cite at paper/reasoning-parts/erdos1049/core.tex:293](../../paper/reasoning-parts/erdos1049/core.tex#L293-L293), [cite at paper/reasoning-parts/erdos1049/core.tex:326](../../paper/reasoning-parts/erdos1049/core.tex#L326-L326), [cite at paper/reasoning-parts/erdos1049/core.tex:477](../../paper/reasoning-parts/erdos1049/core.tex#L477-L477), [cite at paper/reasoning-parts/erdos1049/core.tex:512](../../paper/reasoning-parts/erdos1049/core.tex#L512-L513), [cite at paper/reasoning-parts/erdos1049/core.tex:836](../../paper/reasoning-parts/erdos1049/core.tex#L836-L836), [cite at paper/reasoning-parts/erdos1049/core.tex:849](../../paper/reasoning-parts/erdos1049/core.tex#L849-L849), [cite at paper/reasoning-parts/erdos1049/core.tex:1138](../../paper/reasoning-parts/erdos1049/core.tex#L1138-L1138), [cite at paper/reasoning-parts/erdos1049/core.tex:1147](../../paper/reasoning-parts/erdos1049/core.tex#L1147-L1147), [cite at paper/reasoning-parts/erdos1049/core.tex:1278](../../paper/reasoning-parts/erdos1049/core.tex#L1278-L1278), [cite at paper/reasoning-parts/erdos1049/core.tex:3271](../../paper/reasoning-parts/erdos1049/core.tex#L3271-L3271), [cite at paper/reasoning-parts/erdos1049/core.tex:3427](../../paper/reasoning-parts/erdos1049/core.tex#L3427-L3427), [cite at paper/reasoning-parts/erdos1049/core.tex:3771](../../paper/reasoning-parts/erdos1049/core.tex#L3771-L3771), [cite at paper/reasoning-parts/erdos1049/core.tex:4989](../../paper/reasoning-parts/erdos1049/core.tex#L4989-L4989), [cite at paper/reasoning-parts/erdos1049/core.tex:5031](../../paper/reasoning-parts/erdos1049/core.tex#L5031-L5031), [cite at paper/reasoning-parts/erdos1049/core.tex:5072](../../paper/reasoning-parts/erdos1049/core.tex#L5072-L5072), [cite at paper/reasoning-parts/erdos1049/core.tex:5073](../../paper/reasoning-parts/erdos1049/core.tex#L5073-L5073), [cite at paper/reasoning-parts/erdos1049/core.tex:5078](../../paper/reasoning-parts/erdos1049/core.tex#L5078-L5078), [cite at paper/reasoning-parts/erdos1049/core.tex:5225](../../paper/reasoning-parts/erdos1049/core.tex#L5225-L5225)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1478](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1478-L1478), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7435](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7435-L7435), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1278](../../paper/reasoning-parts/erdos257/a257_front.tex#L1278-L1278), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7235](../../paper/reasoning-parts/erdos257/a257_front.tex#L7235-L7235)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:943](../../paper/synthesis/optimal-sparse-perturbations.tex#L943-L943)

<a id="source-source-169c3d67838965"></a>

### [À propos de la série ∑\_{n≥1} x^n/(q^n−1)](https://numdam.org/item/JTNB_1996__8_1_173_0.pdf)

- Source id: `source-169c3d67838965`
- Author or public identity: D. Duverney
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: A smaller published rational-base region for the same series.
- Source verification: `source\_verified` — The cited passages (Théorème 2, p. 174) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Théorème 2, p. 174](https://numdam.org/item/JTNB_1996__8_1_173_0.pdf)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://numdam.org/item/JTNB_1996__8_1_173_0.pdf)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5243-L5250) — lines `5243–5250`; excerpt `sha256:2e85c59828644ad3c8fb345c8b459c4f9c86946c02a53b466028be600adf3dcf`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5212-L5219) — lines `5212–5219`; excerpt `sha256:2e85c59828644ad3c8fb345c8b459c4f9c86946c02a53b466028be600adf3dcf`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L831-L831) — lines `831–831`; excerpt `sha256:fbce7f2db65bdd8d9f109301fb1bc86d09291626cd9714baf8b44fb0defea1c4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L831-L831) — lines `831–831`; excerpt `sha256:fbce7f2db65bdd8d9f109301fb1bc86d09291626cd9714baf8b44fb0defea1c4`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:862](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L862-L862), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5057](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5057-L5057), [cite at paper/reasoning-parts/erdos1049/core.tex:831](../../paper/reasoning-parts/erdos1049/core.tex#L831-L831), [cite at paper/reasoning-parts/erdos1049/core.tex:5026](../../paper/reasoning-parts/erdos1049/core.tex#L5026-L5026)

<a id="source-source-1713b9ad6350bd"></a>

### [FormalConjectures.ErdosProblems.243](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/243.lean)

- Source id: `source-1713b9ad6350bd`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #243
- Relationship and boundary: External formal statement/corpus context cited by the paper. It is not proof authority for this repository and does not make the local result an upstream contribution.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Paper bibliography commit pin f776d2f2039351b00737ffcafb9d7d7666e1d9af; exact problem file](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/243.lean)
- [Pinned formal problem statement, not a proof.](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/243.lean)

Public implementation or evidence coordinates:

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4153-L4158) — lines `4153–4158`; excerpt `sha256:1aefcf6f7f768fe29af3e6054e3b0cd92df53c67a5b2082873142c699135431c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4114-L4119) — lines `4114–4119`; excerpt `sha256:1aefcf6f7f768fe29af3e6054e3b0cd92df53c67a5b2082873142c699135431c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L1004-L1004) — lines `1004–1004`; excerpt `sha256:adfa536049be0e74065800037ce0ba5a0d022d83f1cf5dfdd9d4c0dda34e205f`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1043-L1043) — lines `1043–1043`; excerpt `sha256:adfa536049be0e74065800037ce0ba5a0d022d83f1cf5dfdd9d4c0dda34e205f`

Paper citation usages:

- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1043](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1043-L1043), [cite at paper/reasoning-parts/erdos243/core.tex:1004](../../paper/reasoning-parts/erdos243/core.tex#L1004-L1004)

<a id="source-source-176d35cb60b651"></a>

### [On a permutation group related to ζ(2)](https://geodesic.mathdoc.fr/articles/10.4064/aa-77-1-23-56/)

- Source id: `source-176d35cb60b651`
- Author or public identity: G. Rhin, C. Viola
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Ordinary-hypergeometric antecedent of the permutation-group denominator reduction.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://geodesic.mathdoc.fr/articles/10.4064/aa-77-1-23-56/)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5266-L5271) — lines `5266–5271`; excerpt `sha256:b75b67635c18f80de0c876644a0d855886ffebd57e78291c56d2b76c6f5fe91f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5235-L5240) — lines `5235–5240`; excerpt `sha256:b75b67635c18f80de0c876644a0d855886ffebd57e78291c56d2b76c6f5fe91f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L3422-L3422) — lines `3422–3422`; excerpt `sha256:7d171ed1577013457353cdde13d778d34a71fbed4c861b7ce3d975c634196d90`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L3422-L3422) — lines `3422–3422`; excerpt `sha256:7d171ed1577013457353cdde13d778d34a71fbed4c861b7ce3d975c634196d90`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3453](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3453-L3453), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5025](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5025-L5025), [cite at paper/reasoning-parts/erdos1049/core.tex:3422](../../paper/reasoning-parts/erdos1049/core.tex#L3422-L3422), [cite at paper/reasoning-parts/erdos1049/core.tex:4994](../../paper/reasoning-parts/erdos1049/core.tex#L4994-L4994)

<a id="source-source-1a7535a5e17a8c"></a>

### [On the irrationality of Cantor and Ahmes series](https://doi.org/10.5486/PMD.2004.3254)

- Source id: `source-1a7535a5e17a8c`
- Author or public identity: J. Hančl, R. Tijdeman
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Normalised-tail form of the Erdős–Straus criterion (§§2–3, Theorem 3.1), cited for the lineage of the tails and their integer recurrence.
- Source verification: `source\_verified` — The cited passages (§§2-3 and Theorem 3.1, pp. 372-375; §§2-3 and Theorem 3.1, pp. 372-375) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [§§2-3 and Theorem 3.1, pp. 372-375](https://doi.org/10.5486/PMD.2004.3254)
- [§§2-3 and Theorem 3.1, pp. 372-375](https://doi.org/10.5486/PMD.2004.3254)
- [Sections 2–3, including the tail construction and complete proof of Theorem 3.1, printed pp. 372–375.](https://publi.math.unideb.hu/paper/982/download/10_5486_PMD_2004_3254.pdf)

Public implementation or evidence coordinates:

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1055-L1058) — lines `1055–1058`; excerpt `sha256:102b617cbf408f358626ce785399d55baf63d64228a12995ce76a5747cad8bfb`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4475-L4478) — lines `4475–4478`; excerpt `sha256:d7d4cedfe807acd8fbf6994b4c4ea185099dead717184730b0485ff8e4adf7fe`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4417-L4420) — lines `4417–4420`; excerpt `sha256:d7d4cedfe807acd8fbf6994b4c4ea185099dead717184730b0485ff8e4adf7fe`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:431](../../paper/269/erdos-269-three-prime-running-lcm.tex#L431-L431), [cite at paper/269/erdos-269-three-prime-running-lcm.tex:989](../../paper/269/erdos-269-three-prime-running-lcm.tex#L989-L989)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:363](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L363-L363), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2547](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2547-L2547), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3933](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3933-L3933), [cite at paper/reasoning-parts/erdos269/core.tex:305](../../paper/reasoning-parts/erdos269/core.tex#L305-L305), [cite at paper/reasoning-parts/erdos269/core.tex:2489](../../paper/reasoning-parts/erdos269/core.tex#L2489-L2489), [cite at paper/reasoning-parts/erdos269/core.tex:3875](../../paper/reasoning-parts/erdos269/core.tex#L3875-L3875)
- `writing-mathematics-from-reviewed-revisions`: [cite at paper/exposition/parts/revisions.tex:62](../../paper/exposition/parts/revisions.tex#L62-L62)

<a id="source-source-1b9324cc5f4641"></a>

### [Optimal bounds for an Erdős problem on matching integers to distinct multiples](https://arxiv.org/abs/2603.28636)

- Source id: `source-1b9324cc5f4641`
- Author or public identity: W. van Doorn, Y. Li, Q. Tang
- Kind: `literature`
- Problems: #243
- Relationship and boundary: Cited by the #243 long record at the lemma on blocks of consecutive multiples: Theorem 2.1 (PDF p. 2) solves Erdős Problem #650 on matching integers to distinct multiples, and the upper-bound construction of Theorem 3.1 with Claim 3.2 (PDF pp. 4–5) applies Chinese remaindering to moduli that need not be pairwise coprime. The #243 lemma assumes pairwise coprime moduli and carries its own proof; the source states nothing about Erdős #243.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- \*\*Publication identity:\*\* arXiv preprint arXiv:2603.28636v1 \[math.CO\], 8 pages, submitted 30 March 2026. The arXiv record states that the paper solves Problem #650 on Bloom's Erdős problems website.](https://arxiv.org/abs/2603.28636)
- [- \*\*Matching reformulation:\*\* PDF p. 2 recasts \`f(m)\` as the minimum, over \`A\` and \`x\`, of the maximum matching size in the bipartite graph \`G(A, x)\` joining \`a\` in \`A\` to an integer \`b\` in \`(x, x + 2a\_m)\` whenever \`a | b\`.](https://arxiv.org/abs/2603.28636)
- [- \*\*Main theorem:\*\* PDF p. 2, Theorem 2.1: \`f(m) = min(m, ceil(2 sqrt(m)))\` for every positive integer \`m\`.](https://arxiv.org/abs/2603.28636)
- [- \*\*Upper-bound construction:\*\* PDF p. 4, Theorem 3.1, proves \`f(st) \<= s + t\` with the set \`alpha\_(i,j) = M + i + jD\`; Claim 3.2, stated on the same page with its proof ending on p. 5, shows that \`gcd(alpha\_(i,j), alpha\_(k,l))\` divides \`i - k\`. PDF p. 5 applies the generalised Chinese remainder theorem to obtain \`x\_0\` congruent to \`i\` modulo every \`alpha\_(i,j)\`, stating that its compatibility condition is exactly Claim 3.2.](https://arxiv.org/abs/2603.28636)
- [Theorem 2.1](https://arxiv.org/abs/2603.28636)
- [Matching-to-distinct-multiples comparison, not a reciprocal-tail theorem.](https://arxiv.org/abs/2603.28636v1)

Public implementation or evidence coordinates:

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4140-L4144) — lines `4140–4144`; excerpt `sha256:d1521927de67d3175dadffc4db2ca2b2786b8297ec43e4eec74b73a350d2d98c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4101-L4105) — lines `4101–4105`; excerpt `sha256:d1521927de67d3175dadffc4db2ca2b2786b8297ec43e4eec74b73a350d2d98c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2908-L2908) — lines `2908–2908`; excerpt `sha256:7031adbd8ee1ddab8aa252c4d2184fcfd608e6225a7ebbe27418145af8fd95d2`

Paper citation usages:

- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2947](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2947-L2947), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2951](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2951-L2951), [cite at paper/reasoning-parts/erdos243/core.tex:2908](../../paper/reasoning-parts/erdos243/core.tex#L2908-L2908), [cite at paper/reasoning-parts/erdos243/core.tex:2912](../../paper/reasoning-parts/erdos243/core.tex#L2912-L2912)

<a id="source-source-20c650f8cf3744"></a>

### [Beweis eines Satzes von Tschebyschef](https://users.renyi.hu/~p_erdos/1932-01.pdf)

- Source id: `source-20c650f8cf3744`
- Author or public identity: P. Erdős
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Central-binomial-coefficient method behind the elementary prime bound of Appendix A.
- Source verification: `source\_verified` — The cited passages (§1, pp. 194-196) were checked against the journal offprint scan with OCR layer copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [§1, pp. 194-196](https://users.renyi.hu/~p_erdos/1932-01.pdf)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3037-L3039) — lines `3037–3039`; excerpt `sha256:e12f144375e5514cf3ca5b5c578990d0af610fa16c55c2bbfa94d6d3dc603533`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2995-L2997) — lines `2995–2997`; excerpt `sha256:e12f144375e5514cf3ca5b5c578990d0af610fa16c55c2bbfa94d6d3dc603533`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L844-L846) — lines `844–846`; excerpt `sha256:9f99ab4abb9eff1473257f6e3d761345f3ec4a6ed070161011aa5016e99df64b`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:410](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L410-L410)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2140](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2140-L2140), [cite at paper/reasoning-parts/erdos251/core.tex:2098](../../paper/reasoning-parts/erdos251/core.tex#L2098-L2098)

<a id="source-source-21738452dcb95c"></a>

### [Erdős Problems discussion thread #251](https://www.erdosproblems.com/forum/thread/251)

- Source id: `source-21738452dcb95c`
- Author or public identity: Thomas F. Bloom, Terence Tao, Joel Land
- Kind: `website\_contribution`
- Problems: #251
- Relationship and boundary: Tao's public forum post of 7 October 2025 recording the summation-by-parts reduction, and Land's posts of 6 September 2026.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://www.erdosproblems.com/forum/thread/251)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3073-L3075) — lines `3073–3075`; excerpt `sha256:2f37d7491f7db374d77d7036431632eaee02b51bfb55b4e5580d8a6e1a5e5239`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3031-L3033) — lines `3031–3033`; excerpt `sha256:2f37d7491f7db374d77d7036431632eaee02b51bfb55b4e5580d8a6e1a5e5239`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L438-L438) — lines `438–438`; excerpt `sha256:febeb70c1e1d0e553f1814d889d3b740a8e14147b23351b3b5af7b4df8b9ffd3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L438-L438) — lines `438–438`; excerpt `sha256:febeb70c1e1d0e553f1814d889d3b740a8e14147b23351b3b5af7b4df8b9ffd3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2067-L2067) — lines `2067–2067`; excerpt `sha256:648252499ac55afe59d7ced844519f662c0143a05709aa5780b718a027ea6304`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L836-L838) — lines `836–838`; excerpt `sha256:3221315fa09146b40ebe5676dd2da36df0ffdcf48a5f7e9dafca3ccc5ff205c8`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:521](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L521-L521)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:480](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L480-L480), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2110](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2110-L2110), [cite at paper/reasoning-parts/erdos251/core.tex:438](../../paper/reasoning-parts/erdos251/core.tex#L438-L438), [cite at paper/reasoning-parts/erdos251/core.tex:2068](../../paper/reasoning-parts/erdos251/core.tex#L2068-L2068)

<a id="source-source-21cdeefea4c8ec"></a>

### [Comment on Erdős Problem #269](https://www.erdosproblems.com/forum/thread/269)

- Source id: `source-21cdeefea4c8ec`
- Author or public identity: S. Fan
- Kind: `website\_contribution`
- Problems: #269
- Relationship and boundary: Public forum post of 26 June 2026 giving the two-prime factorisation, the Hecke–Mahler reduction, the transcendence conclusion and the running-LCM identity for every prime set; the papers credit it with priority for the two-prime case, whose proof in the papers was found independently.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Priority for the running-LCM identity and the repeated two-prime factorisation, reduction and conclusion.](https://www.erdosproblems.com/forum/thread/269#post-7218)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4469-L4472) — lines `4469–4472`; excerpt `sha256:1e613e1240ad72300abf67c0d0bb0f8876f0fc68cf51b5a579626af38b8177e5`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1045-L1048) — lines `1045–1048`; excerpt `sha256:38d333be83004c73220542c256f0931ce00bb2390b3a5378c76418f76b198689`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4411-L4414) — lines `4411–4414`; excerpt `sha256:1e613e1240ad72300abf67c0d0bb0f8876f0fc68cf51b5a579626af38b8177e5`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L79-L79) — lines `79–79`; excerpt `sha256:af947109aab559bea882df279e8e9f19ecaf9561d6fded648d1ef904f80ea733`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L79-L79) — lines `79–79`; excerpt `sha256:af947109aab559bea882df279e8e9f19ecaf9561d6fded648d1ef904f80ea733`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L79-L79) — lines `79–79`; excerpt `sha256:af947109aab559bea882df279e8e9f19ecaf9561d6fded648d1ef904f80ea733`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L79-L79) — lines `79–79`; excerpt `sha256:af947109aab559bea882df279e8e9f19ecaf9561d6fded648d1ef904f80ea733`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1181-L1185) — lines `1181–1185`; excerpt `sha256:b41b2811598b55fde36f7dc6b7e396d5cd3f5f9fea25411ab4689bfbf0303bb0`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:984](../../paper/systems/claim-faithful-publication-systems-paper.tex#L984-L984), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1057](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1057-L1057)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:116](../../paper/269/erdos-269-three-prime-running-lcm.tex#L116-L116), [cite at paper/269/erdos-269-three-prime-running-lcm.tex:642](../../paper/269/erdos-269-three-prime-running-lcm.tex#L642-L642)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:137](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L137-L137), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1850](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1850-L1850), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3813](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3813-L3813), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3862](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3862-L3862), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3943](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3943-L3943), [cite at paper/reasoning-parts/erdos269/core.tex:79](../../paper/reasoning-parts/erdos269/core.tex#L79-L79), [cite at paper/reasoning-parts/erdos269/core.tex:1792](../../paper/reasoning-parts/erdos269/core.tex#L1792-L1792), [cite at paper/reasoning-parts/erdos269/core.tex:3755](../../paper/reasoning-parts/erdos269/core.tex#L3755-L3755), [cite at paper/reasoning-parts/erdos269/core.tex:3804](../../paper/reasoning-parts/erdos269/core.tex#L3804-L3804), [cite at paper/reasoning-parts/erdos269/core.tex:3885](../../paper/reasoning-parts/erdos269/core.tex#L3885-L3885)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1855](../../paper/synthesis/optimal-sparse-perturbations.tex#L1855-L1855)

<a id="source-source-22aba734190d65"></a>

### [Letter to the Editor](https://www.fq.math.ca/Scanned/12-4/letter.pdf)

- Source id: `source-22aba734190d65`
- Author or public identity: P. Erdős
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Erdős's letter of 1 January 1973, which poses the full series as a conjecture and states without proof that the de-duplicated sum is irrational (p. 335).
- Source verification: `source\_verified` — The cited passages (p. 335; (no locator)) were checked against the scan copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [p. 335](https://www.fq.math.ca/Scanned/12-4/letter.pdf)
- [(no locator)](https://www.fq.math.ca/Scanned/12-4/letter.pdf)
- [Historical assertion about distinct heights, without a printed proof; not a new result of this project.](https://www.fq.math.ca/Scanned/12-4/letter.pdf)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4422-L4425) — lines `4422–4425`; excerpt `sha256:c96fc6ec675af873515b2c54bc711717a8fc43e0ef49d8237f9f330492b2bfa1`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1033-L1036) — lines `1033–1036`; excerpt `sha256:c96fc6ec675af873515b2c54bc711717a8fc43e0ef49d8237f9f330492b2bfa1`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4364-L4367) — lines `4364–4367`; excerpt `sha256:c96fc6ec675af873515b2c54bc711717a8fc43e0ef49d8237f9f330492b2bfa1`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L3832-L3832) — lines `3832–3832`; excerpt `sha256:8dbf333f1a138fb93ccef0608ac25e384cc5c3099760d92e2c9e99b5995e8837`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:94](../../paper/269/erdos-269-three-prime-running-lcm.tex#L94-L94)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:105](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L105-L105), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:650](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L650-L650), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3890](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3890-L3890), [cite at paper/reasoning-parts/erdos269/core.tex:47](../../paper/reasoning-parts/erdos269/core.tex#L47-L47), [cite at paper/reasoning-parts/erdos269/core.tex:592](../../paper/reasoning-parts/erdos269/core.tex#L592-L592), [cite at paper/reasoning-parts/erdos269/core.tex:3832](../../paper/reasoning-parts/erdos269/core.tex#L3832-L3832)

<a id="source-source-22ce74d28ddb49"></a>

### [A survey of gcd-sum functions](https://cs.uwaterloo.ca/journals/JIS/VOL13/Toth/toth10.pdf)

- Source id: `source-22ce74d28ddb49`
- Author or public identity: L. Toth
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Accessible source for the classical Pillai gcd-sum identity used in the gcd-moment rung.
- Source verification: `source\_verified` — The cited passages (Section 1, equations (1)-(2), p. 1) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Section 1, equations (1)-(2), p. 1](https://cs.uwaterloo.ca/journals/JIS/VOL13/Toth/toth10.pdf)
- [Divisor-convolution and gcd-sum context.](https://cs.uwaterloo.ca/journals/JIS/VOL13/Toth/toth10.pdf)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10314-L10319) — lines `10314–10319`; excerpt `sha256:6b26831b0198ae83ddcc51944fe34abc4a33f500ca85d17497481409ce3268b5`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10122-L10127) — lines `10122–10127`; excerpt `sha256:6b26831b0198ae83ddcc51944fe34abc4a33f500ca85d17497481409ce3268b5`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1928](../../paper/249/erdos249-totient-reasoning-surface.tex#L1928-L1929), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1736](../../paper/reasoning-parts/erdos249/a249_front.tex#L1736-L1737)

<a id="source-source-22ef36d016ca81"></a>

### [On the non-quadraticity of values of the q-exponential function and related q-series](https://doi.org/10.4064/aa136-3-4)

- Source id: `source-22ef36d016ca81`
- Author or public identity: C. Krattenthaler, I. Rochev, K. Väänänen, W. Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Bézivin's method as used by Zudilin in 2016, and the Lemma 2 and Proposition 3 argument behind his size estimate for the determinant.
- Source verification: `source\_verified` — The cited passages (Lemma 2, p. 12, and Prop. 3, p. 13; (bare cite) Bézivin's method) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Lemma 2, p. 12, and Prop. 3, p. 13](https://doi.org/10.4064/aa136-3-4)
- [(bare cite) Bézivin's method](https://doi.org/10.4064/aa136-3-4)
- [Full-text consultation: tail definition and recurrence in Section 2; leading-order comparison; Proposition 4, pp. 14--15 and derivative/root-of-unity argument culminating in (4.10), p. 17. Not an independent audit of every theorem.](https://doi.org/10.4064/aa136-3-4)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5236-L5243) — lines `5236–5243`; excerpt `sha256:037d8d669c712adb2ce488ddaad6988ca8a9e433e3271c97496d29be910f9ded`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5205-L5212) — lines `5205–5212`; excerpt `sha256:037d8d669c712adb2ce488ddaad6988ca8a9e433e3271c97496d29be910f9ded`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1332-L1339) — lines `1332–1339`; excerpt `sha256:f964675e399704b559c29b51eea44fc7fd16035cbb7bfee0f3491e3f1433945c`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1122](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1122-L1122)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1463](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1463-L1463), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1465](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1465-L1465), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3196](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3196-L3196), [cite at paper/reasoning-parts/erdos1049/core.tex:1432](../../paper/reasoning-parts/erdos1049/core.tex#L1432-L1432), [cite at paper/reasoning-parts/erdos1049/core.tex:1434](../../paper/reasoning-parts/erdos1049/core.tex#L1434-L1434), [cite at paper/reasoning-parts/erdos1049/core.tex:3165](../../paper/reasoning-parts/erdos1049/core.tex#L3165-L3165)

<a id="source-source-25efc27ed2130d"></a>

### [Guidelines for Conducting and Reporting Case Study Research in Software Engineering](https://doi.org/10.1007/s10664-008-9102-8)

- Source id: `source-25efc27ed2130d`
- Author or public identity: Per Runeson, Martin Höst
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1306-L1312) — lines `1306–1312`; excerpt `sha256:4ece33472f9eb3ee10b399b4e65ea39cee778bd9cd7f3f8e4f59aca5de46732f`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:158](../../docs/papers/mirror/plectis-public-system.tex#L158-L158), [cite at docs/papers/mirror/plectis-public-system.tex:205](../../docs/papers/mirror/plectis-public-system.tex#L205-L205), [cite at docs/papers/mirror/plectis-public-system.tex:206](../../docs/papers/mirror/plectis-public-system.tex#L206-L206)

<a id="source-source-27575f46a101c1"></a>

### [On the largest prime factors of n and n+1](https://doi.org/10.1007/BF01818569)

- Source id: `source-27575f46a101c1`
- Author or public identity: P. Erdős, C. Pomerance
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Adjacent proved dyadic irrationality theorem for a bounded indicator digit sequence.
- Source verification: `source\_verified` — The cited passages (§7; §7, p. 320) were checked against the journal offprint scan with OCR layer copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [§7](https://doi.org/10.1007/BF01818569)
- [§7, p. 320](https://doi.org/10.1007/BF01818569)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L557-L562) — lines `557–562`; excerpt `sha256:1aaf5b626bbf92fab7b69d929e63d45171a17423eceba890691f509c0a872392`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3033-L3035) — lines `3033–3035`; excerpt `sha256:b4c77ac8d585a2bd2069a38e1c79a60b2fad942e48f3b3f28ef5324369021f67`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2991-L2993) — lines `2991–2993`; excerpt `sha256:b4c77ac8d585a2bd2069a38e1c79a60b2fad942e48f3b3f28ef5324369021f67`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L520-L520) — lines `520–520`; excerpt `sha256:6145f1750639419f2be2c1cc3dd58772864138a3bf33e3321107e49b5b3fd1b3`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:562](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L562-L562), [cite at paper/reasoning-parts/erdos251/core.tex:520](../../paper/reasoning-parts/erdos251/core.tex#L520-L520)

<a id="source-source-278e74bfddddf0"></a>

### [Software Assurance and Software Safety Standard](https://standards.nasa.gov/standard/NASA/NASA-STD-87398)

- Source id: `source-278e74bfddddf0`
- Author or public identity: National Aeronautics and Space Administration
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1361-L1365) — lines `1361–1365`; excerpt `sha256:e451a824e41d073b225ae1abab1c62ca244baecf39aa9ed66d457b7b7eae3586`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:928](../../docs/papers/mirror/plectis-public-system.tex#L928-L928)

<a id="source-source-285ee90c8dcd62"></a>

### [Apéry-type approximations and irrationality measures for certain q-series](https://arxiv.org/abs/2608.26918)

- Source id: `source-285ee90c8dcd62`
- Author or public identity: J. Koizumi, A. Yokoi
- Kind: `literature`
- Problems: #243, #1049
- Relationship and boundary: Cited by the #1049 long record, where Koizumi and Yokoi identify one of their three-parameter Apéry-type approximations with the Coussement-Smet Padé approximants (Sec. 7, Prop. 7.1, p. 33). The record cites this as related work on Lambert series at reciprocal-integer base and derives nothing from it; the source states nothing about Erdős #1049.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- \*\*Publication identity:\*\* arXiv preprint arXiv:2608.26918v1 \[math.NT\], 37 pages, stamped 27 August 2026.](https://arxiv.org/abs/2608.26918)
- [- \*\*Approximation criterion:\*\* PDF p. 13, Lemma 3.4, with proof on p. 14: integer pairs \`(A\_n, B\_n)\` with \`|A\_n| + |B\_n| \<= X^(kappa n^2 + o(n^2))\` and \`0 \< |B\_n xi - A\_n| \<= X^(-lambda n^2 + o(n^2))\` make \`xi\` irrational, and a nonvanishing determinant \`A\_n B\_(n+1) - A\_(n+1) B\_n\` gives \`mu(xi) \<= 1 + kappa/lambda\`.](https://arxiv.org/abs/2608.26918)
- [- \*\*Integrality step:\*\* PDF p. 14, the proof of Lemma 3.4 uses that \`q |B\_n xi - A\_n| = |p B\_n - q A\_n|\` is a positive integer when \`xi = p/q\`.](https://arxiv.org/abs/2608.26918)
- [Sec. 7, Prop. 7.1, p. 33](https://arxiv.org/abs/2608.26918v1)
- [Version 1 full text selectively consulted: introduction and Proposition 7.1, its proof and Section 7.3. Not a whole-paper proof audit.](https://arxiv.org/abs/2608.26918v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5283-L5287) — lines `5283–5287`; excerpt `sha256:009f0d973b996ec8f00395a65152d98054ea2ab49f230fdc01672a16b260f5cc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5252-L5256) — lines `5252–5256`; excerpt `sha256:009f0d973b996ec8f00395a65152d98054ea2ab49f230fdc01672a16b260f5cc`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4982](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4982-L4982), [cite at paper/reasoning-parts/erdos1049/core.tex:4951](../../paper/reasoning-parts/erdos1049/core.tex#L4951-L4951)

<a id="source-source-296ff41148fff7"></a>

### [Regular sequences and the joint spectral radius](https://doi.org/10.1142/S0129054117500095)

- Source id: `source-296ff41148fff7`
- Author or public identity: M. Coons
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Why a basis and a redundant spanning family differ for regular sequences, and the finite-dimensional kernel span its machinery presupposes.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [\`03fbaca88796cc63f376d2e6e4680ec94632143794df871066df501b5675e7ef\`;](https://arxiv.org/abs/1511.07535)
- [127459 bytes; 5 PDF pages. A fresh download from the official arXiv v1 PDF](https://arxiv.org/abs/1511.07535)
- [\`read\_complete\` for the bound PDF. All five pages were read and visually](https://arxiv.org/abs/1511.07535)
- [- \*\*Definitions and main theorem:\*\* PDF p. 1 defines the \`k\`-kernel, calls a](https://arxiv.org/abs/1511.07535)
- [exponent and the joint spectral radius, and states \*\*Theorem 1\*\*: for a](https://arxiv.org/abs/1511.07535)
- [- \*\*Upper bound from any spanning set:\*\* PDF p. 2 notes that Theorem 1 holds](https://arxiv.org/abs/1511.07535)
- [\*\*Proposition 4\*\*: matrices associated to any spanning set of the kernel](https://arxiv.org/abs/1511.07535)
- [- \*\*Lower bound from a basis, and the comparison:\*\* PDF p. 3 states](https://arxiv.org/abs/1511.07535)
- [\*\*Corollary 7\*\*: the joint spectral radius for a basis is at most that for](https://arxiv.org/abs/1511.07535)
- [- \*\*Strictness and the evaluation argument:\*\* PDF p. 4 gives an example in](https://arxiv.org/abs/1511.07535)
- [\*\*Appendix A\*\*, which begins on the same page, shows that for a basis](https://arxiv.org/abs/1511.07535)
- [- \*\*Bibliographic boundary:\*\* PDF p. 5 completes Appendix A and gives the](https://arxiv.org/abs/1511.07535)
- [- Attribution of the theorem that, for a \`k\`-regular sequence, matrices](https://arxiv.org/abs/1511.07535)
- [- Attribution of the upper bound from any spanning set, and of the comparison](https://arxiv.org/abs/1511.07535)
- [- The evaluation argument of Appendix A (PDF p. 4): the evaluation vectors of](https://arxiv.org/abs/1511.07535)
- [Theorem 1, Proposition 4, Corollary 7 (arXiv v1), Appendix A](https://doi.org/10.1142/S0129054117500095)
- [Theorem 1, Proposition 4 and Corollary 7](https://doi.org/10.1142/S0129054117500095)
- [Theorem 1; Propositions 4 and 6; Corollary 7; Appendix A](https://arxiv.org/pdf/1511.07535v1)

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L877-L884) — lines `877–884`; excerpt `sha256:35232d77de2ddf4ba567da9e409016c66c0f5cf9a2043005e44829a8e3810ecb`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L531-L531) — lines `531–531`; excerpt `sha256:559a32bdd42dcc360fbcdc78de307cb8110fa700323e46aaf4f642fc6a1722b8`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L559-L559) — lines `559–559`; excerpt `sha256:41615846776ae56da36a07dde9a6cc5fa2f23fed4857829de243248f7460d46f`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L6902-L6902) — lines `6902–6902`; excerpt `sha256:c723c9121fa930c5c64b014b964f84584b03d698fff49666383cbf575a0e3068`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10258-L10264) — lines `10258–10264`; excerpt `sha256:de208be728552e87a1ec173f99d8429dd11fd4df8ecf144d7252710e5141acaa`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10066-L10072) — lines `10066–10072`; excerpt `sha256:de208be728552e87a1ec173f99d8429dd11fd4df8ecf144d7252710e5141acaa`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:531](../../paper/249/erdos-249-binary-totient-series.tex#L531-L531), [cite at paper/249/erdos-249-binary-totient-series.tex:560](../../paper/249/erdos-249-binary-totient-series.tex#L560-L560)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7094](../../paper/249/erdos249-totient-reasoning-surface.tex#L7094-L7094), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6902](../../paper/reasoning-parts/erdos249/a249_front.tex#L6902-L6902)

<a id="source-source-29bdada58b414a"></a>

### [Transcendence of Hecke–Mahler Series](https://people.mpi-sws.org/~joel/publications/hecke-mahler25abs.html)

- Source id: `source-29bdada58b414a`
- Author or public identity: Florian Luca, Joël Ouaknine, James Worrell
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Source-specific model for sparse differences and polynomial variation, not a theorem already covering P\_a.
- Source verification: `source\_verified` — Supplied full nine-page article, including Definition 5, Theorem 6 and proof, Theorem 8 and Claims 9–10. arXiv v2 locators cross-checked separately.
- Local mapping: `not recorded`

Exact source locations:

- [Published Definition 5, Theorems 6 and 8, Claim 10; arXiv v2 uses Definition 4, Theorems 5 and 7, Claim 9.](https://people.mpi-sws.org/~joel/publications/hecke-mahler25abs.html)

Public implementation or evidence coordinates:

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1067-L1070) — lines `1067–1070`; excerpt `sha256:c38b879eb5217d10f2aed8b52d4612ade541384e4d3e5da0fc7060cf204a573b`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4496-L4499) — lines `4496–4499`; excerpt `sha256:c38b879eb5217d10f2aed8b52d4612ade541384e4d3e5da0fc7060cf204a573b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4438-L4441) — lines `4438–4441`; excerpt `sha256:c38b879eb5217d10f2aed8b52d4612ade541384e4d3e5da0fc7060cf204a573b`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:999](../../paper/269/erdos-269-three-prime-running-lcm.tex#L999-L999)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3333](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3333-L3333), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3921](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3921-L3921), [cite at paper/reasoning-parts/erdos269/core.tex:3275](../../paper/reasoning-parts/erdos269/core.tex#L3275-L3275), [cite at paper/reasoning-parts/erdos269/core.tex:3863](../../paper/reasoning-parts/erdos269/core.tex#L3863-L3863)

<a id="source-source-29cbac966b8b76"></a>

### [An improved point-line incidence bound over arbitrary fields](https://arxiv.org/abs/1609.06284)

- Source id: `source-29cbac966b8b76`
- Author or public identity: Stevens, Sophie, de Zeeuw, Frank
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Primary arXiv PDF: Theorem 4, arXiv p. 3, and its hypotheses read; not an independent verification of the full proof. Used to delimit the incidence transfer.
- Local mapping: `not recorded`

Exact source locations:

- [Primary arXiv PDF: Theorem 4, arXiv p. 3, and its hypotheses read; not an independent verification of the full proof. Used to delimit the incidence transfer.](https://arxiv.org/abs/1609.06284)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3259-L3263) — lines `3259–3263`; excerpt `sha256:3aaa23b0ee5980d4b7a569cd8945d5e49ec49e7301ec40d1a5ab10ee81d75a3f`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3224-L3228) — lines `3224–3228`; excerpt `sha256:3aaa23b0ee5980d4b7a569cd8945d5e49ec49e7301ec40d1a5ab10ee81d75a3f`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1998](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1998-L1998), [cite at paper/reasoning-parts/erdos68/core.tex:1963](../../paper/reasoning-parts/erdos68/core.tex#L1963-L1963)

<a id="source-source-2a10c7287879c3"></a>

### [On powers of Stieltjes moment sequences, II](https://arxiv.org/abs/math/0412340v1)

- Source id: `source-2a10c7287879c3`
- Author or public identity: Christian Berg
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Existence does not imply uniqueness: factorial powers with exponent greater than two are Stieltjes indeterminate.
- Source verification: `source\_verified` — Full-text sections consulted: Theorem 5.1 and its proof, preprint printed pp. 14--15; endpoint indeterminacy. The PDF body has a later typesetting date; use the specified arXiv identifier.
- Local mapping: `not recorded`

Exact source locations:

- [Full-text sections consulted: Theorem 5.1 and its proof, preprint printed pp. 14--15; endpoint indeterminacy. The PDF body has a later typesetting date; use the specified arXiv identifier.](https://arxiv.org/abs/math/0412340v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1344-L1348) — lines `1344–1348`; excerpt `sha256:67bdfa0d9c73d3ef9074f492e01b18101ff6ce673d7d7e006e7add28eefa7c93`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5368-L5372) — lines `5368–5372`; excerpt `sha256:67bdfa0d9c73d3ef9074f492e01b18101ff6ce673d7d7e006e7add28eefa7c93`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5337-L5341) — lines `5337–5341`; excerpt `sha256:67bdfa0d9c73d3ef9074f492e01b18101ff6ce673d7d7e006e7add28eefa7c93`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1118](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1118-L1118)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2828](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2828-L2828), [cite at paper/reasoning-parts/erdos1049/core.tex:2797](../../paper/reasoning-parts/erdos1049/core.tex#L2797-L2797)

<a id="source-source-2a3af2a360bb15"></a>

### [Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partial Progress on Erdős Problem #243](https://doi.org/10.13140/RG.2.2.36612.08325)

- Source id: `source-2a3af2a360bb15`
- Author or public identity: I. O. Bado
- Kind: `literature`
- Problems: #243
- Relationship and boundary: Public preprint of September 2026 carrying the same CRT forbidden-block mechanism, overlap factor and compressed recurrence, with a compensated mass criterion; the papers state the dictionary between its notation and theirs.
- Source verification: `source\_verified` — The cited passages (Theorem 5.1, p. 4 (proof pp. 4--5); Prop. 7.1 and (16)--(20), pp. 6--7; (34), p. 9; Thm. 11.1 and Remark 11.3, p. 9) were checked against the author preprint copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 5.1, p. 4 (proof pp. 4--5)](https://doi.org/10.13140/RG.2.2.36612.08325)
- [Prop. 7.1 and (16)--(20), pp. 6--7](https://doi.org/10.13140/RG.2.2.36612.08325)
- [(34), p. 9](https://doi.org/10.13140/RG.2.2.36612.08325)
- [Thm. 11.1 and Remark 11.3, p. 9](https://doi.org/10.13140/RG.2.2.36612.08325)
- [Existing overlap in LCM coordinates, prime support and compensated mass.](https://doi.org/10.13140/RG.2.2.36612.08325)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1432-L1437) — lines `1432–1437`; excerpt `sha256:0b698c4756fa8f99456ed34f52b4cf9be3600160caf3f3dec408e04cc0d7d111`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4125-L4130) — lines `4125–4130`; excerpt `sha256:0b698c4756fa8f99456ed34f52b4cf9be3600160caf3f3dec408e04cc0d7d111`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4086-L4091) — lines `4086–4091`; excerpt `sha256:0b698c4756fa8f99456ed34f52b4cf9be3600160caf3f3dec408e04cc0d7d111`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:625](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L625-L625), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:809](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L809-L809)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1488](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1488-L1488), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1904](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1904-L1904), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3002](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3002-L3002), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3265](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3265-L3265), [cite at paper/reasoning-parts/erdos243/core.tex:1449](../../paper/reasoning-parts/erdos243/core.tex#L1449-L1449), [cite at paper/reasoning-parts/erdos243/core.tex:1865](../../paper/reasoning-parts/erdos243/core.tex#L1865-L1865), [cite at paper/reasoning-parts/erdos243/core.tex:2963](../../paper/reasoning-parts/erdos243/core.tex#L2963-L2963), [cite at paper/reasoning-parts/erdos243/core.tex:3226](../../paper/reasoning-parts/erdos243/core.tex#L3226-L3226)

<a id="source-source-2a86f52125aec0"></a>

### [Lemniscates and inequalities for the logarithmic capacities of continua (Russian: Лемниската и неравенства для логарифмической емкости континуума)](https://doi.org/10.4213/mzm2777)

- Source id: `source-2a86f52125aec0`
- Author or public identity: V. N. Dubinin
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Earlier use of the slit decomposition of the inverse Riemann surface into sheets along rays from branch points, credited before the slit-sheet theorem.
- Source verification: `source\_verified` — The cited passages (§2 (before the slit-sheet decomposition theorem)) were checked against the journal (Russian original, Mat. Zametki 80:1) copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [§2 (before the slit-sheet decomposition theorem)](https://doi.org/10.4213/mzm2777)
- [Main theorem p. 34](https://www.mathnet.ru/eng/mzm2777)
- [Inverse-sheet/ray construction §2, pp. 34–35](https://www.mathnet.ru/eng/mzm2777)
- [Corollary 1 p. 36](https://www.mathnet.ru/eng/mzm2777)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5422-L5428) — lines `5422–5428`; excerpt `sha256:2bbaf57338864a16529f3ab7d08eeeff8fb2358b4fafc7034087e3c4761985ee`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5372-L5378) — lines `5372–5378`; excerpt `sha256:2bbaf57338864a16529f3ab7d08eeeff8fb2358b4fafc7034087e3c4761985ee`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1261-L1266) — lines `1261–1266`; excerpt `sha256:b596c679afdf485909e77c3fe5c891b6e74ed84091d4e552b784d92fb5a71aff`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1079](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1079-L1079)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4514](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4514-L4514), [cite at paper/reasoning-parts/erdos1041/core.tex:4464](../../paper/reasoning-parts/erdos1041/core.tex#L4464-L4464)

<a id="source-source-2aa4970cfda278"></a>

### [On a curious property of vulgar fractions](https://doi.org/10.1080/14786441608628487)

- Source id: `source-2aa4970cfda278`
- Author or public identity: J. Farey
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5335-L5338) — lines `5335–5338`; excerpt `sha256:de50551571b8b9704ef2811a545a407c263e582e69b12f840cbb9d96750d359e`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2371](../../paper/archive/erdos249-257-main-paper.tex#L2371-L2371)

<a id="source-source-2b0038d2c239f5"></a>

### [Multigeometric sequences and Cantorvals](https://arxiv.org/abs/1304.4218v2)

- Source id: `source-2b0038d2c239f5`
- Author or public identity: Bartoszewicz, Artur, Filipczak, Ma{\\l}gorzata, Szymonik, Emilia
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — full\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L625-L627) — lines `625–627`; excerpt `sha256:362d881ea52f611773702813f66d486fe4770940533ad01c07ba24d964ad5b46`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3091-L3093) — lines `3091–3093`; excerpt `sha256:3ba50a821565d47f20a7cf904fc3290b1f3c5126a28229eafe3917129456236e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3049-L3051) — lines `3049–3051`; excerpt `sha256:3ba50a821565d47f20a7cf904fc3290b1f3c5126a28229eafe3917129456236e`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:627](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L627-L627), [cite at paper/reasoning-parts/erdos251/core.tex:585](../../paper/reasoning-parts/erdos251/core.tex#L585-L585)

<a id="source-source-2ec6bf87654604"></a>

### [Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zusammenhängende Gebiete](https://archive.org/details/sitzungsbericht1928preu)

- Source id: `source-2ec6bf87654604`
- Author or public identity: G. Pólya
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Historical source of Pólya's area inequality, cited beside the checked formulations in Crane.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1231-L1237) — lines `1231–1237`; excerpt `sha256:550b981b3e8c869d0df50cfb0dea1be1b90d0f2ad814088a1f8a1a3ac9ffade8`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5380-L5386) — lines `5380–5386`; excerpt `sha256:81544feb2d8e4a8dc89d7c14926bbdc17f7c170e2812d2e600bc764613620048`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5330-L5336) — lines `5330–5336`; excerpt `sha256:81544feb2d8e4a8dc89d7c14926bbdc17f7c170e2812d2e600bc764613620048`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L647-L647) — lines `647–647`; excerpt `sha256:e9af8055987c041e602fc36e4a30d002d7968c9be42fc2308fabbfc5f03eda0d`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L647-L647) — lines `647–647`; excerpt `sha256:e9af8055987c041e602fc36e4a30d002d7968c9be42fc2308fabbfc5f03eda0d`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L2088-L2088) — lines `2088–2088`; excerpt `sha256:513d9455ccd8f11d7bcdd4c503ae02528701d9a1e8bef30b6c9cb257b35a2b5f`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:776](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L776-L776)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1121](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1121-L1121), [cite at paper/reasoning-parts/erdos1041/core.tex:1071](../../paper/reasoning-parts/erdos1041/core.tex#L1071-L1071)

<a id="source-source-2ee394177d0f38"></a>

### [Sur certaines séries à valeur irrationnelle](https://users.renyi.hu/~p_erdos/1958-19.pdf)

- Source id: `source-2ee394177d0f38`
- Author or public identity: P. Erdős
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Origin of the fixed-denominator question and of the variable-denominator classification quoted in the long record.
- Source verification: `source\_verified` — The cited passages (p. 94; pp. 93-95 (k=1 argument); §3, pp. 96-97 (variable-denominator classification)) were checked against the journal offprint scan with OCR layer copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [p. 94](https://users.renyi.hu/~p_erdos/1958-19.pdf)
- [pp. 93-95 (k=1 argument); §3, pp. 96-97 (variable-denominator classification)](https://users.renyi.hu/~p_erdos/1958-19.pdf)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L808-L810) — lines `808–810`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3029-L3031) — lines `3029–3031`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2987-L2989) — lines `2987–2989`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L30-L30) — lines `30–30`; excerpt `sha256:9ac9f5c746a4ed69413e2f364cc0753ee3aa969eb39b5d87a0c1c8e8d6797e46`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L30-L30) — lines `30–30`; excerpt `sha256:9ac9f5c746a4ed69413e2f364cc0753ee3aa969eb39b5d87a0c1c8e8d6797e46`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L30-L30) — lines `30–30`; excerpt `sha256:9ac9f5c746a4ed69413e2f364cc0753ee3aa969eb39b5d87a0c1c8e8d6797e46`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:52](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L52-L52)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:72](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L72-L72), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:532](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L532-L532), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:546](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L546-L546), [cite at paper/reasoning-parts/erdos251/core.tex:30](../../paper/reasoning-parts/erdos251/core.tex#L30-L30), [cite at paper/reasoning-parts/erdos251/core.tex:490](../../paper/reasoning-parts/erdos251/core.tex#L490-L490), [cite at paper/reasoning-parts/erdos251/core.tex:504](../../paper/reasoning-parts/erdos251/core.tex#L504-L504)

<a id="source-source-3068a3586a5e8b"></a>

### [On equal products of consecutive integers](https://ems.press/content/serial-article-files/53738)

- Source id: `source-3068a3586a5e8b`
- Author or public identity: Nguyen Xuan Tho
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Primary six-page journal PDF: Theorem 1, context and Section 2 proof consulted; first and third pages inspected as images. This is an established special case, not a general solution.
- Local mapping: `not recorded`

Exact source locations:

- [Primary six-page journal PDF: Theorem 1, context and Section 2 proof consulted; first and third pages inspected as images. This is an established special case, not a general solution.](https://ems.press/content/serial-article-files/53738)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3267-L3271) — lines `3267–3271`; excerpt `sha256:0237824e9b1bc6846e06ebc8479034b15e0574bcf800f0b614d1d0a682ca52bb`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3232-L3236) — lines `3232–3236`; excerpt `sha256:0237824e9b1bc6846e06ebc8479034b15e0574bcf800f0b614d1d0a682ca52bb`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2106](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2106-L2106), [cite at paper/reasoning-parts/erdos68/core.tex:2071](../../paper/reasoning-parts/erdos68/core.tex#L2071-L2071)

<a id="source-source-317a740451ce03"></a>

### [Refinement of the Chowla--Erdős method and linear independence of certain Lambert series](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)

- Source id: `source-317a740451ce03`
- Author or public identity: D. Duverney, Y. Tachiya
- Kind: `literature`
- Problems: #249, #257, #1049
- Relationship and boundary: Attribution to Duverney and Tachiya of the linear-independence theorem for Lambert series over \`F\_s(E)\` under \`|q| L \<= s\`, PDF p. 4, Corollary 1.2, with proof on pp. 10–11. - Attribution of the squarefree specialisation \`F\_2(primes)\` and the independent family at bases \`2^j\`, PDF p. 4, Example 1.1. - The divisibility/growth hypotheses and the support construction that make the specialisation applicable, PDF pp. 3–4 and 10–11. - The publication identity, official retrieval route, exact digest, and page-level locators recorded above.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [81,546 bytes; 11 PDF pages. It was retrieved from the author route and](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [pages 4 and 10 were also visually checked at the theorem/example and proof](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [- \*\*Main irrationality mechanism:\*\* PDF pp. 2–3, Theorem 1.1, assumes the](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [PDF p. 3, Theorem 1.2, lifts this to linear dependence among finitely](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [- \*\*Support-family definitions:\*\* PDF p. 3, equation (1.11), defines](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [- \*\*Exact #257-relevant corollary:\*\* PDF p. 4, Corollary 1.2, states that if](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [- \*\*Concrete squarefree family:\*\* PDF p. 4, Example 1.1, writes the](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [linear independence. The proof of Corollary 1.2 is on PDF pp. 10–11;](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [- \*\*Conjectural context:\*\* PDF p. 4 recalls the Erdős–Graham conjecture for](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [arbitrary increasing supports and says Corollary 1.2 gives irrationality](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [- \*\*End matter:\*\* PDF p. 11 records the references and acknowledgments,](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [- Attribution to Duverney and Tachiya of the linear-independence theorem for](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [Lambert series over \`F\_s(E)\` under \`|q| L \<= s\`, PDF p. 4, Corollary 1.2,](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [independent family at bases \`2^j\`, PDF p. 4, Example 1.1.](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [the specialisation applicable, PDF pp. 3–4 and 10–11.](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [- Any theorem about the Euler-totient series or the #249 totient kernel.](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [Comparator theorem names, totient-kernel rank/basis statements, Erdős #249,](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [the \`q=2\`, \`s=2\`, \`ell=1\` specialisation above, not a universal-base theorem.](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [- \*\*Index selection by averaging:\*\* PDF pp. 5–6, Section 2, proof of](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [Thms. 1.1--1.2, pp. 2--3](https://doi.org/10.1515/forum-2018-0299)
- [p. 3](https://doi.org/10.1515/forum-2018-0299)
- [Section 2, (2.3)-(2.9), pp. 5-6; p. 4](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [p. 2](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [Theorem 1.1, author pp. 2–3; Corollary 1.2 and Example 1.1, p. 4; Section 2, (2.3)–(2.9), pp. 5–6.](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)
- [Complete supplied author manuscript; Theorems 1.1--1.2, Corollary 1.1, and integral-tail/nontermination proof.](https://doi.org/10.1515/forum-2018-0299)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5380-L5388) — lines `5380–5388`; excerpt `sha256:64ec02486225f54bf2dfac8b56940d1a93a770185477df524459a057b87a721e`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1641-L1648) — lines `1641–1648`; excerpt `sha256:0ef99b680f15dcdcdc4890932040fe1bad3f3ee018e801c7204dea8bae0d1b51`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1066-L1066) — lines `1066–1066`; excerpt `sha256:e8f0eb9c08b32d040eb9d382b55721fcbada06cfa90efaa2936a851eae07396b`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L976-L976) — lines `976–976`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8381-L8381) — lines `8381–8381`; excerpt `sha256:53ca69e59ff43d0292ca42e7954e5800d1314c64e4be23c03c224c016e357b49`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8539-L8539) — lines `8539–8539`; excerpt `sha256:1197efd3480c3d18971ff7587e64c3696907146bd64660e41bda3a5ac9fbd8f2`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8943-L8943) — lines `8943–8943`; excerpt `sha256:b02d5126a31d6f516b011882cd7b77604eb511797cbc09d89912554f44c242e9`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1008-L1008) — lines `1008–1008`; excerpt `sha256:9221d992894d2f2ad88d52adc3a37360730affc1220f1d1730cef4677b6f31ce`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1008-L1008) — lines `1008–1008`; excerpt `sha256:9221d992894d2f2ad88d52adc3a37360730affc1220f1d1730cef4677b6f31ce`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1008-L1008) — lines `1008–1008`; excerpt `sha256:9221d992894d2f2ad88d52adc3a37360730affc1220f1d1730cef4677b6f31ce`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L520-L520) — lines `520–520`; excerpt `sha256:1ed1ce69c8bf73f3362ff5a2aca04fe7d02e4cc4dbe0784bc0f09ca0a22ad778`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5298-L5305) — lines `5298–5305`; excerpt `sha256:d84745edafcc3ae3ed868569f0e1e327404f0c2a6ff86a0c327422d4a6ddbebd`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5267-L5274) — lines `5267–5274`; excerpt `sha256:d84745edafcc3ae3ed868569f0e1e327404f0c2a6ff86a0c327422d4a6ddbebd`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9650-L9665) — lines `9650–9665`; excerpt `sha256:639844231444857a119025ab8e330a05e28514cf1dc9e9c65fdc92da1d687928`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9450-L9465) — lines `9450–9465`; excerpt `sha256:639844231444857a119025ab8e330a05e28514cf1dc9e9c65fdc92da1d687928`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1313-L1320) — lines `1313–1320`; excerpt `sha256:1efaad4cfc934457449068fdeec1040f4a4c014a88951973ae9338a1d554132d`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:821](../../paper/systems/claim-faithful-publication-systems-paper.tex#L821-L821), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1056](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1056-L1056)
- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1181](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1181-L1181)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:273](../../paper/257/erdos-257-mersenne-support-subseries.tex#L273-L273), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:865](../../paper/257/erdos-257-mersenne-support-subseries.tex#L865-L865), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1008](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1008-L1008)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5009](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5009-L5009), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5010](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5010-L5010), [cite at paper/reasoning-parts/erdos1049/core.tex:4978](../../paper/reasoning-parts/erdos1049/core.tex#L4978-L4978), [cite at paper/reasoning-parts/erdos1049/core.tex:4979](../../paper/reasoning-parts/erdos1049/core.tex#L4979-L4979)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:738](../../paper/archive/erdos249-257-main-paper.tex#L738-L738)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1480](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1480-L1480), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3286](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3286-L3286), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1280](../../paper/reasoning-parts/erdos257/a257_front.tex#L1280-L1280), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:3086](../../paper/reasoning-parts/erdos257/a257_front.tex#L3086-L3086)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1986](../../paper/synthesis/optimal-sparse-perturbations.tex#L1986-L1987)

<a id="source-source-318b37ba5af2eb"></a>

### [A theorem on irrationality of infinite series and applications](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)

- Source id: `source-318b37ba5af2eb`
- Author or public identity: C. Badea
- Kind: `literature`
- Problems: #243
- Relationship and boundary: Eventual-equality criterion for positive terms (Corollary 2.2, p. 316), which Koizumi's Proposition 1(2) reinterprets, and the comparator for the coefficient-uniform variant.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [# C. Badea source closure: A theorem on irrationality of infinite series](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [- \*\*Author and title:\*\* C. Badea, \*A theorem on irrationality of infinite](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [- \*\*Official routes:\*\* the \[IMPAN publication record\](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/63/4/107785/a-theorem-on-irrationality-of-infinite-series-and-applications), which labels the article “Free download under CC-BY license,” and the \[publisher-hosted PDF\](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf).](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [150131 bytes; 11 pages, printed pp. 313–323. It remains a local](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [title and Theorem A (printed p. 313), Theorem 2.1/2.10 and Corollary 2.2](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [(printed pp. 314–316), the applications (printed pp. 317–322), and the](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [references/end matter (printed pp. 322–323) were visually checked. The](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [publisher-layout PDF is legible; printed page numbers are the locators used](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [- \*\*Theorem A:\*\* printed p. 313. For convergent series of positive rational](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [- \*\*General comparison theorem:\*\* printed pp. 314–316, Theorem 2.1 and](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [Theorem 2.10. The paper defines block products \`S\_k(N)\` and weighted block](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [- \*\*Direct corollary:\*\* printed p. 316, Corollary 2.2. For a rational](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [- \*\*Applications:\*\* printed pp. 317–319, Corollaries 3.2 and 3.4 apply the](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [and Oppenheim-expansion consequences. Printed pp. 322–323 contain the](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [- The exact positive-rational-series inequality/equality criterion in Theorem](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [A, Theorem 2.10, and Corollary 2.2, with the printed locators above.](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [- The fact that Badea's 1993 theorem generalizes the positive-term Sylvester](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [The complete article (printed pp. 313–323) was checked for Lean declarations,](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [the release's theorem names, an unrestricted proof of #243, and any claim](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [Corollary 2.2, p. 316](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)
- [Positive coefficient descent predecessor, not arbitrary signed centred-error rigidity.](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1414-L1419) — lines `1414–1419`; excerpt `sha256:ee897c806cc6764f8001bdbab28ecd44a7ae784f93c8b76cdca0c229578e334b`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4100-L4105) — lines `4100–4105`; excerpt `sha256:ee897c806cc6764f8001bdbab28ecd44a7ae784f93c8b76cdca0c229578e334b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4061-L4066) — lines `4061–4066`; excerpt `sha256:ee897c806cc6764f8001bdbab28ecd44a7ae784f93c8b76cdca0c229578e334b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L1653-L1653) — lines `1653–1653`; excerpt `sha256:2df19ae3d0b16a50ae460b309f4d509936436c1b79c214baa753b21bb87891dd`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1005](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1005-L1005)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:952](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L952-L953), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1692](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1692-L1692), [cite at paper/reasoning-parts/erdos243/core.tex:913](../../paper/reasoning-parts/erdos243/core.tex#L913-L914), [cite at paper/reasoning-parts/erdos243/core.tex:1653](../../paper/reasoning-parts/erdos243/core.tex#L1653-L1653)

<a id="source-source-318ee5e7cf6d74"></a>

### [Bad Polynomials for Newton's Method](https://www.math.stonybrook.edu/preprints/ims92-7.pdf)

- Source id: `source-318ee5e7cf6d74`
- Author or public identity: S. Sutherland
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Historical terminology for the Newton flow and its radial value lines (p. 42).
- Source verification: `source\_verified` — The cited passages (p. 42) were checked against the IMS preprint volume 1992/7 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [p. 42](https://www.math.stonybrook.edu/preprints/ims92-7.pdf)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5405-L5410) — lines `5405–5410`; excerpt `sha256:620501b65c595f397bcb8546b8f32f2dc7376a436f617b51b629ce031def07e1`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5355-L5360) — lines `5355–5360`; excerpt `sha256:620501b65c595f397bcb8546b8f32f2dc7376a436f617b51b629ce031def07e1`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4193-L4193) — lines `4193–4193`; excerpt `sha256:018d096210a7ffec3eb82decf527d824cd58c2bd4eb4f692250cc5c4b2b8caa9`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4243](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4243-L4243), [cite at paper/reasoning-parts/erdos1041/core.tex:4193](../../paper/reasoning-parts/erdos1041/core.tex#L4193-L4193)

<a id="source-source-3479bad7869d7c"></a>

### [A determinant identity for moments of orthogonal polynomials that implies Uvarov's formula for the orthogonal polynomials of rationally related densities](https://arxiv.org/abs/2103.03969v1)

- Source id: `source-3479bad7869d7c`
- Author or public identity: Christian Krattenthaler
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Formal moment-functional determinant transformations do not by themselves provide a positive measure for the new coefficient sequence.
- Source verification: `source\_verified` — Full-text consultation of the 20-page version 1, especially Theorem 1, pp. 2--3, Sections 2, 4 and 6, and Proposition 13.
- Local mapping: `not recorded`

Exact source locations:

- [Full-text consultation of the 20-page version 1, especially Theorem 1, pp. 2--3, Sections 2, 4 and 6, and Proposition 13.](https://arxiv.org/abs/2103.03969v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5348-L5353) — lines `5348–5353`; excerpt `sha256:58eae42e166b8f8a536b9cfe4c4577e41e70667815b654f00bc6a6c1c848d0dc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5317-L5322) — lines `5317–5322`; excerpt `sha256:58eae42e166b8f8a536b9cfe4c4577e41e70667815b654f00bc6a6c1c848d0dc`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3058](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3058-L3058), [cite at paper/reasoning-parts/erdos1049/core.tex:3027](../../paper/reasoning-parts/erdos1049/core.tex#L3027-L3027)

<a id="source-source-34b520c561ee3c"></a>

### [Character sums and congruences with n!](https://arxiv.org/abs/math/0403422)

- Source id: `source-34b520c561ee3c`
- Author or public identity: M. Z. Garaev, F. Luca, I. E. Shparlinski
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Factorial-congruence multiplicity bound (Theorem 12, arXiv v1 p. 16) behind the superseded lcm deduction in the long record.
- Source verification: `source\_verified` — The cited passages (arXiv v1, Thm. 12, p. 16) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [arXiv v1, Thm. 12, p. 16](https://doi.org/10.1090/S0002-9947-04-03612-8)
- [Full text consulted at Theorem 12 and its proof, arXiv v1 p. 16. This is not journal pagination. The joint-fibre inequality is an adaptation written out in the return, not the statement of Theorem 12.](https://arxiv.org/pdf/math/0403422v1)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3175-L3179) — lines `3175–3179`; excerpt `sha256:0758379961a43fb0431ee76d95c75e47c003353f90b6a707964f44a842f3ea87`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3140-L3144) — lines `3140–3144`; excerpt `sha256:0758379961a43fb0431ee76d95c75e47c003353f90b6a707964f44a842f3ea87`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1061-L1061) — lines `1061–1061`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1061-L1061) — lines `1061–1061`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1061-L1061) — lines `1061–1061`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1061-L1061) — lines `1061–1061`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3140-L3144) — lines `3140–3144`; excerpt `sha256:0758379961a43fb0431ee76d95c75e47c003353f90b6a707964f44a842f3ea87`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1096](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1096-L1096), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2058](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2058-L2058), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2320](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2320-L2320), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2692](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2692-L2692), [cite at paper/reasoning-parts/erdos68/core.tex:1061](../../paper/reasoning-parts/erdos68/core.tex#L1061-L1061), [cite at paper/reasoning-parts/erdos68/core.tex:2023](../../paper/reasoning-parts/erdos68/core.tex#L2023-L2023), [cite at paper/reasoning-parts/erdos68/core.tex:2285](../../paper/reasoning-parts/erdos68/core.tex#L2285-L2285), [cite at paper/reasoning-parts/erdos68/core.tex:2657](../../paper/reasoning-parts/erdos68/core.tex#L2657-L2657)

<a id="source-source-365c2b5cf46ebe"></a>

### [Factorial residues modulo a prime: beyond the square-root bound](https://arxiv.org/html/2608.01781v1)

- Source id: `source-365c2b5cf46ebe`
- Author or public identity: Xiyu Hu
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Entire arXiv HTML text read, including Theorem 1.1 and the transition-map/incidence argument. Recent preprint; not treated as peer-reviewed or Lean-verified.
- Local mapping: `not recorded`

Exact source locations:

- [Entire arXiv HTML text read, including Theorem 1.1 and the transition-map/incidence argument. Recent preprint; not treated as peer-reviewed or Lean-verified.](https://arxiv.org/html/2608.01781v1)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3235-L3239) — lines `3235–3239`; excerpt `sha256:c81f5719e7e0059427c6fe7295699d3523c4215f7fe430b755be834cb594cfe9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3200-L3204) — lines `3200–3204`; excerpt `sha256:c81f5719e7e0059427c6fe7295699d3523c4215f7fe430b755be834cb594cfe9`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1983](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1983-L1983), [cite at paper/reasoning-parts/erdos68/core.tex:1948](../../paper/reasoning-parts/erdos68/core.tex#L1948-L1948)

<a id="source-source-36f533b76bc247"></a>

### [Prove2Me: An Open Collaborative Platform for Scaling Math Formalization](https://arxiv.org/abs/2608.28433)

- Source id: `source-36f533b76bc247`
- Author or public identity: Shuze Chen, Kunal Marwaha, Xiaoyang Lu, Henry Yuen, Tianyi Peng
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by both public systems papers as the prior published design of an open agent-native formalisation platform (arXiv v1 28 August 2026, three days before the strategy paper's first public version) and as independent concurrent work for the systems paper (first public July 2026): statement/proof separation, exact-type proof submission, audited mission cores, proof-sketch decomposition, reusable library with reuse credit, and sub-agent read-back. Neither paper claims priority over it.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1707-L1712) — lines `1707–1712`; excerpt `sha256:c89d595871311eec76167add03b720a82202963564fd46493036b4e96b08de98`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1189-L1193) — lines `1189–1193`; excerpt `sha256:f1a3aeaeeeae0343e3ac3f2056c0987792e2a1fcc155d61514b74881c3a74206`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:111](../../paper/systems/claim-faithful-publication-systems-paper.tex#L111-L111), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:597](../../paper/systems/claim-faithful-publication-systems-paper.tex#L597-L597), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:597](../../paper/systems/claim-faithful-publication-systems-paper.tex#L597-L597), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:601](../../paper/systems/claim-faithful-publication-systems-paper.tex#L601-L601), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1049](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1049-L1049)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:898](../../paper/systems/open-source-mathematics-strategy.tex#L898-L898), [cite at paper/systems/open-source-mathematics-strategy.tex:940](../../paper/systems/open-source-mathematics-strategy.tex#L940-L940), [cite at paper/systems/open-source-mathematics-strategy.tex:1028](../../paper/systems/open-source-mathematics-strategy.tex#L1028-L1028)

<a id="source-source-39690ee8e07b0c"></a>

### [On the law of the iterated logarithm. I](https://www.renyi.hu/~p_erdos/1955-06.pdf)

- Source id: `source-39690ee8e07b0c`
- Author or public identity: P. Erdos, I. S. Gal
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Almost-everywhere law of the iterated logarithm behind the heuristic block-sum size, which gives nothing at the particular phase.
- Source verification: `source\_verified` — The cited passages (p. 65) were checked against the scan copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [p. 65](https://www.renyi.hu/~p_erdos/1955-06.pdf)
- [Metric lacunary background, not a theorem about this fixed constant.](https://www.renyi.hu/~p_erdos/1955-06.pdf)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10390-L10394) — lines `10390–10394`; excerpt `sha256:e8efab4ceb7a738eebd6f794631df1b61792fb0a00d2d6d557380dd4e37f9c41`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10198-L10202) — lines `10198–10202`; excerpt `sha256:e8efab4ceb7a738eebd6f794631df1b61792fb0a00d2d6d557380dd4e37f9c41`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8165](../../paper/249/erdos249-totient-reasoning-surface.tex#L8165-L8165), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7973](../../paper/reasoning-parts/erdos249/a249_front.tex#L7973-L7973)

<a id="source-source-39e4fc546549fd"></a>

### [Common Factors in Fraction-Free Matrix Decompositions](https://arxiv.org/abs/2005.12380v1)

- Source id: `source-39e4fc546549fd`
- Author or public identity: Johannes Middeke, David J. Jeffrey, Christoph Koutschan
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Distinguish systematic entry/row factors from extra determinant cancellation and keep the coefficient ring explicit.
- Source verification: `source\_verified` — Full-text Section 2, Algorithm 2 and Theorem 6 on systematic factors and Smith determinantal divisors. Published online 2020; cited by the 2021 issue year.
- Local mapping: `not recorded`

Exact source locations:

- [Full-text Section 2, Algorithm 2 and Theorem 6 on systematic factors and Smith determinantal divisors. Published online 2020; cited by the 2021 issue year.](https://arxiv.org/abs/2005.12380v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5388-L5394) — lines `5388–5394`; excerpt `sha256:bd367f3dba72019c86ec01aacbc2dc2ba3af36d5b42d189d2c16647299c55964`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5357-L5363) — lines `5357–5363`; excerpt `sha256:bd367f3dba72019c86ec01aacbc2dc2ba3af36d5b42d189d2c16647299c55964`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3189](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3189-L3189), [cite at paper/reasoning-parts/erdos1049/core.tex:3158](../../paper/reasoning-parts/erdos1049/core.tex#L3158-L3158)

<a id="source-source-3bc828513b4d63"></a>

### [Mahler series with multiplicative coefficient sequences](https://doi.org/10.48550/arXiv.2603.23456)

- Source id: `source-3bc828513b4d63`
- Author or public identity: J. Bell, D. Smertnig
- Kind: `literature`
- Problems: #1049, #249, #257
- Relationship and boundary: Single-base Mahler obstruction for the divisor generating series (Theorem 1.3 and its consequences on p. 3).
- Source verification: `source\_verified` — Direct primary-source readback verified the authors, title, Theorem 1.3 statement and its explicitly stated divisor-function consequence in the introduction. This is source verification, not an independent proof audit, Lean formalization, novelty review, or claim of local adoption.
- Local mapping: `exact\_bibliographic\_use` — The current short and long #1049 functional-equation discussions cite the same external scalar exclusion; archived uses remain historical.

Exact source locations:

- [Introduction, Theorem 1.3 on p. 2 and divisor-function consequence on p. 3; authors’ public PDF inspected 12 September 2026.](https://math.smertnig.at/paper/multiplicative-mahler.pdf)
- [Thm. 1.3 and the consequences on p. 3](https://arxiv.org/abs/2603.23456v1)
- [Thm. 2.5, p. 5](https://arxiv.org/abs/2603.23456v1)
- [Theorem 1.3, p. 2; totient example, p. 3; Lemma 3.3 and proof, p. 9](https://arxiv.org/pdf/2603.23456v1)
- [Version 1 full text selectively consulted: Theorem 1.3, pp. 2--3 and its explicit divisor/totient consequences. Not a whole-paper proof audit.](https://arxiv.org/abs/2603.23456v1)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5355-L5360) — lines `5355–5360`; excerpt `sha256:b3f91ee983a8672978d0cb4683a9eac57121a743ff8449aa943c718486e5f24d`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1302-L1308) — lines `1302–1308`; excerpt `sha256:f7f8625de08bee4472f7198ac41b6132a598c68fb4f2c5d046fbf4555082ef4d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4721-L4721) — lines `4721–4721`; excerpt `sha256:9c2a91a02fdf0d919533a27cf6d9347afee25f7427ccbde7d620a561bd32d9e8`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4752-L4752) — lines `4752–4752`; excerpt `sha256:9c2a91a02fdf0d919533a27cf6d9347afee25f7427ccbde7d620a561bd32d9e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5291-L5297) — lines `5291–5297`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5322-L5328) — lines `5322–5328`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L924-L928) — lines `924–928`; excerpt `sha256:a596a5a3ab90688c2d2e40605ef4e488e6632133e5a12a5f09f3821c37ac1dbd`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10405-L10409) — lines `10405–10409`; excerpt `sha256:a596a5a3ab90688c2d2e40605ef4e488e6632133e5a12a5f09f3821c37ac1dbd`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10213-L10217) — lines `10213–10217`; excerpt `sha256:a596a5a3ab90688c2d2e40605ef4e488e6632133e5a12a5f09f3821c37ac1dbd`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5322-L5328) — lines `5322–5328`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5291-L5297) — lines `5291–5297`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1190](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1190-L1190)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:543](../../paper/249/erdos-249-binary-totient-series.tex#L543-L543)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4677](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4677-L4677), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5265](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5265-L5265), [cite at paper/reasoning-parts/erdos1049/core.tex:4646](../../paper/reasoning-parts/erdos1049/core.tex#L4646-L4646), [cite at paper/reasoning-parts/erdos1049/core.tex:5234](../../paper/reasoning-parts/erdos1049/core.tex#L5234-L5234)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3181](../../paper/archive/erdos249-257-main-paper.tex#L3181-L3181)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:10212](../../paper/249/erdos249-totient-reasoning-surface.tex#L10212-L10212), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:10020](../../paper/reasoning-parts/erdos249/a249_front.tex#L10020-L10020)

<a id="source-source-3d300ccd5e4cbb"></a>

### [A dynamical proof of the van der Corput inequality](https://doi.org/10.1080/14689367.2022.2100244)

- Source id: `source-3d300ccd5e4cbb`
- Author or public identity: N. Edeko, H. Kreidler, R. Nagel
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Dynamical proof of the van der Corput inequality, cited where the papers correct the description of what the inequality requires.
- Source verification: `source\_verified` — The cited passages (Theorem 2.1, p. 4 (arXiv v3)) were checked against the arXiv v3 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 2.1, p. 4 (arXiv v3)](https://doi.org/10.1080/14689367.2022.2100244)
- [A differencing tool, not a substitute for the missing correlation estimate.](https://arxiv.org/abs/2106.11835v3)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10357-L10363) — lines `10357–10363`; excerpt `sha256:5ea3e979eefb577068ea145beb2c4d5913b323a0f5a413f315280b716ec5eb58`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10165-L10171) — lines `10165–10171`; excerpt `sha256:5ea3e979eefb577068ea145beb2c4d5913b323a0f5a413f315280b716ec5eb58`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8057](../../paper/249/erdos249-totient-reasoning-surface.tex#L8057-L8057), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7865](../../paper/reasoning-parts/erdos249/a249_front.tex#L7865-L7865)

<a id="source-source-3fb9e4907eec24"></a>

### [On the greatest and least prime factors of n!+1](https://www.renyi.hu/~p_erdos/1976-27.pdf)

- Source id: `source-3fb9e4907eec24`
- Author or public identity: Paul Erdős, Cameron L. Stewart
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — All seven pages inspected in page images; in particular p. 514, (5) on p. 515, and §3, pp. 516–517. Historical spacing mechanism, not an lcm theorem.
- Local mapping: `not recorded`

Exact source locations:

- [All seven pages inspected in page images; in particular p. 514, (5) on p. 515, and §3, pp. 516–517. Historical spacing mechanism, not an lcm theorem.](https://www.renyi.hu/~p_erdos/1976-27.pdf)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3184-L3188) — lines `3184–3188`; excerpt `sha256:01afe33226c434943312f632a5b1272516885eec61dfda3c99448c38f71ab1f1`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3219-L3223) — lines `3219–3223`; excerpt `sha256:01afe33226c434943312f632a5b1272516885eec61dfda3c99448c38f71ab1f1`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3184-L3188) — lines `3184–3188`; excerpt `sha256:01afe33226c434943312f632a5b1272516885eec61dfda3c99448c38f71ab1f1`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1027](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1027-L1027), [cite at paper/reasoning-parts/erdos68/core.tex:992](../../paper/reasoning-parts/erdos68/core.tex#L992-L992)

<a id="source-source-40bc4064b92788"></a>

### [The area of polynomial images and preimages](https://arxiv.org/abs/math/0302189)

- Source id: `source-40bc4064b92788`
- Author or public identity: E. Crane
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Formulations of Pólya's disc-preimage area inequality (Theorem 1), the area–capacity inequality (Theorem 6) and the preimage capacity identity (Section 2).
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Theorems 2 and 3 give the measurable-set preimage area inequality and the stronger multiplicity integral inequality, with equality cases.](https://arxiv.org/abs/math/0302189)
- [Theorem 1 (area bound in the 71/10 proof)](https://doi.org/10.1112/S0024609304003509)
- [Theorem 6 (area–capacity step in the separation proof)](https://doi.org/10.1112/S0024609304003509)
- [Theorem 1 (four places)](https://doi.org/10.1112/S0024609304003509)
- [Theorem 6 (capacity-defect corollary; separation proof)](https://doi.org/10.1112/S0024609304003509)
- [§2 (capacity identity for polynomial preimages)](https://doi.org/10.1112/S0024609304003509)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5386-L5392) — lines `5386–5392`; excerpt `sha256:428989f59406f939d2c86c6f7824295f410f97de0a786684b7faeddbd01f4a71`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5336-L5342) — lines `5336–5342`; excerpt `sha256:428989f59406f939d2c86c6f7824295f410f97de0a786684b7faeddbd01f4a71`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1187-L1193) — lines `1187–1193`; excerpt `sha256:cd02a3f4bd4ab2831d4e82f0258f2e99b98627ee1ba71dc7fcd33aaae61f7342`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:543](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L543-L543), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:777](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L777-L777)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:697](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L697-L697), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1121](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1121-L1121), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1244](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1244-L1244), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1413](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1413-L1413), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1486](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1486-L1486), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1665](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1665-L1665), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1665](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1665-L1665), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2002](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2002-L2002), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2190](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2190-L2190), [cite at paper/reasoning-parts/erdos1041/core.tex:647](../../paper/reasoning-parts/erdos1041/core.tex#L647-L647), [cite at paper/reasoning-parts/erdos1041/core.tex:1071](../../paper/reasoning-parts/erdos1041/core.tex#L1071-L1071), [cite at paper/reasoning-parts/erdos1041/core.tex:1194](../../paper/reasoning-parts/erdos1041/core.tex#L1194-L1194), [cite at paper/reasoning-parts/erdos1041/core.tex:1363](../../paper/reasoning-parts/erdos1041/core.tex#L1363-L1363), [cite at paper/reasoning-parts/erdos1041/core.tex:1436](../../paper/reasoning-parts/erdos1041/core.tex#L1436-L1436), [cite at paper/reasoning-parts/erdos1041/core.tex:1615](../../paper/reasoning-parts/erdos1041/core.tex#L1615-L1615), [cite at paper/reasoning-parts/erdos1041/core.tex:1615](../../paper/reasoning-parts/erdos1041/core.tex#L1615-L1615), [cite at paper/reasoning-parts/erdos1041/core.tex:1952](../../paper/reasoning-parts/erdos1041/core.tex#L1952-L1952), [cite at paper/reasoning-parts/erdos1041/core.tex:2140](../../paper/reasoning-parts/erdos1041/core.tex#L2140-L2140)

<a id="source-source-41df26fdff66cb"></a>

### [On the irrationality of certain super-polynomially decaying series](https://arxiv.org/abs/2504.18712v1)

- Source id: `source-41df26fdff66cb`
- Author or public identity: Tonći Crmarić, Vjekoslav Kovač
- Kind: `literature`
- Problems: #243, #251, #249
- Relationship and boundary: Full text of the specified source object/passage was read; this is not independent refereeing of the complete article. The round8 signed interpolation also credits the finite-choice interval covering principle in Lemma4(a)/Remark5; the proof supplies its own packet overlap and moment cancellation estimates.
- Source verification: `source\_verified` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Theorems 1 and 2, arXiv pp. 2–3](https://arxiv.org/abs/2504.18712v1)
- [Construction and measure arguments, §§2–3](https://arxiv.org/abs/2504.18712v1)
- [Version1 section2 Lemma4(a) and Remark5.](https://arxiv.org/abs/2504.18712v1)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1472-L1478) — lines `1472–1478`; excerpt `sha256:94123b672bbe246ca5a1da5c42f627ccc32ae5d9d6727e40019a7798db0120de`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4174-L4180) — lines `4174–4180`; excerpt `sha256:94123b672bbe246ca5a1da5c42f627ccc32ae5d9d6727e40019a7798db0120de`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4135-L4141) — lines `4135–4141`; excerpt `sha256:94123b672bbe246ca5a1da5c42f627ccc32ae5d9d6727e40019a7798db0120de`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L840-L842) — lines `840–842`; excerpt `sha256:06af722f0c1d5bd1dbdd7a2c42574299caad3b8bfea7faed51cebc591365c44c`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3081-L3083) — lines `3081–3083`; excerpt `sha256:828f4da9714361921bc80071c0a1ee81ffb2c4cd7328ba82c26137466ef09a38`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3039-L3041) — lines `3039–3041`; excerpt `sha256:828f4da9714361921bc80071c0a1ee81ffb2c4cd7328ba82c26137466ef09a38`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10428-L10432) — lines `10428–10432`; excerpt `sha256:7ec6c33f36b32e11bbec81e8c966173b30a2c50d056c1ab9103fffc5afc23d94`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L7527-L7527) — lines `7527–7527`; excerpt `sha256:b5f7725d9d9b224c30c605af2ec45cbedb389b6e64791915712d49c8c2ee5bd0`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10236-L10240) — lines `10236–10240`; excerpt `sha256:7ec6c33f36b32e11bbec81e8c966173b30a2c50d056c1ab9103fffc5afc23d94`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7335-L7335) — lines `7335–7335`; excerpt `sha256:b5f7725d9d9b224c30c605af2ec45cbedb389b6e64791915712d49c8c2ee5bd0`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1223](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1223-L1223), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1283](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1283-L1283)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:71](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L71-L71), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:343](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L343-L343)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1031](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1031-L1031), [cite at paper/reasoning-parts/erdos243/core.tex:992](../../paper/reasoning-parts/erdos243/core.tex#L992-L992)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7527](../../paper/249/erdos249-totient-reasoning-surface.tex#L7527-L7527), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7335](../../paper/reasoning-parts/erdos249/a249_front.tex#L7335-L7335)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:377](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L377-L377), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:582](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L582-L582), [cite at paper/reasoning-parts/erdos251/core.tex:335](../../paper/reasoning-parts/erdos251/core.tex#L335-L335), [cite at paper/reasoning-parts/erdos251/core.tex:540](../../paper/reasoning-parts/erdos251/core.tex#L540-L540)
- `writing-mathematics-from-reviewed-revisions`: [cite at paper/exposition/parts/revisions.tex:35](../../paper/exposition/parts/revisions.tex#L35-L35)

<a id="source-source-43a734be32736f"></a>

### [Some problems and results on the irrationality of the sum of infinite series](https://doi.org/10.1007/BF01083693)

- Source id: `source-43a734be32736f`
- Author or public identity: Paul Erdős
- Kind: `literature`
- Problems: #68, #257
- Relationship and boundary: Growth-only irrationality criterion (Theorem 1, p. 1) compared with the Mersenne supports.
- Source verification: `source\_verified` — The cited passages (Theorem 1, p. 1) were checked against the scan copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1, p. 1](https://www.renyi.hu/~p_erdos/1976-44.pdf)
- [Primary seven-page PDF; first-page theorem inspected as an image. No claim to have audited the whole proof.](https://www.renyi.hu/~p_erdos/1976-44.pdf)

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1671-L1674) — lines `1671–1674`; excerpt `sha256:8fe2d89da58a1e4e231d39f70b8dc5e5e218e128f6a1964d09e9a63a746e2b0a`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3159-L3163) — lines `3159–3163`; excerpt `sha256:b938d408a670bde68b8522a01fa71ee3a1b30b4fbb78368431f5fb9cded5f0f9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3124-L3128) — lines `3124–3128`; excerpt `sha256:b938d408a670bde68b8522a01fa71ee3a1b30b4fbb78368431f5fb9cded5f0f9`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:882](../../paper/257/erdos-257-mersenne-support-subseries.tex#L882-L882)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2197](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2197-L2197), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2329](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2329-L2329), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2602](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2602-L2602), [cite at paper/reasoning-parts/erdos68/core.tex:2162](../../paper/reasoning-parts/erdos68/core.tex#L2162-L2162), [cite at paper/reasoning-parts/erdos68/core.tex:2294](../../paper/reasoning-parts/erdos68/core.tex#L2294-L2294), [cite at paper/reasoning-parts/erdos68/core.tex:2567](../../paper/reasoning-parts/erdos68/core.tex#L2567-L2567)

<a id="source-source-45037c29c04bed"></a>

### Three refinements for the lemniscate-path programme

- Source id: `source-45037c29c04bed`
- Author or public identity: {Plectis revision research draft}
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1257-L1261) — lines `1257–1261`; excerpt `sha256:6ea06c00bd0618e69c51b088f55e4fd1b6441571dde55b8bda3d1dc3d28d3e67`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5508-L5512) — lines `5508–5512`; excerpt `sha256:906433dd170c41415919219e15b60b8e1b97efac405ace13999d8cc6451fa785`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5458-L5462) — lines `5458–5462`; excerpt `sha256:906433dd170c41415919219e15b60b8e1b97efac405ace13999d8cc6451fa785`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:854](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L854-L854), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:972](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L972-L972), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1106](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1106-L1106)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1446](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1446-L1446), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2211](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2211-L2211), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3187](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3187-L3187), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3900](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3900-L3900), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4025](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4025-L4025), [cite at paper/reasoning-parts/erdos1041/core.tex:1396](../../paper/reasoning-parts/erdos1041/core.tex#L1396-L1396), [cite at paper/reasoning-parts/erdos1041/core.tex:2161](../../paper/reasoning-parts/erdos1041/core.tex#L2161-L2161), [cite at paper/reasoning-parts/erdos1041/core.tex:3137](../../paper/reasoning-parts/erdos1041/core.tex#L3137-L3137), [cite at paper/reasoning-parts/erdos1041/core.tex:3850](../../paper/reasoning-parts/erdos1041/core.tex#L3850-L3850), [cite at paper/reasoning-parts/erdos1041/core.tex:3975](../../paper/reasoning-parts/erdos1041/core.tex#L3975-L3975)

<a id="source-source-450aed97015b8f"></a>

### [Sums of singular series along arithmetic progressions and with smooth weights](https://arxiv.org/abs/2301.06095v1)

- Source id: `source-450aed97015b8f`
- Author or public identity: Kuperberg, Vivian
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — full\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3093-L3095) — lines `3093–3095`; excerpt `sha256:c13202ba0e0b2c61e1309389eeaf97212f8f3b05eea87b49c4ad2e8748454dc3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3051-L3053) — lines `3051–3053`; excerpt `sha256:c13202ba0e0b2c61e1309389eeaf97212f8f3b05eea87b49c4ad2e8748454dc3`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:665](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L665-L665), [cite at paper/reasoning-parts/erdos251/core.tex:623](../../paper/reasoning-parts/erdos251/core.tex#L623-L623)

<a id="source-source-45ae653f011748"></a>

### [TheoremGraph: Bridging Formal and Informal Mathematics](https://doi.org/10.48550/arXiv.2606.25363)

- Source id: `source-45ae653f011748`
- Author or public identity: Simon Kurgan, Evan Wang, Eric Leonen, Sophie Szeto, Luke Alexander, Artemii Remizov, Jarod Alper, Giovanni Inchiostro, Vasily Ilin
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://arxiv.org/abs/2606.25363v1)

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L711-L714) — lines `711–714`; excerpt `sha256:facbf8174f29ec644aa87ad59cf5ec179262bc093a6f37a813598d55c1c8af77`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1043](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1043-L1043)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:496](../../paper/systems/cold-clone-to-proof-receipt.tex#L496-L496)

<a id="source-source-463b7e9f7264b1"></a>

### [Structured Assurance Case Metamodel (SACM)](https://www.omg.org/spec/SACM/2.3/PDF)

- Source id: `source-463b7e9f7264b1`
- Author or public identity: Object Management Group.
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1329-L1334) — lines `1329–1334`; excerpt `sha256:b72eaf7771719b0f871cf252ff08d155c348754cbbc333e06e0587f20db646de`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:418](../../docs/papers/mirror/plectis-public-system.tex#L418-L418)

<a id="source-source-490b1875016ea4"></a>

### [Lattice paths and branched continued fractions: An infinite sequence of generalizations of the Stieltjes–Rogers and Thron–Rogers polynomials, with coefficientwise Hankel-total positivity](https://arxiv.org/abs/1807.03271v2)

- Source id: `source-490b1875016ea4`
- Author or public identity: Mathias Pétréolle, Alan D. Sokal, Bao-Xuan Zhu
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Stronger coefficientwise total positivity through positive production mechanisms; a research route, not transferred evidence.
- Source verification: `source\_verified` — Full-text selected portions: introductory continued-fraction discussion; Theorems 9.7--9.8 and the production-matrix/path argument in Section 9.5, including printed pp. 43 and 50. Not a cover-to-cover reading of 151 pages.
- Local mapping: `not recorded`

Exact source locations:

- [Full-text selected portions: introductory continued-fraction discussion; Theorems 9.7--9.8 and the production-matrix/path argument in Section 9.5, including printed pp. 43 and 50. Not a cover-to-cover reading of 151 pages.](https://arxiv.org/abs/1807.03271v2)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5380-L5388) — lines `5380–5388`; excerpt `sha256:17a9f0c77da491dc851c4a65e945725b1c61e75da287cb94849f3bb840ee6c33`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5349-L5357) — lines `5349–5357`; excerpt `sha256:17a9f0c77da491dc851c4a65e945725b1c61e75da287cb94849f3bb840ee6c33`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2929](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2929-L2929), [cite at paper/reasoning-parts/erdos1049/core.tex:2898](../../paper/reasoning-parts/erdos1049/core.tex#L2898-L2898)

<a id="source-source-4afc43674f7082"></a>

### [(Logarithmic) densities for automatic sequences along primes and squares](https://arxiv.org/pdf/2009.14773v2)

- Source id: `source-4afc43674f7082`
- Author or public identity: Boris Adamczewski, Michael Drmota, Clemens Müllner
- Kind: `literature`
- Problems: #249, #251
- Relationship and boundary: Density-transfer and local-obstruction boundary for automatic prime sampling. Relevant to the long contextual discussion and Shallit dossier, not needed to prove the short paper’s periodic corollary.
- Source verification: `source\_verified` — arXiv v2 (2021), all 35 pages; published 45-page version checked for metadata, not reread in full
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 1.4 and Remark 1.5, p. 4; Lemmas 3.6–3.7; Proposition 4.1; proof of Theorem 1.4, end of Section 7, p. 19](https://arxiv.org/pdf/2009.14773v2)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10415-L10422) — lines `10415–10422`; excerpt `sha256:c412b56a71492694abbd8a4bb30d4b12dd25d5050689bc96bb8d162c095f07c6`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10223-L10230) — lines `10223–10230`; excerpt `sha256:c412b56a71492694abbd8a4bb30d4b12dd25d5050689bc96bb8d162c095f07c6`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L651-L652) — lines `651–652`; excerpt `sha256:247c067f39becf8fb56e126e3b8f9082fe2ff5beedfff0856ec406a7f8bb7975`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3083-L3085) — lines `3083–3085`; excerpt `sha256:6e5c026e217aafc0c8b121d5e6586f0139ff79cbf8c2871b89cdc840c4041993`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3041-L3043) — lines `3041–3043`; excerpt `sha256:6e5c026e217aafc0c8b121d5e6586f0139ff79cbf8c2871b89cdc840c4041993`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:10220](../../paper/249/erdos249-totient-reasoning-surface.tex#L10220-L10220), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:10028](../../paper/reasoning-parts/erdos249/a249_front.tex#L10028-L10028)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:652](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L652-L652), [cite at paper/reasoning-parts/erdos251/core.tex:610](../../paper/reasoning-parts/erdos251/core.tex#L610-L610)

<a id="source-source-4bb571f8383293"></a>

### [FormalConjectures.ErdosProblems.257](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/257.lean)

- Source id: `source-4bb571f8383293`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #257
- Relationship and boundary: External formal statement of the problem, cited as formal context.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Pinned source attribution inherited from the short paper; not fetched through a personal connector in this pass.](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/257.lean)

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1662-L1667) — lines `1662–1667`; excerpt `sha256:25cf3513f78fba977dc2a6cefb4a67e70b7815d304207cbac09e637aaa5db383`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1596](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1596-L1596)

<a id="source-source-4f5fd0d7405e29"></a>

### [On several irrationality problems for Ahmes series](https://arxiv.org/abs/2406.17593v4)

- Source id: `source-4f5fd0d7405e29`
- Author or public identity: V. Kovač, T. Tao
- Kind: `literature`
- Problems: #1049, #243, #249, #251, #257, #269
- Relationship and boundary: General Ahmes-series background in the long record's prior-work section.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [550706 bytes; 28 PDF pages. It was retrieved from the arXiv v4 PDF route](https://arxiv.org/abs/2406.17593v4)
- [The title/contents page and PDF pp. 2, 4, 5, 10, 11, 13, 14, and 28 were also](https://arxiv.org/abs/2406.17593v4)
- [- \*\*Problem setting and growth boundary:\*\* PDF p. 2 defines Ahmes series and](https://arxiv.org/abs/2406.17593v4)
- [- \*\*Lambert subseries:\*\* PDF pp. 4–5, §2.1.2, defines the subseries](https://arxiv.org/abs/2406.17593v4)
- [- \*\*Strict-tail geometry:\*\* PDF p. 13, Remark 4.1, proves](https://arxiv.org/abs/2406.17593v4)
- [#257 fixed-base geometry discussion. The remark does not assert a measure](https://arxiv.org/abs/2406.17593v4)
- [- \*\*Merged multi-base construction:\*\* PDF p. 5, Theorem 2.3, assumes](https://arxiv.org/abs/2406.17593v4)
- [\*merged\* sum is rational; its proof is on PDF pp. 13–14. The paper itself](https://arxiv.org/abs/2406.17593v4)
- [- \*\*Irrationality-sequence results:\*\* PDF pp. 6–7, Theorems 2.4–2.7,](https://arxiv.org/abs/2406.17593v4)
- [- \*\*Higher-dimensional and infinite-dimensional results:\*\* PDF pp. 8–10,](https://arxiv.org/abs/2406.17593v4)
- [Theorems 2.8 and 2.11, give non-empty-interior and rationality constructions](https://arxiv.org/abs/2406.17593v4)
- [theorem for every infinite support.](https://arxiv.org/abs/2406.17593v4)
- [- \*\*End matter:\*\* PDF p. 28 gives the references and author affiliations,](https://arxiv.org/abs/2406.17593v4)
- [subsums, and their Cantor-set structure, PDF p. 13, Remark 4.1.](https://arxiv.org/abs/2406.17593v4)
- [question and the prime-support open example, PDF pp. 4–5.](https://arxiv.org/abs/2406.17593v4)
- [hypothesis, PDF p. 5, Theorem 2.3, with proof pp. 13–14.](https://arxiv.org/abs/2406.17593v4)
- [questions, PDF p. 2 and §§2.1.2–2.1.3.](https://arxiv.org/abs/2406.17593v4)
- [- A fixed-base rational counterexample from Theorem 2.3: its conclusion is a](https://arxiv.org/abs/2406.17593v4)
- [theorem names, totient-kernel rank/basis statements, Erdős #249, and a proof](https://arxiv.org/abs/2406.17593v4)
- [of universal #257; none occurs. Remark 4.1 supplies strict-tail/Cantor](https://arxiv.org/abs/2406.17593v4)
- [PDF p. 11, Remark 3.1: for a nonincreasing summable positive sequence, the sums of subseries form a finite union of closed intervals exactly when every late term is at most the sum of all later terms, credited to Kakeya.](https://arxiv.org/abs/2406.17593v4)
- [PDF pp. 14-15, Lemma 5.1 and proof: nested covering of the intervals of attainable tail sums, I\_n = I\_{n+1} + {1/j : j in J\_n}, under condition (5.1).](https://arxiv.org/abs/2406.17593v4)
- [PDF pp. 7 and 16-17, Theorem 2.5, its proof and the closing example of Section 5: some b\_n in {1,...,5} give sum 1/(2^n+b\_n) = 3/4, a negative answer to the Erdős-Graham question about 2^n.](https://arxiv.org/abs/2406.17593v4)
- [Sec. 2.1.2 and Thm. 2.3, pp. 4--5](https://doi.org/10.1007/s10474-025-01528-0)
- [Theorem 2.3, p. 5 (arXiv v4)](https://doi.org/10.1007/s10474-025-01528-0)
- [Lemma 5.1; Lemma 5.1, Theorem 2.5 and §5; §1](https://doi.org/10.1007/s10474-025-01528-0)
- [Remark 3.1 (Kakeya criterion); Lemma 5.1; Lemma 5.1, Theorem 2.5 and §5; §1](https://doi.org/10.1007/s10474-025-01528-0)
- [Remark 4.1 (p. 13); Theorem 2.3 (p. 5, proof pp. 13-14)](https://doi.org/10.1007/s10474-025-01528-0)
- [arXiv v4, p. 2](https://arxiv.org/abs/2406.17593v4)
- [Broader Ahmes-series problem context.](https://arxiv.org/abs/2406.17593v4)
- [Rational subsums in selected Lambert/Ahmes settings; do not remove the freedom-to-select hypothesis.](https://arxiv.org/abs/2406.17593v4)
- [Theorem 2.3, p. 5; Remark 4.1 and proof of Theorem 2.3, pp. 13–14 (arXiv v4).](https://arxiv.org/pdf/2406.17593v4)
- [Introduction; statements in Section 2 and the superincreasing-subseries argument in Section 3 (Proposition 2.1). No claim to have audited all later constructions.](https://doi.org/10.1007/s10474-025-01528-0)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://arxiv.org/abs/2406.17593v4)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5388-L5392) — lines `5388–5392`; excerpt `sha256:e74d62894afb08f0bf9f352f2a81f1d8436fc4947ccc8847ea8044e669d88d61`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4118-L4125) — lines `4118–4125`; excerpt `sha256:cc6aca2237133e921cd97b74d25252bfe07f4ac85f0f29888f9c09d741fbe072`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L818-L820) — lines `818–820`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3049-L3051) — lines `3049–3051`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1656-L1660) — lines `1656–1660`; excerpt `sha256:da365fb3627d4a62500ab14506a5fa9a7c61368c1f67b75982752d2ba474ccc5`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4456-L4459) — lines `4456–4459`; excerpt `sha256:854363997d348b739079081250c9280b18fc2f8b82b9e98cfd71f3fe5d758fdf`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5311-L5318) — lines `5311–5318`; excerpt `sha256:31734bb5dbd8d4b44ac368c926cf6ce72c577a3e05d74dab77682764ee7da3da`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5280-L5287) — lines `5280–5287`; excerpt `sha256:31734bb5dbd8d4b44ac368c926cf6ce72c577a3e05d74dab77682764ee7da3da`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5004-L5004) — lines `5004–5004`; excerpt `sha256:1102bfe9b1f75f0d5960a2f3d22f55f277c362853922162565b2ad5506af83b9`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4079-L4086) — lines `4079–4086`; excerpt `sha256:cc6aca2237133e921cd97b74d25252bfe07f4ac85f0f29888f9c09d741fbe072`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L974-L974) — lines `974–974`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L974-L974) — lines `974–974`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L974-L974) — lines `974–974`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3007-L3009) — lines `3007–3009`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L340-L340) — lines `340–340`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4398-L4401) — lines `4398–4401`; excerpt `sha256:854363997d348b739079081250c9280b18fc2f8b82b9e98cfd71f3fe5d758fdf`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L126-L126) — lines `126–126`; excerpt `sha256:3abef61fe6288d78d30765ceaf472ba30b63436843d7f7cb71bd57725ce6dfa1`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L92-L92) — lines `92–92`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1209-L1209) — lines `1209–1209`; excerpt `sha256:2f13d854d17862e3e84cfe8260e36f3e508b7165189455204d23c133aeac237e`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L603-L613) — lines `603–613`; excerpt `sha256:c989aa24e7d0cd4a81a2207dea6e4647a9e1d349d2fb8a86a8fcd45cc9386fd7`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L72-L72) — lines `72–72`; excerpt `sha256:50d32f90b65fd0005fb2987ffe3dda549379dfbd5da510242ea70b71dd44cacd`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L72-L72) — lines `72–72`; excerpt `sha256:50d32f90b65fd0005fb2987ffe3dda549379dfbd5da510242ea70b71dd44cacd`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L340-L340) — lines `340–340`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L340-L340) — lines `340–340`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L340-L340) — lines `340–340`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L382-L382) — lines `382–382`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L382-L382) — lines `382–382`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L382-L382) — lines `382–382`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10331-L10337) — lines `10331–10337`; excerpt `sha256:aa7e7a743f9042755d99379ed9c411c18d6b86186718b25aa42a57c133a0f41e`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10139-L10145) — lines `10139–10145`; excerpt `sha256:aa7e7a743f9042755d99379ed9c411c18d6b86186718b25aa42a57c133a0f41e`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L818-L820) — lines `818–820`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1079-L1082) — lines `1079–1082`; excerpt `sha256:9c3c5db10d94904b54c40a45565db137f38253e6cc98c36fb7f0446f37302911`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:72](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L72-L72)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1132](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1132-L1132)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1006](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1006-L1006)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5035](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5035-L5035), [cite at paper/reasoning-parts/erdos1049/core.tex:5004](../../paper/reasoning-parts/erdos1049/core.tex#L5004-L5004)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1013](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1013-L1013), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1016](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1016-L1016), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1025](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1025-L1025), [cite at paper/reasoning-parts/erdos243/core.tex:974](../../paper/reasoning-parts/erdos243/core.tex#L974-L974), [cite at paper/reasoning-parts/erdos243/core.tex:977](../../paper/reasoning-parts/erdos243/core.tex#L977-L977), [cite at paper/reasoning-parts/erdos243/core.tex:986](../../paper/reasoning-parts/erdos243/core.tex#L986-L986)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:824](../../paper/archive/erdos249-257-main-paper.tex#L824-L824), [cite at paper/archive/erdos249-257-main-paper.tex:825](../../paper/archive/erdos249-257-main-paper.tex#L825-L825), [cite at paper/archive/erdos249-257-main-paper.tex:2146](../../paper/archive/erdos249-257-main-paper.tex#L2146-L2146), [cite at paper/archive/erdos249-257-main-paper.tex:4673](../../paper/archive/erdos249-257-main-paper.tex#L4673-L4673), [cite at paper/archive/erdos249-257-main-paper.tex:5064](../../paper/archive/erdos249-257-main-paper.tex#L5064-L5064), [cite at paper/archive/erdos249-257-main-paper.tex:5110](../../paper/archive/erdos249-257-main-paper.tex#L5110-L5110)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:10181](../../paper/249/erdos249-totient-reasoning-surface.tex#L10181-L10181), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9989](../../paper/reasoning-parts/erdos249/a249_front.tex#L9989-L9989)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:382](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L382-L382), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:591](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L591-L591), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:686](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L686-L686), [cite at paper/reasoning-parts/erdos251/core.tex:340](../../paper/reasoning-parts/erdos251/core.tex#L340-L340), [cite at paper/reasoning-parts/erdos251/core.tex:549](../../paper/reasoning-parts/erdos251/core.tex#L549-L549), [cite at paper/reasoning-parts/erdos251/core.tex:644](../../paper/reasoning-parts/erdos251/core.tex#L644-L644)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9207](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9207-L9207), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9007](../../paper/reasoning-parts/erdos257/a257_front.tex#L9007-L9007)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:184](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L184-L184), [cite at paper/reasoning-parts/erdos269/core.tex:126](../../paper/reasoning-parts/erdos269/core.tex#L126-L126)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:879](../../paper/synthesis/optimal-sparse-perturbations.tex#L879-L879), [cite at paper/synthesis/optimal-sparse-perturbations.tex:906](../../paper/synthesis/optimal-sparse-perturbations.tex#L906-L906), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1013](../../paper/synthesis/optimal-sparse-perturbations.tex#L1013-L1013), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1029](../../paper/synthesis/optimal-sparse-perturbations.tex#L1029-L1029), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1852](../../paper/synthesis/optimal-sparse-perturbations.tex#L1852-L1852), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1971](../../paper/synthesis/optimal-sparse-perturbations.tex#L1971-L1971), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1974](../../paper/synthesis/optimal-sparse-perturbations.tex#L1974-L1974)

<a id="source-source-5122572a1e7312"></a>

### [On the irrationality of certain 2-adic zeta values](https://arxiv.org/abs/2304.00816v1)

- Source id: `source-5122572a1e7312`
- Author or public identity: L. Lai
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Upstream source (Lemma 2.1, arXiv v1 p. 4) of the irrationality criterion quoted by Lai, Lupu and Sprang.
- Source verification: `source\_verified` — The cited passages (Lemma 2.1, p. 4 (arXiv v1); Lemma 2.1, p. 4 (arXiv v1)) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Lemma 2.1, p. 4 (arXiv v1)](https://arxiv.org/abs/2304.00816v1)
- [Lemma 2.1, p. 4 (arXiv v1)](https://arxiv.org/abs/2304.00816v1)
- [Reference and role retained from the attached paper; not independently reread in full in this revision.](https://arxiv.org/abs/2304.00816v1)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3176-L3180) — lines `3176–3180`; excerpt `sha256:c1feb1fd30f80a42ea7b93c301207ea72abff8a1961dc7646ef336d6bf938b73`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3211-L3215) — lines `3211–3215`; excerpt `sha256:c1feb1fd30f80a42ea7b93c301207ea72abff8a1961dc7646ef336d6bf938b73`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3176-L3180) — lines `3176–3180`; excerpt `sha256:c1feb1fd30f80a42ea7b93c301207ea72abff8a1961dc7646ef336d6bf938b73`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1197](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1197-L1197), [cite at paper/reasoning-parts/erdos68/core.tex:1162](../../paper/reasoning-parts/erdos68/core.tex#L1162-L1162)

<a id="source-source-5270112e32002d"></a>

### [Sur le développement en fraction continue d'un nombre choisi au hasard](https://www.numdam.org/item/CM_1936__3__286_0/)

- Source id: `source-5270112e32002d`
- Author or public identity: P. Lévy
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Source of the almost-everywhere comparison values (Gauss–Kuzmin frequencies and Lévy's constant) quoted for the continued-fraction prefix (pp. 288–289).
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Metric continued-fraction comparison only; does not certify the numerical statistics of S.](https://www.numdam.org/item/CM_1936__3__286_0/)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4487-L4490) — lines `4487–4490`; excerpt `sha256:53305164d06918956b307b2a2bd9e37d95e4d93aff557246b8ebc65eee173fbd`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4429-L4432) — lines `4429–4432`; excerpt `sha256:53305164d06918956b307b2a2bd9e37d95e4d93aff557246b8ebc65eee173fbd`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3140](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3140-L3140), [cite at paper/reasoning-parts/erdos269/core.tex:3082](../../paper/reasoning-parts/erdos269/core.tex#L3082-L3082)

<a id="source-source-53a2a9c4a9e7c2"></a>

### [Calculation of Gauss Quadrature Rules](https://doi.org/10.1090/S0025-5718-69-99647-1)

- Source id: `source-53a2a9c4a9e7c2`
- Author or public identity: Gene H. Golub, John H. Welsch
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Classical finite Gaussian quadrature mechanism; not identification of the Lambert coefficient pencil with a Jacobi matrix.
- Source verification: `source\_verified` — Full-text Sections 2 and 4: Jacobi eigenvalue/weight construction, (2.6), printed p. 223; moment Cholesky construction, printed pp. 226--227. Matrix pages visually inspected.
- Local mapping: `not recorded`

Exact source locations:

- [Full-text Sections 2 and 4: Jacobi eigenvalue/weight construction, (2.6), printed p. 223; moment Cholesky construction, printed pp. 226--227. Matrix pages visually inspected.](https://doi.org/10.1090/S0025-5718-69-99647-1)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1353-L1357) — lines `1353–1357`; excerpt `sha256:3b958d96041c8d7357ca2a6320bad4a5c5dd5c24e66c13f3fdcb75343dfb1596`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5394-L5398) — lines `5394–5398`; excerpt `sha256:3b958d96041c8d7357ca2a6320bad4a5c5dd5c24e66c13f3fdcb75343dfb1596`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5363-L5367) — lines `5363–5367`; excerpt `sha256:3b958d96041c8d7357ca2a6320bad4a5c5dd5c24e66c13f3fdcb75343dfb1596`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1119](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1119-L1119)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3053](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3053-L3053), [cite at paper/reasoning-parts/erdos1049/core.tex:3022](../../paper/reasoning-parts/erdos1049/core.tex#L3022-L3022)

<a id="source-source-573a79feb36d47"></a>

### [FormalConjectures.ErdosProblems.269](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/269.lean)

- Source id: `source-573a79feb36d47`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #269
- Relationship and boundary: External formal statement/corpus context cited by the paper. It is not proof authority for this repository and does not make the local result an upstream contribution.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Paper bibliography commit pin f776d2f2039351b00737ffcafb9d7d7666e1d9af; exact problem file](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/269.lean)
- [Statement formalisation, not a proof of #269.](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/269.lean)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4444-L4447) — lines `4444–4447`; excerpt `sha256:dad66e1d91ee56df1368adfe2ef9592eef350506274c14cc06dcf5ad03ef77ed`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4386-L4389) — lines `4386–4389`; excerpt `sha256:dad66e1d91ee56df1368adfe2ef9592eef350506274c14cc06dcf5ad03ef77ed`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L3893-L3893) — lines `3893–3893`; excerpt `sha256:70156aa149e95bc051830fe62c9e4dead62a9dfae84a47de933e386647c09bdb`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L3893-L3893) — lines `3893–3893`; excerpt `sha256:70156aa149e95bc051830fe62c9e4dead62a9dfae84a47de933e386647c09bdb`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3951-L3951) — lines `3951–3951`; excerpt `sha256:70156aa149e95bc051830fe62c9e4dead62a9dfae84a47de933e386647c09bdb`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3931](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3931-L3931), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3951](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3951-L3951), [cite at paper/reasoning-parts/erdos269/core.tex:3873](../../paper/reasoning-parts/erdos269/core.tex#L3873-L3873), [cite at paper/reasoning-parts/erdos269/core.tex:3893](../../paper/reasoning-parts/erdos269/core.tex#L3893-L3893)

<a id="source-source-5752bb5009e4de"></a>

### [The ring of k -regular sequences](https://cs.uwaterloo.ca/~shallit/Papers/as0.pdf)

- Source id: `source-5752bb5009e4de`
- Author or public identity: J.-P. Allouche, J. Shallit
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Definition of k-regular sequences and the kernel and module framework, cited at the first use of the term in both papers.
- Source verification: `source\_verified` — The cited passages (Definition 2.1 (author preprint numbering)) were checked against the author preprint ('To appear, Theoretical Computer Science, Nov. 1992') copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Definition 2.1 (author preprint numbering)](https://doi.org/10.1016/0304-3975(92)90001-V)
- [Definition 2.1; Theorems 2.2, 2.3, 2.9 and 2.10; matrix representation, Section 4](https://cs.uwaterloo.ca/~shallit/Papers/as0.pdf)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5341-L5349) — lines `5341–5349`; excerpt `sha256:28fc1b15f89dedfd49214bfcd5a49cc05823f44376740a8e9ad7fc0e987fb378`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L869-L873) — lines `869–873`; excerpt `sha256:822cceaa2102882ca659544f6f24812353e6082e3f3fd963beaa90ce4be4a49a`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10248-L10253) — lines `10248–10253`; excerpt `sha256:1faa5900afcaadc94dc78596f20f82bc542cdeea10be862bbe3be3e9ca92f21f`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10056-L10061) — lines `10056–10061`; excerpt `sha256:1faa5900afcaadc94dc78596f20f82bc542cdeea10be862bbe3be3e9ca92f21f`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:78](../../paper/249/erdos-249-binary-totient-series.tex#L78-L78)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3173](../../paper/archive/erdos249-257-main-paper.tex#L3173-L3173)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8737](../../paper/249/erdos249-totient-reasoning-surface.tex#L8737-L8737), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8545](../../paper/reasoning-parts/erdos249/a249_front.tex#L8545-L8545)

<a id="source-source-57adfd0cdcd8c2"></a>

### [On the largest prime divisor of n!+1](https://arxiv.org/abs/2103.14894)

- Source id: `source-57adfd0cdcd8c2`
- Author or public identity: L. Lai
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Non-vanishing cutoff for n!+P(n) (Lemma 2.1) and the prime-power form of the gcd subtraction (display (2.5)).
- Source verification: `source\_verified` — arXiv v1 PDF read in full (11 pages); the publisher PDF text confirms the same lemma and display numbers on the printed pages given. Verifies the two cited steps only.
- Local mapping: `not recorded`

Exact source locations:

- [Lemma 2.1, arXiv v1 p. 2: for nonzero f in Z\[X\] there is n\_0 \>= 2, depending only on f, such that f(n)(n+1)...(n+k) - f(n+k) = 0 has no integer solutions with n \>= n\_0 and k \>= 1, and n!+f(n) \> 1 and f(n) != 0 for n \>= n\_0. The proof refers the first assertion to Lemma 3 of Luca and Shparlinski (2005).](https://arxiv.org/abs/2103.14894v1)
- [Proof of Lemma 2.4, display (2.5), arXiv v1 p. 4: a prime power D dividing both n\_i!+f(n\_i) and n\_j!+f(n\_j) divides f(n\_i)(n\_i+1)...(n\_j) - f(n\_j), which is nonzero by Lemma 2.1 and at most 2x^(C\_1+|I\_1|).](https://arxiv.org/abs/2103.14894v1)
- [Published version, Bull. Aust. Math. Soc. 113 (2026), 390-403, with the same numbering: Lemma 2.1 on p. 392, Lemma 2.4 on p. 393, display (2.5) on p. 394.](https://doi.org/10.1017/S0004972725100543)
- [Lemma 2.1 (bibitem: published p. 392)](https://doi.org/10.1017/S0004972725100543)
- [proof of Lemma 2.4, display (2.5) (bibitem: published p. 394)](https://doi.org/10.1017/S0004972725100543)
- [Lemma 2.1; proof of Lemma 2.4, display (2.5)](https://doi.org/10.1017/S0004972725100543)
- [Reference and role retained from the attached paper; not independently reread in full in this revision.](https://arxiv.org/abs/2103.14894v1)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3168-L3172) — lines `3168–3172`; excerpt `sha256:e82d9607acf436d2f4aa8d7afad731fa862ecbfa84e051d3b8579701aa30e049`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3203-L3207) — lines `3203–3207`; excerpt `sha256:e82d9607acf436d2f4aa8d7afad731fa862ecbfa84e051d3b8579701aa30e049`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3168-L3172) — lines `3168–3172`; excerpt `sha256:e82d9607acf436d2f4aa8d7afad731fa862ecbfa84e051d3b8579701aa30e049`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L989-L989) — lines `989–989`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L989-L989) — lines `989–989`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L989-L989) — lines `989–989`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L989-L989) — lines `989–989`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L987-L987) — lines `987–987`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L989-L989) — lines `989–989`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1024](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1024-L1024), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1108](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1108-L1108), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2323](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2323-L2323), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2326](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2326-L2326), [cite at paper/reasoning-parts/erdos68/core.tex:989](../../paper/reasoning-parts/erdos68/core.tex#L989-L989), [cite at paper/reasoning-parts/erdos68/core.tex:1073](../../paper/reasoning-parts/erdos68/core.tex#L1073-L1073), [cite at paper/reasoning-parts/erdos68/core.tex:2288](../../paper/reasoning-parts/erdos68/core.tex#L2288-L2288), [cite at paper/reasoning-parts/erdos68/core.tex:2291](../../paper/reasoning-parts/erdos68/core.tex#L2291-L2291)

<a id="source-source-57fe330e419648"></a>

### [Length functions of lemniscates](https://arxiv.org/abs/math/0306327v2)

- Source id: `source-57fe330e419648`
- Author or public identity: Olga S. Kuznetsova, Vladimir G. Tkachev
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Theorems 1–2](https://arxiv.org/abs/math/0306327v2)
- [Corollaries 4–5](https://arxiv.org/abs/math/0306327v2)
- [Proofs §§2–3](https://arxiv.org/abs/math/0306327v2)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1249-L1254) — lines `1249–1254`; excerpt `sha256:9976334d2d074f47b0f36053eafc88c2da992e02c4c4c2eb6956f0ecc319a48b`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5500-L5505) — lines `5500–5505`; excerpt `sha256:9976334d2d074f47b0f36053eafc88c2da992e02c4c4c2eb6956f0ecc319a48b`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5450-L5455) — lines `5450–5455`; excerpt `sha256:9976334d2d074f47b0f36053eafc88c2da992e02c4c4c2eb6956f0ecc319a48b`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1125](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1125-L1125)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1567](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1567-L1567), [cite at paper/reasoning-parts/erdos1041/core.tex:1517](../../paper/reasoning-parts/erdos1041/core.tex#L1517-L1517)

<a id="source-source-5857f9959e7529"></a>

### [NIST Digital Library of Mathematical Functions, Eq. 17.2.37](https://dlmf.nist.gov/17.2.E37)

- Source id: `source-5857f9959e7529`
- Author or public identity: F. W. J. Olver et al. (eds.)
- Kind: `website\_contribution`
- Problems: #1049
- Relationship and boundary: Standard q-binomial theorem (Eq. 17.2.37) used in the positive-measure estimate.
- Source verification: `source\_verified` — The cited passages (Eq. 17.2.37) were checked against the downloaded copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Eq. 17.2.37](https://dlmf.nist.gov/17.2.E37)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://dlmf.nist.gov/17.2.E37)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5328-L5332) — lines `5328–5332`; excerpt `sha256:1f93dd63fdcecc1c50a9e4192bb21b88580fe393bef2b1a4a2bd32200489b8f2`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5297-L5301) — lines `5297–5301`; excerpt `sha256:1f93dd63fdcecc1c50a9e4192bb21b88580fe393bef2b1a4a2bd32200489b8f2`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1696](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1696-L1696), [cite at paper/reasoning-parts/erdos1049/core.tex:1665](../../paper/reasoning-parts/erdos1049/core.tex#L1665-L1665)

<a id="source-source-5911448b65fdf9"></a>

### [On an incomplete argument of Erdős on the irrationality of Lambert series](https://arxiv.org/abs/1206.0340)

- Source id: `source-5911448b65fdf9`
- Author or public identity: J. Vandehey
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Integer-base results for divisor-weighted Lambert series.
- Source verification: `source\_verified` — The cited passages (Thm. 1.1, p. 2) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Thm. 1.1, p. 2](https://arxiv.org/abs/1206.0340)
- [Complete five-page version 1, especially Theorems 1.1--1.2, p. 2 and the corrected digit argument.](https://arxiv.org/abs/1206.0340v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5287-L5292) — lines `5287–5292`; excerpt `sha256:8145c4e8df8a670bb4c71753052c607b975795318f4a6fdaaed256f6644f773f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5256-L5261) — lines `5256–5261`; excerpt `sha256:8145c4e8df8a670bb4c71753052c607b975795318f4a6fdaaed256f6644f773f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4967-L4967) — lines `4967–4967`; excerpt `sha256:4cba849220b6d89a05527440677a635fe05b976de1d3d125b3c7d9e3b37a61fe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4967-L4967) — lines `4967–4967`; excerpt `sha256:4cba849220b6d89a05527440677a635fe05b976de1d3d125b3c7d9e3b37a61fe`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1308-L1313) — lines `1308–1313`; excerpt `sha256:8d3a5a9309dacce42b935afcf56eac11bf777dafe926a5de5f7e5dbb71726aca`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1180](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1180-L1180)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4998](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4998-L4998), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5001](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5001-L5001), [cite at paper/reasoning-parts/erdos1049/core.tex:4967](../../paper/reasoning-parts/erdos1049/core.tex#L4967-L4967), [cite at paper/reasoning-parts/erdos1049/core.tex:4970](../../paper/reasoning-parts/erdos1049/core.tex#L4970-L4970)

<a id="source-source-5b5c84cd208fff"></a>

### [The Oracle Problem in Software Testing: A Survey](https://doi.org/10.1109/TSE.2014.2372785)

- Source id: `source-5b5c84cd208fff`
- Author or public identity: Earl T. Barr, Mark Harman, Phil McMinn, Muzammil Shahbaz, Shin Yoo
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1318-L1324) — lines `1318–1324`; excerpt `sha256:0b4c870e91ea3111d69ea85b7c94783a709618f7b2b3124f463426effcfb8ffc`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:400](../../docs/papers/mirror/plectis-public-system.tex#L400-L400), [cite at docs/papers/mirror/plectis-public-system.tex:404](../../docs/papers/mirror/plectis-public-system.tex#L404-L404)

<a id="source-source-5c72388a6ca10f"></a>

### [On arithmetical properties of Lambert series](https://users.renyi.hu/~p_erdos/1948-04.pdf)

- Source id: `source-5c72388a6ca10f`
- Author or public identity: P. Erdős
- Kind: `literature`
- Problems: #1049, #249, #257
- Relationship and boundary: Attribution of the full-support Erdős--Borwein divisor series \`Σ\_ r≥1 d(r)/t^r\` to Erdős's 1948 theorem, printed p. 63. - The prime-congruence and long base-expansion-zero mechanism used in that theorem, printed pp. 63--65. - The exact source-level warning that the analogous Euler-totient series is not proved there and “seem\[s\] to present difficulties,” printed p. 66. - The published identity, official retrieval route, exact local digest, and conservative redistribution posture recorded above. The comment explicitly attributes the full-support Lambert-series irrationality engine or a stated proof component to Erdős (1948). This is theorem/proof lineage, bounded to the comment; it does not claim a line-by-line transcription of the paper. The complete module comment compares the open weighted rung with Erdős’s 1948 congruence mechanism and explicitly leaves extension to the primitive-conductor weight open. The complete module comment explicitly identifies the level-1 irrational rung with Erdős 1948; this is historical theorem lineage for the already checked full-support result. The comment explicitly identifies the level-1 Lambert rung as irrational by Erdős 1948, contrasted with the externally cited q-Padé level-2 rung.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Lambert theorem to the release's prior-art map and records its explicit](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [603601 bytes; 4 scanned PDF pages. The copy was retrieved from the](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [- \*\*Definitions and theorem:\*\* Printed p. 63 (PDF p. 1) defines](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [notes Chowla's earlier result for \`g(1/t)\`, and states Erdős's theorem:](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [divisor-weighted Lambert theorem used for the Erdős--Borwein row.](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [- \*\*Positive-base proof:\*\* Printed pp. 63--65 (PDF pp. 1--3) construct](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [theorem and its proof mechanism, not a totient-series conclusion.](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [- \*\*Negative-base boundary:\*\* Printed p. 66 (PDF p. 4) says the negative-\`t\`](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [totient-kernel rank formula, Comparator theorem names, Erdős Problem #249,](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [divisor-weighted \`f(1/t)\` and the sine-weighted \`g(1/t)\` theorem, but does not](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [\`Σ\_ r≥1 d(r)/t^r\` to Erdős's 1948 theorem, printed p. 63.](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [theorem, printed pp. 63--65.](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [not proved there and “seem\[s\] to present difficulties,” printed p. 66.](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [any totient-kernel rank, basis, or Lean theorem.](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [only the positive-base theorem is fully detailed in the source.](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [pp. 63-66](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [(no locator)](https://www.renyi.hu/~p_erdos/1948-04.pdf)
- [(no locator, three places)](https://www.renyi.hu/~p_erdos/1948-04.pdf)
- [Classical Lambert-series irrationality context; not an automatic transfer to the totient value.](https://users.renyi.hu/~p_erdos/1948-04.pdf)
- [Inherited historical statement; author archive bibliography checked. Original proof not independently re-audited in this pass.](https://www.renyi.hu/~p_erdos/1948-04.pdf)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://users.renyi.hu/~p_erdos/1948-04.pdf)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5304-L5307) — lines `5304–5307`; excerpt `sha256:20b0b33ebb4cd3cbf86a87600342b42670e722c45b2b8f83015e0c8f3160e9da`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1660-L1662) — lines `1660–1662`; excerpt `sha256:12e925bb796b6215db708d25b5d1ab1c5640c351e7f3683e2c91ae968206b259`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5173-L5177) — lines `5173–5177`; excerpt `sha256:cf446c3cbb0c405bcc80ec2c25d599a8a83cd781fed2f9312d32338c1383374d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5142-L5146) — lines `5142–5146`; excerpt `sha256:cf446c3cbb0c405bcc80ec2c25d599a8a83cd781fed2f9312d32338c1383374d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:194861111962ca5a85afc5639a358723997616a84a229c8644fbd6c0a2083724`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:194861111962ca5a85afc5639a358723997616a84a229c8644fbd6c0a2083724`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:194861111962ca5a85afc5639a358723997616a84a229c8644fbd6c0a2083724`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L2142-L2143) — lines `2142–2143`; excerpt `sha256:da5a2b6be594eb622f6493ba7b287897955792d0f4a849924d6977e44d0c48c1`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L976-L976) — lines `976–976`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L6098-L6119) — lines `6098–6119`; excerpt `sha256:a95f4e16d02653c65f588bc0fd5f0e3f55a90bf1d71001919b1d99ef57cb4c09`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L6243-L6250) — lines `6243–6250`; excerpt `sha256:805528d897858369226c74fabbea7797cc6d0177de72a05d5d9ad3f7ebea91a7`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L6328-L6333) — lines `6328–6333`; excerpt `sha256:104253059dee729cc85b58c2713b9d8b6de5bccc9989a0ee23dfd65ccd734629`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L6353-L6356) — lines `6353–6356`; excerpt `sha256:5ffb6cd2ac1849cbfdb6e1fc7ba67a5326f70a9c0616d044e9ced53b9103a72b`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L6499-L6504) — lines `6499–6504`; excerpt `sha256:c664bf2f1961e2f3015e4e80d509b1e8b09f178dbb364c22485d3ef4952374e7`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L6700-L6707) — lines `6700–6707`; excerpt `sha256:74c892103b8f2d0947e305e488c345670a29680e7072bdb043543e285b8a803e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L7567-L7571) — lines `7567–7571`; excerpt `sha256:35b2398291b21096db7432ac4b455e076a178c3a2e879ac853425feb0cc6a024`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L8183-L8186) — lines `8183–8186`; excerpt `sha256:46c6b9380e4b46c3c80eb61c177747eb67703808cd88b424c264d329df2663f2`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L8323-L8336) — lines `8323–8336`; excerpt `sha256:4dd52b98469586f790b57d5c6f03f4123ba69beb7e52b98ecbded9725d1fcffa`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L8701-L8705) — lines `8701–8705`; excerpt `sha256:e11d6af41d5a80d2fbff24672b0dce72b541203748520420a5eeb3eb778eec50`
- [lean/Erdos249257/MersenneLambertLadder.lean](../../lean/Erdos249257/MersenneLambertLadder.lean#L47-L53) — lines `47–53`; excerpt `sha256:b45aeb51359d86c158845274d46ed767649efa27afd80d32195fc657d97717bd`
- [lean/Erdos249257/GcdMomentCalculus.lean](../../lean/Erdos249257/GcdMomentCalculus.lean#L42-L45) — lines `42–45`; excerpt `sha256:e52069568abc708f08d10023d2061bcfdd5c0f984b8a5a65ed3e8571e54ee9bd`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L18621-L18623) — lines `18621–18623`; excerpt `sha256:7baad49acd6e8043e207763ff59a2f21df42069c613ca2bc3b8ba3b297dda26e`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10294-L10298) — lines `10294–10298`; excerpt `sha256:83ff6ef68815bf0b391a143e9e5336b1ff5b127bd0fbcac01ed9f7a399d02225`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10102-L10106) — lines `10102–10106`; excerpt `sha256:83ff6ef68815bf0b391a143e9e5336b1ff5b127bd0fbcac01ed9f7a399d02225`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9607-L9610) — lines `9607–9610`; excerpt `sha256:7a684bfaefd18d542b221d902849314551f3d7d7c0bdd860824a938e6896ecd7`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9407-L9410) — lines `9407–9410`; excerpt `sha256:7a684bfaefd18d542b221d902849314551f3d7d7c0bdd860824a938e6896ecd7`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:55](../../paper/257/erdos-257-mersenne-support-subseries.tex#L55-L55), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:830](../../paper/257/erdos-257-mersenne-support-subseries.tex#L830-L830)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:64](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L64-L64), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3826](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3826-L3826), [cite at paper/reasoning-parts/erdos1049/core.tex:33](../../paper/reasoning-parts/erdos1049/core.tex#L33-L33), [cite at paper/reasoning-parts/erdos1049/core.tex:3795](../../paper/reasoning-parts/erdos1049/core.tex#L3795-L3795)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:115](../../paper/archive/erdos249-257-main-paper.tex#L115-L115), [cite at paper/archive/erdos249-257-main-paper.tex:619](../../paper/archive/erdos249-257-main-paper.tex#L619-L619), [cite at paper/archive/erdos249-257-main-paper.tex:622](../../paper/archive/erdos249-257-main-paper.tex#L622-L622)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1845](../../paper/249/erdos249-totient-reasoning-surface.tex#L1845-L1845), [cite at paper/249/erdos249-totient-reasoning-surface.tex:1868](../../paper/249/erdos249-totient-reasoning-surface.tex#L1868-L1868), [cite at paper/249/erdos249-totient-reasoning-surface.tex:2795](../../paper/249/erdos249-totient-reasoning-surface.tex#L2795-L2795), [cite at paper/249/erdos249-totient-reasoning-surface.tex:5708](../../paper/249/erdos249-totient-reasoning-surface.tex#L5708-L5708), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8081](../../paper/249/erdos249-totient-reasoning-surface.tex#L8081-L8081), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8091](../../paper/249/erdos249-totient-reasoning-surface.tex#L8091-L8091), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1653](../../paper/reasoning-parts/erdos249/a249_front.tex#L1653-L1653), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1676](../../paper/reasoning-parts/erdos249/a249_front.tex#L1676-L1676), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:2603](../../paper/reasoning-parts/erdos249/a249_front.tex#L2603-L2603), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:5516](../../paper/reasoning-parts/erdos249/a249_front.tex#L5516-L5516), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7889](../../paper/reasoning-parts/erdos249/a249_front.tex#L7889-L7889), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7899](../../paper/reasoning-parts/erdos249/a249_front.tex#L7899-L7899)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1176](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1176-L1176), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1477](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1477-L1477), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3026](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3026-L3026), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:6923](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L6923-L6923), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:976](../../paper/reasoning-parts/erdos257/a257_front.tex#L976-L976), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1277](../../paper/reasoning-parts/erdos257/a257_front.tex#L1277-L1277), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2826](../../paper/reasoning-parts/erdos257/a257_front.tex#L2826-L2826), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:6723](../../paper/reasoning-parts/erdos257/a257_front.tex#L6723-L6723)

<a id="source-source-5cac1ad51acb12"></a>

### [Integer sequences and periodic points](https://ueaeprints.uea.ac.uk/id/eprint/19710/1/apew2.pdf)

- Source id: `source-5cac1ad51acb12`
- Author or public identity: G. Everest, A. J. van der Poorten, Y. Puri, T. Ward
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Classical integrality condition for primitive orbit counts behind the primitive-Euler coordinates.
- Source verification: `source\_verified` — The cited passages (Lemma 3.1, p. 5 (preprint pagination)) were checked against the preprint pagination (J. Integer Seq. 5 (2002), Article 02.2.3) copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Lemma 3.1, p. 5 (preprint pagination)](https://ueaeprints.uea.ac.uk/id/eprint/19710/1/apew2.pdf)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10386-L10390) — lines `10386–10390`; excerpt `sha256:77de149e1b9e4c1cbd9c39690b007e9959c56e7732149a19d644b96ce9c396c8`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10194-L10198) — lines `10194–10198`; excerpt `sha256:77de149e1b9e4c1cbd9c39690b007e9959c56e7732149a19d644b96ce9c396c8`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:4384](../../paper/249/erdos249-totient-reasoning-surface.tex#L4384-L4384), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:4192](../../paper/reasoning-parts/erdos249/a249_front.tex#L4192-L4192)

<a id="source-source-5edeb2408c36bd"></a>

### [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)

- Source id: `source-5edeb2408c36bd`
- Author or public identity: Google DeepMind
- Kind: `software`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1681-L1686) — lines `1681–1686`; excerpt `sha256:573f52e0c7b894eeeb44cdeb82b9844001ad1c0155ff50cf96d645b233996e9d`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1373-L1374) — lines `1373–1374`; excerpt `sha256:ed477db421c75bd2bf0fc9a8324059f75c74acbb2096b75ffc57c88c0fabd274`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1000](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1000-L1000), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1052](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1052-L1052)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:574](../../paper/systems/open-source-mathematics-strategy.tex#L574-L574), [cite at paper/systems/open-source-mathematics-strategy.tex:1002](../../paper/systems/open-source-mathematics-strategy.tex#L1002-L1002)

<a id="source-source-5ee5f85bd606ee"></a>

### [Continued Fractions](https://store.doverpublications.com/products/9780486696300)

- Source id: `source-5ee5f85bd606ee`
- Author or public identity: A. Ya. Khinchin
- Kind: `literature`
- Problems: #251, #269
- Relationship and boundary: Classical best-approximation property (§6, Theorems 16 and 17) used by the continued-fraction denominator exclusion.
- Source verification: `source\_verified` — The cited passages (Lemma 10.1.2, p. 106) were checked against the authors' notes copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://store.doverpublications.com/products/9780486696300)
- [Lemma 10.1.2, p. 106](https://www.math.ru.nl/~bosma/Students/CF.pdf)
- [Lemma 10.1.2, p. 106 (inherited)](https://www.math.ru.nl/~bosma/Students/CF.pdf)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3047-L3049) — lines `3047–3049`; excerpt `sha256:46d4d39e3d51b2837c93b4e701c6caaf1022bcecb3c0b0c8dcc4e198022fc852`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3005-L3007) — lines `3005–3007`; excerpt `sha256:46d4d39e3d51b2837c93b4e701c6caaf1022bcecb3c0b0c8dcc4e198022fc852`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4490-L4493) — lines `4490–4493`; excerpt `sha256:3bb82e6b41bc7ebd606d251e5b57d3c92e82927c527268e1c978c3131c24c529`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4432-L4435) — lines `4432–4435`; excerpt `sha256:3bb82e6b41bc7ebd606d251e5b57d3c92e82927c527268e1c978c3131c24c529`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1372](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1372-L1372), [cite at paper/reasoning-parts/erdos251/core.tex:1330](../../paper/reasoning-parts/erdos251/core.tex#L1330-L1330)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3119](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3119-L3119), [cite at paper/reasoning-parts/erdos269/core.tex:3061](../../paper/reasoning-parts/erdos269/core.tex#L3061-L3061)

<a id="source-source-5f85fb0bd75b8b"></a>

### [Prime divisors of shifted factorials](https://doi.org/10.1112/S0024609305004923)

- Source id: `source-5f85fb0bd75b8b`
- Author or public identity: F. Luca, I. E. Shparlinski
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited in both #68 manuscripts as the source of the nonvanishing statement behind the cutoff for polynomial shifts (Lemma 3, which Lai's Lemma 2.1 restates with the bound n!+f(n) \> 1) and of the common-divisor relation for n!+f(n) and (n+k)!+f(n+k) (proof of Lemma 5), both used in the common-denominator growth estimate and its polynomial-shift extension. The paper's theorems concern large prime factors of n!+f(n) and give no irrationality result for the #68 series.
- Source verification: `source\_verified` — Publisher PDF of the published version, printed pp. 809-812, visually inspected. Verifies the two cited steps only.
- Local mapping: `not recorded`

Exact source locations:

- [Lemma 3, printed p. 810: for nonzero f in Z\[X\] there is n\_0, depending only on f, such that f(n)(n+1)...(n+k) - f(n+k) = 0 has no integer solutions (n, k) with n \>= n\_0 and k \>= 1.](https://doi.org/10.1112/S0024609305004923)
- [Proof of Lemma 5, printed p. 811: an integer q \>= 2 dividing both n!+f(n) and (n+k)!+f(n+k) divides f(n)(n+1)...(n+k) - f(n+k), which is nonzero for n \>= n\_0, so q is at most its absolute value.](https://doi.org/10.1112/S0024609305004923)
- [Supplied journal PDF extracted locally and consulted at Lemmas 3–5 with their proofs. No independent audit of the later prime-factor estimates.](https://doi.org/10.1112/S0024609305004923)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3164-L3168) — lines `3164–3168`; excerpt `sha256:dd044dad6d56b9bf4fbea7b10c5f1541732d45804e9ab24eba3d70dc193802b7`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3199-L3203) — lines `3199–3203`; excerpt `sha256:dd044dad6d56b9bf4fbea7b10c5f1541732d45804e9ab24eba3d70dc193802b7`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3164-L3168) — lines `3164–3168`; excerpt `sha256:dd044dad6d56b9bf4fbea7b10c5f1541732d45804e9ab24eba3d70dc193802b7`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L987-L987) — lines `987–987`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L987-L987) — lines `987–987`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L987-L987) — lines `987–987`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L987-L987) — lines `987–987`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L987-L987) — lines `987–987`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L987-L987) — lines `987–987`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1022](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1022-L1022), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1107](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1107-L1107), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2323](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2323-L2323), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2325](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2325-L2325), [cite at paper/reasoning-parts/erdos68/core.tex:987](../../paper/reasoning-parts/erdos68/core.tex#L987-L987), [cite at paper/reasoning-parts/erdos68/core.tex:1072](../../paper/reasoning-parts/erdos68/core.tex#L1072-L1072), [cite at paper/reasoning-parts/erdos68/core.tex:2288](../../paper/reasoning-parts/erdos68/core.tex#L2288-L2288), [cite at paper/reasoning-parts/erdos68/core.tex:2290](../../paper/reasoning-parts/erdos68/core.tex#L2290-L2290)

<a id="source-source-608828559136f9"></a>

### [LeanExplore: A Search Engine for Lean 4 Declarations](https://doi.org/10.48550/arXiv.2506.11085)

- Source id: `source-608828559136f9`
- Author or public identity: J. Asher
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L717-L720) — lines `717–720`; excerpt `sha256:6e5e795918967c2ca83bcb0a103c3da562b3b3aa08b5719dc822b75f46a612b9`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1043](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1043-L1043)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:499](../../paper/systems/cold-clone-to-proof-receipt.tex#L499-L499)

<a id="source-source-619de19af78c4c"></a>

### [Generating special arithmetic functions by Lambert series factorizations](https://doi.org/10.55016/ojs/cdm.v14i1.62425)

- Source id: `source-619de19af78c4c`
- Author or public identity: M. Merca, M. D. Schmidt
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Classical divisor-sum Lambert identity behind the squared-Lambert transfer, which the papers prove directly.
- Source verification: `source\_verified` — The cited passages (equation (1), p. 2 (arXiv v2)) were checked against the arXiv v2 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [equation (1), p. 2 (arXiv v2)](https://doi.org/10.55016/ojs/cdm.v14i1.62425)
- [Lambert factorisation background, not the missing central-residue supply.](https://arxiv.org/abs/1706.00393v2)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5328-L5332) — lines `5328–5332`; excerpt `sha256:3a65bfeacf2ad8a25e0f67d84cbd49de341eed686e5744522532edb843972cc8`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L92-L92) — lines `92–92`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10319-L10326) — lines `10319–10326`; excerpt `sha256:168b06eeef0d655602ef10d79d4d5a2c298c562e5b09b730a812b94d0458d1a2`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10127-L10134) — lines `10127–10134`; excerpt `sha256:168b06eeef0d655602ef10d79d4d5a2c298c562e5b09b730a812b94d0458d1a2`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:489](../../paper/archive/erdos249-257-main-paper.tex#L489-L489), [cite at paper/archive/erdos249-257-main-paper.tex:4083](../../paper/archive/erdos249-257-main-paper.tex#L4083-L4083), [cite at paper/archive/erdos249-257-main-paper.tex:4782](../../paper/archive/erdos249-257-main-paper.tex#L4782-L4782)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1896](../../paper/249/erdos249-totient-reasoning-surface.tex#L1896-L1897), [cite at paper/249/erdos249-totient-reasoning-surface.tex:10184](../../paper/249/erdos249-totient-reasoning-surface.tex#L10184-L10184), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1704](../../paper/reasoning-parts/erdos249/a249_front.tex#L1704-L1705), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9992](../../paper/reasoning-parts/erdos249/a249_front.tex#L9992-L9992)

<a id="source-source-61ce6ad8b2f0ff"></a>

### [Metric properties of polynomials](https://doi.org/10.1007/BF02790232)

- Source id: `source-61ce6ad8b2f0ff`
- Author or public identity: P. Erdős, F. Herzog, G. Piranian
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Original source of the problem (Problem 5, p. 139); its Theorem 1 gives the collinear root-pair segment that the sharp collinear theorem refines, and the remark before Problem 5 gives the two-zero component used in degree three.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [841421 bytes; 24 scanned pages corresponding to printed pages 125–148.](https://doi.org/10.1007/BF02790232)
- [24 pages were read. The title/summary page (PDF p. 1, printed p. 125), the](https://doi.org/10.1007/BF02790232)
- [target boundary (PDF p. 15, printed p. 139), and the references/added-in-proof](https://doi.org/10.1007/BF02790232)
- [page (PDF p. 24, printed p. 148) were also visually checked. OCR is degraded in](https://doi.org/10.1007/BF02790232)
- [- \*\*Notation and scope:\*\* printed p. 125 defines the polynomial](https://doi.org/10.1007/BF02790232)
- [sections.](https://doi.org/10.1007/BF02790232)
- [- \*\*Immediate input:\*\* printed pp. 136–139, Section 5, establishes the local](https://doi.org/10.1007/BF02790232)
- [- \*\*Exact open boundary:\*\* printed p. 139 (PDF p. 15), immediately after that](https://doi.org/10.1007/BF02790232)
- [- \*\*Continuation check:\*\* printed pp. 139–148 proceed through further component](https://doi.org/10.1007/BF02790232)
- [component-with-two-zeros input described at printed p. 139.](https://doi.org/10.1007/BF02790232)
- [- An answer to Problem 5, a universal path-below-two theorem, or a sharp](https://doi.org/10.1007/BF02790232)
- [release's geometric theorem or a solution.](https://doi.org/10.1007/BF02790232)
- [Problem 5, p. 139](https://doi.org/10.1007/BF02790232)
- [Theorem 1, p. 126 (collinear deduction after Theorem 14.1; also Sources paragraph)](https://doi.org/10.1007/BF02790232)
- [remark before Problem 5, p. 139 (cubic proof)](https://doi.org/10.1007/BF02790232)
- [Theorem 1, p. 126 (after Corollary 7.3)](https://doi.org/10.1007/BF02790232)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1163-L1167) — lines `1163–1167`; excerpt `sha256:eacde95a2a008044b34dad3bc740d3a6e33953232b7364e5c222730a382b3f1e`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5394-L5398) — lines `5394–5398`; excerpt `sha256:b88bf461b59f2aca4fbd717fe1f7fae9a31ad41586223d8984be19883d35f1de`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5344-L5348) — lines `5344–5348`; excerpt `sha256:b88bf461b59f2aca4fbd717fe1f7fae9a31ad41586223d8984be19883d35f1de`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:eb2e17e35b577140954a7591acc551095ed9c734b8b3766759d96d44591ed27d`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:eb2e17e35b577140954a7591acc551095ed9c734b8b3766759d96d44591ed27d`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:eb2e17e35b577140954a7591acc551095ed9c734b8b3766759d96d44591ed27d`
- [lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean](../../lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean#L47-L52) — lines `47–52`; excerpt `sha256:33cfc2f7e37e3a2c10db006bdf734166bb372b874a1933fa3324a066b6552b44`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1153-L1157) — lines `1153–1157`; excerpt `sha256:30a59f5e096ba7505dd35cd675d019c9ca2baccd756374cea58317676ce9b011`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1000](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1000-L1000), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1057](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1057-L1057)
- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:70](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L70-L70), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:907](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L907-L907)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:83](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L83-L83), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1717](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1717-L1717), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2329](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2329-L2329), [cite at paper/reasoning-parts/erdos1041/core.tex:33](../../paper/reasoning-parts/erdos1041/core.tex#L33-L33), [cite at paper/reasoning-parts/erdos1041/core.tex:1667](../../paper/reasoning-parts/erdos1041/core.tex#L1667-L1667), [cite at paper/reasoning-parts/erdos1041/core.tex:2279](../../paper/reasoning-parts/erdos1041/core.tex#L2279-L2279)

<a id="source-source-62ee65065db497"></a>

### [On the set of points of convergence of a lacunary trigonometric series and the equidistribution properties of related sequences](https://doi.org/10.1112/plms/s3-7.1.598)

- Source id: `source-62ee65065db497`
- Author or public identity: P. Erdős, S. J. Taylor
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Bounded-ratio countability theorem for increasing sequences (Theorem 1, p. 600), cited beside Fan's formulation.
- Source verification: `source\_verified` — The cited passages (Theorem 1, p. 600; Theorem 1, p. 600) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1, p. 600](https://doi.org/10.1112/plms/s3-7.1.598)
- [Theorem 1, p. 600](https://doi.org/10.1112/plms/s3-7.1.598)
- [Theorem 1, p. 600 (inherited)](https://doi.org/10.1112/plms/s3-7.1.598)

Public implementation or evidence coordinates:

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1058-L1061) — lines `1058–1061`; excerpt `sha256:a90c5dfbfb8e145cf527f538fca7dae79167bd3b9090eb55e85806bc4d0edba4`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4481-L4484) — lines `4481–4484`; excerpt `sha256:a90c5dfbfb8e145cf527f538fca7dae79167bd3b9090eb55e85806bc4d0edba4`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4423-L4426) — lines `4423–4426`; excerpt `sha256:a90c5dfbfb8e145cf527f538fca7dae79167bd3b9090eb55e85806bc4d0edba4`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:991](../../paper/269/erdos-269-three-prime-running-lcm.tex#L991-L991)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2229](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2229-L2229), [cite at paper/reasoning-parts/erdos269/core.tex:2171](../../paper/reasoning-parts/erdos269/core.tex#L2171-L2171)

<a id="source-source-62f9190aeb7d34"></a>

### [On the irrationality of ∑ 1/(q^n+r)](https://doi.org/10.1016/S0022-314X(05)80041-1)

- Source id: `source-62f9190aeb7d34`
- Author or public identity: P. B. Borwein
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Padé-approximation irrationality results for shifted series at integer bases, cited in the prior-work survey.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- \*\*Reading status:\*\* all seven scanned pages were read through their rendered pages with OCR-assisted transcription. Printed pages 253–259 are PDF pages 1–7.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [1. \*\*Main series and theorem statement (abstract and Theorem 4, PDF pp. 1 and 5–6; printed pp. 253 and 257–258).\*\* The source considers \`sum\_ n\>=1 1/(q^n + r)\` and proves that when \`q\` is an integer greater than one, \`r\` is a nonzero rational, and \`r != -q^n\` for every \`n \>= 1\`, the sum is irrational and is not a Liouville number.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [2. \*\*q-logarithm/Stieltjes function (equations (1)–(4), PDF pp. 2–3; printed pp. 254–255).\*\* It defines \`L^q(x) = sum\_ n\>=1 1/(q^n - x)\` together with its convergent geometric-series form, records the domain restrictions, and gives the functional relation used for the Padé analysis. The paper explains that \`L^q\` is a q-analogue of the logarithm.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [3. \*\*Padé denominator and numerator (Theorem 1, PDF pp. 3–4; printed pp. 255–256).\*\* The main-diagonal Padé approximant \`P\_n(x)/Q\_n(x)\` is constructed explicitly. The source states that \`Q\_n\` has degree \`n\` in \`x\` and degree \`n^2\` in \`q\` with integer coefficients, and that the normalized numerator has the corresponding polynomial and integrality properties.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [4. \*\*Three-term recurrence (Theorem 2, PDF p. 4; printed p. 256).\*\* The denominator polynomials satisfy an explicit three-term recurrence with coefficients displayed in the source. This recurrence belongs to Borwein’s Padé family; the source does not identify it with the Amdeberhan–Zeilberger q-WZ operator.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [5. \*\*Approximation estimate (Theorem 3, PDF p. 5; printed p. 257).\*\* For the stated real range of \`x\`, the source bounds the nonzero Padé error by a quantity that decays rapidly with the diagonal index. It attributes the theorem to Borwein’s earlier Padé analysis and uses it as the approximation input to Theorem 4.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [6. \*\*Arithmetic conversion and non-Liouville conclusion (proof of Theorem 4, PDF pp. 5–6; printed pp. 257–258).\*\* The proof shifts the q-logarithm argument, clears the finite denominators using products of \`q^n - r\` and the q-factorial factors, and obtains integer polynomials in the rational offset. After substituting \`r = A/l\`, the resulting integer linear forms tend to zero too rapidly for rationality. The closing paragraph derives a uniform lower bound of order \`1 / |q|^(constant \* s)\` for rational approximants and concludes that the value is not Liouville.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [7. \*\*Historical boundary (Introduction, PDF p. 1; printed p. 253).\*\* The paper notes that the case \`q = 2, r = -1\` is the Lambert series proved irrational by Erdős, and that the then-unresolved-looking \`sum\_ n\>=1 1/(2^n - 3)\` is a special case of the new theorem.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [- The integer-base hypothesis is essential to the theorem as stated. It does not establish the release’s rational noninteger-base claim at \`3/2\`, and it does not settle universal Erdős Problem #257.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [- The source’s Padé denominator recurrence is not the q-WZ scalar recurrence compared in the local #1049 work. No recurrence transport, endpoint, lattice, valuation, denominator gain, Lean theorem, Comparator result, or Palomar qualification follows from the shared Lambert-series setting.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [- The attribution ceiling is Borwein’s Padé/Stieltjes construction, the displayed polynomial recurrence, the approximation estimate, and Theorem 4 under its exact integer-base and rational-offset hypotheses. No novelty or priority claim is made for the release’s separate formal results.](https://doi.org/10.1016/S0022-314X(05)80041-1)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://doi.org/10.1016/S0022-314X(05)80041-1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5181-L5185) — lines `5181–5185`; excerpt `sha256:ba25c19782edca439fc59536016a13c5d36a33cd2f359c1c6f2080fb7a229a6d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5150-L5154) — lines `5150–5154`; excerpt `sha256:ba25c19782edca439fc59536016a13c5d36a33cd2f359c1c6f2080fb7a229a6d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4895-L4895) — lines `4895–4895`; excerpt `sha256:c2aaa0c462b306e178c3f673ec026c7a33d2885dc0bdb20b45061a7ba1d2ad52`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4926](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4926-L4926), [cite at paper/reasoning-parts/erdos1049/core.tex:4895](../../paper/reasoning-parts/erdos1049/core.tex#L4895-L4895)

<a id="source-source-6346eeeac5036d"></a>

### [Modular functions and transcendence questions](https://doi.org/10.1070/SM1996v187n09ABEH000158)

- Source id: `source-6346eeeac5036d`
- Author or public identity: Yu. V. Nesterenko
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Transcendence result (Corollary 2, p. 1320) behind the Eisenstein rung, with the identification of Ramanujan's P(1/2).
- Source verification: `source\_verified` — The cited passages (Corollary 2, p. 1320) were checked against the journal (English translation) copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Corollary 2, p. 1320](https://doi.org/10.1070/SM1996v187n09ABEH000158)
- [Modular-form transcendence context, not a value theorem for an arbitrary Lambert series.](https://doi.org/10.1070/SM1996v187n09ABEH000158)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5360-L5366) — lines `5360–5366`; excerpt `sha256:77bdb4aaccf3767207aeaa531daa9b36b72b6f99ea6282713f5fedd223ebf6a0`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L2602-L2602) — lines `2602–2602`; excerpt `sha256:4981ac14d5920d3c14f3419aeb71ae38c99632f3a948fda8a4f21229dd4514f8`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L2602-L2602) — lines `2602–2602`; excerpt `sha256:4981ac14d5920d3c14f3419aeb71ae38c99632f3a948fda8a4f21229dd4514f8`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L18396-L18404) — lines `18396–18404`; excerpt `sha256:6d631a23b443180906d917bb60d1a6c65c9fd2a705b5a9ed4ed4e026e91ae20d`
- [lean/Erdos249257/MersenneLambertLadder.lean](../../lean/Erdos249257/MersenneLambertLadder.lean#L15-L27) — lines `15–27`; excerpt `sha256:b17ccf4eb86418af3ba24ecd888e62fe5e23ef5fbf22c02f21fad26eef0562d0`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10304-L10309) — lines `10304–10309`; excerpt `sha256:786abf98fbd01e8ff40ec5a22574fff70c8c6565197a70a1b1cf5f71fbf62c38`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10112-L10117) — lines `10112–10117`; excerpt `sha256:786abf98fbd01e8ff40ec5a22574fff70c8c6565197a70a1b1cf5f71fbf62c38`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:518](../../paper/archive/erdos249-257-main-paper.tex#L518-L518), [cite at paper/archive/erdos249-257-main-paper.tex:549](../../paper/archive/erdos249-257-main-paper.tex#L549-L549)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:2794](../../paper/249/erdos249-totient-reasoning-surface.tex#L2794-L2794), [cite at paper/249/erdos249-totient-reasoning-surface.tex:3980](../../paper/249/erdos249-totient-reasoning-surface.tex#L3980-L3980), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:2602](../../paper/reasoning-parts/erdos249/a249_front.tex#L2602-L2602), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:3788](../../paper/reasoning-parts/erdos249/a249_front.tex#L3788-L3788)

<a id="source-source-63a234b13e4427"></a>

### [Subsum sets: intervals, Cantor sets, and Cantorvals](https://arxiv.org/abs/1106.3779v2)

- Source id: `source-63a234b13e4427`
- Author or public identity: Z. Nitecki
- Kind: `literature`
- Problems: #257, #251
- Relationship and boundary: Strict-tail Cantor and measure theorem (Theorem 4(1), p. 9), credited there to Hornich, behind the achievement-set measure statements.
- Source verification: `source\_verified` — The cited passages (Theorem 4(1), p. 9; Theorem 4(1), p. 9 (three places)) were checked against the arXiv v2 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 4(1), p. 9](https://arxiv.org/abs/1106.3779v2)
- [Theorem 4(1), p. 9 (three places)](https://arxiv.org/abs/1106.3779v2)
- [Theorem 4(1), p. 9 (v2).](https://arxiv.org/pdf/1106.3779v2)

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1678-L1681) — lines `1678–1681`; excerpt `sha256:defd9a2ce501d09c198612d2849b08f6a067d1b43209958db0a0f1bc2c6a9fee`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9630-L9636) — lines `9630–9636`; excerpt `sha256:bfddd679ba6ccf3efd131b25b49729ba82e27339010d41e166fd995306f8494a`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9430-L9436) — lines `9430–9436`; excerpt `sha256:bfddd679ba6ccf3efd131b25b49729ba82e27339010d41e166fd995306f8494a`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L635-L636) — lines `635–636`; excerpt `sha256:4c4861d2cae484653a1e3d2ea0d051919da8b0b8cd404dba7e783d700375f2ff`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3099-L3101) — lines `3099–3101`; excerpt `sha256:17a384a1fdc66bdc50bfc789563acfc6b6e42f091c58ab6c6108261e4a3dd127`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3057-L3059) — lines `3057–3059`; excerpt `sha256:17a384a1fdc66bdc50bfc789563acfc6b6e42f091c58ab6c6108261e4a3dd127`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1126](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1126-L1126), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1593](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1593-L1593)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:635](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L635-L635), [cite at paper/reasoning-parts/erdos251/core.tex:593](../../paper/reasoning-parts/erdos251/core.tex#L593-L593)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1409](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1409-L1409), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2405](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2405-L2405), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:5613](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L5613-L5613), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9549](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9549-L9549), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1209](../../paper/reasoning-parts/erdos257/a257_front.tex#L1209-L1209), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2205](../../paper/reasoning-parts/erdos257/a257_front.tex#L2205-L2205), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:5413](../../paper/reasoning-parts/erdos257/a257_front.tex#L5413-L5413), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9349](../../paper/reasoning-parts/erdos257/a257_front.tex#L9349-L9349)

<a id="source-source-6564b203677735"></a>

### [Small gaps between primes](https://doi.org/10.4007/annals.2015.181.1.7)

- Source id: `source-6564b203677735`
- Author or public identity: J. Maynard
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Bounded-cluster theorem, with the explicit bound 600 at Theorem 1.3, p. 385, cited as a comparison.
- Source verification: `source\_verified` — The cited passages (Theorem 1.1, p. 384; Theorem 1.3, p. 385; Theorem 1.1, p. 384; Theorem 1.3, p. 385) were checked against the published PDF copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1.1, p. 384; Theorem 1.3, p. 385](https://doi.org/10.4007/annals.2015.181.1.7)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L828-L830) — lines `828–830`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3059-L3061) — lines `3059–3061`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3017-L3019) — lines `3017–3019`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2052-L2052) — lines `2052–2052`; excerpt `sha256:1c353b92a6150c3c1fd31caf9ea67c600326deef9ecc2bd683a7fda752871261`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2053-L2053) — lines `2053–2053`; excerpt `sha256:b6e73fa3c5843b9322f980cfbc458e10518d0b0d75da433be27f464b8b1db2c8`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L21-L21) — lines `21–21`; excerpt `sha256:07dad1a6dbaa03c54631370154c906de91a50cd710b3b9c6e143f85e14b3c973`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L828-L830) — lines `828–830`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3059-L3061) — lines `3059–3061`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3017-L3019) — lines `3017–3019`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:768](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L768-L768)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2095](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2095-L2095), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2097](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2097-L2097), [cite at paper/reasoning-parts/erdos251/core.tex:2053](../../paper/reasoning-parts/erdos251/core.tex#L2053-L2053), [cite at paper/reasoning-parts/erdos251/core.tex:2055](../../paper/reasoning-parts/erdos251/core.tex#L2055-L2055)

<a id="source-source-685765cbd1ebe2"></a>

### [Quantitative correlations and some problems on prime factors of consecutive integers](https://arxiv.org/abs/2512.01739v2)

- Source id: `source-685765cbd1ebe2`
- Author or public identity: T. Tao, J. Teräväinen
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Prime-support irrationality at base 2 (Theorem 1.3, p. 4) and its stated extension to every integer base and to prime-power support.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [prime-support irrationality theorem to the release's #257 prior-art map. It](https://arxiv.org/abs/2512.01739v2)
- [records the exact theorem, proof boundary, and source disposition; it is](https://arxiv.org/abs/2512.01739v2)
- [2,133,534 bytes; 61 PDF pages. It was retrieved from the official arXiv](https://arxiv.org/abs/2512.01739v2)
- [pages 4, 44, 56, and 61 were also visually inspected at the theorem, proof,](https://arxiv.org/abs/2512.01739v2)
- [- \*\*Exact release-relevant theorem:\*\* PDF p. 4, Theorem 1.3 (Erdős #69),](https://arxiv.org/abs/2512.01739v2)
- [the details of those modifications to the interested reader. Those remarks](https://arxiv.org/abs/2512.01739v2)
- [theorem claims here.](https://arxiv.org/abs/2512.01739v2)
- [- \*\*Proof entry:\*\* PDF p. 44 begins Section 5, “Application to an irrationality](https://arxiv.org/abs/2512.01739v2)
- [- \*\*Cancellation mechanism:\*\* PDF pp. 45–46, equations (5.4)–(5.8), choose a](https://arxiv.org/abs/2512.01739v2)
- [- \*\*Contradictory variance reduction:\*\* PDF pp. 47–49, equations (5.16)–](https://arxiv.org/abs/2512.01739v2)
- [Reduction Theorem 5.1, whose lower bound contradicts it.](https://arxiv.org/abs/2512.01739v2)
- [- \*\*Parameter and prime-cube input:\*\* PDF pp. 49–50, equations (5.22)–(5.31),](https://arxiv.org/abs/2512.01739v2)
- [set the scales. PDF p. 50, Lemma 5.2, supplies distinct primes in a dyadic](https://arxiv.org/abs/2512.01739v2)
- [through PDF pp. 50–56, treating near, far, and very-far shifts and closing](https://arxiv.org/abs/2512.01739v2)
- [the error estimates; PDF p. 56 records the final Selberg-sieve estimate.](https://arxiv.org/abs/2512.01739v2)
- [- \*\*Auxiliary theorem boundary:\*\* PDF pp. 24–34, Theorem 3.1 and its proof,](https://arxiv.org/abs/2512.01739v2)
- [- \*\*Attribution end point:\*\* PDF p. 61 contains the bibliography and author](https://arxiv.org/abs/2512.01739v2)
- [prime-tuples result; Tao–Teräväinen's Theorem 1.3 is the unconditional](https://arxiv.org/abs/2512.01739v2)
- [series at base 2, PDF p. 4, Theorem 1.3 / equation (1.7), with proof on](https://arxiv.org/abs/2512.01739v2)
- [prime-support sum, as displayed in PDF p. 4, equation (1.7); the release's](https://arxiv.org/abs/2512.01739v2)
- [PDF pp. 24–34, Theorem 3.1, without importing that theorem as a release](https://arxiv.org/abs/2512.01739v2)
- [- Any theorem about the Euler-totient series or the #249 totient kernel.](https://arxiv.org/abs/2512.01739v2)
- [names, Comparator theorem names, Palomar verdicts, totient-kernel rank/basis](https://arxiv.org/abs/2512.01739v2)
- [closed result is Theorem 1.3's base-2 prime-support specialization, not the](https://arxiv.org/abs/2512.01739v2)
- [remarks about other bases and prime powers do not close the universal fixed-](https://arxiv.org/abs/2512.01739v2)
- [Theorem 1.3, p. 4; Theorem 3.1, p. 24](https://arxiv.org/abs/2512.01739v2)
- [Theorem 1.3, p. 4](https://arxiv.org/abs/2512.01739v2)
- [Theorem 1.3 and following paragraph, p. 4; proof, Section 5, pp. 44–56 (v2).](https://arxiv.org/pdf/2512.01739v2)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5419-L5425) — lines `5419–5425`; excerpt `sha256:f3e98b048d91936f24d3575618c5935a8f710849e94afd0c3c7451115a89db41`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1652-L1656) — lines `1652–1656`; excerpt `sha256:b8aeba1b74c5004a308c7a77d0dacb7f303d2e1210da60dac512f3834b9dfb1d`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1066-L1066) — lines `1066–1066`; excerpt `sha256:e8f0eb9c08b32d040eb9d382b55721fcbada06cfa90efaa2936a851eae07396b`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1968-L1968) — lines `1968–1968`; excerpt `sha256:65cd5e4e29d1cdc61e86b1fdfd3aa0da4bc9945beae2af9f53b372cd68363f58`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8192-L8192) — lines `8192–8192`; excerpt `sha256:15ac24d3bb2a60a3a8644dbaa74f8f7584e82afe96beea17331f198e477b3da8`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8545-L8545) — lines `8545–8545`; excerpt `sha256:7ddfabbfa80938c48b779f2b3418205424c4f3e925ef9cc11a07e77b0ce99902`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9141-L9146) — lines `9141–9146`; excerpt `sha256:c427aea096590bf4f8315ac8e13c2e92925eb10e1f02993b79815bfea6191556`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9651-L9656) — lines `9651–9656`; excerpt `sha256:01736f364c6af6f08a7498583610f9761ec3023900cdc6b3a5a25a416cccbf9e`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9665-L9676) — lines `9665–9676`; excerpt `sha256:3171372fd423eb3435f8b30446d71ac1de6f8b8a34d05c55191952194f66d6dd`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9465-L9476) — lines `9465–9476`; excerpt `sha256:3171372fd423eb3435f8b30446d71ac1de6f8b8a34d05c55191952194f66d6dd`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:845](../../paper/257/erdos-257-mersenne-support-subseries.tex#L845-L845)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:756](../../paper/archive/erdos249-257-main-paper.tex#L756-L757)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2249](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2249-L2249), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2049](../../paper/reasoning-parts/erdos257/a257_front.tex#L2049-L2049)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1854](../../paper/synthesis/optimal-sparse-perturbations.tex#L1854-L1854)

<a id="source-source-691e9cc3c46273"></a>

### [Über beliebige Teilsummen absolut konvergenter Reihen](https://doi.org/10.1007/BF01707309)

- Source id: `source-691e9cc3c46273`
- Author or public identity: Hans Hornich
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Original strict-tail geometry/measure provenance, as attributed in Nitecki.
- Source verification: `source\_verified` — Publisher bibliographic record checked; original full text not read.
- Local mapping: `not recorded`

Exact source locations:

- [Publisher article record](https://doi.org/10.1007/BF01707309)
- [Nitecki 2013, Theorem 4](https://doi.org/10.1007/BF01707309)

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1706-L1713) — lines `1706–1713`; excerpt `sha256:9fb245c54bf24e5b9fefda94bc836f1a8dae5e0a9c852475ce12f264cb114471`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9720-L9726) — lines `9720–9726`; excerpt `sha256:e9c60c753e365223406c899dee816ed5743af3cc67081cc3002ceb4f8cf6b1da`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9520-L9526) — lines `9520–9526`; excerpt `sha256:e9c60c753e365223406c899dee816ed5743af3cc67081cc3002ceb4f8cf6b1da`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1125](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1125-L1125)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9548](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9548-L9548), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9348](../../paper/reasoning-parts/erdos257/a257_front.tex#L9348-L9348)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:877](../../paper/synthesis/optimal-sparse-perturbations.tex#L877-L877), [cite at paper/synthesis/optimal-sparse-perturbations.tex:904](../../paper/synthesis/optimal-sparse-perturbations.tex#L904-L904), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1969](../../paper/synthesis/optimal-sparse-perturbations.tex#L1969-L1969)

<a id="source-source-6a5bf83735fdef"></a>

### [A geometric proof that e is irrational and a new measure of its irrationality](https://arxiv.org/pdf/0704.1282v2)

- Source id: `source-6a5bf83735fdef`
- Author or public identity: Jonathan Sondow
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Full text, §§3–4 and 7 including Theorems 1–2 and proofs; the seven-page version includes the addendum. The factorial-index definition is used; the bound for e is not transferred to S.
- Local mapping: `not recorded`

Exact source locations:

- [Full text, §§3–4 and 7 including Theorems 1–2 and proofs; the seven-page version includes the addendum. The factorial-index definition is used; the bound for e is not transferred to S.](https://arxiv.org/pdf/0704.1282v2)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3196-L3200) — lines `3196–3200`; excerpt `sha256:e676e6cb0116aea00ea8f9c6ab98b451db00b3a8f7711be43649ec04855f1014`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3231-L3235) — lines `3231–3235`; excerpt `sha256:e676e6cb0116aea00ea8f9c6ab98b451db00b3a8f7711be43649ec04855f1014`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3196-L3200) — lines `3196–3200`; excerpt `sha256:e676e6cb0116aea00ea8f9c6ab98b451db00b3a8f7711be43649ec04855f1014`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1867](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1867-L1867), [cite at paper/reasoning-parts/erdos68/core.tex:1832](../../paper/reasoning-parts/erdos68/core.tex#L1832-L1832)

<a id="source-source-6accca20cd5e44"></a>

### [Linear independence results for the values of divisor functions series](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf)

- Source id: `source-6accca20cd5e44`
- Author or public identity: F. Luca, Y. Tachiya
- Kind: `literature`
- Problems: #1049, #249, #257
- Relationship and boundary: Restatement of the periodic-coefficient irrationality theorem at integer bases (Theorem A) and the divisor-function example.
- Source verification: `source\_verified` — The cited passages (Theorem A, p. 139; Example 1, p. 140) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem A, p. 139; Example 1, p. 140](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf)
- [Theorem A, p. 139, and Example 2, p. 140](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf)
- [Theorem A, p. 139; Example 2, p. 140 (seven places)](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf)
- [Theorem A, p. 139; Example 2, p. 140.](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5373-L5380) — lines `5373–5380`; excerpt `sha256:690f1f58f32c3dd75fa57e5966f1e713460a42c814f9ab411c04c7e2183ee0b0`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5292-L5298) — lines `5292–5298`; excerpt `sha256:7edeec595003b28ac91040a61c50d3a57a5872bbc9871d704d9ba32a048e1a23`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5261-L5267) — lines `5261–5267`; excerpt `sha256:7edeec595003b28ac91040a61c50d3a57a5872bbc9871d704d9ba32a048e1a23`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4975-L4975) — lines `4975–4975`; excerpt `sha256:21196a6cc9019dd41d30945a6a3d9e8e466447c7c1830ee9e83704db25a0ef1f`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L11735-L11740) — lines `11735–11740`; excerpt `sha256:563923daea706e56c4f2e7175d13053380af2dc3a24ac50d9212c2b0b6d7634e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L12806-L12811) — lines `12806–12811`; excerpt `sha256:448131d83b624b6ce5520dce8ac090fcec58010089d33f41e6a4644fb0ca8a01`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L12962-L12969) — lines `12962–12969`; excerpt `sha256:85e296ca403f80f61aacb885a69266e7645176834ee36a40fbd6e9652cf62bce`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L13680-L13685) — lines `13680–13685`; excerpt `sha256:0de2a3ac66ecee1b3a0e617d573bb7de8678b3975f019984a2d7a83aa43ffbf9`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L14196-L14200) — lines `14196–14200`; excerpt `sha256:12fe3f3b9cef7b6405e234a689ac1e837abfeb24254cb43a2d6815961f8e0b30`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1681-L1687) — lines `1681–1687`; excerpt `sha256:e2ea1dec26aa5bc12b24ae324b5eec9758dfe18eef2464f06f2c610f65164b7d`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9619-L9630) — lines `9619–9630`; excerpt `sha256:dc3b6825148962fe6dcac631ca31bbed24b0c5d155adf89e2b13951655dda752`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9419-L9430) — lines `9419–9430`; excerpt `sha256:dc3b6825148962fe6dcac631ca31bbed24b0c5d155adf89e2b13951655dda752`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1591](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1591-L1591)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5006](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5006-L5006), [cite at paper/reasoning-parts/erdos1049/core.tex:4975](../../paper/reasoning-parts/erdos1049/core.tex#L4975-L4975)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:707](../../paper/archive/erdos249-257-main-paper.tex#L707-L707), [cite at paper/archive/erdos249-257-main-paper.tex:709](../../paper/archive/erdos249-257-main-paper.tex#L709-L709), [cite at paper/archive/erdos249-257-main-paper.tex:713](../../paper/archive/erdos249-257-main-paper.tex#L713-L713), [cite at paper/archive/erdos249-257-main-paper.tex:715](../../paper/archive/erdos249-257-main-paper.tex#L715-L715), [cite at paper/archive/erdos249-257-main-paper.tex:718](../../paper/archive/erdos249-257-main-paper.tex#L718-L718), [cite at paper/archive/erdos249-257-main-paper.tex:3850](../../paper/archive/erdos249-257-main-paper.tex#L3850-L3851), [cite at paper/archive/erdos249-257-main-paper.tex:3856](../../paper/archive/erdos249-257-main-paper.tex#L3856-L3856)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1180](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1180-L1180), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1183](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1183-L1183), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1289](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1289-L1289), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2357](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2357-L2357), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2384](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2384-L2384), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3118](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3118-L3118), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3149](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3149-L3149), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3153](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3153-L3153), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3274](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3274-L3274), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7039](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7039-L7039), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7196](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7196-L7196), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9540](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9540-L9540), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:980](../../paper/reasoning-parts/erdos257/a257_front.tex#L980-L980), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:983](../../paper/reasoning-parts/erdos257/a257_front.tex#L983-L983), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1089](../../paper/reasoning-parts/erdos257/a257_front.tex#L1089-L1089), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2157](../../paper/reasoning-parts/erdos257/a257_front.tex#L2157-L2157), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2184](../../paper/reasoning-parts/erdos257/a257_front.tex#L2184-L2184), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2918](../../paper/reasoning-parts/erdos257/a257_front.tex#L2918-L2918), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2949](../../paper/reasoning-parts/erdos257/a257_front.tex#L2949-L2949), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2953](../../paper/reasoning-parts/erdos257/a257_front.tex#L2953-L2953), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:3074](../../paper/reasoning-parts/erdos257/a257_front.tex#L3074-L3074), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:6839](../../paper/reasoning-parts/erdos257/a257_front.tex#L6839-L6839), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:6996](../../paper/reasoning-parts/erdos257/a257_front.tex#L6996-L6996), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9340](../../paper/reasoning-parts/erdos257/a257_front.tex#L9340-L9340)

<a id="source-source-6ade6fbcd34d79"></a>

### [Advancing Mathematical Research via Human-AI Interactive Theorem Proving](https://arxiv.org/abs/2512.09443)

- Source id: `source-6ade6fbcd34d79`
- Author or public identity: Chenyi Li, Zichen Lai, Dongruo An, Jiang Hu, Zaiwen Wen
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the systems paper as prior published interactive protocol (December 2025): generation and validation held apart by local and global human checks, prove-or-disprove branches, portable proof schemas; no proof assistant, checks are numerical scripts.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1230-L1234) — lines `1230–1234`; excerpt `sha256:efda1bcea3bdd260e4c65a32ee535929550041f56b1b8d4bea22ef144c19c9b4`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1051](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1051-L1051)

<a id="source-source-6b460d123159d9"></a>

### [How to prove that a sequence is not automatic](https://arxiv.org/pdf/2104.13072v1)

- Source id: `source-6b460d123159d9`
- Author or public identity: Jean-Paul Allouche, Jeffrey Shallit, Reem Yassawi
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Survey pointer to Yazdani, the Myhill–Nerode viewpoint and Minsky–Papert gap property. Published in 2022, not merely the 2021 preprint.
- Source verification: `source\_verified` — arXiv v1 (2021), all 23 pages; journal metadata checked separately
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 3, p. 4; Example 4 and Remark 7, p. 5; Theorem 23, p. 11](https://arxiv.org/pdf/2104.13072v1)

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L918-L924) — lines `918–924`; excerpt `sha256:baac1f8ff06d86954ea6fb3d6ea4be3f7ba3e7cc9c207ea61e4e3d1c42db53d0`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10399-L10405) — lines `10399–10405`; excerpt `sha256:baac1f8ff06d86954ea6fb3d6ea4be3f7ba3e7cc9c207ea61e4e3d1c42db53d0`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10207-L10213) — lines `10207–10213`; excerpt `sha256:baac1f8ff06d86954ea6fb3d6ea4be3f7ba3e7cc9c207ea61e4e3d1c42db53d0`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:533](../../paper/249/erdos-249-binary-totient-series.tex#L533-L533)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:299](../../paper/249/erdos249-totient-reasoning-surface.tex#L299-L300), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:107](../../paper/reasoning-parts/erdos249/a249_front.tex#L107-L108)

<a id="source-source-6c2fbacaba626f"></a>

### [Irrationality of ζ\_q(1) and ζ\_q(2)](https://arxiv.org/abs/math/0604312v1)

- Source id: `source-6c2fbacaba626f`
- Author or public identity: K. Postelmans, W. Van Assche
- Kind: `literature`
- Problems: #249, #257, #1049
- Relationship and boundary: Linear independence of 1, zeta\_q(1) and zeta\_q(2) (Theorem 1.3), which the difference rung needs.
- Source verification: `source\_verified` — The cited passages (Theorem 1.3, p. 3 (arXiv v1)) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1.3, p. 3 (arXiv v1)](https://doi.org/10.1016/j.jnt.2006.11.011)
- [q-zeta approximation background; hypotheses and coefficient series differ.](https://arxiv.org/abs/math/0604312v1)
- [Complete 34-page version 1; Theorem 1.3, p. 3; multiple little q-Jacobi construction; Theorem 5.2; Section 6, pp. 29--33.](https://arxiv.org/abs/math/0604312v1)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5366-L5373) — lines `5366–5373`; excerpt `sha256:5a1a511c5f97e370e3878ea3ba811d494255649a47bf397f5ba6a6bc5538a1f3`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L18614-L18619) — lines `18614–18619`; excerpt `sha256:1ddc9c03c740ef6c475f6cab866ca8afd592972f666408305d7d85b4399ccba6`
- [lean/Erdos249257/GcdMomentCalculus.lean](../../lean/Erdos249257/GcdMomentCalculus.lean#L31-L37) — lines `31–37`; excerpt `sha256:df63d9348b43000b662da16518b601491c3fd177be47b864cb61bf0db772b86c`
- [lean/Erdos249257/GcdMomentCalculus.lean](../../lean/Erdos249257/GcdMomentCalculus.lean#L210-L216) — lines `210–216`; excerpt `sha256:f2f4533d57864d5d1c1ccb3b19e15365cab99d16e5b432b8737687af0eb24265`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10298-L10304) — lines `10298–10304`; excerpt `sha256:d225e8a6b24e1aa1895e5b08441a48c78042c267387c9e1c0073591e2991cb37`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10106-L10112) — lines `10106–10112`; excerpt `sha256:d225e8a6b24e1aa1895e5b08441a48c78042c267387c9e1c0073591e2991cb37`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1326-L1332) — lines `1326–1332`; excerpt `sha256:4ce4046469794790aba2dd446aea947f73b80cbd8f7aa313de40dda280a3a9ef`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5338-L5344) — lines `5338–5344`; excerpt `sha256:ae062de55b96a5c30b121b0f18d20452951075be7688d2b736a0ddcd2277483b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5307-L5313) — lines `5307–5313`; excerpt `sha256:ae062de55b96a5c30b121b0f18d20452951075be7688d2b736a0ddcd2277483b`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1106](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1106-L1106)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1237](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1237-L1237), [cite at paper/reasoning-parts/erdos1049/core.tex:1206](../../paper/reasoning-parts/erdos1049/core.tex#L1206-L1206)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3967](../../paper/archive/erdos249-257-main-paper.tex#L3967-L3968)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1912](../../paper/249/erdos249-totient-reasoning-surface.tex#L1912-L1912), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1720](../../paper/reasoning-parts/erdos249/a249_front.tex#L1720-L1720)

<a id="source-source-6cfe654e650970"></a>

### [Arithmetical functions and irrationality of Lambert series](https://doi.org/10.1063/1.3630035)

- Source id: `source-6cfe654e650970`
- Author or public identity: Daniel Duverney
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Only the elementary integral-tail criterion is used. No reliance on the problematic congruence sentence in the separate square-index proof.
- Source verification: `source\_verified` — Complete 12-page author manuscript; Theorem 2, p. 4; separate Lemma 8 proof on p. 8 checked and a local error recorded.
- Local mapping: `not recorded`

Exact source locations:

- [Complete 12-page author manuscript; Theorem 2, p. 4; separate Lemma 8 proof on p. 8 checked and a local error recorded.](https://doi.org/10.1063/1.3630035)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5363-L5368) — lines `5363–5368`; excerpt `sha256:4948c1fb7d6744d97873f78ed67c6b8f64ed69d62dfe299bf8c4335148a7d850`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5332-L5337) — lines `5332–5337`; excerpt `sha256:4948c1fb7d6744d97873f78ed67c6b8f64ed69d62dfe299bf8c4335148a7d850`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5012](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5012-L5012), [cite at paper/reasoning-parts/erdos1049/core.tex:4981](../../paper/reasoning-parts/erdos1049/core.tex#L4981-L4981)

<a id="source-source-6d8837bbc174ce"></a>

### [On Kakeya Conditions for Achievement Sets](https://link.springer.com/article/10.1007/s00025-021-01479-2)

- Source id: `source-6d8837bbc174ce`
- Author or public identity: Marchwicki, Jacek, Miska, Piotr
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — selected\_primary\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3103-L3105) — lines `3103–3105`; excerpt `sha256:4b2c462e9156fcefa9deab67573f0793906c11306432364ce53464dbb6c19538`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3061-L3063) — lines `3061–3063`; excerpt `sha256:4b2c462e9156fcefa9deab67573f0793906c11306432364ce53464dbb6c19538`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:640](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L640-L640), [cite at paper/reasoning-parts/erdos251/core.tex:598](../../paper/reasoning-parts/erdos251/core.tex#L598-L598)

<a id="source-source-6dbbb774ff928e"></a>

### [Goal Structuring Notation Community Standard, Version 3](https://scsc.uk/gsn-standard)

- Source id: `source-6dbbb774ff928e`
- Author or public identity: SCSC Assurance Case Working Group
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://scsc.uk/gsn-standard)

<a id="source-source-71037224a1dd7c"></a>

### [Comment and formula added to OEIS A256936 (revisions 28 and 31)](https://oeis.org/history?seq=A256936)

- Source id: `source-71037224a1dd7c`
- Author or public identity: A. Eldar
- Kind: `website\_contribution`
- Problems: #249
- Relationship and boundary: Earliest located public post (OEIS revisions of 15 March 2026) of the Möbius-square formula and the coprimality interpretation.
- Source verification: `source\_verified` — The cited passages (revisions 28 and 31, 15 March 2026; revisions 28 and 31) were checked against the downloaded copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [revisions 28 and 31, 15 March 2026](https://oeis.org/history?seq=A256936)
- [revisions 28 and 31](https://oeis.org/history?seq=A256936)
- [Public antecedent for the Möbius-square form; revisions are not calendar dates.](https://oeis.org/history?seq=A256936)

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L898-L901) — lines `898–901`; excerpt `sha256:56a8f02f756379e8b9f86571b2146e088317bf4d41df88c247647efa76da475f`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10282-L10286) — lines `10282–10286`; excerpt `sha256:bb9e02a0cb308737040e1d9af54ab2a42d227d1dbf584528d1d8763f1f2fe1e1`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10090-L10094) — lines `10090–10094`; excerpt `sha256:bb9e02a0cb308737040e1d9af54ab2a42d227d1dbf584528d1d8763f1f2fe1e1`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:710](../../paper/249/erdos-249-binary-totient-series.tex#L710-L710)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1753](../../paper/249/erdos249-totient-reasoning-surface.tex#L1753-L1753), [cite at paper/249/erdos249-totient-reasoning-surface.tex:9870](../../paper/249/erdos249-totient-reasoning-surface.tex#L9870-L9870), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1561](../../paper/reasoning-parts/erdos249/a249_front.tex#L1561-L1561), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9678](../../paper/reasoning-parts/erdos249/a249_front.tex#L9678-L9678)

<a id="source-source-71fb76f6e1363b"></a>

### [Strongly complete sets and a conjecture of Erdős](https://arxiv.org/abs/2607.14071)

- Source id: `source-71fb76f6e1363b`
- Author or public identity: Steve Fan
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Lemma 3.1 (p. 7): the bounded-ratio countability statement in the form used in the papers.
- Source verification: `source\_verified` — The cited preprint's identity, authors, version and the quoted section, lemma, corollary and page locators were directly checked against the v1 PDF. This does not certify the mathematics or imply local adoption.
- Local mapping: `not recorded`

Exact source locations:

- [arXiv v1 (15 July 2026) PDF read in full on 2026-09-15; Lemma 3.1, p. 7, countability of the theta with dist(a\_n theta, Z) -\> 0 for unbounded positive integers with a\_{n+1} \<= lambda a\_n; the paragraph before it credits Eggleston (1952) and Erdős-Taylor (1957); Theorem 1.1 and Corollary 1.2 answer the conjecture listed as Erdős Problem #254.](https://arxiv.org/abs/2607.14071v1)
- [Lemma 3.1, p. 7](https://arxiv.org/abs/2607.14071v1)
- [Supplied v1: Lemma 3.1, proof and preceding attribution paragraph, p. 7; no audit of the entire proof of #254.](https://arxiv.org/abs/2607.14071v1)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4484-L4487) — lines `4484–4487`; excerpt `sha256:4fd45772ff7add1f64a2a0aceb707abf3ec134b84b8189985e359c4a31876a7b`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1061-L1064) — lines `1061–1064`; excerpt `sha256:89365f17cd5c9375bfee104214e4355cd14808bfdc25bae5d0d57d71698246ad`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4426-L4429) — lines `4426–4429`; excerpt `sha256:4fd45772ff7add1f64a2a0aceb707abf3ec134b84b8189985e359c4a31876a7b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2173-L2173) — lines `2173–2173`; excerpt `sha256:b87bb3e4a7af82e9910a8693bb635b75f50fdfb4e5b86a06543454c0545aca25`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L992-L992) — lines `992–992`; excerpt `sha256:25f62404517277408df2984823356363c2bc4a97bfc1509a78dca579fdbc0562`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:992](../../paper/269/erdos-269-three-prime-running-lcm.tex#L992-L992)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2231](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2231-L2231), [cite at paper/reasoning-parts/erdos269/core.tex:2173](../../paper/reasoning-parts/erdos269/core.tex#L2173-L2173)

<a id="source-source-724fef812699b7"></a>

### [Distribution of factorials modulo $p$](https://www.numdam.org/article/JTNB_2017__29_1_169_0.pdf)

- Source id: `source-724fef812699b7`
- Author or public identity: Klurman, Oleksiy, Munsch, Marc
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Primary journal PDF: introduction and Theorems 2.1–2.2; proof of Theorem 2.1 consulted through p. 174. Analytic inputs not independently re-proved.
- Local mapping: `not recorded`

Exact source locations:

- [Primary journal PDF: introduction and Theorems 2.1–2.2; proof of Theorem 2.1 consulted through p. 174. Analytic inputs not independently re-proved.](https://www.numdam.org/article/JTNB_2017__29_1_169_0.pdf)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3251-L3255) — lines `3251–3255`; excerpt `sha256:a48ddc588b042ca4c1ef063504be6dd2e3c0c0d8f6ce9a6a0b3fe1989375c081`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3216-L3220) — lines `3216–3220`; excerpt `sha256:a48ddc588b042ca4c1ef063504be6dd2e3c0c0d8f6ce9a6a0b3fe1989375c081`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1978](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1978-L1978), [cite at paper/reasoning-parts/erdos68/core.tex:1943](../../paper/reasoning-parts/erdos68/core.tex#L1943-L1943)

<a id="source-source-741da55b02c5a9"></a>

### [(Non)automaticity of number theoretic functions](https://doi.org/10.5802/jtnb.718)

- Source id: `source-741da55b02c5a9`
- Author or public identity: M. Coons
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Non-k-regularity of the totient, the antecedent that the exact finite-level ranks refine.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [795513 bytes; 15 PDF pages. The copy was retrieved from the official](https://doi.org/10.5802/jtnb.718)
- [PDF pages were read, and all 15 PDF pages were visually checked;](https://doi.org/10.5802/jtnb.718)
- [- \*\*Definitions and scope:\*\* Printed pp. 339--340 (PDF pp. 2--3) define the](https://doi.org/10.5802/jtnb.718)
- [- \*\*Regularity framework:\*\* Printed p. 348 (PDF p. 11) defines a](https://doi.org/10.5802/jtnb.718)
- [\`ℤ\`-module. The same page states Theorem 3.1, the meromorphic-continuation](https://doi.org/10.5802/jtnb.718)
- [property for Dirichlet series of \`k\`-regular sequences, and Corollary 3.1,](https://doi.org/10.5802/jtnb.718)
- [the non-regularity criteria used in the next theorem.](https://doi.org/10.5802/jtnb.718)
- [- \*\*Totient theorem:\*\* Printed p. 348 (PDF p. 11) states \*\*Theorem 3.2\*\*:](https://doi.org/10.5802/jtnb.718)
- [zero-counting input and Corollary 3.1. This is the exact external source](https://doi.org/10.5802/jtnb.718)
- [- \*\*Bibliographic and rights boundary:\*\* Printed p. 352 (PDF p. 15) gives](https://doi.org/10.5802/jtnb.718)
- [determinant construction, Erdős Problem #249, and the repository's theorem](https://doi.org/10.5802/jtnb.718)
- [names; none occurs. The source states the global non-\`k\`-regularity theorem,](https://doi.org/10.5802/jtnb.718)
- [or the separate all-base conditional theorem.](https://doi.org/10.5802/jtnb.718)
- [- Attribution of the theorem that Euler's totient function is not](https://doi.org/10.5802/jtnb.718)
- [\`k\`-regular for any integer \`k ≥ 2\` to Coons, Theorem 3.2, stated on](https://doi.org/10.5802/jtnb.718)
- [\`k\`-kernel over \`ℤ\`, printed p. 348.](https://doi.org/10.5802/jtnb.718)
- [totient non-regularity theorem, printed p. 349.](https://doi.org/10.5802/jtnb.718)
- [- The all-base affine-totient independence theorem attributed to Martin, or](https://doi.org/10.5802/jtnb.718)
- [the global non-\`k\`-regularity theorem settles Erdős Problem #249.](https://doi.org/10.5802/jtnb.718)
- [rank theorem stated by Coons. The bridge is elementary for integer-valued](https://doi.org/10.5802/jtnb.718)
- [Theorem 3.2, p. 348 (also Cor. 3.1)](https://doi.org/10.5802/jtnb.718)
- [Theorem 3.2](https://doi.org/10.5802/jtnb.718)
- [Earlier non-regularity of the totient in every base; not the exact rank formula.](https://doi.org/10.5802/jtnb.718)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5349-L5355) — lines `5349–5355`; excerpt `sha256:4a7aa0cbb0dba5d29390adbbc95554c796fb3eee93f2efae803d6c97270c9768`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L873-L877) — lines `873–877`; excerpt `sha256:3a615d5188e3c811f81c9421c1fae9cae57aa51eaecc361017b08887fd690350`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L78-L78) — lines `78–78`; excerpt `sha256:c1960cd50c0146b008839691c83ef53220ec6bdf251ce3c02d30ff006670e01a`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L79-L79) — lines `79–79`; excerpt `sha256:b6ce0fb599e9bf02898ae89ea89e3bf47a7a31efcaab7ffbe2a9e2aaaae8ab8c`
- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L166-L166) — lines `166–166`; excerpt `sha256:3260d5a1253a2750f8cda31532306f204142e47cb4ce3964043dff2fdb598f14`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L279-L279) — lines `279–279`; excerpt `sha256:48a3dc935a9efd4f525b4196ade8751cfd054cab2285d0b3acf1c074f18578f9`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L95-L95) — lines `95–95`; excerpt `sha256:cb49a811183c00893bef1ffc247d63d3efebe505db66c5ea17d14f12b750a7bf`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L95-L95) — lines `95–95`; excerpt `sha256:cb49a811183c00893bef1ffc247d63d3efebe505db66c5ea17d14f12b750a7bf`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L279-L279) — lines `279–279`; excerpt `sha256:48a3dc935a9efd4f525b4196ade8751cfd054cab2285d0b3acf1c074f18578f9`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10253-L10258) — lines `10253–10258`; excerpt `sha256:5cedcebcfca20ab63e92ba4441d035c85b0a632e564a43408ffe6b79fe30ae48`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10061-L10066) — lines `10061–10066`; excerpt `sha256:5cedcebcfca20ab63e92ba4441d035c85b0a632e564a43408ffe6b79fe30ae48`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:990](../../paper/systems/claim-faithful-publication-systems-paper.tex#L990-L990), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1056](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1056-L1056)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:79](../../paper/249/erdos-249-binary-totient-series.tex#L79-L79), [cite at paper/249/erdos-249-binary-totient-series.tex:527](../../paper/249/erdos-249-binary-totient-series.tex#L527-L527)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3176](../../paper/archive/erdos249-257-main-paper.tex#L3176-L3176)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:287](../../paper/249/erdos249-totient-reasoning-surface.tex#L287-L287), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7005](../../paper/249/erdos249-totient-reasoning-surface.tex#L7005-L7005), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8742](../../paper/249/erdos249-totient-reasoning-surface.tex#L8742-L8742), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:95](../../paper/reasoning-parts/erdos249/a249_front.tex#L95-L95), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6813](../../paper/reasoning-parts/erdos249/a249_front.tex#L6813-L6813), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8550](../../paper/reasoning-parts/erdos249/a249_front.tex#L8550-L8550)

<a id="source-source-75e79d15dfab15"></a>

### [Mathematics in the age of AI](https://doi.org/10.48550/arXiv.2608.16753)

- Source id: `source-75e79d15dfab15`
- Author or public identity: T. Tao
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1642-L1646) — lines `1642–1646`; excerpt `sha256:0e32e51882f8449928d597050d67e151bf67b120c65ffffdeb1ad3182cbfbb6a`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1054](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1054-L1054)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:434](../../paper/systems/open-source-mathematics-strategy.tex#L434-L434), [cite at paper/systems/open-source-mathematics-strategy.tex:1107](../../paper/systems/open-source-mathematics-strategy.tex#L1107-L1107)

<a id="source-source-77333436a9e579"></a>

### [Achievement sets -- current results and open problems](https://arxiv.org/abs/2512.17285v1)

- Source id: `source-77333436a9e579`
- Author or public identity: G{\\l}\\k{a}b, Szymon, Prus-Wi\\'sniowski, Franciszek
- Kind: `literature`
- Problems: #251, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Sections 1 and 6](https://arxiv.org/abs/2512.17285v1)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L634-L634) — lines `634–634`; excerpt `sha256:8d5dd05c085a4fd98e3f503d81e2c85f42cafdb7ab70462763044bc5e7a1c380`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3087-L3089) — lines `3087–3089`; excerpt `sha256:61ad353ab13c9df0f317f4f72d599dc10397c01254ccf1035a02cf84853d8304`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3045-L3047) — lines `3045–3047`; excerpt `sha256:61ad353ab13c9df0f317f4f72d599dc10397c01254ccf1035a02cf84853d8304`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9726-L9732) — lines `9726–9732`; excerpt `sha256:e118982ef9fb8a4e691c79683424d1b891a905dfc8672b0a0f1e9237f5fb3d99`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9526-L9532) — lines `9526–9532`; excerpt `sha256:e118982ef9fb8a4e691c79683424d1b891a905dfc8672b0a0f1e9237f5fb3d99`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:634](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L634-L634), [cite at paper/reasoning-parts/erdos251/core.tex:592](../../paper/reasoning-parts/erdos251/core.tex#L592-L592)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9550](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9550-L9550), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9350](../../paper/reasoning-parts/erdos257/a257_front.tex#L9350-L9350)

<a id="source-source-779915b8355ac1"></a>

### [Achievable Cantorvals almost without reversed Kakeya conditions](https://arxiv.org/abs/2412.08768v1)

- Source id: `source-779915b8355ac1`
- Author or public identity: Prus-Wi\\'sniowski, Franciszek, Ptak, Jolanta
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — full\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L628-L629) — lines `628–629`; excerpt `sha256:b7acbadf514865bc634e221a2b56c30a420e8adc4a8760dde974814e250b0456`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3089-L3091) — lines `3089–3091`; excerpt `sha256:a876ac96db99087a07bfa49f869f9990f286e49a52310ceab8423d7980641577`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3047-L3049) — lines `3047–3049`; excerpt `sha256:a876ac96db99087a07bfa49f869f9990f286e49a52310ceab8423d7980641577`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:629](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L629-L629), [cite at paper/reasoning-parts/erdos251/core.tex:587](../../paper/reasoning-parts/erdos251/core.tex#L587-L587)

<a id="source-source-77ddbf43e364f7"></a>

### [On the irrationality of polynomial Cantor series](https://www.impan.pl/shop/en/publication/transaction/download/product/82186)

- Source id: `source-77ddbf43e364f7`
- Author or public identity: Jaroslav Hančl, Robert Tijdeman
- Kind: `literature`
- Problems: #243, #269
- Relationship and boundary: The polynomial theorem supports public attribution. The general signed-array step is analysed separately in SOURCE\_BOUNDARY\_NOTE.md; do not import it without boundary control.
- Source verification: `source\_verified` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 2.2 and derivation, printed pp. 39–40](https://www.impan.pl/shop/en/publication/transaction/download/product/82186)
- [Theorem 4.2 and proof, printed p. 51](https://www.impan.pl/shop/en/publication/transaction/download/product/82186)
- [Author text: Theorems 2.2 and 3.1 with proofs (pp. 3–6), and Theorems 4.1–4.2 with proofs (pp. 13–15).](https://www.math.leidenuniv.nl/~tijdeman/hancti17.pdf)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1460-L1466) — lines `1460–1466`; excerpt `sha256:fdc72e5f8bd263e4a323f5c9a3cde8b9b721106fee45e5666a814b1163e3a605`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4162-L4168) — lines `4162–4168`; excerpt `sha256:fdc72e5f8bd263e4a323f5c9a3cde8b9b721106fee45e5666a814b1163e3a605`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4123-L4129) — lines `4123–4129`; excerpt `sha256:fdc72e5f8bd263e4a323f5c9a3cde8b9b721106fee45e5666a814b1163e3a605`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1064-L1067) — lines `1064–1067`; excerpt `sha256:45604844b23b875721c499f1d941719928dcc2b6bb269b97c8564702e5d3051b`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4493-L4496) — lines `4493–4496`; excerpt `sha256:45604844b23b875721c499f1d941719928dcc2b6bb269b97c8564702e5d3051b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4435-L4438) — lines `4435–4438`; excerpt `sha256:45604844b23b875721c499f1d941719928dcc2b6bb269b97c8564702e5d3051b`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1222](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1222-L1222), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1277](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1277-L1277)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:994](../../paper/269/erdos-269-three-prime-running-lcm.tex#L994-L994)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:846](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L846-L846), [cite at paper/reasoning-parts/erdos243/core.tex:807](../../paper/reasoning-parts/erdos243/core.tex#L807-L807)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2590](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2590-L2590), [cite at paper/reasoning-parts/erdos269/core.tex:2532](../../paper/reasoning-parts/erdos269/core.tex#L2532-L2532)

<a id="source-source-78565c625f0ea3"></a>

### [On the number of positive integers ≤ x and free of prime factors \> y](https://doi.org/10.1016/0022-314X(86)90013-2)

- Source id: `source-78565c625f0ea3`
- Author or public identity: A. Hildebrand
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Smooth-number counting theory, cited to distinguish its varying-bound notion of smoothness from the fixed prime set used here.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Contrast with varying-smoothness asymptotics; not used for the fixed-prime shell bound.](https://doi.org/10.1016/0022-314x(86)90013-2)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4450-L4453) — lines `4450–4453`; excerpt `sha256:5eafead45851c5d9d3dbc7e8333b2811c3bfb396c82d092e088a35955fc4a00e`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4392-L4395) — lines `4392–4395`; excerpt `sha256:5eafead45851c5d9d3dbc7e8333b2811c3bfb396c82d092e088a35955fc4a00e`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L122-L122) — lines `122–122`; excerpt `sha256:46b167725fbe089dbde15bd1c1125d18dbd277b79357403bbf40c73a4a9a1c6c`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:180](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L180-L180), [cite at paper/reasoning-parts/erdos269/core.tex:122](../../paper/reasoning-parts/erdos269/core.tex#L122-L122)

<a id="source-source-7935fe19eb831b"></a>

### [q-Apéry irrationality proofs by q-WZ pairs](https://arxiv.org/abs/math/9804122)

- Source id: `source-7935fe19eb831b`
- Author or public identity: T. Amdeberhan, D. Zeilberger
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: q-WZ construction for the same Lambert value; its operator gives the nonzero residual on Van Assche's diagonal.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- \*\*Reading status:\*\* the complete seven-page source was read from its text layer and page renders. Printed page numbers 1–7 match PDF pages 1–7.](https://arxiv.org/abs/math/9804122)
- [1. \*\*Target q-series (Introduction, printed p. 1; PDF p. 1).\*\* The paper defines](https://arxiv.org/abs/math/9804122)
- [2. \*\*q-WZ setup and explicit scalar operator (Sections 1.1–1.5, printed pp. 2–3; PDF pp. 2–3).\*\* The source defines q-WZ pairs and the associated q-WZ 1-form, then gives explicit potential and mollifier functions, sequences (a(n),b(n)), and an order-two operator](https://arxiv.org/abs/math/9804122)
- [Its displayed telescoping identities show that both constructed sequences solve (Lu(n)=0). The coefficient formulas (y\_0,y\_1,y\_2) are printed in Sections 1.5 and 2.5.](https://arxiv.org/abs/math/9804122)
- [3. \*\*q-harmonic approximation and theorem (Sections 1.6–1.7, printed pp. 3–4; PDF pp. 3–4).\*\* Equations (1.6.1)–(1.6.4) give the growth and rational approximation estimates; Lemmas 1–2 clear denominators and state the error exponent. Theorem 1 on printed p. 4 states: if (|q|\>1) is an integer, then (h\_q(1)) is irrational with irrationality measure 4.80.](https://arxiv.org/abs/math/9804122)
- [4. \*\*Alternating q-analogue (Sections 2.1–2.7, printed pp. 5–6; PDF pp. 5–6).\*\* The paper supplies the analogous explicit q-WZ form, operator, telescoping identities, approximation estimates, and denominator-clearing Lemmas 3–4 for ( Ln \_q(2)). Theorem 2 on printed p. 6 states: if (|q|0,1) is an integer, then ( Ln \_q(2)) is irrational with irrationality measure 4.80.](https://arxiv.org/abs/math/9804122)
- [5. \*\*Computer-assisted construction disclosure (printed pp. 2 and 5; PDF pp. 2 and 5).\*\* The authors state that the claims in Sections 1.1–1.5 and 2.1–2.5 were found using the Maple package qEKHAD and that a script substantiating them is available on the paper’s web pages. The printed telescoping identities and subsequent estimates are the source’s mathematical record; this disclosure is not a Lean verification.](https://arxiv.org/abs/math/9804122)
- [- The local residual at (n=0) for Van Assche’s different moving diagonal is \*\*not\*\* a theorem stated in this paper. It is a separately computed and Lean-checked non-transfer statement; the source supplies only the original operator and its own sequences.](https://arxiv.org/abs/math/9804122)
- [- The attribution ceiling is the authors’ q-WZ/Apéry construction and the two stated integer-parameter irrationality theorems with their reported irrationality measure. No novelty or priority claim is made for the local residual or its formal proof.](https://arxiv.org/abs/math/9804122)
- [Sec. 1.5, p. 2](https://doi.org/10.1006/aama.1997.0565)
- [(bare cite) Theorems 1-2, measure 4.80](https://doi.org/10.1006/aama.1997.0565)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://doi.org/10.1006/aama.1997.0565)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5191-L5197) — lines `5191–5197`; excerpt `sha256:d5178dbf9e857836e9898ea177d620546af9d24a1826f669a5c173ec6dea9c58`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5160-L5166) — lines `5160–5166`; excerpt `sha256:d5178dbf9e857836e9898ea177d620546af9d24a1826f669a5c173ec6dea9c58`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4909-L4909) — lines `4909–4909`; excerpt `sha256:e85a60b5f00cd26f892425661c3e141ada248c650f76fa1bbab1b0d4d117a642`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L88-L95) — lines `88–95`; excerpt `sha256:2223d196ea50c7aa4910ff7135c17302d35865756bc58597c18dfb8b05e931ac`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4940](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4940-L4940), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4961](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4961-L4961), [cite at paper/reasoning-parts/erdos1049/core.tex:4909](../../paper/reasoning-parts/erdos1049/core.tex#L4909-L4909), [cite at paper/reasoning-parts/erdos1049/core.tex:4930](../../paper/reasoning-parts/erdos1049/core.tex#L4930-L4930)

<a id="source-source-79afab8abaf9d5"></a>

### [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the Erdős Problems](https://arxiv.org/abs/2601.22401)

- Source id: `source-79afab8abaf9d5`
- Author or public identity: Tony Feng, Trieu Trinh, Garrett Bingham, Jiwon Kang, Shengtong Zhang, Sang-hyun Kim, Kevin Barreto, Carl Schildkraut, Junehyuk Jung, Jaehyeon Seo, Carlo Pagano, Yuri Chervonyi, Dawsen Hwang, Kaiying Hou, Sergei Gukov, Cheng-Chiang Tsai, Hyunwoo Choi, Youngbeom Jin, Wei-Yuan Li, Hao-An Wu, Ruey-An Shiu, Yu-Sheng Shih, Quoc V. Le, Thang Luong
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: The round-7 research-commons note cites the version-1 human evaluation distinction between technical validity and intended-problem meaning. Older systems-paper citations remain registered as bibliography contexts, without passage-level verification by this round-7 review.
- Source verification: `source\_verified` — Only the round-7 README passage at lines 50–54 is source-verified against arXiv:2601.22401v1 §1.1 and Table 2. No full paper audit, global comparison, or verification of older manuscript claims.
- Local mapping: `bounded\_round7\_source\_use` — Version-1 §1.1 and Table 2 checked for the round-7 README statement; prior manuscript comparisons are outside this review.

Exact source locations:

- [§1.1, human evaluation and Table 2: 200 adjudicated responses; 63 technically correct; 13 meaningfully correct; 50 valid under unintended readings.](https://arxiv.org/html/2601.22401v1)

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1712-L1717) — lines `1712–1717`; excerpt `sha256:35c50b80ea4e9bece2ad431b8db8fe260367c76ed945564205813263b357e81f`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1139-L1143) — lines `1139–1143`; excerpt `sha256:10b6425a7219ff0ff262d8974728a77849f4d7543b958b9923084c67335ca1f3`
- [docs/research-commons/rounds/round7/README.md](../../docs/research-commons/rounds/round7/README.md#L56-L60) — lines `56–60`; excerpt `sha256:1d66252ee7cb6baaf5065f96ec3ab4dad3e7296eca6d2c98ed0d5c7e41e08a97`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1051](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1051-L1051)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:742](../../paper/systems/open-source-mathematics-strategy.tex#L742-L742), [cite at paper/systems/open-source-mathematics-strategy.tex:822](../../paper/systems/open-source-mathematics-strategy.tex#L822-L822), [cite at paper/systems/open-source-mathematics-strategy.tex:854](../../paper/systems/open-source-mathematics-strategy.tex#L854-L854), [cite at paper/systems/open-source-mathematics-strategy.tex:1064](../../paper/systems/open-source-mathematics-strategy.tex#L1064-L1064)

<a id="source-source-7a9657920d576b"></a>

### [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.144)

- Source id: `source-7a9657920d576b`
- Author or public identity: Pavol Kebis, Florian Luca, Joël Ouaknine, Andrew Scoones, James Worrell
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Fixed-base finite-alphabet echoing, including non-vanishing mismatch sums; a radix-word coding alone does not apply it.
- Source verification: `source\_verified` — Supplied full text, especially Definition 3, Theorems 4 and 6, Claim 7 and the Subspace-Theorem argument. Not a fresh audit of every Arnoux–Rauzy example.
- Local mapping: `not recorded`

Exact source locations:

- [Supplied full text, especially Definition 3, Theorems 4 and 6, Claim 7 and the Subspace-Theorem argument. Not a fresh audit of every Arnoux–Rauzy example.](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.144)

Public implementation or evidence coordinates:

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1070-L1073) — lines `1070–1073`; excerpt `sha256:b9e2249bc4d01297697400d9029b3c8e7883b75d69de50546f4bde27319bc74f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4499-L4502) — lines `4499–4502`; excerpt `sha256:b9e2249bc4d01297697400d9029b3c8e7883b75d69de50546f4bde27319bc74f`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4441-L4444) — lines `4441–4444`; excerpt `sha256:b9e2249bc4d01297697400d9029b3c8e7883b75d69de50546f4bde27319bc74f`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:999](../../paper/269/erdos-269-three-prime-running-lcm.tex#L999-L999)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3394](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3394-L3394), [cite at paper/reasoning-parts/erdos269/core.tex:3336](../../paper/reasoning-parts/erdos269/core.tex#L3336-L3336)

<a id="source-source-7aa96129ebb643"></a>

### [The File Drawer Problem and Tolerance for Null Results](https://doi.org/10.1037/0033-2909.86.3.638)

- Source id: `source-7aa96129ebb643`
- Author or public identity: Robert Rosenthal
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1324-L1329) — lines `1324–1329`; excerpt `sha256:8c9e993b368de8fbbc0268799b73c63a9a57820cb67067d572137c49613f2ef8`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:410](../../docs/papers/mirror/plectis-public-system.tex#L410-L410), [cite at docs/papers/mirror/plectis-public-system.tex:664](../../docs/papers/mirror/plectis-public-system.tex#L664-L664)

<a id="source-source-7ac8693558c1a2"></a>

### [Critical points and values of complex polynomials](https://www.mathnet.ru/eng/sm1434)

- Source id: `source-7ac8693558c1a2`
- Author or public identity: David Tischler
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — indirect\_via\_full\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1254-L1257) — lines `1254–1257`; excerpt `sha256:6aaf6da69e5a056c56565ce65b93dc9624cd8a22480a7b32eacbb405f875508a`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5505-L5508) — lines `5505–5508`; excerpt `sha256:6aaf6da69e5a056c56565ce65b93dc9624cd8a22480a7b32eacbb405f875508a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5455-L5458) — lines `5455–5458`; excerpt `sha256:6aaf6da69e5a056c56565ce65b93dc9624cd8a22480a7b32eacbb405f875508a`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:971](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L971-L971)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3182](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3182-L3182), [cite at paper/reasoning-parts/erdos1041/core.tex:3132](../../paper/reasoning-parts/erdos1041/core.tex#L3132-L3132)

<a id="source-source-7c8ba4ea6eea79"></a>

### [On the complexity of algebraic numbers I. Expansions in integer bases](https://annals.math.princeton.edu/2007/165-2/p04)

- Source id: `source-7c8ba4ea6eea79`
- Author or public identity: B. Adamczewski, Y. Bugeaud
- Kind: `literature`
- Problems: #249, #269
- Relationship and boundary: Digit-complexity theorem for algebraic numbers, cited for what the method actually asserts and what it conditions on.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1, p. 549; definition of block complexity on the same page](https://annals.math.princeton.edu/2007/165-2/p04)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10382-L10386) — lines `10382–10386`; excerpt `sha256:48c8f377367df5c421434058ed0f1e7474c781ee36061cf7ab0d39eda785c36d`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10190-L10194) — lines `10190–10194`; excerpt `sha256:48c8f377367df5c421434058ed0f1e7474c781ee36061cf7ab0d39eda785c36d`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1085-L1089) — lines `1085–1089`; excerpt `sha256:2d8e8e60c166ca01ea9461e45af9157b2f035c8a50a7d38749db5dbf50c5e728`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4508-L4512) — lines `4508–4512`; excerpt `sha256:ef78f91a2a53616a917a9b8d574a5da55953d5024938b45990e8decb1515b07b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4450-L4454) — lines `4450–4454`; excerpt `sha256:ef78f91a2a53616a917a9b8d574a5da55953d5024938b45990e8decb1515b07b`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1000](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1000-L1000)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8616](../../paper/249/erdos249-totient-reasoning-surface.tex#L8616-L8616), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8424](../../paper/reasoning-parts/erdos249/a249_front.tex#L8424-L8424)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3520](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3520-L3520), [cite at paper/reasoning-parts/erdos269/core.tex:3462](../../paper/reasoning-parts/erdos269/core.tex#L3462-L3462)

<a id="source-source-7d871bf2920e53"></a>

### [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Sleep Theorem-Proving Agent](https://doi.org/10.48550/arXiv.2604.26311)

- Source id: `source-7d871bf2920e53`
- Author or public identity: Youyuan Zhang, Jialiang Sun, Hangrui Bi, Chuqin Geng, Wenjie Ma, Zhaoyu Li, Xujie Si
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://arxiv.org/abs/2604.26311v1)

<a id="source-source-7d923cace5602a"></a>

### [The product of consecutive integers is never a power](https://www.renyi.hu/~p_erdos/1975-46.pdf)

- Source id: `source-7d923cace5602a`
- Author or public identity: Erdős, Paul, Selfridge, John L.
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Primary PDF: introduction and Theorem 1, p. 292, read in text and page image. Deep proof not independently re-proved; square case already predates this paper.
- Local mapping: `not recorded`

Exact source locations:

- [Primary PDF: introduction and Theorem 1, p. 292, read in text and page image. Deep proof not independently re-proved; square case already predates this paper.](https://www.renyi.hu/~p_erdos/1975-46.pdf)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3271-L3275) — lines `3271–3275`; excerpt `sha256:ea1e57fc8df0e5e2dc90fc296ae5b3eb8139cdc0ae9ec706f448b795a1933541`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3236-L3240) — lines `3236–3240`; excerpt `sha256:ea1e57fc8df0e5e2dc90fc296ae5b3eb8139cdc0ae9ec706f448b795a1933541`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2101](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2101-L2101), [cite at paper/reasoning-parts/erdos68/core.tex:2066](../../paper/reasoning-parts/erdos68/core.tex#L2066-L2066)

<a id="source-source-7dc956ce55b7a0"></a>

### [On the irrationality of certain series](https://users.renyi.hu/~p_erdos/1969-09.pdf)

- Source id: `source-7dc956ce55b7a0`
- Author or public identity: P. Erdős
- Kind: `literature`
- Problems: #249, #257, #269, #251, #243
- Relationship and boundary: Attribution to Erdős of the irrationality theorem for pairwise-coprime supports with convergent reciprocal support sum, at every integer base \`t \>= 2\`, printed p. 222 with proof on pp. 223–225. - The divisor-count coefficient identity, congruence construction, and long-base-\`t\` zero-block mechanism in the proof, printed pp. 223–225. - The paper's explicit record of the unproved pairwise-coprimality removal, the unresolved all-primes case, and the other open examples, printed pp. 222–223 and 226. - The publication identity, official retrieval route, exact digest, and page-level locators recorded above. The docstring explicitly identifies the pairwise-coprime support theorem as Erdős (1968) and states the hypotheses retained by the Lean theorem. Corrected attribution: this section develops the pairwise-coprime support theorem whose explicit theorem at lines 10768–10779 and the primary source closure identify as Erdős (1968), not the 1948 full-support Lambert paper.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded` — The CertificateKernel section heading at line9741 says1948, while its theorem docstring at10768 and the primary-source closure identify this pairwise-coprime result as Erdős1968. This source record resolves the attribution; the pinned Lean source heading is retained verbatim.

Exact source locations:

- [This source-evidence record binds Erdős's pairwise-coprime support theorem to](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [the release's #257 prior-art map. It records the theorem's explicit hypotheses](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [436234 bytes; 5 scanned PDF pages, printed pp. 222–226. It was retrieved](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [The title page identifies the author, title, receipt date, and printed page](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [- \*\*Full-support and conjectural context:\*\* printed p. 222 (PDF p. 1) recalls](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [Erdős's earlier theorem that](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [is known. The page states the theorem: if the positive integers](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [- \*\*Additional open examples:\*\* printed p. 223 (PDF p. 2) says the recurrence](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [- \*\*Coefficient identity and congruences:\*\* printed pp. 223–224 (PDF pp. 2–3),](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [- \*\*Long zero block and non-termination:\*\* printed pp. 224–225 (PDF pp. 3–4),](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [theorem.](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [- \*\*Closing boundary:\*\* printed p. 226 (PDF p. 5) says the proof without the](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [- Attribution to Erdős of the irrationality theorem for pairwise-coprime](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [\`t \>= 2\`, printed p. 222 with proof on pp. 223–225.](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [long-base-\`t\` zero-block mechanism in the proof, printed pp. 223–225.](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [proved theorem has pairwise-coprime support and \`sum 1/n\_i \< infinity\`.](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [weaker growth condition as a theorem; the paper supplies no proof for those](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [- Any theorem about the Euler-totient series or the #249 totient kernel.](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [Comparator theorem names, totient-kernel rank/basis statements, Erdős #249,](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [and a proof of universal #257; none occurs. The explicit p. 222 theorem and](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [Theorem 2.1 and (2.4), pp. 85-86](https://doi.org/10.2140/pjm.1974.55.85)
- [Theorem 2.1, pp. 85-86](https://doi.org/10.2140/pjm.1974.55.85)
- [p. 222; pp. 222 and 226](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [p. 222](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [Theorem 2.1, pp. 85–86; proof through p. 87](https://msp.org/pjm/1974/55-1/pjm-v55-n1-p08-s.pdf)
- [p. 222 and p. 226, as already recorded in the supplied papers.](https://users.renyi.hu/~p_erdos/1969-09.pdf)
- [Theorem 2.1, equation (2.4), and proof on printed pp. 85–86; later applications not audited.](https://msp.org/pjm/1974/55-1/pjm-v55-n1-p08-s.pdf)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5307-L5312) — lines `5307–5312`; excerpt `sha256:87ad1ba0f311b57b61a187d8e3c5bf6b16922e8b73a12590b746f135bbf6f48f`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1667-L1671) — lines `1667–1671`; excerpt `sha256:4ea0575269b0cc301d69524665b7d6cb05120bcbba9460851e9fa2718c3cafec`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L142-L142) — lines `142–142`; excerpt `sha256:991b168a6e80106e87c200dde8f2bf29239f5928740465826640d6a7ebc1b93e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L10768-L10777) — lines `10768–10777`; excerpt `sha256:162189e1cf0c892075ed7cffb8ef885d1d9da766b3f16a7a6ae07d5c83afc90e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9741-L9741) — lines `9741–9741`; excerpt `sha256:cdc7c634e30bd34ca3a9b807193c3645b42bcbe20c8c45508b70001c4eae795d`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L136-L136) — lines `136–136`; excerpt `sha256:60f0bf58b5d046c11ae864617ad78433b1670a5ab39cc8ef4eff8211a6ac9f01`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L342-L342) — lines `342–342`; excerpt `sha256:991b168a6e80106e87c200dde8f2bf29239f5928740465826640d6a7ebc1b93e`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L136-L136) — lines `136–136`; excerpt `sha256:60f0bf58b5d046c11ae864617ad78433b1670a5ab39cc8ef4eff8211a6ac9f01`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L149-L149) — lines `149–149`; excerpt `sha256:e3872dd726142058db24d451b073eb106f0d6e35aea52bb385f849574ba5ce02`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1052-L1055) — lines `1052–1055`; excerpt `sha256:38cd73fc723cb87858bf5ad1ff85bc3a6aed38bc336429f816ee84816442c7d9`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4472-L4475) — lines `4472–4475`; excerpt `sha256:38cd73fc723cb87858bf5ad1ff85bc3a6aed38bc336429f816ee84816442c7d9`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4414-L4417) — lines `4414–4417`; excerpt `sha256:38cd73fc723cb87858bf5ad1ff85bc3a6aed38bc336429f816ee84816442c7d9`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3041-L3043) — lines `3041–3043`; excerpt `sha256:f27417f97884dcd2e5140620cdfa45a7fbcbc3cec44992f67d8feb50d91f535c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2999-L3001) — lines `2999–3001`; excerpt `sha256:f27417f97884dcd2e5140620cdfa45a7fbcbc3cec44992f67d8feb50d91f535c`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9610-L9619) — lines `9610–9619`; excerpt `sha256:23b75d9385f4d7c31ec74d72a39ca533b7b4c020d60c4718af8894c4ba6f4ed4`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9410-L9419) — lines `9410–9419`; excerpt `sha256:23b75d9385f4d7c31ec74d72a39ca533b7b4c020d60c4718af8894c4ba6f4ed4`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1456-L1460) — lines `1456–1460`; excerpt `sha256:7534aa59bb234c308a55714341b32d4a03d5c73d5381c36bf619a6d8cdc5e0c4`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4158-L4162) — lines `4158–4162`; excerpt `sha256:7534aa59bb234c308a55714341b32d4a03d5c73d5381c36bf619a6d8cdc5e0c4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4119-L4123) — lines `4119–4123`; excerpt `sha256:7534aa59bb234c308a55714341b32d4a03d5c73d5381c36bf619a6d8cdc5e0c4`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:817](../../paper/systems/claim-faithful-publication-systems-paper.tex#L817-L817), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1056](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1056-L1056)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1220](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1220-L1220), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1274](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1274-L1274)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:56](../../paper/257/erdos-257-mersenne-support-subseries.tex#L56-L56), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:136](../../paper/257/erdos-257-mersenne-support-subseries.tex#L136-L136), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:927](../../paper/257/erdos-257-mersenne-support-subseries.tex#L927-L927), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:940](../../paper/257/erdos-257-mersenne-support-subseries.tex#L940-L940), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1590](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1590-L1590)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:430](../../paper/269/erdos-269-three-prime-running-lcm.tex#L430-L430), [cite at paper/269/erdos-269-three-prime-running-lcm.tex:988](../../paper/269/erdos-269-three-prime-running-lcm.tex#L988-L988)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:841](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L841-L841), [cite at paper/reasoning-parts/erdos243/core.tex:802](../../paper/reasoning-parts/erdos243/core.tex#L802-L802)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:694](../../paper/archive/erdos249-257-main-paper.tex#L694-L694)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1962](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1962-L1962), [cite at paper/reasoning-parts/erdos251/core.tex:1920](../../paper/reasoning-parts/erdos251/core.tex#L1920-L1920)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1178](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1178-L1178), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:978](../../paper/reasoning-parts/erdos257/a257_front.tex#L978-L978)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:362](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L362-L362), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2542](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2542-L2542), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3932](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3932-L3932), [cite at paper/reasoning-parts/erdos269/core.tex:304](../../paper/reasoning-parts/erdos269/core.tex#L304-L304), [cite at paper/reasoning-parts/erdos269/core.tex:2484](../../paper/reasoning-parts/erdos269/core.tex#L2484-L2484), [cite at paper/reasoning-parts/erdos269/core.tex:3874](../../paper/reasoning-parts/erdos269/core.tex#L3874-L3874)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:938](../../paper/synthesis/optimal-sparse-perturbations.tex#L938-L938)

<a id="source-source-7f1f2a3fd9238c"></a>

### [On the length of lemniscates](https://arxiv.org/abs/0805.2295)

- Source id: `source-7f1f2a3fd9238c`
- Author or public identity: A. Eremenko, W. Hayman
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Level-curve length bound (Theorem 1) and existence of an extremal with critical points on the level set (Lemma 5).
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Introduction and Theorem 1 state the EHP conjecture and prove |E(p)| \<= alpha\_0 d \< 9.173d for monic degree-d polynomials.](https://arxiv.org/abs/0805.2295)
- [Lemma 5 (arXiv v2 p. 5): some extremal polynomial for the level-curve length has all its critical points on E(p) = {|p| = 1}; Lemma 6 (p. 7): some extremal polynomial has connected E(p).](https://arxiv.org/abs/0805.2295)
- [Thm. 1 and the lemma on connectedness](https://doi.org/10.1307/mmj/1030132418)
- [Lemma 5](https://doi.org/10.1307/mmj/1030132418)
- [Lemma 5; Theorem 1](https://doi.org/10.1307/mmj/1030132418)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5452-L5457) — lines `5452–5457`; excerpt `sha256:fbbf29db45c62cfa84769c87ea4dfb6dcbc312a557a3335deb161872d3ae4d44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5402-L5407) — lines `5402–5407`; excerpt `sha256:fbbf29db45c62cfa84769c87ea4dfb6dcbc312a557a3335deb161872d3ae4d44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1641-L1641) — lines `1641–1641`; excerpt `sha256:9b744f2b7f5621dd470311a82aeee2e8b051a79200911c2b6b0f3b283301c6d6`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1200-L1205) — lines `1200–1205`; excerpt `sha256:03547751579bddb06550186cbd4cd5363e790e059ff80b147b313232f2329016`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1119](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1119-L1119)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1691](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1691-L1691), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2362](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2362-L2362), [cite at paper/reasoning-parts/erdos1041/core.tex:1641](../../paper/reasoning-parts/erdos1041/core.tex#L1641-L1641), [cite at paper/reasoning-parts/erdos1041/core.tex:2312](../../paper/reasoning-parts/erdos1041/core.tex#L2312-L2312)

<a id="source-source-80c9ae60b7f7be"></a>

### [LeanArchitect: Automating Blueprint Generation for Humans and AI](https://doi.org/10.4230/LIPIcs.ITP.2026.25)

- Source id: `source-80c9ae60b7f7be`
- Author or public identity: T. Zhu, P. Monticone, S. Welleck, J. Avigad
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: The round-7 research-commons note cites LeanArchitect as prior art for a blueprint generated from annotated Lean source. Older manuscript citations remain bibliography contexts, not source-verified by this bounded reading.
- Source verification: `source\_verified` — Only the round-7 README passage at lines 55–58 is source-verified against arXiv:2601.22554v1 Methods §§3.1–3.3 and Figure 1. The informal/formal correspondence distinction is a bounded inference from the paper’s stated mechanism, not a claim of a full audit or unique architecture.
- Local mapping: `bounded\_round7\_source\_use` — Version-1 Methods §§3.1–3.3 and Figure 1 checked for the round-7 README statement.

Exact source locations:

- [§3.1 Overview, §3.2 Blueprint Attribute, §3.3 Environment Extension, and Figure 1: annotated Lean declarations own blueprint metadata, inferred dependencies and proof-status projection.](https://arxiv.org/html/2601.22554v1)

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L692-L697) — lines `692–697`; excerpt `sha256:1f3f3c8f59b09e017af2d71374c7c46368d97929557de076c9b6d0b5f80c83bf`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1363-L1365) — lines `1363–1365`; excerpt `sha256:2791c8042dc468854cefb24a74e27b8ce018aa3c98bb4987cd94e39599e9c97d`
- [docs/research-commons/rounds/round7/README.md](../../docs/research-commons/rounds/round7/README.md#L61-L64) — lines `61–64`; excerpt `sha256:874b2be52514deae844bef1f44fcbc81dfb88cf010c98a26bf6bc0cfa4dae767`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:111](../../paper/systems/claim-faithful-publication-systems-paper.tex#L111-L111), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1042](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1042-L1042)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:477](../../paper/systems/cold-clone-to-proof-receipt.tex#L477-L477)

<a id="source-source-811205223e0788"></a>

### [Sums of singular series with large sets and the tail of the distribution of primes](https://arxiv.org/abs/2210.09775v2)

- Source id: `source-811205223e0788`
- Author or public identity: V. Kuperberg
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Uniform Hardy-Littlewood prime-tuples conjecture (Conjecture 1.3) assumed by the Land and Ringer results.
- Source verification: `source\_verified` — The cited passages (Conjecture 1.3; Conjecture 1.3) were checked against the arXiv v2 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Conjecture 1.3](https://arxiv.org/abs/2210.09775v2)
- [Conjecture 1.3](https://arxiv.org/abs/2210.09775v2)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L820-L822) — lines `820–822`; excerpt `sha256:5cfb10540069185577d738da52c429d1b74a4f8ce94c54018d941550c730eeaf`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3051-L3053) — lines `3051–3053`; excerpt `sha256:5cfb10540069185577d738da52c429d1b74a4f8ce94c54018d941550c730eeaf`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3009-L3011) — lines `3009–3011`; excerpt `sha256:5cfb10540069185577d738da52c429d1b74a4f8ce94c54018d941550c730eeaf`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:488](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L488-L488)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:496](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L496-L496), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:663](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L663-L663), [cite at paper/reasoning-parts/erdos251/core.tex:454](../../paper/reasoning-parts/erdos251/core.tex#L454-L454), [cite at paper/reasoning-parts/erdos251/core.tex:621](../../paper/reasoning-parts/erdos251/core.tex#L621-L621)

<a id="source-source-818467bc1cb170"></a>

### [A bound for Smale's mean value conjecture for complex polynomials](https://people.maths.bris.ac.uk/~maetc/SMVCbound.pdf)

- Source id: `source-818467bc1cb170`
- Author or public identity: Edward Crane
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 1.1 p. 2](https://people.maths.bris.ac.uk/~maetc/SMVCbound.pdf)
- [Lemma 2.1 and Theorem 2.2 p. 5](https://people.maths.bris.ac.uk/~maetc/SMVCbound.pdf)
- [Proof §§3–4](https://people.maths.bris.ac.uk/~maetc/SMVCbound.pdf)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1241-L1246) — lines `1241–1246`; excerpt `sha256:dd81dda92210816aa997d12725fdd2b3d2f7a70097cbd438d5ef8102c0c13e44`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5492-L5497) — lines `5492–5497`; excerpt `sha256:dd81dda92210816aa997d12725fdd2b3d2f7a70097cbd438d5ef8102c0c13e44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5442-L5447) — lines `5442–5447`; excerpt `sha256:dd81dda92210816aa997d12725fdd2b3d2f7a70097cbd438d5ef8102c0c13e44`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1115](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1115-L1115)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:5127](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5127-L5127), [cite at paper/reasoning-parts/erdos1041/core.tex:5077](../../paper/reasoning-parts/erdos1041/core.tex#L5077-L5077)

<a id="source-source-81b67bfd835ac9"></a>

### [The Network Structure of Mathlib](https://doi.org/10.48550/arXiv.2604.24797)

- Source id: `source-81b67bfd835ac9`
- Author or public identity: X. Li, N. Peng, S. Severini, P. Shafto
- Kind: `software`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L714-L717) — lines `714–717`; excerpt `sha256:ebb7c8c62fa7ff44ee571f137c47de8e5508a51405cbdd51807c60b2bad5a1f3`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:496](../../paper/systems/cold-clone-to-proof-receipt.tex#L496-L496)

<a id="source-source-82459d858b7d75"></a>

### [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](https://doi.org/10.48550/arXiv.2605.13137)

- Source id: `source-82459d858b7d75`
- Author or public identity: Guoxiong Gao, Zeming Sun, Jiedong Jiang, Yutong Wang, Jingda Xu, Peihao Wu, Bryan Dai, Bin Dong
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://arxiv.org/abs/2605.13137v2)

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L720-L723) — lines `720–723`; excerpt `sha256:8662990def0156ee9fa798ccb6915b9367683e2590ac54e5debcf5a71f027cb9`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1043](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1043-L1043)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:499](../../paper/systems/cold-clone-to-proof-receipt.tex#L499-L499)

<a id="source-source-86d1745e2d139b"></a>

### [Irrationality of the reciprocal sum of doubly exponential sequences](https://math.colgate.edu/~integers/aa28/aa28.pdf)

- Source id: `source-86d1745e2d139b`
- Author or public identity: J. Koizumi
- Kind: `literature`
- Problems: #243
- Relationship and boundary: The pseudo-greedy formulation with its denominator-cleared tail variables and exact updates, the absorption and descent lemmas, and the product-weighted criteria used as comparators in both papers.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [read. PDF pp. 1, 2, 10, 11, 14, 15, and 17 were also visually checked. The](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [- \*\*Main approximation theorem:\*\* PDF pp. 1–2, Theorem 1, assumes positive](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [- \*\*Problem and pseudo-greedy bridge:\*\* PDF pp. 3–4 state Erdős–Graham's](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [and gap sequence, and explain the open boundary. PDF p. 9, Corollary 3,](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [- \*\*Local state mechanism:\*\* PDF p. 10, Lemmas 2–3, gives the gap-to-next-term](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [recurrence and \`epsilon\_n = 0\` propagation. PDF pp. 11–12, Lemma 4 and its](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [- \*\*Equivalence and conditional endpoint:\*\* PDF pp. 12–13, Theorem 3,](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [proves equivalence of Conjecture 1 and Question 1. PDF pp. 14–15,](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [Proposition 1(1–2), proves eventual zero gaps under its two sign/product](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [conditions; the same pages state Corollary 4, the corresponding recurrence](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [\`a\_(n+1) \>= a\_n^2-a\_n+1\`. PDF p. 16, Remark 3, records the](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [- \*\*End matter:\*\* PDF p. 17 gives the bibliography, including the cited](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [| Corollary 3, p. 9 | Corollary 10, p. 8 | eventual pseudo-greedy transfer and gap convergence |](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [| Lemma 3, p. 10 | Lemma 13, p. 9 | zero-gap absorption |](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [| Lemma 4, pp. 11–12 | Lemma 15, p. 9 | rational state coordinates and updates |](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [| Theorem 3, pp. 12–13 | Theorem 16, pp. 10–11 | equivalence with the Erdős–Graham question |](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [| Proposition 1, pp. 14–15 | Proposition 19, pp. 12–13 | eventual nonnegative-gap descent |](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [| Corollary 4, pp. 14–15 | Corollary 20, pp. 12–13 | conditional recurrence criteria |](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [| Remark 3, p. 16 | Remark 21, p. 13 | Erdős–Straus sufficient rate |](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [preprint citation into a new theorem or change the note's claim ceiling.](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [- Prior art for zero-gap absorption (Lemma 3), eventual nonnegative-gap](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [descent (Proposition 1(2)), and the conditional recurrence statements in](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [Proposition 1/Corollary 4, subject to the published/preprint crosswalk.](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [release's theorem names, and a proof of the unrestricted Erdős–Graham](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [Corollary 3, p. 9](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [Lemmas 2--4, pp. 10--12 (Lemma 3, p. 10; Lemma 4, pp. 11--12)](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [Proposition 1(2), p. 14](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [Corollary 4(1), pp. 14--15](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [(11)--(12), p. 15](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [Remark 3, p. 16](https://math.colgate.edu/~integers/aa28/aa28.pdf)
- [Remark 2 and Algorithm 1, pp. 13--14](https://math.colgate.edu/~integers/aa28/aa28.pdf)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1447-L1453) — lines `1447–1453`; excerpt `sha256:eb7d5ec7e254bbf424e424d7b70e149f642ec316eed5ca8d2357045a54b32cc6`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4144-L4150) — lines `4144–4150`; excerpt `sha256:eb7d5ec7e254bbf424e424d7b70e149f642ec316eed5ca8d2357045a54b32cc6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4105-L4111) — lines `4105–4111`; excerpt `sha256:eb7d5ec7e254bbf424e424d7b70e149f642ec316eed5ca8d2357045a54b32cc6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:116](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L116-L116), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:156](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L156-L156), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:535](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L535-L535), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:540](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L540-L540), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:689](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L689-L689), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1161](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1161-L1162)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:238](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L238-L238), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:859](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L859-L859), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:879](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L879-L879), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:961](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L961-L961), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:967](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L967-L967), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:978](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L978-L978), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:991](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L991-L991), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:992](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L992-L992), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:994](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L994-L994), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1000](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1000-L1000), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1077](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1077-L1077), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2440](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2440-L2440), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2449](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2449-L2449), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2474](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2474-L2474), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2525](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2525-L2525), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2585](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2585-L2585), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2900](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2900-L2900), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2904](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2904-L2904), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3199](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3199-L3199), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3279](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3279-L3279), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3280](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3280-L3280), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3584](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3584-L3584), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3587](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3587-L3587), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3593](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3593-L3593), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3978](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3978-L3979), [cite at paper/reasoning-parts/erdos243/core.tex:199](../../paper/reasoning-parts/erdos243/core.tex#L199-L199), [cite at paper/reasoning-parts/erdos243/core.tex:820](../../paper/reasoning-parts/erdos243/core.tex#L820-L820), [cite at paper/reasoning-parts/erdos243/core.tex:840](../../paper/reasoning-parts/erdos243/core.tex#L840-L840), [cite at paper/reasoning-parts/erdos243/core.tex:922](../../paper/reasoning-parts/erdos243/core.tex#L922-L922), [cite at paper/reasoning-parts/erdos243/core.tex:928](../../paper/reasoning-parts/erdos243/core.tex#L928-L928), [cite at paper/reasoning-parts/erdos243/core.tex:939](../../paper/reasoning-parts/erdos243/core.tex#L939-L939), [cite at paper/reasoning-parts/erdos243/core.tex:952](../../paper/reasoning-parts/erdos243/core.tex#L952-L952), [cite at paper/reasoning-parts/erdos243/core.tex:953](../../paper/reasoning-parts/erdos243/core.tex#L953-L953), [cite at paper/reasoning-parts/erdos243/core.tex:955](../../paper/reasoning-parts/erdos243/core.tex#L955-L955), [cite at paper/reasoning-parts/erdos243/core.tex:961](../../paper/reasoning-parts/erdos243/core.tex#L961-L961), [cite at paper/reasoning-parts/erdos243/core.tex:1038](../../paper/reasoning-parts/erdos243/core.tex#L1038-L1038), [cite at paper/reasoning-parts/erdos243/core.tex:2401](../../paper/reasoning-parts/erdos243/core.tex#L2401-L2401), [cite at paper/reasoning-parts/erdos243/core.tex:2410](../../paper/reasoning-parts/erdos243/core.tex#L2410-L2410), [cite at paper/reasoning-parts/erdos243/core.tex:2435](../../paper/reasoning-parts/erdos243/core.tex#L2435-L2435), [cite at paper/reasoning-parts/erdos243/core.tex:2486](../../paper/reasoning-parts/erdos243/core.tex#L2486-L2486), [cite at paper/reasoning-parts/erdos243/core.tex:2546](../../paper/reasoning-parts/erdos243/core.tex#L2546-L2546), [cite at paper/reasoning-parts/erdos243/core.tex:2861](../../paper/reasoning-parts/erdos243/core.tex#L2861-L2861), [cite at paper/reasoning-parts/erdos243/core.tex:2865](../../paper/reasoning-parts/erdos243/core.tex#L2865-L2865), [cite at paper/reasoning-parts/erdos243/core.tex:3160](../../paper/reasoning-parts/erdos243/core.tex#L3160-L3160), [cite at paper/reasoning-parts/erdos243/core.tex:3240](../../paper/reasoning-parts/erdos243/core.tex#L3240-L3240), [cite at paper/reasoning-parts/erdos243/core.tex:3241](../../paper/reasoning-parts/erdos243/core.tex#L3241-L3241), [cite at paper/reasoning-parts/erdos243/core.tex:3545](../../paper/reasoning-parts/erdos243/core.tex#L3545-L3545), [cite at paper/reasoning-parts/erdos243/core.tex:3548](../../paper/reasoning-parts/erdos243/core.tex#L3548-L3548), [cite at paper/reasoning-parts/erdos243/core.tex:3554](../../paper/reasoning-parts/erdos243/core.tex#L3554-L3554), [cite at paper/reasoning-parts/erdos243/core.tex:3939](../../paper/reasoning-parts/erdos243/core.tex#L3939-L3940)

<a id="source-source-8710374c3e8c9f"></a>

### [Shortest paths in polynomial lemniscate sublevel sets and a problem of Erdős](https://doi.org/10.48550/arXiv.2606.19178)

- Source id: `source-8710374c3e8c9f`
- Author or public identity: V. S. Pendyala
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Origin-to-unit-circle path problem (Erdős #1120; Definition 1.1 and Theorem 1.2), cited to separate its endpoints from the root-pair problem.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded` — {'previous\_public\_locator': 'Theorem 1.2 and introductory discussion, pp. 1–2', 'verified\_correction': 'Theorem 1.2 and introductory discussion, printed/PDF pp. 2–3. The source identifies the online problem as #1120.'}

Exact source locations:

- [Introduction, printed/PDF p. 2: states the origin-to-unit-circle shortest-path problem in the filled sublevel set and identifies the distinct level-lemniscate problem.](https://arxiv.org/abs/2606.19178)
- [Definition 1.1 and Theorem 1.2, printed/PDF p. 3: defines S(n) and proves c√log n ≤ S(n) ≤ πn for sufficiently large n.](https://arxiv.org/abs/2606.19178)
- [Reference \[5\], printed/PDF p. 34: identifies the online record as Erdős Problems #1120.](https://arxiv.org/abs/2606.19178)
- [Definition 1.1 and Theorem 1.2](https://arxiv.org/abs/2606.19178v1)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1176-L1182) — lines `1176–1182`; excerpt `sha256:82d28a8215cfaad9830f9c69ac73ab8a39b6b8fde4ba10c62ec7be6337dc3ff0`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1133](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1133-L1133)

<a id="source-source-892c567092d6f3"></a>

### [Lacunary sequences whose reciprocal sums represent all rational numbers in an interval](https://arxiv.org/abs/2509.24971v3)

- Source id: `source-892c567092d6f3`
- Author or public identity: W. van Doorn, V. Kovač
- Kind: `literature`
- Problems: #251, #257
- Relationship and boundary: Finite reciprocal-sum filling with a divisibility chain, compared with the factorial-modulus chain used here.
- Source verification: `source\_verified` — Primary arXiv v3 PDF, 17 pages, read in full on 15 September 2026; journal reference and DOI taken from the arXiv abstract page and the second author's publication list.
- Local mapping: `not recorded`

Exact source locations:

- [PDF pp. 7-8, Lemma 7 and proof: if x\_1 \> ... \> x\_m \> 0 and x\_i \<= x\_{i+1} + ... + x\_m + x\_m for i \< m, the finite subset sums fill \[0, x\_1 + ... + x\_m\] with gaps at most x\_m.](https://arxiv.org/abs/2509.24971v3)
- [PDF pp. 8-9, Proposition 8 and proof: if every positive integer divides some n\_i, each distinguished n\_{m\_k} is divisible by all earlier terms, and inequality (3.1) holds, then the finite reciprocal sums are exactly the rationals in \[0, sum 1/n\_i).](https://arxiv.org/abs/2509.24971v3)
- [Journal version, Acta Arith. 223 (2026), 275-295; the notes cite statement numbers from arXiv v3.](https://doi.org/10.4064/aa251001-13-1)
- [- \*\*Read artifact:\*\* the arXiv v3 PDF, SHA-256](https://arxiv.org/abs/2509.24971v3)
- [- \*\*Lemma 7, dense filling:\*\* statement on PDF p. 7; proof by induction on](https://arxiv.org/abs/2509.24971v3)
- [- \*\*Proposition 8, sufficient conditions:\*\* statement on PDF p. 8. For a](https://arxiv.org/abs/2509.24971v3)
- [- Any statement about Erdős #251, the series \`sum p\_n 2^(-n)\`, prime](https://arxiv.org/abs/2509.24971v3)
- [Lemma 7 and Proposition 8](https://doi.org/10.4064/aa251001-13-1)
- [Lemma 7 and Proposition 8; Proposition 8](https://doi.org/10.4064/aa251001-13-1)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L593-L594) — lines `593–594`; excerpt `sha256:acd0118c6668b66ae11eee7978ef8959e8909aa7c6b93b4273df7e0a9fefef1b`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3067-L3069) — lines `3067–3069`; excerpt `sha256:9418f72235db07cc6cd7f1772c2ce7a82d075de7ad72f5c574173c93b1d28da6`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3025-L3027) — lines `3025–3027`; excerpt `sha256:9418f72235db07cc6cd7f1772c2ce7a82d075de7ad72f5c574173c93b1d28da6`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L594-L594) — lines `594–594`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L552-L552) — lines `552–552`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L552-L552) — lines `552–552`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L594-L594) — lines `594–594`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L594-L594) — lines `594–594`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1713-L1719) — lines `1713–1719`; excerpt `sha256:08841993ec7ee7aa859d0a63801cb36c9d22ae35f6f155707172b3fa7712308a`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9739-L9748) — lines `9739–9748`; excerpt `sha256:d09ac96b0131bd7dfc76f01dbf0e7d50ec3b4558035379307812584b13065d36`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9539-L9548) — lines `9539–9548`; excerpt `sha256:d09ac96b0131bd7dfc76f01dbf0e7d50ec3b4558035379307812584b13065d36`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:886](../../paper/257/erdos-257-mersenne-support-subseries.tex#L886-L886)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:594](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L594-L594), [cite at paper/reasoning-parts/erdos251/core.tex:552](../../paper/reasoning-parts/erdos251/core.tex#L552-L552)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9214](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9214-L9214), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9014](../../paper/reasoning-parts/erdos257/a257_front.tex#L9014-L9014)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1852](../../paper/synthesis/optimal-sparse-perturbations.tex#L1852-L1852), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1853](../../paper/synthesis/optimal-sparse-perturbations.tex#L1853-L1853), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1972](../../paper/synthesis/optimal-sparse-perturbations.tex#L1972-L1972)

<a id="source-source-8935df46fb4693"></a>

### [The Lambert series factorization theorem](https://doi.org/10.1007/s11139-016-9856-3)

- Source id: `source-8935df46fb4693`
- Author or public identity: M. Merca
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Partition-factorisation background (Theorem 1.2, p. 420) for the Möbius-Mersenne coordinate.
- Source verification: `source\_verified` — The cited passages (Theorem 1.2, p. 420) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1.2, p. 420](https://doi.org/10.1007/s11139-016-9856-3)
- [Earlier Lambert factorisation machinery.](https://doi.org/10.1007/s11139-016-9856-3)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5325-L5328) — lines `5325–5328`; excerpt `sha256:2cc1d6adac4a799350b2f110f64e22883a9a6da730739cce9c316980e35947b3`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L92-L92) — lines `92–92`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10326-L10331) — lines `10326–10331`; excerpt `sha256:68764d4d7a89374c4c04bae75c94f6c2e0e288f6e20da9c4a285948259753998`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10134-L10139) — lines `10134–10139`; excerpt `sha256:68764d4d7a89374c4c04bae75c94f6c2e0e288f6e20da9c4a285948259753998`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:486](../../paper/archive/erdos249-257-main-paper.tex#L486-L486), [cite at paper/archive/erdos249-257-main-paper.tex:487](../../paper/archive/erdos249-257-main-paper.tex#L487-L487), [cite at paper/archive/erdos249-257-main-paper.tex:4082](../../paper/archive/erdos249-257-main-paper.tex#L4082-L4082), [cite at paper/archive/erdos249-257-main-paper.tex:4781](../../paper/archive/erdos249-257-main-paper.tex#L4781-L4781)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:10183](../../paper/249/erdos249-totient-reasoning-surface.tex#L10183-L10183), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9991](../../paper/reasoning-parts/erdos249/a249_front.tex#L9991-L9991)

<a id="source-source-89b9a294db76bb"></a>

### [The arc length of the lemniscate |p(z)|=1](https://doi.org/10.1090/S0002-9939-1995-1223265-3)

- Source id: `source-89b9a294db76bb`
- Author or public identity: P. Borwein
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Level-curve length bound in the history of Erdős #114.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5447-L5452) — lines `5447–5452`; excerpt `sha256:2eb3162258360253b5cf7a590c5d7eefeabfb1b4633350ee641a14035d11359c`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5397-L5402) — lines `5397–5402`; excerpt `sha256:2eb3162258360253b5cf7a590c5d7eefeabfb1b4633350ee641a14035d11359c`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1640-L1640) — lines `1640–1640`; excerpt `sha256:5b6b0635f8d7bc8209166c68611d1605127309d1ef4997e63819762365a6909a`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1690](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1690-L1690), [cite at paper/reasoning-parts/erdos1041/core.tex:1640](../../paper/reasoning-parts/erdos1041/core.tex#L1640-L1640)

<a id="source-source-8ac37c92429a46"></a>

### Über die einfachen Zahlensysteme

- Source id: `source-8ac37c92429a46`
- Author or public identity: G. Cantor
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Historical source of factorial (Cantor) expansions and their termination criterion.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3132-L3136) — lines `3132–3136`; excerpt `sha256:495e90612bc48250f516ad11282d20ee19e249325363e3dd38cfe59a6de6a6c5`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3167-L3171) — lines `3167–3171`; excerpt `sha256:495e90612bc48250f516ad11282d20ee19e249325363e3dd38cfe59a6de6a6c5`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3132-L3136) — lines `3132–3136`; excerpt `sha256:495e90612bc48250f516ad11282d20ee19e249325363e3dd38cfe59a6de6a6c5`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1422-L1422) — lines `1422–1422`; excerpt `sha256:05ae035c98ef1be04452fd7e72676d785c26a101271763e5bf6acf84902d1963`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1422-L1422) — lines `1422–1422`; excerpt `sha256:05ae035c98ef1be04452fd7e72676d785c26a101271763e5bf6acf84902d1963`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1457](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1457-L1457), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2309](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2309-L2309), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2499](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2499-L2499), [cite at paper/reasoning-parts/erdos68/core.tex:1422](../../paper/reasoning-parts/erdos68/core.tex#L1422-L1422), [cite at paper/reasoning-parts/erdos68/core.tex:2274](../../paper/reasoning-parts/erdos68/core.tex#L2274-L2274), [cite at paper/reasoning-parts/erdos68/core.tex:2464](../../paper/reasoning-parts/erdos68/core.tex#L2464-L2464)

<a id="source-source-91756d895a28a8"></a>

### [Smith normal form in combinatorics](https://doi.org/10.1016/j.jcta.2016.06.013)

- Source id: `source-91756d895a28a8`
- Author or public identity: R. P. Stanley
- Kind: `literature`
- Problems: #1049, #269
- Relationship and boundary: Description of Smith invariants through gcds of minors (Theorems 2.3–2.4), used for the rank-two lattice index formulas. The selected staircase Smith factors are computed directly by unimodular operations in the round8 #269 section; the citation supplies standard Smith-form context, not a new rank or irrationality theorem.
- Source verification: `source\_verified` — The cited passages (Thms. 2.3--2.4, p. 3) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Thms. 2.3--2.4, p. 3](https://doi.org/10.1016/j.jcta.2016.06.013)
- [Full text consulted at Theorems 2.3--2.4, p. 3, on Smith invariants and determinantal divisors.](https://doi.org/10.1016/j.jcta.2016.06.013)
- [Smith invariant conventions; arXiv1602.00166v1 Theorems2.3-2.4.](https://arxiv.org/abs/1602.00166v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1288-L1293) — lines `1288–1293`; excerpt `sha256:3e8d9bba274ba0d1fa7883a36808baad3612c511dcd54421d1fb5d61d279fd1e`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5358-L5363) — lines `5358–5363`; excerpt `sha256:f56843a81f14f05368c09617997aad73fc6b35003af9f80f751f87b4ad29611f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5327-L5332) — lines `5327–5332`; excerpt `sha256:f56843a81f14f05368c09617997aad73fc6b35003af9f80f751f87b4ad29611f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4459-L4463) — lines `4459–4463`; excerpt `sha256:e828b32afe869265193334410009d5198e4188e0ff2dbfb72332db658f289473`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1931-L1931) — lines `1931–1931`; excerpt `sha256:16452cca21c31d1c0ed13a43089946f8ae7c468e95a04481e8bfeb79ff69f18c`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4401-L4405) — lines `4401–4405`; excerpt `sha256:e828b32afe869265193334410009d5198e4188e0ff2dbfb72332db658f289473`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L1873-L1873) — lines `1873–1873`; excerpt `sha256:16452cca21c31d1c0ed13a43089946f8ae7c468e95a04481e8bfeb79ff69f18c`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1138](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1138-L1138)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4539](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4539-L4539), [cite at paper/reasoning-parts/erdos1049/core.tex:4508](../../paper/reasoning-parts/erdos1049/core.tex#L4508-L4508)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1931](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1931-L1931), [cite at paper/reasoning-parts/erdos269/core.tex:1873](../../paper/reasoning-parts/erdos269/core.tex#L1873-L1873)

<a id="source-source-91aa380a16dba9"></a>

### [Variants of the Selberg sieve, and bounded intervals containing many primes](https://arxiv.org/abs/1407.4897v4)

- Source id: `source-91aa380a16dba9`
- Author or public identity: {D. H. J. Polymath}
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — selected\_primary\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L846-L848) — lines `846–848`; excerpt `sha256:4ef9d8671b8ce392778e642dc0289749457d7d772ade16d4e14764d4b2b041dd`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3097-L3099) — lines `3097–3099`; excerpt `sha256:b91b61385dc89f0e6767647854a990d52e4590e0b3e52ac921e4d46e37c4a36b`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3055-L3057) — lines `3055–3057`; excerpt `sha256:b91b61385dc89f0e6767647854a990d52e4590e0b3e52ac921e4d46e37c4a36b`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:768](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L768-L768), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:771](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L771-L771)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2099](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2099-L2099), [cite at paper/reasoning-parts/erdos251/core.tex:2057](../../paper/reasoning-parts/erdos251/core.tex#L2057-L2057)

<a id="source-source-92b0dfb67f5009"></a>

### [Computing the Newtonian Graph](https://doi.org/10.1006/jsco.1997.0118)

- Source id: `source-92b0dfb67f5009`
- Author or public identity: D. Kozen, K. Stefánsson
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Records the Shub–Tischler–Williams value identity (Lemma 2.1), the classification of maximal Newton-flow orbits (Lemma 2.2) and the Newtonian graph (Section 2), credited where the papers use them.
- Source verification: `source\_verified` — The cited passages (Lemma 2.1 (before Theorem 8.1; Sources paragraph); §2 (after Corollary 8.2); Lemma 2.2; Definition 2.1 (canonical descent arc); Lemma 2.1; §2; Lemma 2.2; Definition 2.1 and §2) were checked against the authors' copy, identical to https://www.cs.cornell.edu/kozen/Papers/newton.pdf copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Lemma 2.1 (before Theorem 8.1; Sources paragraph)](https://doi.org/10.1006/jsco.1997.0118)
- [§2 (after Corollary 8.2)](https://doi.org/10.1006/jsco.1997.0118)
- [Lemma 2.2](https://doi.org/10.1006/jsco.1997.0118)
- [Definition 2.1 (canonical descent arc)](https://doi.org/10.1006/jsco.1997.0118)
- [Lemma 2.1; §2; Lemma 2.2; Definition 2.1 and §2](https://doi.org/10.1006/jsco.1997.0118)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1182-L1187) — lines `1182–1187`; excerpt `sha256:ed2e1d97e25042a1c3cc333a2f890caed82f4b663b8b32c55aee9808f3380583`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5410-L5415) — lines `5410–5415`; excerpt `sha256:bfa2ad242e4a6f037e19e479a20a53b503839419b0cda9e5daa5e3cb598fe13a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5360-L5365) — lines `5360–5365`; excerpt `sha256:bfa2ad242e4a6f037e19e479a20a53b503839419b0cda9e5daa5e3cb598fe13a`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1005](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1005-L1005)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4238](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4238-L4238), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4244](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4244-L4244), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4246](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4246-L4246), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4257](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4257-L4257), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4311](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4311-L4311), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4345](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4345-L4345), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4509](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4509-L4509), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4996](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4996-L4996), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:5000](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5000-L5000), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:5004](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5004-L5004), [cite at paper/reasoning-parts/erdos1041/core.tex:4188](../../paper/reasoning-parts/erdos1041/core.tex#L4188-L4188), [cite at paper/reasoning-parts/erdos1041/core.tex:4194](../../paper/reasoning-parts/erdos1041/core.tex#L4194-L4194), [cite at paper/reasoning-parts/erdos1041/core.tex:4196](../../paper/reasoning-parts/erdos1041/core.tex#L4196-L4196), [cite at paper/reasoning-parts/erdos1041/core.tex:4207](../../paper/reasoning-parts/erdos1041/core.tex#L4207-L4207), [cite at paper/reasoning-parts/erdos1041/core.tex:4261](../../paper/reasoning-parts/erdos1041/core.tex#L4261-L4261), [cite at paper/reasoning-parts/erdos1041/core.tex:4295](../../paper/reasoning-parts/erdos1041/core.tex#L4295-L4295), [cite at paper/reasoning-parts/erdos1041/core.tex:4459](../../paper/reasoning-parts/erdos1041/core.tex#L4459-L4459), [cite at paper/reasoning-parts/erdos1041/core.tex:4946](../../paper/reasoning-parts/erdos1041/core.tex#L4946-L4946), [cite at paper/reasoning-parts/erdos1041/core.tex:4950](../../paper/reasoning-parts/erdos1041/core.tex#L4950-L4950), [cite at paper/reasoning-parts/erdos1041/core.tex:4954](../../paper/reasoning-parts/erdos1041/core.tex#L4954-L4954)

<a id="source-source-944a1a754b1f3a"></a>

### [leanblueprint](https://github.com/PatrickMassot/leanblueprint)

- Source id: `source-944a1a754b1f3a`
- Author or public identity: P. Massot
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L688-L692) — lines `688–692`; excerpt `sha256:bb8a82a2eaf9299171683c436633a3cdfe8688aba06e1bc995a951bd364c907e`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1205-L1207) — lines `1205–1207`; excerpt `sha256:9f7cd13126bc86bb2e14538da4a22cac99dbf4eaaabadfd3aba8c94ea897364f`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:111](../../paper/systems/claim-faithful-publication-systems-paper.tex#L111-L111), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:593](../../paper/systems/claim-faithful-publication-systems-paper.tex#L593-L593), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1042](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1042-L1042)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:474](../../paper/systems/cold-clone-to-proof-receipt.tex#L474-L474)

<a id="source-source-951f70d8dfc418"></a>

### [A Degree-Four Lemniscate Path Theorem](https://doi.org/10.48550/arXiv.2606.24875)

- Source id: `source-951f70d8dfc418`
- Author or public identity: V. S. Pendyala
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Degree-four case of the problem (Theorem 1); its chord estimate and four-point radial lemma (Lemma 1) supply the quotient geometry of the translated quartic fibres.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 1, PDF p. 1: every monic quartic with its four listed zeros in the open unit disk has two distinct indices joined inside {|f|\<1} by a possibly degenerate polygonal path of length \<2.](https://arxiv.org/abs/2606.24875)
- [Lemma 1, PDF pp. 1–2: four-point radial lemma; proof of Theorem 1, PDF p. 3.](https://arxiv.org/abs/2606.24875)
- [Theorem 1](https://arxiv.org/abs/2606.24875v1)
- [Thm. 1, p. 1](https://arxiv.org/abs/2606.24875v1)
- [Theorem 1 and Lemma 1 (translated quartic quotient fibres)](https://arxiv.org/abs/2606.24875v1)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1171-L1176) — lines `1171–1176`; excerpt `sha256:de6f7f3e7ce0991e2f6ce37362689f9baf718419396e29df27966f24fa9d4a1f`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5437-L5442) — lines `5437–5442`; excerpt `sha256:47c15ddd8236ce68dd0ecbf6270bce0d6213cbaaf1750e780da87c87894d6230`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5387-L5392) — lines `5387–5392`; excerpt `sha256:47c15ddd8236ce68dd0ecbf6270bce0d6213cbaaf1750e780da87c87894d6230`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L50-L50) — lines `50–50`; excerpt `sha256:8cd1420d63ac6dba85e07a367f50e3b3fbcbda60ea0f87fa3c34a8351bb2ee01`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L50-L50) — lines `50–50`; excerpt `sha256:8cd1420d63ac6dba85e07a367f50e3b3fbcbda60ea0f87fa3c34a8351bb2ee01`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L50-L50) — lines `50–50`; excerpt `sha256:8cd1420d63ac6dba85e07a367f50e3b3fbcbda60ea0f87fa3c34a8351bb2ee01`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:83](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L83-L83)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:100](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L100-L100), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1784](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1784-L1784), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3067](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3067-L3067), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3068](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3068-L3068), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3146](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3146-L3146), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3148](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3148-L3148), [cite at paper/reasoning-parts/erdos1041/core.tex:50](../../paper/reasoning-parts/erdos1041/core.tex#L50-L50), [cite at paper/reasoning-parts/erdos1041/core.tex:1734](../../paper/reasoning-parts/erdos1041/core.tex#L1734-L1734), [cite at paper/reasoning-parts/erdos1041/core.tex:3017](../../paper/reasoning-parts/erdos1041/core.tex#L3017-L3017), [cite at paper/reasoning-parts/erdos1041/core.tex:3018](../../paper/reasoning-parts/erdos1041/core.tex#L3018-L3018), [cite at paper/reasoning-parts/erdos1041/core.tex:3096](../../paper/reasoning-parts/erdos1041/core.tex#L3096-L3096), [cite at paper/reasoning-parts/erdos1041/core.tex:3098](../../paper/reasoning-parts/erdos1041/core.tex#L3098-L3098)

<a id="source-source-967c9acd787096"></a>

### [BOINC: A Platform for Volunteer Computing](https://doi.org/10.1007/s10723-019-09497-9)

- Source id: `source-967c9acd787096`
- Author or public identity: D. P. Anderson
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1646-L1651) — lines `1646–1651`; excerpt `sha256:b08b660d84c300da10b0cff0235eddaac275ba376ce6b7d77fbee66ccfb561fd`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:609](../../paper/systems/claim-faithful-publication-systems-paper.tex#L609-L609), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1052](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1052-L1052)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:585](../../paper/systems/open-source-mathematics-strategy.tex#L585-L585), [cite at paper/systems/open-source-mathematics-strategy.tex:926](../../paper/systems/open-source-mathematics-strategy.tex#L926-L926), [cite at paper/systems/open-source-mathematics-strategy.tex:984](../../paper/systems/open-source-mathematics-strategy.tex#L984-L984)

<a id="source-source-96aef073e2ea33"></a>

### [On the irrationality of certain series](https://doi.org/10.1017/S030500410007081X)

- Source id: `source-96aef073e2ea33`
- Author or public identity: P. B. Borwein
- Kind: `literature`
- Problems: #1049, #249, #257
- Relationship and boundary: Source (Lemma 2, p. 143) of the neighbouring evaluation recorded by Van Assche.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [irrationality theorems to the release's prior-art map. It records the exact](https://doi.org/10.1017/S030500410007081X)
- [3,425,078 bytes; six PDF pages, printed pp. 141–146. It was retrieved from](https://doi.org/10.1017/S030500410007081X)
- [surface for the theorem statements, proof bounds, and bibliography.](https://doi.org/10.1017/S030500410007081X)
- [- \*\*Abstract and publication scope:\*\* printed p. 141 states that the series](https://doi.org/10.1017/S030500410007081X)
- [- \*\*Full-support Mersenne context:\*\* printed p. 141 recalls Erdős's](https://doi.org/10.1017/S030500410007081X)
- [the theorem as a full-support \`q^n+c\` extension; it also recalls the](https://doi.org/10.1017/S030500410007081X)
- [- \*\*Theorem 1:\*\* printed p. 142 states that for an integer \`q\` with \`|q|\>1\`](https://doi.org/10.1017/S030500410007081X)
- [\`F\_n(q)\` displayed on p. 142 and the denominator/error lemmas on](https://doi.org/10.1017/S030500410007081X)
- [- \*\*Proof closure for Theorem 1:\*\* printed pp. 143–144 establish the integral](https://doi.org/10.1017/S030500410007081X)
- [- \*\*Theorem 2:\*\* printed p. 145 states the alternating analogue: for integer](https://doi.org/10.1017/S030500410007081X)
- [- \*\*Non-Liouville conclusion:\*\* printed p. 146 states that the estimates in](https://doi.org/10.1017/S030500410007081X)
- [Theorems 1 and 2 also give a uniform rational-approximation lower bound, so](https://doi.org/10.1017/S030500410007081X)
- [- \*\*Release specialization:\*\* Theorem 1 with \`q=2\` and \`c=-1\` contains the](https://doi.org/10.1017/S030500410007081X)
- [- Attribution to Borwein of the full-support irrationality theorem for](https://doi.org/10.1017/S030500410007081X)
- [\`sum 1/(q^n+c)\` and its alternating companion, printed pp. 142 and 145,](https://doi.org/10.1017/S030500410007081X)
- [printed p. 141 and by Theorem 1 on p. 142.](https://doi.org/10.1017/S030500410007081X)
- [- Attribution of the stronger “not Liouville” conclusion, printed p. 146.](https://doi.org/10.1017/S030500410007081X)
- [- A universal solution of Erdős #257, a squarefree-support theorem, or a](https://doi.org/10.1017/S030500410007081X)
- [prime-support theorem. The full-support Mersenne specialization is only](https://doi.org/10.1017/S030500410007081X)
- [- Any theorem about the Euler-totient series or the #249 totient kernel.](https://doi.org/10.1017/S030500410007081X)
- [All six printed pages were checked for the release's Lean declaration names,](https://doi.org/10.1017/S030500410007081X)
- [Comparator theorem names, Palomar verdicts, totient-kernel rank/basis](https://doi.org/10.1017/S030500410007081X)
- [relevant result is the full-support \`q^n+c\` theorem, not an arbitrary-support](https://doi.org/10.1017/S030500410007081X)
- [Lemma 2, p. 143](https://doi.org/10.1017/S030500410007081X)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://doi.org/10.1017/S030500410007081X)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5319-L5322) — lines `5319–5322`; excerpt `sha256:a2986b3c4ad5444edff29257bbeccf1dbda70fa87ceb63468d3192cdd636ac3b`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5185-L5191) — lines `5185–5191`; excerpt `sha256:62e9f12c9446297c621f7f486af4e1739cd6b6e5b979419191df4d31b8bb4cdc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5154-L5160) — lines `5154–5160`; excerpt `sha256:62e9f12c9446297c621f7f486af4e1739cd6b6e5b979419191df4d31b8bb4cdc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4926-L4926) — lines `4926–4926`; excerpt `sha256:5fd985589a096c7284944042b00248690d1d7fceed1258356a6e91864e8e051c`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4957](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4957-L4957), [cite at paper/reasoning-parts/erdos1049/core.tex:4926](../../paper/reasoning-parts/erdos1049/core.tex#L4926-L4926)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:631](../../paper/archive/erdos249-257-main-paper.tex#L631-L631)

<a id="source-source-9733ab875d6048"></a>

### [About Palomar](https://palomar-registry.org/about)

- Source id: `source-9733ab875d6048`
- Author or public identity: Palomar Registry
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1686-L1692) — lines `1686–1692`; excerpt `sha256:50025897e9875f1e8eb278c5a5c91ea2be1d03b9c7afc2bedf2dcec1c82f6162`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1052](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1052-L1052)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:579](../../paper/systems/open-source-mathematics-strategy.tex#L579-L579), [cite at paper/systems/open-source-mathematics-strategy.tex:785](../../paper/systems/open-source-mathematics-strategy.tex#L785-L785)

<a id="source-source-97b4e6a82335a7"></a>

### [Number of Components of Polynomial Lemniscates: A Problem of Erdős, Herzog, and Piranian](https://arxiv.org/abs/2312.13673)

- Source id: `source-97b4e6a82335a7`
- Author or public identity: S. Ghosh, K. Ramachandran
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Component count of the open unit sublevel set through critical values (Lemma 2.5 of arXiv v1).
- Source verification: `source\_verified` — The cited passages (Lemma 2.5 (was 'Lemma 7')) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Lemma 2.5 (was 'Lemma 7')](https://doi.org/10.1016/j.jmaa.2024.128571)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5398-L5405) — lines `5398–5405`; excerpt `sha256:ac93a1f2c5c87957117830efd99688e57dc988e65987811c68128cdf2f71aa9f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5348-L5355) — lines `5348–5355`; excerpt `sha256:ac93a1f2c5c87957117830efd99688e57dc988e65987811c68128cdf2f71aa9f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4362-L4362) — lines `4362–4362`; excerpt `sha256:789975730662255be1953f14644da72f9bee1ce16a61867e38c8b7ddd266fcb5`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4412](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4412-L4412), [cite at paper/reasoning-parts/erdos1041/core.tex:4362](../../paper/reasoning-parts/erdos1041/core.tex#L4362-L4362)

<a id="source-source-984f2b78d220ea"></a>

### [A Blueprint for the Formalization of Carleson's Theorem on Convergence of Fourier Series](https://doi.org/10.48550/arXiv.2405.06423)

- Source id: `source-984f2b78d220ea`
- Author or public identity: Lars Becker, María Inés de Frutos-Fernández, Leo Diedering, Floris van Doorn, Sébastien Gouëzel, Asgar Jamneshan, Evgenia Karunus, Edward van de Meent, Pietro Monticone, Jasper Mulder-Sohn, Jim Portegies, Joris Roos, Michael Rothgang, Rajula Srivastava, James Sundstrom, Jeremy Tan, Christoph Thiele
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://arxiv.org/abs/2405.06423v2)

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L697-L700) — lines `697–700`; excerpt `sha256:6a2d98ee6e3166e49ad37af7f7fe86c949a4155e4ba493a60d73e7ff90e2c8e9`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1666-L1671) — lines `1666–1671`; excerpt `sha256:a4a2cd5ff74bcf8ec7bc773aba6629192b6c1e90033142603ec6d7509d3e306e`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:609](../../paper/systems/claim-faithful-publication-systems-paper.tex#L609-L609), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1052](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1052-L1052)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:482](../../paper/systems/cold-clone-to-proof-receipt.tex#L482-L482)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:999](../../paper/systems/open-source-mathematics-strategy.tex#L999-L999)

<a id="source-source-99385343e032a3"></a>

### [Introduction to Analytic Number Theory](https://doi.org/10.1007/978-1-4757-5579-4)

- Source id: `source-99385343e032a3`
- Author or public identity: T. M. Apostol
- Kind: `literature`
- Problems: #269, #249, #257
- Relationship and boundary: General textbook reference for lcm(1,…,N) and ψ(N).
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [General background, not a source of the project’s specific rank theorem.](https://doi.org/10.1007/978-1-4757-5579-4)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4447-L4450) — lines `4447–4450`; excerpt `sha256:24eacdd006d27f46e0ea49feb1a0b92cc03b5cd554204a5ff82c31aef527f7d2`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4389-L4392) — lines `4389–4392`; excerpt `sha256:24eacdd006d27f46e0ea49feb1a0b92cc03b5cd554204a5ff82c31aef527f7d2`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L317-L317) — lines `317–317`; excerpt `sha256:714f7e7837698f5625120d30f22eb2fd6a2f960836d9458c5bd06eb68baabd97`
- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5322-L5325) — lines `5322–5325`; excerpt `sha256:d83b8379aa5d3a8d993822c9518436371502939df5b9c449f945ffb60730454b`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:484](../../paper/archive/erdos249-257-main-paper.tex#L484-L484), [cite at paper/archive/erdos249-257-main-paper.tex:4081](../../paper/archive/erdos249-257-main-paper.tex#L4081-L4081), [cite at paper/archive/erdos249-257-main-paper.tex:4675](../../paper/archive/erdos249-257-main-paper.tex#L4675-L4675), [cite at paper/archive/erdos249-257-main-paper.tex:4779](../../paper/archive/erdos249-257-main-paper.tex#L4779-L4779)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:375](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L375-L375), [cite at paper/reasoning-parts/erdos269/core.tex:317](../../paper/reasoning-parts/erdos269/core.tex#L317-L317)

<a id="source-source-99c2f3cb190b95"></a>

### [Comment on Erdős Problem #249](https://www.erdosproblems.com/forum/thread/249)

- Source id: `source-99c2f3cb190b95`
- Author or public identity: S. Fan
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Later dated public forum post of the same identity.
- Source verification: `source\_verified` — The cited passages (comment of 16 May 2026, 19:01; comment of 16 May 2026) were checked against the downloaded copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [comment of 16 May 2026, 19:01](https://www.erdosproblems.com/forum/thread/249)
- [comment of 16 May 2026](https://www.erdosproblems.com/forum/thread/249)
- [Public antecedent for the coprimality interpretation; preserve original credit.](https://www.erdosproblems.com/forum/thread/249)

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L901-L904) — lines `901–904`; excerpt `sha256:2fd518712f78c5863c24df2988af2303d5d5610ce069a736fcb6f69c30c4d37b`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10286-L10290) — lines `10286–10290`; excerpt `sha256:6f68ca842cab80e0e80859b0448d856556a74a77fbf2793f408455173289681c`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10094-L10098) — lines `10094–10098`; excerpt `sha256:6f68ca842cab80e0e80859b0448d856556a74a77fbf2793f408455173289681c`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:711](../../paper/249/erdos-249-binary-totient-series.tex#L711-L711)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1755](../../paper/249/erdos249-totient-reasoning-surface.tex#L1755-L1755), [cite at paper/249/erdos249-totient-reasoning-surface.tex:9872](../../paper/249/erdos249-totient-reasoning-surface.tex#L9872-L9872), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1563](../../paper/reasoning-parts/erdos249/a249_front.tex#L1563-L1563), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9680](../../paper/reasoning-parts/erdos249/a249_front.tex#L9680-L9680)

<a id="source-source-9a04cbea11fd0b"></a>

### [Pantograph: A Machine-to-Machine Interaction Interface for Advanced Theorem Proving, High Level Reasoning, and Data Extraction in Lean 4](https://doi.org/10.1007/978-3-031-90643-5_6)

- Source id: `source-9a04cbea11fd0b`
- Author or public identity: L. Aniva, C. Sun, B. Miranda, C. Barrett, S. Koyejo
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L705-L711) — lines `705–711`; excerpt `sha256:915b21de98fc6d842625837028364b4383eeb5ccd9db3a58c6484bb7d7791545`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1043](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1043-L1043)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:405](../../paper/systems/cold-clone-to-proof-receipt.tex#L405-L405), [cite at paper/systems/cold-clone-to-proof-receipt.tex:488](../../paper/systems/cold-clone-to-proof-receipt.tex#L488-L488)

<a id="source-source-9a38b2d8b0dada"></a>

### [Local gap statistics, telescoping, and normality](https://github.com/StefanRinger/erdos-251)

- Source id: `source-9a38b2d8b0dada`
- Author or public identity: S. Ringer
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Public preprint of 11 September 2026 proving base-B normality under Kuperberg's conjecture.
- Source verification: `source\_verified` — Primary preprint PDF (31 pages, dated 11 September 2026, SHA-256 22332707548c833b691a20e9d7e03a548478f49ac85cb5a54a18ba5ec1b5c989, repository commit d2c92e2795) read on 15 September 2026 at the abstract, Section 1, Section 3, Sections 5.2 to 5.4, Section 6 and Appendix C, together with the Lean definition of KuperbergConj13 and the recorded endpoint audit. The proof was not checked in full and the Lean build was not replayed; the stated relation bounds what the notes use.
- Local mapping: `not recorded`

Exact source locations:

- [PDF p. 3, Theorem 1.1 and Corollary 1.2: under the one-sided averaged prime-tuples hypothesis, periodic local polynomial prime-gap series are rational or normal; Corollary 1.2 gives normality of sum p\_n B^-n to base B, and Kuperberg's conjecture suffices for every integer B \>= 2.](https://github.com/StefanRinger/erdos-251/blob/main/paper/prime_gap_normality.pdf)
- [PDF pp. 19-20, Section 5.4: Kuperberg's Conjecture 1.3 (arXiv:2210.09775v2, equation (7)) implies the averaged hypothesis for every fixed kappa.](https://github.com/StefanRinger/erdos-251/blob/main/paper/prime_gap_normality.pdf)
- [PDF pp. 26-28, Appendix C, Proposition C.1 on p. 27: sum p\_n B^-S\_n with S\_n = sum\_{j\<=n} ceil(log\_B log(j+3)) is unconditionally normal to base B.](https://github.com/StefanRinger/erdos-251/blob/main/paper/prime_gap_normality.pdf)
- [KuperbergConj13 is a named Prop matching Conjecture 1.3 of Kuperberg; the recorded audit lean/verification/completed/theorem-types-and-axioms.txt prints CorePeriodicPositionEnd.primePositionSeries\_isNormal\_of\_kuperberg with hypothesis KuperbergConj13 and axioms propext, Classical.choice and Quot.sound.](https://github.com/StefanRinger/erdos-251/blob/main/lean/PrimeGapNormality/Prime/EndAPI.lean)
- [Corollary 1.2](https://github.com/StefanRinger/erdos-251)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L489-L489) — lines `489–489`; excerpt `sha256:7e61b42ea68ba67af8f394d8ccf905ab7a64c0866af88228cdd70633340422fa`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L838-L840) — lines `838–840`; excerpt `sha256:a68775eea867950e9742ad93dd4089e04252a31cf488340177ac456e7b57c84f`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L489-L489) — lines `489–489`; excerpt `sha256:3411ca8b06103cfe9c649bff064c056e7f9e43045265fcc7e8409ac7f0236feb`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3079-L3081) — lines `3079–3081`; excerpt `sha256:a68775eea867950e9742ad93dd4089e04252a31cf488340177ac456e7b57c84f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L447-L447) — lines `447–447`; excerpt `sha256:3411ca8b06103cfe9c649bff064c056e7f9e43045265fcc7e8409ac7f0236feb`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3037-L3039) — lines `3037–3039`; excerpt `sha256:a68775eea867950e9742ad93dd4089e04252a31cf488340177ac456e7b57c84f`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:489](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L489-L489)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:489](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L489-L489), [cite at paper/reasoning-parts/erdos251/core.tex:447](../../paper/reasoning-parts/erdos251/core.tex#L447-L447)

<a id="source-source-9b23918ce33c38"></a>

### [Ford circles, continued fractions, and best approximation of the second kind](https://arxiv.org/abs/0912.1997v1)

- Source id: `source-9b23918ce33c38`
- Author or public identity: I. Short
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Accessible statement and proof (Theorem 1.1) of the convergent property used by the continued-fraction exclusion.
- Source verification: `source\_verified` — The cited passages (Theorem 1.1) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1.1](https://arxiv.org/abs/0912.1997v1)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3065-L3067) — lines `3065–3067`; excerpt `sha256:2bdb1af734a1c86a2ea7603f390d84d3309c1d1abf8a8f4eb21930714a5a0c9d`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3023-L3025) — lines `3023–3025`; excerpt `sha256:2bdb1af734a1c86a2ea7603f390d84d3309c1d1abf8a8f4eb21930714a5a0c9d`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1373](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1373-L1373), [cite at paper/reasoning-parts/erdos251/core.tex:1331](../../paper/reasoning-parts/erdos251/core.tex#L1331-L1331)

<a id="source-source-9c2776b87b1155"></a>

### [On the arithmetic properties of complex values of Hecke-Mahler series I. The rank one case](https://www.numdam.org/item/ASNSP_2006_5_5_3_329_0/)

- Source id: `source-9c2776b87b1155`
- Author or public identity: Federico Pellarin
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Quadratic-irrational slope and rank-one module hypotheses; not a theorem for arbitrary two-dimensional floor sums.
- Source verification: `source\_verified` — Published introduction, domain, quadratic-slope and rank-one conditions, Theorem 1.1. Not a complete proof audit.
- Local mapping: `not recorded`

Exact source locations:

- [Introduction, pp. 329--331; Theorem 1.1, p. 330](https://www.numdam.org/item/ASNSP_2006_5_5_3_329_0/)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4512-L4517) — lines `4512–4517`; excerpt `sha256:4d3c475c2dd44a15da10bb68d05eedaa5bb7ef373c98a81bf0994e003e8022e6`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4454-L4459) — lines `4454–4459`; excerpt `sha256:4d3c475c2dd44a15da10bb68d05eedaa5bb7ef373c98a81bf0994e003e8022e6`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3621](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3621-L3621), [cite at paper/reasoning-parts/erdos269/core.tex:3563](../../paper/reasoning-parts/erdos269/core.tex#L3563-L3563)

<a id="source-source-9ce84321e202f1"></a>

### [Irrationality of Lambert series associated with a periodic sequence](https://doi.org/10.1142/S1793042113501121)

- Source id: `source-9ce84321e202f1`
- Author or public identity: Florian Luca, Yohei Tachiya
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Original periodic-sequence priority; theorem formulation used through the 2017 author account.
- Source verification: `existing\_source\_closure` — Original metadata checked against the author publication list and the authors' 2017 overview; original publisher PDF returned 403.
- Local mapping: `not recorded`

Exact source locations:

- [Luca author publication list, 2014](https://doi.org/10.1142/S1793042113501121)
- [Luca--Tachiya 2017, Theorem A, p.139](https://doi.org/10.1142/S1793042113501121)

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1687-L1693) — lines `1687–1693`; excerpt `sha256:3f90c9c82f80686f1efe4c911cd5f754201a1464c150d626d59690b5e96927f9`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9701-L9707) — lines `9701–9707`; excerpt `sha256:3f90c9c82f80686f1efe4c911cd5f754201a1464c150d626d59690b5e96927f9`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9501-L9507) — lines `9501–9507`; excerpt `sha256:3f90c9c82f80686f1efe4c911cd5f754201a1464c150d626d59690b5e96927f9`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1591](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1591-L1591)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1288](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1288-L1288), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9540](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9540-L9540), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1088](../../paper/reasoning-parts/erdos257/a257_front.tex#L1088-L1088), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9340](../../paper/reasoning-parts/erdos257/a257_front.tex#L9340-L9340)

<a id="source-source-9db8c3859cdc81"></a>

### [Ueber eine zahlentheoretische Funktion](https://doi.org/10.1515/crll.1858.55.193)

- Source id: `source-9db8c3859cdc81`
- Author or public identity: M. Stern
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5338-L5341) — lines `5338–5341`; excerpt `sha256:3ac7773843e9a2678e1438fae3c683df643a9de180d07f049ef248f6010429ec`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:4087](../../paper/archive/erdos249-257-main-paper.tex#L4087-L4087)

<a id="source-source-9e37cc2fe7db3e"></a>

### [Two-dimensional shapes and lemniscates](https://doi.org/10.1090/conm/553/10931)

- Source id: `source-9e37cc2fe7db3e`
- Author or public identity: P. Ebenfelt, D. Khavinson, H. S. Shapiro
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Component-wise Riemann–Hurwitz count (proof of Proposition 2.1) and finite Blaschke representation used by the proper-map arguments.
- Source verification: `source\_verified` — The cited passages (proof of Proposition 2.1 (square-root uniformisation); Proposition 2.1 (Ghosh sentence; separation proof; slit-sheet credit); (2.2) (Blaschke product after Riemann mapping)) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [proof of Proposition 2.1 (square-root uniformisation)](https://doi.org/10.1090/conm/553/10931)
- [Proposition 2.1 (Ghosh sentence; separation proof; slit-sheet credit)](https://doi.org/10.1090/conm/553/10931)
- [(2.2) (Blaschke product after Riemann mapping)](https://doi.org/10.1090/conm/553/10931)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1193-L1200) — lines `1193–1200`; excerpt `sha256:0b086dc6c508b56a163e9e87eadee8f83406883c0bb951c90f8c3195b296ef03`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5415-L5422) — lines `5415–5422`; excerpt `sha256:ff50af06cc617795c60c2ca89ddaec781a6c4593028140edc22775c58cb3e3a9`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5365-L5372) — lines `5365–5372`; excerpt `sha256:ff50af06cc617795c60c2ca89ddaec781a6c4593028140edc22775c58cb3e3a9`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:148](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L148-L148), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:389](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L389-L389), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:574](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L574-L574)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:490](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L490-L490), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:702](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L702-L702), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1604](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1604-L1604), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1722](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1722-L1722), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1858](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1858-L1858), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3923](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3923-L3923), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4413](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4413-L4413), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4510](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4510-L4510), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4590](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4590-L4590), [cite at paper/reasoning-parts/erdos1041/core.tex:440](../../paper/reasoning-parts/erdos1041/core.tex#L440-L440), [cite at paper/reasoning-parts/erdos1041/core.tex:652](../../paper/reasoning-parts/erdos1041/core.tex#L652-L652), [cite at paper/reasoning-parts/erdos1041/core.tex:1554](../../paper/reasoning-parts/erdos1041/core.tex#L1554-L1554), [cite at paper/reasoning-parts/erdos1041/core.tex:1672](../../paper/reasoning-parts/erdos1041/core.tex#L1672-L1672), [cite at paper/reasoning-parts/erdos1041/core.tex:1808](../../paper/reasoning-parts/erdos1041/core.tex#L1808-L1808), [cite at paper/reasoning-parts/erdos1041/core.tex:3873](../../paper/reasoning-parts/erdos1041/core.tex#L3873-L3873), [cite at paper/reasoning-parts/erdos1041/core.tex:4363](../../paper/reasoning-parts/erdos1041/core.tex#L4363-L4363), [cite at paper/reasoning-parts/erdos1041/core.tex:4460](../../paper/reasoning-parts/erdos1041/core.tex#L4460-L4460), [cite at paper/reasoning-parts/erdos1041/core.tex:4540](../../paper/reasoning-parts/erdos1041/core.tex#L4540-L4540)

<a id="source-source-9ef9271dbecbce"></a>

### [Preventing pwn requests](https://docs.github.com/en/actions/reference/security/secure-use)

- Source id: `source-9ef9271dbecbce`
- Author or public identity: GitHub
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1742-L1747) — lines `1742–1747`; excerpt `sha256:a2823f7bc0eabe07dcb16e2476c88ca0a6ae7777617c24762b0674c83ce2e1da`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:642](../../paper/systems/claim-faithful-publication-systems-paper.tex#L642-L642), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1052](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1052-L1052)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:946](../../paper/systems/open-source-mathematics-strategy.tex#L946-L946)

<a id="source-source-a028dc6bb31c0c"></a>

### [Towards Autonomous Mathematics Research](https://arxiv.org/abs/2602.10177)

- Source id: `source-a028dc6bb31c0c`
- Author or public identity: Tony Feng, Trieu H. Trinh, Garrett Bingham, Dawsen Hwang, Yuri Chervonyi, Junehyuk Jung, Joonkyung Lee, Carlo Pagano, Sang-hyun Kim, Federico Pasqualotto, Sergei Gukov, Jonathan N. Lee, Junsu Kim, Kaiying Hou, Golnaz Ghiasi, Yi Tay, YaGuang Li, Chenkai Kuang, Yuan Liu, Hanzhao Lin, Evan Zheran Liu, Nigamaa Nayakanti, Xiaomeng Yang, Heng-Tze Cheng, Demis Hassabis, Koray Kavukcuoglu, Quoc V. Le, Thang Luong
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by both public systems papers as prior published work (v3, 6 March 2026) for the two-axis autonomy-by-significance disclosure taxonomy, human-AI interaction cards with published raw prompts, the separated natural-language verifier that declines to answer, the persistence of misquoted real references under tool use, and the human-authorship rule. None of this repository's eight problems appears in its results.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1717-L1722) — lines `1717–1722`; excerpt `sha256:17dfc81b2347996ae518d9ae35b9f4cbbe428802c4df971c821bb500a90d87de`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1193-L1197) — lines `1193–1197`; excerpt `sha256:2595846643eaeb52b16f7156659896435256034246319719e7ecd470260c4445`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1051](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1051-L1051)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:683](../../paper/systems/open-source-mathematics-strategy.tex#L683-L683), [cite at paper/systems/open-source-mathematics-strategy.tex:753](../../paper/systems/open-source-mathematics-strategy.tex#L753-L753), [cite at paper/systems/open-source-mathematics-strategy.tex:832](../../paper/systems/open-source-mathematics-strategy.tex#L832-L832), [cite at paper/systems/open-source-mathematics-strategy.tex:961](../../paper/systems/open-source-mathematics-strategy.tex#L961-L961), [cite at paper/systems/open-source-mathematics-strategy.tex:1076](../../paper/systems/open-source-mathematics-strategy.tex#L1076-L1076)

<a id="source-source-a0d109b4492fba"></a>

### [Multiplicative functions and k-automatic sequences](https://www.numdam.org/item/JTNB_2001__13_2_651_0.pdf)

- Source id: `source-a0d109b4492fba`
- Author or public identity: Soroosh Yazdani
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Origin of the CRT–Dirichlet separation mechanism used in the proof; totient residues are non-automatic. Explicitly credits Shallit.
- Source verification: `source\_verified` — Published article, all 9 PDF pages
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 2 and proof, pp. 652–653; Corollary 4, p. 654; acknowledgement, p. 657](https://www.numdam.org/item/JTNB_2001__13_2_651_0.pdf)

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L913-L918) — lines `913–918`; excerpt `sha256:1afac1390d37599a1aabc74b5e4f00b9c13fe3b5510b23747164aafc5cabb79f`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10394-L10399) — lines `10394–10399`; excerpt `sha256:1afac1390d37599a1aabc74b5e4f00b9c13fe3b5510b23747164aafc5cabb79f`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10202-L10207) — lines `10202–10207`; excerpt `sha256:1afac1390d37599a1aabc74b5e4f00b9c13fe3b5510b23747164aafc5cabb79f`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:131](../../paper/249/erdos-249-binary-totient-series.tex#L131-L131)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:296](../../paper/249/erdos249-totient-reasoning-surface.tex#L296-L296), [cite at paper/249/erdos249-totient-reasoning-surface.tex:298](../../paper/249/erdos249-totient-reasoning-surface.tex#L298-L298), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:104](../../paper/reasoning-parts/erdos249/a249_front.tex#L104-L104), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:106](../../paper/reasoning-parts/erdos249/a249_front.tex#L106-L106)

<a id="source-source-a38774d9a4f1f9"></a>

### [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathematical Proofs](https://arxiv.org/abs/2506.21621)

- Source id: `source-a38774d9a4f1f9`
- Author or public identity: Jasper Dekoninck, Ivo Petrov, Kristian Minchev, Mislav Balunovic, Martin Vechev, Miroslav Marinov, Maria Drencheva, Lyuba Konova, Milen Shumanov, Kaloyan Tsvetkov
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by both public systems papers, via Henkel, for the judge-by-solver finding that each model scores lowest when grading its own proofs.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1727-L1732) — lines `1727–1732`; excerpt `sha256:d7199ff140a739a7be732b44e20113885c623918791626d0f99bd6c7e2a83cc2`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1050](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1050-L1050)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:779](../../paper/systems/open-source-mathematics-strategy.tex#L779-L779), [cite at paper/systems/open-source-mathematics-strategy.tex:1020](../../paper/systems/open-source-mathematics-strategy.tex#L1020-L1020)

<a id="source-source-a67b8dc01791ec"></a>

### [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](https://arxiv.org/abs/0808.0717)

- Source id: `source-a67b8dc01791ec`
- Author or public identity: Alexander Fryntov, Fedor Nazarov
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Asymptotically sharp level-curve length bound; its introduction records the history, including Pommerenke's 74n² bound.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Introduction surveys the EHP level-lemniscate problem and states the paper proves local maximality of z^n-1 and an upper bound 2n+o(n).](https://arxiv.org/abs/0808.0717)
- [Published version: Linear and Complex Analysis, Amer. Math. Soc. Transl. Ser. 2 226, Amer. Math. Soc., Providence, RI, 2009, pp. 49-60 (Crossref record for DOI 10.1090/trans2/226/05; zbMATH 1181.30002). The long record cites this venue together with arXiv:0808.0717.](https://doi.org/10.1090/trans2/226/05)
- [Introduction (history: Dolzhenko 4πn, Pommerenke 74n^2, Borwein 8πen)](https://doi.org/10.1090/trans2/226/05)
- [plain citation (2n+o(n))](https://doi.org/10.1090/trans2/226/05)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5457-L5463) — lines `5457–5463`; excerpt `sha256:bcdad75ad0ef6a705b6fe89763d0da02f0663ec648798c57bec9c5455264dc47`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5407-L5413) — lines `5407–5413`; excerpt `sha256:bcdad75ad0ef6a705b6fe89763d0da02f0663ec648798c57bec9c5455264dc47`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1638-L1638) — lines `1638–1638`; excerpt `sha256:8f0116d285182c3169d8171b8d13c4c752a018a50c51df8dfd0a78fe648e1fe0`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1688](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1688-L1688), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1692](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1692-L1692), [cite at paper/reasoning-parts/erdos1041/core.tex:1638](../../paper/reasoning-parts/erdos1041/core.tex#L1638-L1638), [cite at paper/reasoning-parts/erdos1041/core.tex:1642](../../paper/reasoning-parts/erdos1041/core.tex#L1642-L1642)

<a id="source-source-a87fa25f28c7b0"></a>

### [Irrationality of certain infinite series II](https://doi.org/10.1524/anly.2011.1094)

- Source id: `source-a87fa25f28c7b0`
- Author or public identity: W. Koepf, D. Schmersau
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Irrationality direction of the factorial-digit criterion for digits that are not eventually maximal (Example 3.2, p. 121), and the integrality and strict-tail criterion compared in the long record.
- Source verification: `source\_verified` — The cited passages (Example 3.2, p. 121; Example 3.2, p. 121; Thm. 1.1, p. 117; (2.1) and (2.3), p. 118; Thms. 2.2-2.3, pp. 119-120) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Example 3.2, p. 121](https://doi.org/10.1524/anly.2011.1094)
- [Thm. 1.1, p. 117](https://doi.org/10.1524/anly.2011.1094)
- [(2.1) and (2.3), p. 118](https://doi.org/10.1524/anly.2011.1094)
- [Thms. 2.2-2.3, pp. 119-120](https://doi.org/10.1524/anly.2011.1094)
- [Reference and role retained from the attached paper; not independently reread in full in this revision.](https://doi.org/10.1524/anly.2011.1094)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3183-L3187) — lines `3183–3187`; excerpt `sha256:3a26f5bc4eb9c2426ec95588f15ecf2d22cd99dd0ae4aa88e40f0d69fe5e8750`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3148-L3152) — lines `3148–3152`; excerpt `sha256:3a26f5bc4eb9c2426ec95588f15ecf2d22cd99dd0ae4aa88e40f0d69fe5e8750`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1426-L1426) — lines `1426–1426`; excerpt `sha256:5139a5f6ebb95c3e704baeace6907b8ca37b7f8ea44fd4d7e73ced8285e38c76`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1426-L1426) — lines `1426–1426`; excerpt `sha256:5139a5f6ebb95c3e704baeace6907b8ca37b7f8ea44fd4d7e73ced8285e38c76`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L568-L572) — lines `568–572`; excerpt `sha256:e8cae7318c8c143094d52d1da99fd4dda7271236e256e02a746de55f05d72d67`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:96](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L96-L96)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1461](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1461-L1461), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2311](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2311-L2311), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2550](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2550-L2550), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2557](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2557-L2557), [cite at paper/reasoning-parts/erdos68/core.tex:1426](../../paper/reasoning-parts/erdos68/core.tex#L1426-L1426), [cite at paper/reasoning-parts/erdos68/core.tex:2276](../../paper/reasoning-parts/erdos68/core.tex#L2276-L2276), [cite at paper/reasoning-parts/erdos68/core.tex:2515](../../paper/reasoning-parts/erdos68/core.tex#L2515-L2515), [cite at paper/reasoning-parts/erdos68/core.tex:2522](../../paper/reasoning-parts/erdos68/core.tex#L2522-L2522)

<a id="source-source-aa2d5c249362f1"></a>

### [Zero Coefficients of Rational Power Series and Rational Lambert Series](https://arxiv.org/abs/2604.25151)

- Source id: `source-aa2d5c249362f1`
- Author or public identity: I. Rivin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Nonrationality of the Lambert function Σ zⁿ/(1−zⁿ), used in the Mahler proposition.
- Source verification: `source\_verified` — The cited passages (Theorem 1.1, p. 2; proof pp. 6--7; Cor. 6.4, p. 9) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1.1, p. 2; proof pp. 6--7](https://arxiv.org/abs/2604.25151v1)
- [Cor. 6.4, p. 9](https://arxiv.org/abs/2604.25151v1)
- [Supplied ten-page text consulted for Theorem 1.1, proof pp. 6--7 and Corollary 6.4, p. 9; served version 1 title and locators checked again.](https://arxiv.org/abs/2604.25151v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5305-L5311) — lines `5305–5311`; excerpt `sha256:547a282df5e35d2d260581efbb9d6958a6a3bf47c2d9a4d9b39949fd65e27f76`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5274-L5280) — lines `5274–5280`; excerpt `sha256:547a282df5e35d2d260581efbb9d6958a6a3bf47c2d9a4d9b39949fd65e27f76`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4712-L4712) — lines `4712–4712`; excerpt `sha256:54e3d1ef752ffcb54e8ee1bfe7534ff85b97adcfec7a02daa218a664d09cd7f7`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4712-L4712) — lines `4712–4712`; excerpt `sha256:54e3d1ef752ffcb54e8ee1bfe7534ff85b97adcfec7a02daa218a664d09cd7f7`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4712-L4712) — lines `4712–4712`; excerpt `sha256:54e3d1ef752ffcb54e8ee1bfe7534ff85b97adcfec7a02daa218a664d09cd7f7`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4743](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4743-L4743), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4909](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4909-L4909), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4914](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4914-L4914), [cite at paper/reasoning-parts/erdos1049/core.tex:4712](../../paper/reasoning-parts/erdos1049/core.tex#L4712-L4712), [cite at paper/reasoning-parts/erdos1049/core.tex:4878](../../paper/reasoning-parts/erdos1049/core.tex#L4878-L4878), [cite at paper/reasoning-parts/erdos1049/core.tex:4883](../../paper/reasoning-parts/erdos1049/core.tex#L4883-L4883)

<a id="source-source-ab6d6d6b890f57"></a>

### [On integers generated by a finite number of fixed primes](https://www.numdam.org/article/CM_1974__29_3_273_0.pdf)

- Source id: `source-ab6d6d6b890f57`
- Author or public identity: Robert Tijdeman, H. G. Meijer
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Appropriate fixed-prime geometry and adjacent-quotient context; not a weighted-shell asymptotic or a cancellation theorem.
- Source verification: `source\_verified` — Sections 1–4: fixed-prime definition, Lemmas 1–5, Theorem 1 and its proof (pp. 273–278); no new use of Theorem 3.
- Local mapping: `not recorded`

Exact source locations:

- [Sections 1–4: fixed-prime definition, Lemmas 1–5, Theorem 1 and its proof (pp. 273–278); no new use of Theorem 3.](https://www.numdam.org/article/CM_1974__29_3_273_0.pdf)

Public implementation or evidence coordinates:

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1073-L1076) — lines `1073–1076`; excerpt `sha256:56c3313573f1c66b97e759caddfa08857ff02beecce742ca74aa60516751dfb8`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4502-L4505) — lines `4502–4505`; excerpt `sha256:56c3313573f1c66b97e759caddfa08857ff02beecce742ca74aa60516751dfb8`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4444-L4447) — lines `4444–4447`; excerpt `sha256:56c3313573f1c66b97e759caddfa08857ff02beecce742ca74aa60516751dfb8`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1005](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1005-L1005)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:180](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L180-L180), [cite at paper/reasoning-parts/erdos269/core.tex:122](../../paper/reasoning-parts/erdos269/core.tex#L122-L122)

<a id="source-source-abedb02f9939e5"></a>

### [Chebotarëv and his density theorem](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1994c/art.pdf)

- Source id: `source-abedb02f9939e5`
- Author or public identity: P. Stevenhagen, H. W. Lenstra, Jr.
- Kind: `literature`
- Problems: #243
- Relationship and boundary: Standard statement of the Chebotarev density theorem, cited at the square-specialisation lemma.
- Source verification: `source\_verified` — The cited passages (§3, p. 15 (author version)) were checked against the author version 19950323 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [§3, p. 15 (author version)](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1994c/art.pdf)
- [Classical Chebotarev input to the cubic argument.](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1994c/art.pdf)

Public implementation or evidence coordinates:

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4134-L4140) — lines `4134–4140`; excerpt `sha256:114c6c590cc9d93a8ef21180697160ce21e5fd0ef2e6801cfa8c3bd3dc16e78c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4095-L4101) — lines `4095–4101`; excerpt `sha256:114c6c590cc9d93a8ef21180697160ce21e5fd0ef2e6801cfa8c3bd3dc16e78c`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1441-L1447) — lines `1441–1447`; excerpt `sha256:4a2a8e4fc977c8352311e72ae7979c821e66a3545b5d72c4ade3b36bc5e51666`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:354](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L354-L354)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:389](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L389-L389), [cite at paper/reasoning-parts/erdos243/core.tex:350](../../paper/reasoning-parts/erdos243/core.tex#L350-L350)

<a id="source-source-ae32306341559a"></a>

### [Lean Atlas: An Integrated Proof Environment for Scalable Human--AI Collaborative Formalization](https://doi.org/10.48550/arXiv.2604.16347)

- Source id: `source-ae32306341559a`
- Author or public identity: B. Yanahama, A. Sannai
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L728-L732) — lines `728–732`; excerpt `sha256:3a090cc943cde6fe32e768b3fec5c8f9941b86fe85cffb0b1e502eff8703ea31`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1697-L1702) — lines `1697–1702`; excerpt `sha256:990e7e409c51244fcd270d46681ee6ca48f5d9a561bcdbc931d9db6b4df3c30c`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1043](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1043-L1043)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:522](../../paper/systems/cold-clone-to-proof-receipt.tex#L522-L522)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:1009](../../paper/systems/open-source-mathematics-strategy.tex#L1009-L1009)

<a id="source-source-ae5cc4ddfa6af5"></a>

### [Agent Hunt: Bounty Based Collaborative Autoformalization With LLM Agents](https://doi.org/10.48550/arXiv.2603.06737)

- Source id: `source-ae5cc4ddfa6af5`
- Author or public identity: C. E. Brown, C. Kaliszyk, J. Urban
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1692-L1697) — lines `1692–1697`; excerpt `sha256:ba3b7d334c4533a7eb892544f07793a641502451252ef40f9dd35e8d49823e68`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:1007](../../paper/systems/open-source-mathematics-strategy.tex#L1007-L1007)

<a id="source-source-ae9859af28fdcd"></a>

### [On the irrationality of generalized q-logarithm](https://arxiv.org/abs/1601.02688)

- Source id: `source-ae9859af28fdcd`
- Author or public identity: W. Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Normalised Hankel determinant and its lower bound for the q-order, which the papers prove is an equality; remark on rational-base extensions with an uncomputed constant (Section 2, p. 4).
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Reading status: complete arXiv v2 PDF read from rendered pages; page references are to that version.](https://arxiv.org/abs/1601.02688)
- [Section 2, arXiv v2 p. 4, paragraph beginning 'Finally, we remark': non-integer p = r/s under log|r| \> c log|s| with c computable and unspecified.](https://arxiv.org/abs/1601.02688)
- [Section 4, (6)–(8) and Lemma 1, arXiv v2 pp. 6–8: normalised moments, backward-shift operator and the q-order inequality for V\_n^\*.](https://arxiv.org/abs/1601.02688)
- [Sec. 2, p. 4](https://arxiv.org/abs/1601.02688v2)
- [Sec. 2, p. 3](https://arxiv.org/abs/1601.02688v2)
- [(6), pp. 6--7; Sec. 4, (6), p. 6; Sec. 4, (7), p. 6; Sec. 4, Lemma 1, pp. 6--7](https://arxiv.org/abs/1601.02688v2)
- [Sec. 4, p. 7](https://arxiv.org/abs/1601.02688v2)
- [Version 2 full text consulted, especially Section 2, p. 4; Section 3, p. 5; Section 4, pp. 6--7.](https://arxiv.org/abs/1601.02688v2)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1277-L1288) — lines `1277–1288`; excerpt `sha256:ded7a6e73c64eb888bff8d92fdf9045c0912b78b36a09aaf5d4f28ab76caf53f`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5211-L5222) — lines `5211–5222`; excerpt `sha256:28607cac7b070bebdf820b61863c3daadc81c336a532ef5ffb850e0444467fbe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5180-L5191) — lines `5180–5191`; excerpt `sha256:28607cac7b070bebdf820b61863c3daadc81c336a532ef5ffb850e0444467fbe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L834-L834) — lines `834–834`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L834-L834) — lines `834–834`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L834-L834) — lines `834–834`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L834-L834) — lines `834–834`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L834-L834) — lines `834–834`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L834-L834) — lines `834–834`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L3-L12) — lines `3–12`; excerpt `sha256:2c6a0d27c905ea48c1f25e9aa96f3007e323409c7b093d69e63e5d6389c5dd78`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L294-L341) — lines `294–341`; excerpt `sha256:079ff692126bd3e4d34f548fea370a492cd0c13ef7f93ce3fb3dd3ad6697e51f`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L1373-L1380) — lines `1373–1380`; excerpt `sha256:00ffa8698a1534c856de8c5358848f0e1631280815d61cd62dccca5b31c96703`
- [lean/ErdosProblems/Erdos1049/AdelicHeightBridge.lean](../../lean/ErdosProblems/Erdos1049/AdelicHeightBridge.lean#L177-L184) — lines `177–184`; excerpt `sha256:48cded238c23f3b69267c7634831949873ba61edbfc1d81d7be4e4f53a9dfa1f`
- [lean/ErdosProblems/Erdos1049/AllRow/Producer.lean](../../lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L139-L144) — lines `139–144`; excerpt `sha256:d91ba4591cce7012da8fb4b68e2c502744e2a86cbff69f02ac661f05bbbc77f0`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L675-L679) — lines `675–679`; excerpt `sha256:f4bd612442f7360245d4b631cbdc499c687fc3d6d13818a39db22dc67e091077`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:57](../../paper/1049/erdos-1049-rational-base-lambert.tex#L57-L57), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:79](../../paper/1049/erdos-1049-rational-base-lambert.tex#L79-L79), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:628](../../paper/1049/erdos-1049-rational-base-lambert.tex#L628-L628), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1071](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1071-L1071)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:67](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L67-L67), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:865](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L865-L865), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1463](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1463-L1463), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1466](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1466-L1466), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1483](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1483-L1483), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1494](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1494-L1494), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1518](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1518-L1518), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1810](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1810-L1810), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2791](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2791-L2791), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5046](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5046-L5046), [cite at paper/reasoning-parts/erdos1049/core.tex:36](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36), [cite at paper/reasoning-parts/erdos1049/core.tex:834](../../paper/reasoning-parts/erdos1049/core.tex#L834-L834), [cite at paper/reasoning-parts/erdos1049/core.tex:1432](../../paper/reasoning-parts/erdos1049/core.tex#L1432-L1432), [cite at paper/reasoning-parts/erdos1049/core.tex:1435](../../paper/reasoning-parts/erdos1049/core.tex#L1435-L1435), [cite at paper/reasoning-parts/erdos1049/core.tex:1452](../../paper/reasoning-parts/erdos1049/core.tex#L1452-L1452), [cite at paper/reasoning-parts/erdos1049/core.tex:1463](../../paper/reasoning-parts/erdos1049/core.tex#L1463-L1463), [cite at paper/reasoning-parts/erdos1049/core.tex:1487](../../paper/reasoning-parts/erdos1049/core.tex#L1487-L1487), [cite at paper/reasoning-parts/erdos1049/core.tex:1779](../../paper/reasoning-parts/erdos1049/core.tex#L1779-L1779), [cite at paper/reasoning-parts/erdos1049/core.tex:2760](../../paper/reasoning-parts/erdos1049/core.tex#L2760-L2760), [cite at paper/reasoning-parts/erdos1049/core.tex:5015](../../paper/reasoning-parts/erdos1049/core.tex#L5015-L5015)

<a id="source-source-af9e99293e9dd0"></a>

### [General polymath rules](https://polymathprojects.org/general-polymath-rules/)

- Source id: `source-af9e99293e9dd0`
- Author or public identity: Polymath Project
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1656-L1661) — lines `1656–1661`; excerpt `sha256:6f2b691dbea0a4758a07048f06dca1acfc4049444971d8bdfab57f8bf75e6a02`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:609](../../paper/systems/claim-faithful-publication-systems-paper.tex#L609-L609), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1052](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1052-L1052)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:583](../../paper/systems/open-source-mathematics-strategy.tex#L583-L583), [cite at paper/systems/open-source-mathematics-strategy.tex:992](../../paper/systems/open-source-mathematics-strategy.tex#L992-L992)

<a id="source-source-b0b779fff5defe"></a>

### [Irrationality of fast converging series of rational numbers](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)

- Source id: `source-b0b779fff5defe`
- Author or public identity: D. Duverney
- Kind: `literature`
- Problems: #243, #68
- Relationship and boundary: The exact statement and printed locator of Corollary 3.2, including its one-sided summability condition, signed numerators, and eventual signed recurrence. - The relationship of Corollary 3.2 to Theorem 3.1 and the all-positive specialisation relevant to the #243 note. - The source identity, official retrieval route, digest, and page-level locators recorded above.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [251001 bytes; 42 pages, printed pp. 275–316. It remains a local](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [The title page (printed p. 275), Corollary 3.2 (printed p. 287), and the](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [references/end matter (printed pp. 314–315) were also visually checked. The](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [typeset PDF is legible; the printed page numbers are the locators used below.](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [- \*\*Historical setup:\*\* printed pp. 275–280, especially Theorem 2.1 on](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [Sylvester expansions, Theorem 2.2 on Ahmes series under a limsup and LCM](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [bound, and Theorem 2.3 on the Erdős–Straus perturbed doubly-exponential](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [- \*\*General conditional criterion:\*\* printed pp. 285–287, Theorem 3.1 and its](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [- \*\*Signed #243 criterion:\*\* printed p. 287, Corollary 3.2 assumes positive](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [- \*\*Proof boundary:\*\* printed pp. 299–300, section 5.2 derives Corollary 3.2](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [from Theorem 3.1 by reducing \`p\_n/q\_n\`, bounding the successive numerator](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [then gives the Erdős–Straus specialisation as Corollary 3.3 on p. 300.](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [- \*\*End matter:\*\* printed pp. 314–315 contain the references, including the](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [original Erdős–Straus source and Badea's theorem; p. 316 contains the](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [not be attributed to Duverney as the exact hypothesis of Corollary 3.2.](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [- The exact statement and printed locator of Corollary 3.2, including its](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [- The relationship of Corollary 3.2 to Theorem 3.1 and the all-positive](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [unbounded-negative regimes, or any release theorem about #249 or #257.](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [Corollary 3.2 is the first signed criterion of this kind.](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [The complete article (printed pp. 275–316) was checked for Lean declarations,](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [the release's theorem names, an unrestricted proof of #243, and any claim](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [about the release's #249/#257 results; none occurs. Corollary 3.2 is a](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [the source-aware exposition and its corrected Corollary 3.2 hypothesis.](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [The allowed outward statement is therefore: Duverney's Corollary 3.2 gives a](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [(1.3), p. 275; Thm. 3.1, pp. 285-286](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [Cor. 3.2, p. 287; pp. 275, 285-287](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [Corollary 3.2, p. 287](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [Primary journal PDF introduction and Theorem 1.1 read this pass; the Theorem 3.1/Corollary 3.2 comparison retains the previous pass’s stated locators rather than claiming a fresh proof audit.](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [Theorem 3.1, pp. 285–286](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [§4.2, pp. 294–297](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)
- [§5.2, pp. 299–300](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1410-L1414) — lines `1410–1414`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4096-L4100) — lines `4096–4100`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4057-L4061) — lines `4057–4061`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L857-L857) — lines `857–857`; excerpt `sha256:ed7a349b06c0fa968d6eac74252e7f637f42e8018159ddf7e209ad4a3fae8037`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L857-L857) — lines `857–857`; excerpt `sha256:ed7a349b06c0fa968d6eac74252e7f637f42e8018159ddf7e209ad4a3fae8037`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3187-L3191) — lines `3187–3191`; excerpt `sha256:82a9d3633d44a7f0d1eb428949e60377edee33c29aa6e38e5941bceb6b962b77`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3152-L3156) — lines `3152–3156`; excerpt `sha256:82a9d3633d44a7f0d1eb428949e60377edee33c29aa6e38e5941bceb6b962b77`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2160-L2160) — lines `2160–2160`; excerpt `sha256:29422f1117ddf0cfe478b48719a3b1d57db703b18e788e0dd9e85d0344241384`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2160-L2160) — lines `2160–2160`; excerpt `sha256:29422f1117ddf0cfe478b48719a3b1d57db703b18e788e0dd9e85d0344241384`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2160-L2160) — lines `2160–2160`; excerpt `sha256:29422f1117ddf0cfe478b48719a3b1d57db703b18e788e0dd9e85d0344241384`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1007](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1007-L1007)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:896](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L896-L896), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1766](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1766-L1766), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3731](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3731-L3731), [cite at paper/reasoning-parts/erdos243/core.tex:857](../../paper/reasoning-parts/erdos243/core.tex#L857-L857), [cite at paper/reasoning-parts/erdos243/core.tex:1727](../../paper/reasoning-parts/erdos243/core.tex#L1727-L1727), [cite at paper/reasoning-parts/erdos243/core.tex:3692](../../paper/reasoning-parts/erdos243/core.tex#L3692-L3692)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2195](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2195-L2195), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2590](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2590-L2590), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2593](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2593-L2593), [cite at paper/reasoning-parts/erdos68/core.tex:2160](../../paper/reasoning-parts/erdos68/core.tex#L2160-L2160), [cite at paper/reasoning-parts/erdos68/core.tex:2555](../../paper/reasoning-parts/erdos68/core.tex#L2555-L2555), [cite at paper/reasoning-parts/erdos68/core.tex:2558](../../paper/reasoning-parts/erdos68/core.tex#L2558-L2558)

<a id="source-source-b10b965e63a00d"></a>

### [Inequalities for critical values of polynomials](https://www.mathnet.ru/eng/sm1434)

- Source id: `source-b10b965e63a00d`
- Author or public identity: Vladimir N. Dubinin
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 1, p. 1167; proof §1, pp. 1169–1172](https://www.mathnet.ru/eng/sm1434)
- [Inverse sheets and adjacency tree, pp. 1169–1170](https://www.mathnet.ru/eng/sm1434)
- [Theorem 2, identity (9), pp. 1172–1173](https://www.mathnet.ru/eng/sm1434)
- [Theorem 3 and Tischler antecedent, p. 1174](https://www.mathnet.ru/eng/sm1434)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1237-L1241) — lines `1237–1241`; excerpt `sha256:e71562d62b7120e70fe7b834f65baa80911382d9eec508f8396928584ab1dacf`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5488-L5492) — lines `5488–5492`; excerpt `sha256:e71562d62b7120e70fe7b834f65baa80911382d9eec508f8396928584ab1dacf`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5438-L5442) — lines `5438–5442`; excerpt `sha256:e71562d62b7120e70fe7b834f65baa80911382d9eec508f8396928584ab1dacf`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:968](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L968-L968), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1078](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1078-L1078)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3165](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3165-L3165), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4513](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4513-L4513), [cite at paper/reasoning-parts/erdos1041/core.tex:3115](../../paper/reasoning-parts/erdos1041/core.tex#L3115-L3115), [cite at paper/reasoning-parts/erdos1041/core.tex:4463](../../paper/reasoning-parts/erdos1041/core.tex#L4463-L4463)

<a id="source-source-b202a3f125817d"></a>

### [FormalConjectures.ErdosProblems.251](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/251.lean)

- Source id: `source-b202a3f125817d`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #251
- Relationship and boundary: External formal statement/corpus context cited by the paper. It is not proof authority for this repository and does not make the local result an upstream contribution.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Paper bibliography commit pin f776d2f2039351b00737ffcafb9d7d7666e1d9af; exact problem file](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/251.lean)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3077-L3079) — lines `3077–3079`; excerpt `sha256:8724712f34a0b9289550c3ab049d6a1ee5927433c0a4731b5a6cab0280040067`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3035-L3037) — lines `3035–3037`; excerpt `sha256:8724712f34a0b9289550c3ab049d6a1ee5927433c0a4731b5a6cab0280040067`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L631-L631) — lines `631–631`; excerpt `sha256:afde66f79f7325fc6e5739cbb7f5cf67d57b23b919e011448cce112b14fd5df0`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L808-L810) — lines `808–810`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L673-L673) — lines `673–673`; excerpt `sha256:afde66f79f7325fc6e5739cbb7f5cf67d57b23b919e011448cce112b14fd5df0`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:673](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L673-L673), [cite at paper/reasoning-parts/erdos251/core.tex:631](../../paper/reasoning-parts/erdos251/core.tex#L631-L631)

<a id="source-source-b378189f39ed98"></a>

### [On the irrationality of certain series: problems and results](https://doi.org/10.1017/CBO9780511897184.009)

- Source id: `source-b378189f39ed98`
- Author or public identity: P. Erdős
- Kind: `literature`
- Problems: #1049, #243, #249, #251, #257, #269, #68
- Relationship and boundary: Erdős's statement of the question and of the Erdős-Straus criterion, including the display whose indexing the long record discusses.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [# Erdős (1988) source closure: problem statements and an LCM theorem](https://doi.org/10.1017/CBO9780511897184.009)
- [open subseries question from the separate theorem proved in the article; it](https://doi.org/10.1017/CBO9780511897184.009)
- [553,229 bytes; eight PDF pages, printed pp. 102–109. It was retrieved from](https://doi.org/10.1017/CBO9780511897184.009)
- [The complete eight-page OCR text layer was checked, and PDF pages containing](https://doi.org/10.1017/CBO9780511897184.009)
- [printed pp. 103, 105, 106, and 109 were visually checked against the scan.](https://doi.org/10.1017/CBO9780511897184.009)
- [- \*\*Earlier full-support theorem and open problems:\*\* printed p. 102 recalls](https://doi.org/10.1017/CBO9780511897184.009)
- [Erdős's irrationality theorem for the divisor-weighted full-support series](https://doi.org/10.1017/CBO9780511897184.009)
- [- \*\*Squarefree and sparse context:\*\* printed p. 103 states the question for](https://doi.org/10.1017/CBO9780511897184.009)
- [- \*\*Direct #257-family problem statement:\*\* printed p. 105, in the list of](https://doi.org/10.1017/CBO9780511897184.009)
- [- \*\*A separate proved prime/LCM result:\*\* printed p. 106 first notes that if](https://doi.org/10.1017/CBO9780511897184.009)
- [least common multiple. It then proves the following broader theorem:](https://doi.org/10.1017/CBO9780511897184.009)
- [- \*\*Proof locator for the LCM theorem:\*\* printed pp. 106–108 assume a](https://doi.org/10.1017/CBO9780511897184.009)
- [omitted term. Printed p. 109 gives the references, including Erdős (1948),](https://doi.org/10.1017/CBO9780511897184.009)
- [- Attribution to Erdős of the density/LCM irrationality theorem on p. 106,](https://doi.org/10.1017/CBO9780511897184.009)
- [posed as a question, and no arbitrary-support Lambert theorem is proved in](https://doi.org/10.1017/CBO9780511897184.009)
- [or any claim that the separate LCM theorem applies to the Mersenne](https://doi.org/10.1017/CBO9780511897184.009)
- [- Any theorem about the Euler-totient series or the #249 totient kernel.](https://doi.org/10.1017/CBO9780511897184.009)
- [declaration names, Comparator theorem names, Palomar verdicts, totient-kernel](https://doi.org/10.1017/CBO9780511897184.009)
- [the proved result on pp. 106–108 is an LCM-denominator theorem with a](https://doi.org/10.1017/CBO9780511897184.009)
- [density/LCM irrationality theorem; it does not settle universal Erdős #257 or](https://doi.org/10.1017/CBO9780511897184.009)
- [p. 102](https://doi.org/10.1017/CBO9780511897184.009)
- [p. 106](https://doi.org/10.1017/CBO9780511897184.009)
- [p. 106 (three places)](https://doi.org/10.1017/CBO9780511897184.009)
- [p. 103](https://doi.org/10.1017/CBO9780511897184.009)
- [p. 105](https://users.renyi.hu/~p_erdos/1988-22.pdf)
- [Reference and role retained from the attached paper; not independently reread in full in this revision.](https://doi.org/10.1017/CBO9780511897184.009)
- [Historical problem statement, p. 105; bibliography context.](https://users.renyi.hu/~p_erdos/1988-22.pdf)
- [p. 106](https://doi.org/10.1017/cbo9780511897184.009)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://doi.org/10.1017/CBO9780511897184.009)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5315-L5319) — lines `5315–5319`; excerpt `sha256:ef4a3136894b8a7edf6c08674740c39ae6802868494e203a59f1f0b740884aad`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L560-L564) — lines `560–564`; excerpt `sha256:b630a0f0ca592293699970eda53a16eea623a9f1d81f881c6dc903179a78eeec`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3151-L3155) — lines `3151–3155`; excerpt `sha256:b630a0f0ca592293699970eda53a16eea623a9f1d81f881c6dc903179a78eeec`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1427-L1432) — lines `1427–1432`; excerpt `sha256:78f98ff5782c3f26518953792349ad37efb90e1c262886d330c17b9bd9667677`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4113-L4118) — lines `4113–4118`; excerpt `sha256:eaf6cb9470a050bc0ac5978773ab824fd5e2486d1c128ad600ecc049ec5e1863`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L812-L814) — lines `812–814`; excerpt `sha256:d48a3b5fc1a3db1218dc2cebafed7ac30142d5ecb2e63f7fecff1e2a5c569695`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3035-L3037) — lines `3035–3037`; excerpt `sha256:33443e1df07646c816cedeb1eb59f9662fa5abee19c5b12c98dc3dbea83c505f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4419-L4422) — lines `4419–4422`; excerpt `sha256:a170cdfc562020c04faf65c58a81863df6e925b08eae36eba6e3fe186dbf1eb0`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1030-L1033) — lines `1030–1033`; excerpt `sha256:a170cdfc562020c04faf65c58a81863df6e925b08eae36eba6e3fe186dbf1eb0`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1259-L1263) — lines `1259–1263`; excerpt `sha256:46dc589925f18c98a38b701dc32978cf7bf47298f8b19fc97e2d6eb3b37ddaf2`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5177-L5181) — lines `5177–5181`; excerpt `sha256:5dc4499ba85b2a90c1b7eeae654d404e424be3f9aa288c8eaf30e698ab7cf0e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5146-L5150) — lines `5146–5150`; excerpt `sha256:5dc4499ba85b2a90c1b7eeae654d404e424be3f9aa288c8eaf30e698ab7cf0e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L31-L31) — lines `31–31`; excerpt `sha256:7adf3bc061fe0f3cf8e51e2c18b9fb9d24dc2ab9d668f7d627844a0e5cfb8186`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4074-L4079) — lines `4074–4079`; excerpt `sha256:eaf6cb9470a050bc0ac5978773ab824fd5e2486d1c128ad600ecc049ec5e1863`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2993-L2995) — lines `2993–2995`; excerpt `sha256:33443e1df07646c816cedeb1eb59f9662fa5abee19c5b12c98dc3dbea83c505f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L31-L31) — lines `31–31`; excerpt `sha256:626083ad8fe32513999d7b51bd99f24ffcd6a8a982d19d34d4cffaf234f372b5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L31-L31) — lines `31–31`; excerpt `sha256:626083ad8fe32513999d7b51bd99f24ffcd6a8a982d19d34d4cffaf234f372b5`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4361-L4364) — lines `4361–4364`; excerpt `sha256:a170cdfc562020c04faf65c58a81863df6e925b08eae36eba6e3fe186dbf1eb0`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L60-L60) — lines `60–60`; excerpt `sha256:89b37a0d3340796c5590d761a39d83444f6987ea56bf2f2eaf180f3f1f9e9178`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L60-L60) — lines `60–60`; excerpt `sha256:89b37a0d3340796c5590d761a39d83444f6987ea56bf2f2eaf180f3f1f9e9178`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L60-L60) — lines `60–60`; excerpt `sha256:89b37a0d3340796c5590d761a39d83444f6987ea56bf2f2eaf180f3f1f9e9178`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3116-L3120) — lines `3116–3120`; excerpt `sha256:b630a0f0ca592293699970eda53a16eea623a9f1d81f881c6dc903179a78eeec`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L24-L24) — lines `24–24`; excerpt `sha256:eedf58c8921c99e121942c72f945730fb30f151860f8a859f47e2254e6ba7731`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:114](../../paper/1049/erdos-1049-rational-base-lambert.tex#L114-L114)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:70](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L70-L70)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:53](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L53-L53)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:105](../../paper/269/erdos-269-three-prime-running-lcm.tex#L105-L105)
- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:48](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L48-L48)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:62](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L62-L62), [cite at paper/reasoning-parts/erdos1049/core.tex:31](../../paper/reasoning-parts/erdos1049/core.tex#L31-L31)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:75](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L75-L75), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:876](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L876-L876), [cite at paper/reasoning-parts/erdos243/core.tex:36](../../paper/reasoning-parts/erdos243/core.tex#L36-L36), [cite at paper/reasoning-parts/erdos243/core.tex:837](../../paper/reasoning-parts/erdos243/core.tex#L837-L837)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:193](../../paper/archive/erdos249-257-main-paper.tex#L193-L193), [cite at paper/archive/erdos249-257-main-paper.tex:195](../../paper/archive/erdos249-257-main-paper.tex#L195-L195)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:73](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L73-L73), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:537](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L537-L537), [cite at paper/reasoning-parts/erdos251/core.tex:31](../../paper/reasoning-parts/erdos251/core.tex#L31-L31), [cite at paper/reasoning-parts/erdos251/core.tex:495](../../paper/reasoning-parts/erdos251/core.tex#L495-L495)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:118](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L118-L118), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3882](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3882-L3882), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3918](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3918-L3918), [cite at paper/reasoning-parts/erdos269/core.tex:60](../../paper/reasoning-parts/erdos269/core.tex#L60-L60), [cite at paper/reasoning-parts/erdos269/core.tex:3824](../../paper/reasoning-parts/erdos269/core.tex#L3824-L3824), [cite at paper/reasoning-parts/erdos269/core.tex:3860](../../paper/reasoning-parts/erdos269/core.tex#L3860-L3860)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:59](../../paper/68/erdos68-factorial-reasoning-surface.tex#L59-L59), [cite at paper/reasoning-parts/erdos68/core.tex:24](../../paper/reasoning-parts/erdos68/core.tex#L24-L24)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:72](../../paper/synthesis/optimal-sparse-perturbations.tex#L72-L72)

<a id="source-source-b3b7518e07e159"></a>

### [On the irrationality of certain p-adic zeta values](https://arxiv.org/abs/2505.23088v1)

- Source id: `source-b3b7518e07e159`
- Author or public identity: L. Lai, C. Lupu, J. Sprang
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Methodological comparison for denominator saving in p-adic linear forms; no p-adic theorem is applied to the series.
- Source verification: `source\_verified` — arXiv v1 PDF read in full (24 pages). Locators refer to arXiv v1; the published numbering was not compared.
- Local mapping: `not recorded`

Exact source locations:

- [Lemma 2.1, arXiv v1 p. 3, quoted there from L. Lai, Int. J. Number Theory 21 (2025), Lemma 2.1: if integer linear forms L\_n satisfy max\_i |l\_(i,n)| |L\_n(xi)|\_p -\> 0 along an unbounded set of n and L\_n(xi) != 0 there, then some xi\_i is irrational.](https://arxiv.org/abs/2505.23088v1)
- [Section 5, arXiv v1 pp. 10-14: Lemma 5.3 bounds the coefficient denominators by powers of d\_n = lcm(1,...,n); Lemmas 5.4-5.7 show that the cleared coefficients remain integral after division by Phi\_n, a product of powers of primes in (sqrt(pn), n\].](https://arxiv.org/abs/2505.23088v1)
- [Lemma 7.3, arXiv v1 p. 20, and inequality (8.1), p. 22: Phi\_n = exp(varpi\_p n + o(n)), and varpi\_p enters the inequality under which the rescaled forms Phi\_n^(-1) d\_n^(p-1+s) S\_n, which have integer coefficients, meet the criterion quoted in Lemma 2.1.](https://arxiv.org/abs/2505.23088v1)
- [Lemma 2.1, p. 3](https://doi.org/10.1007/s40687-025-00559-x)
- [§5 (Lemmas 5.3-5.7, pp. 10-14); Lemma 7.3, p. 20; (8.1), p. 22](https://doi.org/10.1007/s40687-025-00559-x)
- [Lemma 2.1, p. 3; Lemmas 5.3-5.7 and 7.3; (8.1)](https://doi.org/10.1007/s40687-025-00559-x)
- [Reference and role retained from the attached paper; not independently reread in full in this revision.](https://arxiv.org/abs/2505.23088v1)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3172-L3176) — lines `3172–3176`; excerpt `sha256:eb4b28f73e685f8395aaa64be8cef4676a9807d8e5c53e9480cb7c0132a381f6`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3207-L3211) — lines `3207–3211`; excerpt `sha256:eb4b28f73e685f8395aaa64be8cef4676a9807d8e5c53e9480cb7c0132a381f6`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3172-L3176) — lines `3172–3176`; excerpt `sha256:eb4b28f73e685f8395aaa64be8cef4676a9807d8e5c53e9480cb7c0132a381f6`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1158-L1159) — lines `1158–1159`; excerpt `sha256:cd316c6943ef18c9bbad142ab7006cfcf46286294169d293916558a1689e6225`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1158-L1159) — lines `1158–1159`; excerpt `sha256:cd316c6943ef18c9bbad142ab7006cfcf46286294169d293916558a1689e6225`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1158-L1159) — lines `1158–1159`; excerpt `sha256:cd316c6943ef18c9bbad142ab7006cfcf46286294169d293916558a1689e6225`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1158-L1159) — lines `1158–1159`; excerpt `sha256:cd316c6943ef18c9bbad142ab7006cfcf46286294169d293916558a1689e6225`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1158-L1158) — lines `1158–1158`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1158-L1158) — lines `1158–1158`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1158-L1158) — lines `1158–1158`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1193](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1193-L1193), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1194](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1194-L1194), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1196](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1196-L1196), [cite at paper/reasoning-parts/erdos68/core.tex:1158](../../paper/reasoning-parts/erdos68/core.tex#L1158-L1158), [cite at paper/reasoning-parts/erdos68/core.tex:1159](../../paper/reasoning-parts/erdos68/core.tex#L1159-L1159), [cite at paper/reasoning-parts/erdos68/core.tex:1161](../../paper/reasoning-parts/erdos68/core.tex#L1161-L1161)

<a id="source-source-b3decc410aa4b5"></a>

### [On the Value Set of $n!$ Modulo a Prime](https://journals.tubitak.gov.tr/math/vol29/iss2/6/)

- Source id: `source-b3decc410aa4b5`
- Author or public identity: Banks, William D., Luca, Florian, Shparlinski, Igor E., Stichtenoth, Henning
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `existing\_source\_closure` — Publisher landing page and abstract verified; PDF access failed. DOI field is omitted because the publisher shows a dash, not a DOI.
- Local mapping: `not recorded`

Exact source locations:

- [Publisher landing page and abstract verified; PDF access failed. DOI field is omitted because the publisher shows a dash, not a DOI.](https://journals.tubitak.gov.tr/math/vol29/iss2/6/)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3247-L3251) — lines `3247–3251`; excerpt `sha256:3505a37c28e494a2a50e4fe25e04a275f47dea02e877ed8c2299dbfd058f927a`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3212-L3216) — lines `3212–3216`; excerpt `sha256:3505a37c28e494a2a50e4fe25e04a275f47dea02e877ed8c2299dbfd058f927a`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1976](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1976-L1976), [cite at paper/reasoning-parts/erdos68/core.tex:1941](../../paper/reasoning-parts/erdos68/core.tex#L1941-L1941)

<a id="source-source-b46f8a083b4271"></a>

### [More on Kakeya Conditions for Achievement Sets](https://ruj.uj.edu.pl/server/api/core/bitstreams/d6630f7b-e6ee-4de8-8a1b-81c7b4c59d2e/content)

- Source id: `source-b46f8a083b4271`
- Author or public identity: Miska, Piotr, Prus-Wi\\'sniowski, Franciszek, Ptak, Jolanta
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — selected\_primary\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L640-L641) — lines `640–641`; excerpt `sha256:4129ae8a548eb28a7e3432bbf4bbcc912b7dd61b2142446ce4caac2e976ce178`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3101-L3103) — lines `3101–3103`; excerpt `sha256:4d23f3968fb1ccd53933b23fc840988fd48072550d470fc5a28559b929df023f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3059-L3061) — lines `3059–3061`; excerpt `sha256:4d23f3968fb1ccd53933b23fc840988fd48072550d470fc5a28559b929df023f`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:641](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L641-L641), [cite at paper/reasoning-parts/erdos251/core.tex:599](../../paper/reasoning-parts/erdos251/core.tex#L599-L599)

<a id="source-source-b4b0f2811b1d2d"></a>

### [Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit ganzzahligen Koeffizienten](https://www.mathnet.ru/eng/sm1434)

- Source id: `source-b4b0f2811b1d2d`
- Author or public identity: Issai Schur
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — indirect\_via\_full\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5512-L5516) — lines `5512–5516`; excerpt `sha256:7634243bb1a190b0aeb3ad7cffcd772a6f9cb9cb1e54e1b3ea7d5bf9c9b18a25`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5462-L5466) — lines `5462–5466`; excerpt `sha256:7634243bb1a190b0aeb3ad7cffcd772a6f9cb9cb1e54e1b3ea7d5bf9c9b18a25`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3184](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3184-L3184), [cite at paper/reasoning-parts/erdos1041/core.tex:3134](../../paper/reasoning-parts/erdos1041/core.tex#L3134-L3134)

<a id="source-source-b6603e42453ff3"></a>

### [The Lean 4 theorem prover and programming language](https://doi.org/10.1007/978-3-030-79876-5_37)

- Source id: `source-b6603e42453ff3`
- Author or public identity: Leonardo de Moura, Sebastian Ullrich
- Kind: `software`
- Problems: #249, #251, #257
- Relationship and boundary: Proof assistant cited where the kernel check is described.
- Source verification: `source\_verified` — The cited passages (plain citation at the verification paragraph (previously uncited); plain citation at the verification paragraph (previously uncited)) were checked against the author/project PDF copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [plain citation at the verification paragraph (previously uncited)](https://doi.org/10.1007/978-3-030-79876-5_37)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5425-L5431) — lines `5425–5431`; excerpt `sha256:693e1e0134f09226af4a4f04bb1f50d763c2bc0c40320ed6d730242cab1263bf`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L824-L826) — lines `824–826`; excerpt `sha256:ad96b93897cb722f9a63aa344b11a333231b11971c032d6bf1a0781e0d6ded9f`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3055-L3057) — lines `3055–3057`; excerpt `sha256:ad96b93897cb722f9a63aa344b11a333231b11971c032d6bf1a0781e0d6ded9f`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1676-L1681) — lines `1676–1681`; excerpt `sha256:10b82bb930fe79ac10a4ea88fdca0fe6cef302ef6284568b8ea7a1bd56f969d0`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3013-L3015) — lines `3013–3015`; excerpt `sha256:ad96b93897cb722f9a63aa344b11a333231b11971c032d6bf1a0781e0d6ded9f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L100-L100) — lines `100–100`; excerpt `sha256:8e56484cbb8a2a51938d6d95f9eb16930424134d3eb232b2a1c1323f9489b0f2`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1110-L1115) — lines `1110–1115`; excerpt `sha256:c5fd8bab00b679d203057c594bf20120be28a4b4637d2f3f497872234e129474`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:108](../../paper/systems/claim-faithful-publication-systems-paper.tex#L108-L108), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:593](../../paper/systems/claim-faithful-publication-systems-paper.tex#L593-L593), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1040](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1040-L1040)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:781](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L781-L781)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3770](../../paper/archive/erdos249-257-main-paper.tex#L3770-L3770)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2257](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2257-L2257), [cite at paper/reasoning-parts/erdos251/core.tex:2215](../../paper/reasoning-parts/erdos251/core.tex#L2215-L2215)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:572](../../paper/systems/open-source-mathematics-strategy.tex#L572-L572)

<a id="source-source-b6d577df139d85"></a>

### [On Equal Products of Consecutive Integers](https://doi.org/10.4153/CMB-1970-052-8)

- Source id: `source-b6d577df139d85`
- Author or public identity: Macleod, R. A., Barrodale, I.
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `existing\_source\_closure` — Primary publisher title/author/volume/pages/DOI and extract checked; full paper not obtained. No proof claim relies on this entry.
- Local mapping: `not recorded`

Exact source locations:

- [Primary publisher title/author/volume/pages/DOI and extract checked; full paper not obtained. No proof claim relies on this entry.](https://doi.org/10.4153/CMB-1970-052-8)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3263-L3267) — lines `3263–3267`; excerpt `sha256:e3b1d19fa4854f7153d25ef24896c1b7f697c819f9574977485c2759ead98276`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3228-L3232) — lines `3228–3232`; excerpt `sha256:e3b1d19fa4854f7153d25ef24896c1b7f697c819f9574977485c2759ead98276`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2105](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2105-L2105), [cite at paper/reasoning-parts/erdos68/core.tex:2070](../../paper/reasoning-parts/erdos68/core.tex#L2070-L2070)

<a id="source-source-b791f5b49e0da6"></a>

### [Transcendence of generating functions whose coefficients are multiplicative](https://arxiv.org/pdf/1003.2221v2)

- Source id: `source-b791f5b49e0da6`
- Author or public identity: Jason P. Bell, Nils Bruin, Michael Coons
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Earlier algebraic and D-finite classification; distinguish generating functions from numerical values. Preserve Bézivin’s earlier role when describing the classification’s history.
- Source verification: `source\_verified` — arXiv v2, all 25 pages; journal metadata checked separately
- Local mapping: `not recorded`

Exact source locations:

- [Theorems 1.5–1.6, p. 2; algebraic proof, Sections 3–5; D-finite proof, Section 6; Appendix A](https://arxiv.org/pdf/1003.2221v2)

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L928-L934) — lines `928–934`; excerpt `sha256:6cb7dcabcbc0e388ffa8e2348251a577293e5169688f4aaaffac1b8ae868d1ea`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10409-L10415) — lines `10409–10415`; excerpt `sha256:e10593522712515931ddcbaa7131d36a55628516394338e405b737d442819636`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10217-L10223) — lines `10217–10223`; excerpt `sha256:e10593522712515931ddcbaa7131d36a55628516394338e405b737d442819636`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:546](../../paper/249/erdos-249-binary-totient-series.tex#L546-L546)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:10214](../../paper/249/erdos249-totient-reasoning-surface.tex#L10214-L10214), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:10022](../../paper/reasoning-parts/erdos249/a249_front.tex#L10022-L10022)

<a id="source-source-b95bf142df7fb5"></a>

### [{Digital Library of Mathematical Functions}, {Section} 5.11(iii): Ratios](https://dlmf.nist.gov/5.11.E12)

- Source id: `source-b95bf142df7fb5`
- Author or public identity: {{National Institute of Standards and Technology}}
- Kind: `literature`
- Problems: #243
- Relationship and boundary: Fixed-parameter Gamma-ratio asymptotic used in extraction.
- Source verification: `source\_verified` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Fixed-parameter Gamma-ratio asymptotic used in extraction.](https://dlmf.nist.gov/5.11.E12)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1483-L1486) — lines `1483–1486`; excerpt `sha256:10c3199fda8e6b96e9871391653c60d86629257f2027c73dec8028c99d52a01a`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4185-L4188) — lines `4185–4188`; excerpt `sha256:68ea153c3563a568a2f8dd959b99f6641b703032a1460306b051df5a3a19d4f9`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4146-L4149) — lines `4146–4149`; excerpt `sha256:68ea153c3563a568a2f8dd959b99f6641b703032a1460306b051df5a3a19d4f9`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1227](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1227-L1227)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:667](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L667-L667), [cite at paper/reasoning-parts/erdos243/core.tex:628](../../paper/reasoning-parts/erdos243/core.tex#L628-L628)

<a id="source-source-b9d7160919621f"></a>

### [Transcendence and continued fraction expansion of values of Hecke--Mahler series](https://irma.math.unistra.fr/~bugeaud/travaux/BuMLAA.pdf)

- Source id: `source-b9d7160919621f`
- Author or public identity: Y. Bugeaud, M. Laurent
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Modern form (Theorem 1.1) of the Hecke–Mahler value theorem applied to the two-prime boundary sum.
- Source verification: `source\_verified` — The cited passages (Theorem 1.1; Theorem 1.1 (two places; journal 'p. 61' removed)) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1.1](https://irma.math.unistra.fr/~bugeaud/travaux/BuMLAA.pdf)
- [Theorem 1.1 (two places; journal 'p. 61' removed)](https://irma.math.unistra.fr/~bugeaud/travaux/BuMLAA.pdf)
- [Theorem 1.1; supplied PDF p. 3](https://irma.math.unistra.fr/~bugeaud/travaux/BuMLAA.pdf)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4463-L4466) — lines `4463–4466`; excerpt `sha256:3566f4017e8d66bd416398ee1ff4829b468fbfc27cdd460a22f7d3c1443a3892`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1039-L1042) — lines `1039–1042`; excerpt `sha256:3566f4017e8d66bd416398ee1ff4829b468fbfc27cdd460a22f7d3c1443a3892`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4405-L4408) — lines `4405–4408`; excerpt `sha256:3566f4017e8d66bd416398ee1ff4829b468fbfc27cdd460a22f7d3c1443a3892`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L84-L84) — lines `84–84`; excerpt `sha256:83a2da03f72cdfe7d20a66a82e8d957584ade075bfcbcc042444582792ef211e`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L84-L84) — lines `84–84`; excerpt `sha256:83a2da03f72cdfe7d20a66a82e8d957584ade075bfcbcc042444582792ef211e`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:702](../../paper/269/erdos-269-three-prime-running-lcm.tex#L702-L702)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:142](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L142-L142), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:588](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L588-L588), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1345](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1345-L1345), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1628](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1628-L1628), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3904](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3904-L3904), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:4396](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4396-L4396), [cite at paper/reasoning-parts/erdos269/core.tex:84](../../paper/reasoning-parts/erdos269/core.tex#L84-L84), [cite at paper/reasoning-parts/erdos269/core.tex:530](../../paper/reasoning-parts/erdos269/core.tex#L530-L530), [cite at paper/reasoning-parts/erdos269/core.tex:1287](../../paper/reasoning-parts/erdos269/core.tex#L1287-L1287), [cite at paper/reasoning-parts/erdos269/core.tex:1570](../../paper/reasoning-parts/erdos269/core.tex#L1570-L1570), [cite at paper/reasoning-parts/erdos269/core.tex:3846](../../paper/reasoning-parts/erdos269/core.tex#L3846-L3846), [cite at paper/reasoning-parts/erdos269/core.tex:4338](../../paper/reasoning-parts/erdos269/core.tex#L4338-L4338)

<a id="source-source-bae14c21d3e920"></a>

### [Lean Language Reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

- Source id: `source-bae14c21d3e920`
- Author or public identity: Lean Project.
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1367-L1373) — lines `1367–1373`; excerpt `sha256:848005fb515337995c8dbc8192771103fe3414debe3bde5da05f345ee7b14055`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:1260](../../docs/papers/mirror/plectis-public-system.tex#L1260-L1260)

<a id="source-source-baker-harman-pintz-2001"></a>

### [The difference between consecutive primes, II](https://doi.org/10.1112/plms/83.3.532)

- Source id: `source-baker-harman-pintz-2001`
- Author or public identity: R. C. Baker, Glyn Harman, János Pintz
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Named in a Lean comment as the Baker–Harman–Pintz bound g\_n ≪ p\_n^0.525, among prime-gap estimates shown insufficient by the local bounded-perturbation countermodel. No theorem from the paper is formalized. The comment names the Baker–Harman–Pintz bound g\_n ≪ p\_n^0.525 among prime-gap theorems invariant under bounded additive perturbation. This is a limitation/comparison statement; the paper’s proof is not formalized.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `not recorded`

Exact source locations:

- [Proceedings of the London Mathematical Society 83 (2001), 532–562; primary DOI publication identity.](https://doi.org/10.1112/plms/83.3.532)
- [Glyn Harman institutional publication record: authors, 2001, volume 83, pp. 532–562.](https://pure.royalholloway.ac.uk/en/publications/on-the-difference-between-consecutive-primes-ii/)

Public implementation or evidence coordinates:

- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L19-L20) — lines `19–20`; excerpt `sha256:e24d4fe9967be0a811dc1c113c9c1c4b79c42b042947459ceca902012638f6ec`

<a id="source-source-bbb68df5b83380"></a>

### [Sequences of integers generated by two fixed primes](https://link.springer.com/article/10.1007/s12188-025-00293-9)

- Source id: `source-bbb68df5b83380`
- Author or public identity: Alessandro Languasco, Florian Luca, Pieter Moree, Alain Togbé
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Modern fixed-two-prime lattice and neighbour context. Use the published version; an explicit constant changed from the early preprint.
- Source verification: `source\_verified` — Version-of-record introduction and Section 2 (Theorem 1.3 and proof), plus Appendix A statements. Earlier arXiv text checked only as a version comparison.
- Local mapping: `not recorded`

Exact source locations:

- [Version-of-record introduction and Section 2 (Theorem 1.3 and proof), plus Appendix A statements. Earlier arXiv text checked only as a version comparison.](https://link.springer.com/article/10.1007/s12188-025-00293-9)

Public implementation or evidence coordinates:

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1076-L1079) — lines `1076–1079`; excerpt `sha256:4882a3b299d75653e0733b29ff553b0c30bef3f7e4584c239baa2dc69d719f05`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4505-L4508) — lines `4505–4508`; excerpt `sha256:d2de58d8a1aef218af5e1cbe7a8d2d2e6c1b7fa33cca90bcee80d5265ac4b37f`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4447-L4450) — lines `4447–4450`; excerpt `sha256:d2de58d8a1aef218af5e1cbe7a8d2d2e6c1b7fa33cca90bcee80d5265ac4b37f`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1005](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1005-L1005)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:182](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L182-L182), [cite at paper/reasoning-parts/erdos269/core.tex:124](../../paper/reasoning-parts/erdos269/core.tex#L124-L124)

<a id="source-source-bc5d16b84e62c7"></a>

### [Smooth numbers: computational number theory and beyond](https://library.slmath.org/books/Book44/files/09andrew.pdf)

- Source id: `source-bc5d16b84e62c7`
- Author or public identity: A. Granville
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Smooth-number asymptotics named where the non-supplier budget needs them; the deduction that would close the budget is not made in the papers.
- Source verification: `source\_verified` — The cited passages ((1.1) and (1.3), p. 268) were checked against the chapter, printed pagination copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [(1.1) and (1.3), p. 268](https://library.slmath.org/books/Book44/files/09andrew.pdf)
- [Smooth-number estimates; fixed and varying parameter regimes must be distinguished.](https://library.slmath.org/books/Book44/files/09andrew.pdf)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10343-L10348) — lines `10343–10348`; excerpt `sha256:3b4314143d0179f0e80db37bd37b8d4c9238a3d5a98cff4c888fcdf15fd2d416`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10151-L10156) — lines `10151–10156`; excerpt `sha256:3b4314143d0179f0e80db37bd37b8d4c9238a3d5a98cff4c888fcdf15fd2d416`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8273](../../paper/249/erdos249-totient-reasoning-surface.tex#L8273-L8273), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8274](../../paper/249/erdos249-totient-reasoning-surface.tex#L8274-L8274), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8081](../../paper/reasoning-parts/erdos249/a249_front.tex#L8081-L8081), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8082](../../paper/reasoning-parts/erdos249/a249_front.tex#L8082-L8082)

<a id="source-source-bd5fabd398bdfa"></a>

### [Goal Structuring Notation Community Standard, Version 3](https://scsc.uk/scsc-141c)

- Source id: `source-bd5fabd398bdfa`
- Author or public identity: SCSC Assurance Case Working Group (ACWG).
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1334-L1340) — lines `1334–1340`; excerpt `sha256:18a8d4297efae6feb71647744dd95041e21981acc49c27a0e1687c67df212362`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:422](../../docs/papers/mirror/plectis-public-system.tex#L422-L422)

<a id="source-source-c29036ef9c4da8"></a>

### [Contributing to mathlib](https://leanprover-community.github.io/contribute/index.html)

- Source id: `source-c29036ef9c4da8`
- Author or public identity: Lean community
- Kind: `software`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1661-L1666) — lines `1661–1666`; excerpt `sha256:a61b861ef9dfbc8c5a24e60e162f7b7fa072c019024917cf1a7847ac064e8432`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:483](../../paper/systems/claim-faithful-publication-systems-paper.tex#L483-L483), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1040](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1040-L1040)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:999](../../paper/systems/open-source-mathematics-strategy.tex#L999-L999), [cite at paper/systems/open-source-mathematics-strategy.tex:1421](../../paper/systems/open-source-mathematics-strategy.tex#L1421-L1421)

<a id="source-source-c32d672658410d"></a>

### [Bounded gaps between primes](https://doi.org/10.4007/annals.2014.179.3.7)

- Source id: `source-c32d672658410d`
- Author or public identity: Y. Zhang
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Bounded-gap theorem cited as a comparison.
- Source verification: `source\_verified` — The cited passages (Theorem 1, p. 1122; Theorem 1, p. 1122) were checked against the published PDF copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1, p. 1122](https://doi.org/10.4007/annals.2014.179.3.7)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L832-L834) — lines `832–834`; excerpt `sha256:5bb26410e95839b64ea4bf5f23b0e11414c0841dab9afdc4a31c006cc4754751`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3069-L3071) — lines `3069–3071`; excerpt `sha256:5bb26410e95839b64ea4bf5f23b0e11414c0841dab9afdc4a31c006cc4754751`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3027-L3029) — lines `3027–3029`; excerpt `sha256:5bb26410e95839b64ea4bf5f23b0e11414c0841dab9afdc4a31c006cc4754751`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L21-L21) — lines `21–21`; excerpt `sha256:07dad1a6dbaa03c54631370154c906de91a50cd710b3b9c6e143f85e14b3c973`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:767](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L767-L767)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2092](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2092-L2092), [cite at paper/reasoning-parts/erdos251/core.tex:2050](../../paper/reasoning-parts/erdos251/core.tex#L2050-L2050)

<a id="source-source-c61a0cf3f328ce"></a>

### [Continued-fraction characterization of Stieltjes moment sequences with support in \[ξ,∞)](https://arxiv.org/abs/2404.12131v1)

- Source id: `source-c61a0cf3f328ce`
- Author or public identity: Alan D. Sokal, James Walrad
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Formal S-fraction reformulation; uniqueness of fraction coefficients must not be confused with uniqueness of a representing measure.
- Source verification: `source\_verified` — Full-text pp. 1--3: classical Stieltjes continued-fraction criterion recalled in the introduction and support refinements. No claim that these authors originated the classical criterion.
- Local mapping: `not recorded`

Exact source locations:

- [Full-text pp. 1--3: classical Stieltjes continued-fraction criterion recalled in the introduction and support refinements. No claim that these authors originated the classical criterion.](https://arxiv.org/abs/2404.12131v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1348-L1353) — lines `1348–1353`; excerpt `sha256:8b16aa8ce3f46b281fb40b2e16b106525ac072214009c4f43d3751d3148a85ef`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5372-L5377) — lines `5372–5377`; excerpt `sha256:e0b4d65450b872a2ec9473172bcabec68557987449286f48db42d3c226f70988`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5341-L5346) — lines `5341–5346`; excerpt `sha256:e0b4d65450b872a2ec9473172bcabec68557987449286f48db42d3c226f70988`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1117](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1117-L1117)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2999](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2999-L2999), [cite at paper/reasoning-parts/erdos1049/core.tex:2968](../../paper/reasoning-parts/erdos1049/core.tex#L2968-L2968)

<a id="source-source-c6e97d89c9fa5f"></a>

### [Irrationality Criteria for Series by Erdős and Straus](https://www.isa-afp.org/entries/Irrational_Series_Erdos_Straus.html)

- Source id: `source-c6e97d89c9fa5f`
- Author or public identity: A. Koutsoukou-Argyraki, W. Li
- Kind: `software`
- Problems: #269, #243
- Relationship and boundary: Isabelle/HOL formalisation of the Erdős–Straus criteria, cited in the carry-lineage paragraph.
- Source verification: `source\_verified` — The cited passages ((no locator)) were checked against the AFP proof document, build dated 6 February 2026 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [(no locator)](https://www.isa-afp.org/entries/Irrational_Series_Erdos_Straus.html)
- [Archive entry: scope paragraph and publication date](https://isa-afp.org/entries/Irrational_Series_Erdos_Straus.html)
- [Entry plus proof document Section 2: context hypotheses and theorem-2-1-Erdos-Straus; not a fresh Isabelle replay.](https://isa-afp.org/entries/Irrational_Series_Erdos_Straus.html)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4478-L4481) — lines `4478–4481`; excerpt `sha256:fc54218ee2caf5338f8576a083a77ebf02ded7474aabe6fadbda0c33f1624c08`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4420-L4423) — lines `4420–4423`; excerpt `sha256:fc54218ee2caf5338f8576a083a77ebf02ded7474aabe6fadbda0c33f1624c08`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1478-L1483) — lines `1478–1483`; excerpt `sha256:24a478d3e71a9e5ce6ab2dcf8084cf9ba533270acd0b15cdfd19710d0c338733`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4180-L4185) — lines `4180–4185`; excerpt `sha256:24a478d3e71a9e5ce6ab2dcf8084cf9ba533270acd0b15cdfd19710d0c338733`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4141-L4146) — lines `4141–4146`; excerpt `sha256:24a478d3e71a9e5ce6ab2dcf8084cf9ba533270acd0b15cdfd19710d0c338733`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1082-L1085) — lines `1082–1085`; excerpt `sha256:997988654d9ef70ccc079da055de714cc3514f6ed4822ee4b84eab7c073da669`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1224](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1224-L1224), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1280](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1280-L1280)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:995](../../paper/269/erdos-269-three-prime-running-lcm.tex#L995-L995)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1050](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1050-L1050), [cite at paper/reasoning-parts/erdos243/core.tex:1011](../../paper/reasoning-parts/erdos243/core.tex#L1011-L1011)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2549](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2549-L2549), [cite at paper/reasoning-parts/erdos269/core.tex:2491](../../paper/reasoning-parts/erdos269/core.tex#L2491-L2491)

<a id="source-source-c742deb980b53c"></a>

### [Irrationality of rapidly converging series: a problem of Erdős and Graham](https://arxiv.org/abs/2601.21442)

- Source id: `source-c742deb980b53c`
- Author or public identity: Kevin Barreto, Jiwon Kang, Sang-hyun Kim, Vjekoslav Kovač, Shengtong Zhang
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Rapid-growth and interval-filling results (Theorems 2 and 5, Lemma 14) cited as adjacent literature.
- Source verification: `source\_verified` — The cited passages (Theorem 2, pp. 2-3; Theorem 5 and Remark 4(4), p. 5; Lemma 14, p. 13) were checked against the arXiv v3 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 2, pp. 2-3; Theorem 5 and Remark 4(4), p. 5; Lemma 14, p. 13](https://arxiv.org/abs/2601.21442v3)
- [Theorems 2–3, pp. 2–4; Remark 4(4), p. 5; Lemma 14, p. 13 (v3).](https://arxiv.org/pdf/2601.21442v3)

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1674-L1678) — lines `1674–1678`; excerpt `sha256:156df176c039566fa6a406e54730ac45e0fabbf03ff99eaeb3b08442cc0945c5`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:885](../../paper/257/erdos-257-mersenne-support-subseries.tex#L885-L885)

<a id="source-source-c786f202d47318"></a>

### [The Fourier transform of functions of the greatest common divisor](https://math.colgate.edu/~integers/i50/i50.pdf)

- Source id: `source-c786f202d47318`
- Author or public identity: W. Schramm
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Fourier transform of gcd-functions, the general antecedent of the cyclotomic gcd-word projection specialised in the papers.
- Source verification: `source\_verified` — The cited passages (Theorem and equation (2), p. 2) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem and equation (2), p. 2](https://math.colgate.edu/~integers/i50/i50.pdf)
- [Finite Fourier/gcd identities used in coordinate changes.](https://math.colgate.edu/~integers/i50/i50.pdf)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10309-L10314) — lines `10309–10314`; excerpt `sha256:cda83ebde02e28a432b8ceb19002a8a337d3c75febb082deef2e12df21f76d3e`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10117-L10122) — lines `10117–10122`; excerpt `sha256:cda83ebde02e28a432b8ceb19002a8a337d3c75febb082deef2e12df21f76d3e`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:2688](../../paper/249/erdos249-totient-reasoning-surface.tex#L2688-L2688), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:2496](../../paper/reasoning-parts/erdos249/a249_front.tex#L2496-L2496)

<a id="source-source-c835bc94aad831"></a>

### [On the irrationality of factorial series](https://geodesic.mathdoc.fr/articles/10.4064/aa118-4-5/)

- Source id: `source-c835bc94aad831`
- Author or public identity: J. Hančl, R. Tijdeman
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Factorial-tail integrality argument (Lemma 2.1 and the following remark, p. 385), the polynomial-coefficient classification (Theorem 3.1, Corollary 3.1) and the reproduced Oppenheim criterion (Lemma 2.2) with its hypotheses.
- Source verification: `source\_verified` — Primary publisher PDF p. 385 visually inspected. This verifies the normalized-tail integrality precedent; it supplies no irrationality proof for individual denominators n!-1.
- Local mapping: `not recorded`

Exact source locations:

- [Section 2, Basic lemmas, printed p. 385: Lemma 2.1 and the following Remark. Integer coefficients and cumulative linear-product denominators; rationality implies denominator-cleared normalized tails are integers. For ordinary factorial denominators the multiplier is eventually unnecessary.](https://doi.org/10.4064/aa118-4-5)
- [Lemma 2.1 and following Remark, printed page 385: normalized-tail integrality for rational integer-coefficient factorial series; separate finite-difference criteria retain their additional hypotheses.](https://www.impan.pl/shop/en/publication/transaction/download/product/83588)
- [Lemma 2.1 and the following remark, p. 385](https://doi.org/10.4064/aa118-4-5)
- [Theorem 3.1 and Corollary 3.1, pp. 390-391](https://doi.org/10.4064/aa118-4-5)
- [Thm. 3.1 and Cor. 3.1, pp. 390-391](https://doi.org/10.4064/aa118-4-5)
- [Lem. 2.2, p. 385](https://doi.org/10.4064/aa118-4-5)
- [Pass-one full-text scope retained from supplied review: Lemma 2.1 with following remark, p. 385, and Theorem 3.1/Corollary 3.1, pp. 390–391. This pass edits the formulation; it does not claim a new full-proof audit.](https://doi.org/10.4064/aa118-4-5)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3191-L3195) — lines `3191–3195`; excerpt `sha256:1c1ed4ef4c6101db50bde9f966d63761d20c722b5a1a19916cb663d42ee249fd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3156-L3160) — lines `3156–3160`; excerpt `sha256:1c1ed4ef4c6101db50bde9f966d63761d20c722b5a1a19916cb663d42ee249fd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2613-L2613) — lines `2613–2613`; excerpt `sha256:eaef0eb562b2565c4e6cca9b9e2071d569a2d058ca3df8fe1a95c3b9fbbe116f`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L572-L576) — lines `572–576`; excerpt `sha256:dda39d0b8061ef15651d6453ded0f99da28a8186817fb5bf3e6a3ea605fd1b5c`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:90](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L90-L91)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1349](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1349-L1350), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2315](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2315-L2316), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2648](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2648-L2648), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2651](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2651-L2651), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2659](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2659-L2659), [cite at paper/reasoning-parts/erdos68/core.tex:1314](../../paper/reasoning-parts/erdos68/core.tex#L1314-L1315), [cite at paper/reasoning-parts/erdos68/core.tex:2280](../../paper/reasoning-parts/erdos68/core.tex#L2280-L2281), [cite at paper/reasoning-parts/erdos68/core.tex:2613](../../paper/reasoning-parts/erdos68/core.tex#L2613-L2613), [cite at paper/reasoning-parts/erdos68/core.tex:2616](../../paper/reasoning-parts/erdos68/core.tex#L2616-L2616), [cite at paper/reasoning-parts/erdos68/core.tex:2624](../../paper/reasoning-parts/erdos68/core.tex#L2624-L2624)

<a id="source-source-c9b987093aaf4e"></a>

### [The Poisson Tail Conjecture for primes in short intervals](https://arxiv.org/abs/2605.23014v2)

- Source id: `source-c9b987093aaf4e`
- Author or public identity: Jha, Abhishek
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — full\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3095-L3097) — lines `3095–3097`; excerpt `sha256:e6fc69e63673756998024749e72cb913b9a0094933c34fd8e81d93f0eeca483e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3053-L3055) — lines `3053–3055`; excerpt `sha256:e6fc69e63673756998024749e72cb913b9a0094933c34fd8e81d93f0eeca483e`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:667](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L667-L667), [cite at paper/reasoning-parts/erdos251/core.tex:625](../../paper/reasoning-parts/erdos251/core.tex#L625-L625)

<a id="source-source-ca19e504149107"></a>

### [Irrationality proof of certain Lambert series using little q-Jacobi polynomials](https://doi.org/10.1016/j.cam.2009.02.036)

- Source id: `source-ca19e504149107`
- Author or public identity: J. Coussement, C. Smet
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Neighbouring little q-Jacobi Padé construction for Lambert series at integer-reciprocal base parameter.
- Source verification: `source\_verified` — The cited passages (Thms. 1.2--1.3, p. 2; Sec. 2) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Thms. 1.2--1.3, p. 2; Sec. 2](https://doi.org/10.1016/j.cam.2009.02.036)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://doi.org/10.1016/j.cam.2009.02.036)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5277-L5283) — lines `5277–5283`; excerpt `sha256:b6b59c3f516fe753628de797f741e46ad1554bcd562427e309cfd40f794a23f8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5246-L5252) — lines `5246–5252`; excerpt `sha256:b6b59c3f516fe753628de797f741e46ad1554bcd562427e309cfd40f794a23f8`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4979](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4979-L4979), [cite at paper/reasoning-parts/erdos1049/core.tex:4948](../../paper/reasoning-parts/erdos1049/core.tex#L4948-L4948)

<a id="source-source-cbaba7aeeb0f71"></a>

### [On the rationality of Cantor and Ahmes series](https://doi.org/10.1016/S0019-3577(02)80018-0)

- Source id: `source-cbaba7aeeb0f71`
- Author or public identity: R. Tijdeman, P. Yuan
- Kind: `literature`
- Problems: #243
- Relationship and boundary: Classical LCM-weighted criterion of the same kind for positive numerators, named at the LCM comparison and in the pointwise-sign discussion.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Retained Cantor/Ahmes and LCM comparison.](https://doi.org/10.1016/S0019-3577(02)80018-0)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1419-L1423) — lines `1419–1423`; excerpt `sha256:8a847cb8c6d7ed0d59130cbc1d2e6cc75ca5363d7b766e4b4549f87e237f59d6`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4105-L4109) — lines `4105–4109`; excerpt `sha256:8a847cb8c6d7ed0d59130cbc1d2e6cc75ca5363d7b766e4b4549f87e237f59d6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4066-L4070) — lines `4066–4070`; excerpt `sha256:8a847cb8c6d7ed0d59130cbc1d2e6cc75ca5363d7b766e4b4549f87e237f59d6`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:987](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L987-L987), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1005](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1005-L1005)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:882](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L882-L882), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1693](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1693-L1693), [cite at paper/reasoning-parts/erdos243/core.tex:843](../../paper/reasoning-parts/erdos243/core.tex#L843-L843), [cite at paper/reasoning-parts/erdos243/core.tex:1654](../../paper/reasoning-parts/erdos243/core.tex#L1654-L1654)

<a id="source-source-cc1c19967d418f"></a>

### [GIMPS](https://www.mersenne.org/)

- Source id: `source-cc1c19967d418f`
- Author or public identity: Great Internet Mersenne Prime Search
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1651-L1656) — lines `1651–1656`; excerpt `sha256:3b1c1f707242e20b5d386d4825b37ac2214783f7d5eabb0ada5326605f0fc4cd`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:609](../../paper/systems/claim-faithful-publication-systems-paper.tex#L609-L609), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1052](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1052-L1052)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:585](../../paper/systems/open-source-mathematics-strategy.tex#L585-L585), [cite at paper/systems/open-source-mathematics-strategy.tex:929](../../paper/systems/open-source-mathematics-strategy.tex#L929-L929), [cite at paper/systems/open-source-mathematics-strategy.tex:984](../../paper/systems/open-source-mathematics-strategy.tex#L984-L984)

<a id="source-source-cc823e517ced81"></a>

### [EurekAgent: Agent Environment Engineering is All You Need for Autonomous Scientific Discovery](https://doi.org/10.48550/arXiv.2606.13662)

- Source id: `source-cc823e517ced81`
- Author or public identity: Amy Xin, Jiening Siow, Junjie Wang, Zijun Yao, Fanjin Zhang, Jian Song, Lei Hou, Juanzi Li
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://arxiv.org/abs/2606.13662v2)

<a id="source-source-cd126799fede94"></a>

### [Little q-Legendre polynomials and irrationality of certain Lambert series](https://arxiv.org/abs/math/0101187)

- Source id: `source-cd126799fede94`
- Author or public identity: W. Van Assche
- Kind: `literature`
- Problems: #1049, #257
- Relationship and boundary: Little q-Legendre Padé approximants for F at integer bases, compared with the Amdeberhan–Zeilberger diagonal.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- \*\*Reading status:\*\* the complete source was read from its text layer and page renders. The arXiv front matter is PDF page 1; the body’s printed pages are PDF pages 1–15.](https://arxiv.org/abs/math/0101187)
- [1. \*\*Lambert values (Introduction, equations (1)–(2), PDF pp. 1–2).\*\* For \`p = 1/q \> 1\`, the paper defines \`h\_p(1) = sum\_ k\>=1 1/(p^k - 1) = sum\_ k\>=1 q^k/(1 - q^k)\` and \`ln\_p(2) = sum\_ k\>=1 (-1)^k/(p^k - 1) = sum\_ k\>=1 (-q)^k/(1 - q^k)\`. It places these values against the earlier Erdős, Borwein, Bundschuh–Väänänen, and Matala-aho–Väänänen results.](https://arxiv.org/abs/math/0101187)
- [2. \*\*Little q-Legendre kernel (Section 2, equations (3)–(16), PDF pp. 3–4).\*\* The source defines \`P\_n(x | q)\` as a basic hypergeometric polynomial, records orthogonality on \` q^k : k \>= 0 \`, gives its \`p\`-binomial expansion, and gives a Rodrigues formula and the \`(qx;q)\_k\`-basis expansion.](https://arxiv.org/abs/math/0101187)
- [3. \*\*Stieltjes/Padé approximation route (Section 3, equations (17)–(22), PDF pp. 5–6).\*\* The paper defines the Stieltjes function for the discrete measure on \` q^k \`, identifies \`f(p^n)\` with \`h\_p(1)\` up to a finite rational prefix, and applies the orthogonal-polynomial identity to construct rational approximants.](https://arxiv.org/abs/math/0101187)
- [4. \*\*Integer approximants and error identity (Section 3, equations (23)–(35), PDF pp. 6–9).\*\* Equations (23)–(26) and (31)–(33) give the evaluated polynomial, cyclotomic denominator factor \`d\_n(p)\`, integer sequences \`a\_n,b\_n\`, and the error sum. Equation (34) rewrites the error as a positive square-norm sum, and (35) bounds it.](https://arxiv.org/abs/math/0101187)
- [5. \*\*q-harmonic theorem (Theorem 1, PDF p. 10; publication p. 304).\*\* The source states that for every integer \`p \> 1\`, the constructed \`a\_n,b\_n\` give \`h\_p(1)\` irrational and records the bound \`r(h\_p(1)) \<= 2 pi^2/(pi^2 - 2) = 2.50828...\`.](https://arxiv.org/abs/math/0101187)
- [6. \*\*q-logarithm theorem (Section 4, equations (38)–(44), Theorem 2, PDF pp. 11–13; publication pp. 305–307).\*\* The analogous evaluation at \`-p^n\` gives integer approximants for \`ln\_p(2)\`. Theorem 2 states irrationality for every integer \`p \> 1\` and records \`r(ln\_p(2)) \<= 2 pi^2/(pi^2 - 4) = 3.36295...\`.](https://arxiv.org/abs/math/0101187)
- [7. \*\*Rational-parameter extension (Section 5, equations (45)–(46), Theorem 3, PDF pp. 13–14; publication pp. 307–308).\*\* For rational \`c = a/b\` with \`c p^k != 1\`, the paper extends the construction to \`L = sum\_ k\>=1 1/(c p^k - 1)\`, proves irrationality, and records the bound \`r(L) \<= 3 pi^2/(pi^2 - 3) = 4.310119...\`.](https://arxiv.org/abs/math/0101187)
- [- The source supplies a Padé/little-q-Legendre construction and its own irrationality theorems. The local residual at \`n = 0\` for the Van Assche diagonal, and the resulting non-transfer statement for the Amdeberhan–Zeilberger scalar recurrence, are separately computed and Lean-checked; they are not claims stated by Van Assche.](https://arxiv.org/abs/math/0101187)
- [- The attribution ceiling is Van Assche’s Padé construction, the stated little-q-Legendre identities, and Theorems 1–3 with their hypotheses and reported irrationality-measure bounds. No novelty or priority claim is made for the local residual or its formal proof.](https://arxiv.org/abs/math/0101187)
- [(23) and the following paragraph, p. 6](https://arxiv.org/abs/math/0101187v1)
- [Thm. 1, p. 10 (and proof pp. 10--11)](https://arxiv.org/abs/math/0101187v1)
- [Thm. 3, p. 14](https://arxiv.org/abs/math/0101187v1)
- [Lemma 1, p.2](https://arxiv.org/abs/math/0101187v1)
- [Section 3](https://arxiv.org/abs/math/0101187v1)
- [(34)--(35), p.9](https://arxiv.org/abs/math/0101187v1)
- [Full-text consultation, especially (4), (9), pp. 3--4; alternative expansion (16), p. 4; Padé/Markov formulas (17)--(21).](https://arxiv.org/abs/math/0101187v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5271-L5277) — lines `5271–5277`; excerpt `sha256:caca3710f524135671e299fa1162e5d77947646ae83681362b020268b6f0aac0`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5240-L5246) — lines `5240–5246`; excerpt `sha256:caca3710f524135671e299fa1162e5d77947646ae83681362b020268b6f0aac0`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L847-L847) — lines `847–847`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L847-L847) — lines `847–847`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L847-L847) — lines `847–847`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L847-L847) — lines `847–847`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L4-L13) — lines `4–13`; excerpt `sha256:9e02e269f490c0d8ee088d184d3cf2b53af45d9b0144a4623c9110e7230e7af9`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L19-L32) — lines `19–32`; excerpt `sha256:ed4a3e5b020b06b3f16f2771e4c9518cf5e0c23e46e275e30a93b5b498f5db23`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L58-L62) — lines `58–62`; excerpt `sha256:6fab9c0293d1ca17fe26b54f24d0f7366711b09b71d8f6e869df1315fb5c2dbc`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1699-L1706) — lines `1699–1706`; excerpt `sha256:c67b14d05ad70fe87ae10882e6666f671b4fb879b6ad3b2ac2f9cd21da8d1764`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9713-L9720) — lines `9713–9720`; excerpt `sha256:c67b14d05ad70fe87ae10882e6666f671b4fb879b6ad3b2ac2f9cd21da8d1764`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9513-L9520) — lines `9513–9520`; excerpt `sha256:c67b14d05ad70fe87ae10882e6666f671b4fb879b6ad3b2ac2f9cd21da8d1764`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1320-L1326) — lines `1320–1326`; excerpt `sha256:72d40703f422b4e9c77e9b7f7d1db51028590dcfa3b80e0dfd26187887ef7b98`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1105](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1105-L1105)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1059](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1059-L1059)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:878](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L878-L878), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2806](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2806-L2806), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4930](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4930-L4930), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4934](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4934-L4934), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4956](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4956-L4956), [cite at paper/reasoning-parts/erdos1049/core.tex:847](../../paper/reasoning-parts/erdos1049/core.tex#L847-L847), [cite at paper/reasoning-parts/erdos1049/core.tex:2775](../../paper/reasoning-parts/erdos1049/core.tex#L2775-L2775), [cite at paper/reasoning-parts/erdos1049/core.tex:4899](../../paper/reasoning-parts/erdos1049/core.tex#L4899-L4899), [cite at paper/reasoning-parts/erdos1049/core.tex:4903](../../paper/reasoning-parts/erdos1049/core.tex#L4903-L4903), [cite at paper/reasoning-parts/erdos1049/core.tex:4925](../../paper/reasoning-parts/erdos1049/core.tex#L4925-L4925)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9544](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9544-L9544), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9344](../../paper/reasoning-parts/erdos257/a257_front.tex#L9344-L9344)

<a id="source-source-ce27d27dd5ec77"></a>

### [On a new condition implying that an achievement set is a Cantorval and its applications](https://arxiv.org/abs/2512.17761v1)

- Source id: `source-ce27d27dd5ec77`
- Author or public identity: Nowakowski, Piotr
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — selected\_primary\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L644-L645) — lines `644–645`; excerpt `sha256:593651151526dd9c60804cafcb6f765f4f855a943dd88f568cbe7e65e48b06fe`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3105-L3107) — lines `3105–3107`; excerpt `sha256:6287f2e5f5563289d4064e0d820c7d7f4d40b15e0efeaa8af2f7bf000182a58a`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3063-L3065) — lines `3063–3065`; excerpt `sha256:6287f2e5f5563289d4064e0d820c7d7f4d40b15e0efeaa8af2f7bf000182a58a`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:645](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L645-L645), [cite at paper/reasoning-parts/erdos251/core.tex:603](../../paper/reasoning-parts/erdos251/core.tex#L603-L603)

<a id="source-source-ce5fddc99aff3f"></a>

### [Association for Computing Machinery](https://www.acm.org/publications/policies/artifact-review-and-badging-current)

- Source id: `source-ce5fddc99aff3f`
- Author or public identity: Association for Computing Machinery
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1346-L1351) — lines `1346–1351`; excerpt `sha256:82ba5ed7e06a2f42df45b4196b5caba7c6b634aab7fa76273b92a7cc6bf3768e`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:437](../../docs/papers/mirror/plectis-public-system.tex#L437-L437)

<a id="source-source-cf94fac28d0ff1"></a>

### [AlphaEvolve: A coding agent for scientific and algorithmic discovery](https://arxiv.org/html/2506.13131v1)

- Source id: `source-cf94fac28d0ff1`
- Author or public identity: Alexander Novikov, Ngân Vũ, Marvin Eisenberger, Emilien Dupont, Po-Sen Huang, Adam Zsolt Wagner, Sergey Shirobokov, Borislav Kozlovskii, Francisco J. R. Ruiz, Abbas Mehrabian, M. Pawan Kumar, Abigail See, Swarat Chaudhuri, George Holland, Alex Davies, Sebastian Nowozin, Pushmeet Kohli, Matej Balog
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: The round-7 research-commons note uses evaluator-scoped program evolution as a prior-art comparison for prospective mechanism-transfer experiments.
- Source verification: `source\_verified` — Only the round-7 README passage at lines 63–66 is source-verified against arXiv:2506.13131v1 §§2.1, 2.4 and 2.5. The local target/baseline/disconfirmation requirement is this project’s experimental protocol, not an AlphaEvolve outcome.
- Local mapping: `bounded\_round7\_source\_use` — Version-1 task-specification, evaluation and evolution passages checked for the round-7 README design choice.

Exact source locations:

- [§2.1 Task specification, §2.4 Evaluation, §2.5 Evolution: supplied program, evolvable regions and automatically computable evaluators bound scored program search.](https://arxiv.org/html/2506.13131v1)

Public implementation or evidence coordinates:

- [docs/research-commons/rounds/round7/README.md](../../docs/research-commons/rounds/round7/README.md#L69-L72) — lines `69–72`; excerpt `sha256:cd2254d00d767097a5253778989b0a7f0e7faeb4113eb8147432197bdcc8ac18`

<a id="source-source-coons-nonautomaticity-0810-3709v3"></a>

### [(Non)Automaticity of number theoretic functions (arXiv v3)](https://arxiv.org/abs/0810.3709v3)

- Source id: `source-coons-nonautomaticity-0810.3709v3`
- Author or public identity: Michael Coons
- Kind: `literature`
- Problems: #249
- Relationship and boundary: The Dirichlet-series/nonregularity comparison concerns functions and coefficient sequences; it is not an irrationality result for one function value. Version-specific theorem numbering is preserved alongside the older journal citation.
- Source verification: `bibliography\_only` — Exact edition is in local source custody; the named locus is return-reported and is not certified here as an independent full-text review.
- Local mapping: `exact\_bibliographic\_use` — Round8 manuscript transfer; ordinary proof and citation authority remain separate.

Exact source locations:

- [Version3 Theorem3.3; distinct from Theorem3.2 in the journal edition.](https://arxiv.org/abs/0810.3709v3)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10432-L10436) — lines `10432–10436`; excerpt `sha256:2f294b2503d2448477ab88b5f01e57b82be38261f6866fa51e12cb42fdaf1931`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L7653-L7653) — lines `7653–7653`; excerpt `sha256:ea2c18fcbd108947a85f0c7ad3832b7c5a50121404e6ee760f1a053d967d615f`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10240-L10244) — lines `10240–10244`; excerpt `sha256:2f294b2503d2448477ab88b5f01e57b82be38261f6866fa51e12cb42fdaf1931`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7461-L7461) — lines `7461–7461`; excerpt `sha256:ea2c18fcbd108947a85f0c7ad3832b7c5a50121404e6ee760f1a053d967d615f`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7653](../../paper/249/erdos249-totient-reasoning-surface.tex#L7653-L7653), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7461](../../paper/reasoning-parts/erdos249/a249_front.tex#L7461-L7461)

<a id="source-source-corvaja-zannier-2002-subspace"></a>

### [Some New Applications of the Subspace Theorem](https://doi.org/10.1023/A:1015594913393)

- Source id: `source-corvaja-zannier-2002-subspace`
- Author or public identity: Pietro Corvaja, Umberto Zannier
- Kind: `literature`
- Problems: #257, #1049
- Relationship and boundary: The S-unit approximation method is close prior art for the rational-chain and separated-cut proofs. The local Lambert expansion is not claimed to satisfy Corollary5. No historical priority follows from this comparison.
- Source verification: `bibliography\_only` — Exact edition is in local source custody; the named locus is return-reported and is not certified here as an independent full-text review.
- Local mapping: `exact\_bibliographic\_use` — Round8 manuscript transfer; ordinary proof and citation authority remain separate.

Exact source locations:

- [Theorem4; distinguish Corollary5 and its Hadamard-gap hypothesis.](https://doi.org/10.1023/A:1015594913393)

Public implementation or evidence coordinates:

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2209-L2214) — lines `2209–2214`; excerpt `sha256:de88340cc2b28c69940b64cf1bcdbf90dd118bb326ff5edd71abe0001f11021c`
- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L1350-L1350) — lines `1350–1350`; excerpt `sha256:c5730ed1aecc44a1cef58487cebc75be161e05aa5a960b5dcbb3825e6b92cf96`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1282](../../paper/synthesis/optimal-sparse-perturbations.tex#L1282-L1282), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1350](../../paper/synthesis/optimal-sparse-perturbations.tex#L1350-L1350)

<a id="source-source-d14cd7f6920a31"></a>

### [There are infinitely many Carmichael numbers](https://doi.org/10.2307/2118576)

- Source id: `source-d14cd7f6920a31`
- Author or public identity: W. R. Alford, A. Granville, C. Pomerance
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5412-L5419) — lines `5412–5419`; excerpt `sha256:93d139a71e461686d30e06c7802e159563a317a1df01f8e655071348c500dd47`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2246](../../paper/archive/erdos249-257-main-paper.tex#L2246-L2246)

<a id="source-source-d1710db60eae06"></a>

### [On the greatest and least prime factors of n!+1 , II](https://publi.math.unideb.hu/paper/989/download/10_5486_PMD_2004_3190.pdf)

- Source id: `source-d1710db60eae06`
- Author or public identity: C. L. Stewart
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Wilson reflection identity (p. 462, (4)) and the least-prime-factor bound transferred to n!−1 (pp. 463–464).
- Source verification: `source\_verified` — The cited passages (p. 462, (4); p. 463 (Theorem 1, (9)); p. 464) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [p. 462, (4)](https://doi.org/10.5486/PMD.2004.3190)
- [p. 463 (Theorem 1, (9))](https://doi.org/10.5486/PMD.2004.3190)
- [p. 464](https://doi.org/10.5486/PMD.2004.3190)
- [Full text consulted: reflection (4), p. 462; entire Lemma 2 and proof, pp. 464–470; especially (16)–(17), (21), (23)–(24). No claim to have rechecked the unrelated remainder.](https://publi.math.unideb.hu/paper/989/download/10_5486_PMD_2004_3190.pdf)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3179-L3183) — lines `3179–3183`; excerpt `sha256:3460ef54d7c16f79f21ea0acd344175689e099e53fd07f95423bbc149ab01fcc`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3144-L3148) — lines `3144–3148`; excerpt `sha256:3460ef54d7c16f79f21ea0acd344175689e099e53fd07f95423bbc149ab01fcc`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L951-L951) — lines `951–951`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L951-L951) — lines `951–951`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L951-L951) — lines `951–951`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [lean/ErdosProblems/Erdos68/PrimeZeroBranch.lean](../../lean/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3134-L3139) — lines `3134–3139`; excerpt `sha256:c866f4949ed4ad3259541be1ab078fcd2c3b951e2dcb35d831286f21d4ff0dae`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3144-L3148) — lines `3144–3148`; excerpt `sha256:3460ef54d7c16f79f21ea0acd344175689e099e53fd07f95423bbc149ab01fcc`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:986](../../paper/68/erdos68-factorial-reasoning-surface.tex#L986-L986), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2046](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2046-L2046), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2093](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2093-L2093), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2097](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2097-L2097), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2307](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2307-L2307), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2941](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2941-L2941), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2942](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2942-L2942), [cite at paper/reasoning-parts/erdos68/core.tex:951](../../paper/reasoning-parts/erdos68/core.tex#L951-L951), [cite at paper/reasoning-parts/erdos68/core.tex:2011](../../paper/reasoning-parts/erdos68/core.tex#L2011-L2011), [cite at paper/reasoning-parts/erdos68/core.tex:2058](../../paper/reasoning-parts/erdos68/core.tex#L2058-L2058), [cite at paper/reasoning-parts/erdos68/core.tex:2062](../../paper/reasoning-parts/erdos68/core.tex#L2062-L2062), [cite at paper/reasoning-parts/erdos68/core.tex:2272](../../paper/reasoning-parts/erdos68/core.tex#L2272-L2272), [cite at paper/reasoning-parts/erdos68/core.tex:2906](../../paper/reasoning-parts/erdos68/core.tex#L2906-L2906), [cite at paper/reasoning-parts/erdos68/core.tex:2907](../../paper/reasoning-parts/erdos68/core.tex#L2907-L2907)

<a id="source-source-d31e3bc51f2784"></a>

### [OpenProver: Agentic and Interactive Theorem Proving with Lean 4](https://doi.org/10.48550/arXiv.2607.09217)

- Source id: `source-d31e3bc51f2784`
- Author or public identity: M. Kripner, M. Straka
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1387-L1389) — lines `1387–1389`; excerpt `sha256:c66e4c643708ca23615d9d6c9473c802267b432d3f477cb5deb758c7fb5f7d69`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1049](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1049-L1049)

<a id="source-source-d3995db1508bc9"></a>

### [Long gaps between primes](https://doi.org/10.1090/jams/876)

- Source id: `source-d3995db1508bc9`
- Author or public identity: K. Ford, B. Green, S. Konyagin, J. Maynard, T. Tao
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Large-gap theorem cited as a comparison of a different shape of question.
- Source verification: `source\_verified` — The cited passages (Theorem 1 (page locator dropped); Theorem 1 (two citations; page locator dropped)) were checked against the arXiv v3 (14 July 2016) copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1 (page locator dropped)](https://doi.org/10.1090/jams/876)
- [Theorem 1 (two citations; page locator dropped)](https://doi.org/10.1090/jams/876)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L814-L816) — lines `814–816`; excerpt `sha256:7d4b3edd3f0259421dd8a74baf144d917da4ddfbfce902474872b62fbe04ff8c`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3043-L3045) — lines `3043–3045`; excerpt `sha256:7d4b3edd3f0259421dd8a74baf144d917da4ddfbfce902474872b62fbe04ff8c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3001-L3003) — lines `3001–3003`; excerpt `sha256:7d4b3edd3f0259421dd8a74baf144d917da4ddfbfce902474872b62fbe04ff8c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1063-L1063) — lines `1063–1063`; excerpt `sha256:fb59e0780e408bca1499f60eeea9ba2361376ec468ffa18034717c0b6bfa9c53`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2060-L2060) — lines `2060–2060`; excerpt `sha256:eaaaa84d309b1a0c1d56fc36e531a59a4fa33af5709a256b9b48f214908ca467`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L22-L22) — lines `22–22`; excerpt `sha256:6fe10d86cfbff9e425bdd6578dd696a5a4e58cae9a09bb6b9e1d399e6bd9e791`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:769](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L769-L769)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1103](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1103-L1103), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2103](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2103-L2103), [cite at paper/reasoning-parts/erdos251/core.tex:1061](../../paper/reasoning-parts/erdos251/core.tex#L1061-L1061), [cite at paper/reasoning-parts/erdos251/core.tex:2061](../../paper/reasoning-parts/erdos251/core.tex#L2061-L2061)

<a id="source-source-d471eacdba0f87"></a>

### [The irrationality of some number theoretical series](https://arxiv.org/abs/1105.1451)

- Source id: `source-d471eacdba0f87`
- Author or public identity: J.-C. Schlage-Puchta
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Selberg-sieve nonconcentration lemma (Lemma 4) cited at each prime-gap nonconcentration use.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Theorems 2 and 3 state the digit-concatenation rationality criterion and Q-linear independence of 1,S\_0,S\_1,... .](https://arxiv.org/abs/1105.1451)
- [Selberg-sieve setup and Lemma 4 show that a nonzero polynomial in consecutive prime gaps vanishes only on a density-zero set; the proof is included.](https://arxiv.org/abs/1105.1451)
- [Theorem 3; Lemma 4, pp. 5-6 (three citations: the nonconcentration subsection, the corollary proof, the sparsity proof)](https://arxiv.org/abs/1105.1451v1)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3063-L3065) — lines `3063–3065`; excerpt `sha256:1a14b5dab89311efa51f08c6a1083aa9a70ec67efa331a3a3b2b5c065768d4e5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3021-L3023) — lines `3021–3023`; excerpt `sha256:1a14b5dab89311efa51f08c6a1083aa9a70ec67efa331a3a3b2b5c065768d4e5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L493-L493) — lines `493–493`; excerpt `sha256:f299553286b4320e16b47eddc966a0712f4f7aa504c996308e3b4654f6115f5e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L493-L493) — lines `493–493`; excerpt `sha256:f299553286b4320e16b47eddc966a0712f4f7aa504c996308e3b4654f6115f5e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L493-L493) — lines `493–493`; excerpt `sha256:f299553286b4320e16b47eddc966a0712f4f7aa504c996308e3b4654f6115f5e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1407-L1414) — lines `1407–1414`; excerpt `sha256:5f6919f6f6f0d056ce159d53b5e9796ab4e2ae6a3e46c34b596e2ae84458afac`
- [lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean](../../lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L7-L23) — lines `7–23`; excerpt `sha256:321f1f193ba6cea89edee0e703684bdf6234e2bc38d8b5dc53a6395d1b42cf33`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L842-L844) — lines `842–844`; excerpt `sha256:a3a48dc0af2ce0549ba6c3e9eea30a30f6e3554c01f26cebd6566dc236f816dc`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:438](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L438-L438), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:457](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L457-L457), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:639](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L639-L639)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:535](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L535-L535), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:570](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L570-L570), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:577](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L577-L577), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1451](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1451-L1451), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1557](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1557-L1557), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1569](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1569-L1569), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1616](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1616-L1616), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1625](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1625-L1625), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1682](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1682-L1682), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1689](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1689-L1689), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2279](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2279-L2279), [cite at paper/reasoning-parts/erdos251/core.tex:493](../../paper/reasoning-parts/erdos251/core.tex#L493-L493), [cite at paper/reasoning-parts/erdos251/core.tex:528](../../paper/reasoning-parts/erdos251/core.tex#L528-L528), [cite at paper/reasoning-parts/erdos251/core.tex:535](../../paper/reasoning-parts/erdos251/core.tex#L535-L535), [cite at paper/reasoning-parts/erdos251/core.tex:1409](../../paper/reasoning-parts/erdos251/core.tex#L1409-L1409), [cite at paper/reasoning-parts/erdos251/core.tex:1515](../../paper/reasoning-parts/erdos251/core.tex#L1515-L1515), [cite at paper/reasoning-parts/erdos251/core.tex:1527](../../paper/reasoning-parts/erdos251/core.tex#L1527-L1527), [cite at paper/reasoning-parts/erdos251/core.tex:1574](../../paper/reasoning-parts/erdos251/core.tex#L1574-L1574), [cite at paper/reasoning-parts/erdos251/core.tex:1583](../../paper/reasoning-parts/erdos251/core.tex#L1583-L1583), [cite at paper/reasoning-parts/erdos251/core.tex:1640](../../paper/reasoning-parts/erdos251/core.tex#L1640-L1640), [cite at paper/reasoning-parts/erdos251/core.tex:1647](../../paper/reasoning-parts/erdos251/core.tex#L1647-L1647), [cite at paper/reasoning-parts/erdos251/core.tex:2237](../../paper/reasoning-parts/erdos251/core.tex#L2237-L2237)

<a id="source-source-d517c8a2d6f84d"></a>

### [CRediT: Contributor Roles Taxonomy](https://credit.niso.org/contributor-roles-defined/)

- Source id: `source-d517c8a2d6f84d`
- Author or public identity: NISO
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1737-L1742) — lines `1737–1742`; excerpt `sha256:0e1fe3e7471b6a0f3864ce0578266000a9fbb85f892248701cd17ba615c3e182`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:489](../../paper/systems/claim-faithful-publication-systems-paper.tex#L489-L489), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1052](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1052-L1052)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:845](../../paper/systems/open-source-mathematics-strategy.tex#L845-L845)

<a id="source-source-d7a43109c64c0c"></a>

### [FormalConjectures.ErdosProblems.1049](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/1049.lean)

- Source id: `source-d7a43109c64c0c`
- Author or public identity: The Formal Conjectures Authors
- Kind: `software`
- Problems: #1049
- Relationship and boundary: External formal statement/corpus context cited by the paper. It is not proof authority for this repository and does not make the local result an upstream contribution.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Paper bibliography commit pin f776d2f2039351b00737ffcafb9d7d7666e1d9af; exact problem file](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/1049.lean)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://github.com/google-deepmind/formal-conjectures/blob/f776d2f2039351b00737ffcafb9d7d7666e1d9af/FormalConjectures/ErdosProblems/1049.lean)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5332-L5338) — lines `5332–5338`; excerpt `sha256:fd04dc6525552320cb5e54a12e8e0739172ac9163ecf01bedfd7dcf7a6485be2`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5301-L5307) — lines `5301–5307`; excerpt `sha256:fd04dc6525552320cb5e54a12e8e0739172ac9163ecf01bedfd7dcf7a6485be2`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5129-L5129) — lines `5129–5129`; excerpt `sha256:a687d79281dfe79c9bc043998a9b0da79a7a7066f72571d9b7a84107de6bf44d`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5160-L5160) — lines `5160–5160`; excerpt `sha256:a687d79281dfe79c9bc043998a9b0da79a7a7066f72571d9b7a84107de6bf44d`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5160](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5160-L5160), [cite at paper/reasoning-parts/erdos1049/core.tex:5129](../../paper/reasoning-parts/erdos1049/core.tex#L5129-L5129)

<a id="source-source-d8b2a7c411bc2d"></a>

### [The Lean mathematical library](https://doi.org/10.1145/3372885.3373824)

- Source id: `source-d8b2a7c411bc2d`
- Author or public identity: The mathlib Community
- Kind: `software`
- Problems: #249, #251, #257
- Relationship and boundary: Library cited beside the Lean 4 citation.
- Source verification: `source\_verified` — The cited passages (plain citation at the verification paragraph (previously uncited); abstract and §1.1, p. 367) were checked against the arXiv v2, 16 December 2019 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [plain citation at the verification paragraph (previously uncited)](https://doi.org/10.1145/3372885.3373824)
- [abstract and §1.1, p. 367](https://doi.org/10.1145/3372885.3373824)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5431-L5438) — lines `5431–5438`; excerpt `sha256:add18eb59b9977acb225b85709240b860573b28552d807c45eec7058c8a77d79`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L826-L828) — lines `826–828`; excerpt `sha256:d72e98994bd66ed7b43de80a46537b74234c2d45f82d4b6ff1a1a24103ce7117`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3057-L3059) — lines `3057–3059`; excerpt `sha256:d72e98994bd66ed7b43de80a46537b74234c2d45f82d4b6ff1a1a24103ce7117`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3015-L3017) — lines `3015–3017`; excerpt `sha256:d72e98994bd66ed7b43de80a46537b74234c2d45f82d4b6ff1a1a24103ce7117`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2215-L2215) — lines `2215–2215`; excerpt `sha256:b1ae69e2196d41354ed68c8e0ab198e7acf792ec623ef06ddcd83aa926219a98`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:108](../../paper/systems/claim-faithful-publication-systems-paper.tex#L108-L108), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:593](../../paper/systems/claim-faithful-publication-systems-paper.tex#L593-L593), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1040](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1040-L1040)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:782](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L782-L782)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3772](../../paper/archive/erdos249-257-main-paper.tex#L3772-L3772)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2257](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2257-L2257), [cite at paper/reasoning-parts/erdos251/core.tex:2215](../../paper/reasoning-parts/erdos251/core.tex#L2215-L2215)

<a id="source-source-dbbc7de069eeee"></a>

### [Partitions with prescribed sum of reciprocals: asymptotic bounds](https://arxiv.org/abs/2502.02200v2)

- Source id: `source-dbbc7de069eeee`
- Author or public identity: van Doorn, Wouter
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — full\_text
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L609-L612) — lines `609–612`; excerpt `sha256:a46579d416d03f380705b4e9553347ab0b66c9e1ec6b4d3a84ac0f5a246008c1`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3085-L3087) — lines `3085–3087`; excerpt `sha256:0ff84f114bce1e696b9859dc6944ea26811f851d98955e2f5cf233d48165ac05`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3043-L3045) — lines `3043–3045`; excerpt `sha256:0ff84f114bce1e696b9859dc6944ea26811f851d98955e2f5cf233d48165ac05`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:612](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L612-L612), [cite at paper/reasoning-parts/erdos251/core.tex:570](../../paper/reasoning-parts/erdos251/core.tex#L570-L570)

<a id="source-source-dcbe400c96be59"></a>

### [Some inequalities for polynomials and rational functions associated with a lemniscate](https://doi.org/10.1007/s10958-013-1432-4)

- Source id: `source-dcbe400c96be59`
- Author or public identity: V. N. Dubinin
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Relative area inequality under a full annular covering (Theorem 1), recorded as a neighbouring result that the proofs do not use.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1226-L1231) — lines `1226–1231`; excerpt `sha256:ada915f17a1ed537b753f4f88aa73ca8631254a748c99e5c556dd0dcde0016c1`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5442-L5447) — lines `5442–5447`; excerpt `sha256:8c9bd3c3345cf07ffa6815f7ec1a90485fe63e2b80e1724053327490204d780a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5392-L5397) — lines `5392–5397`; excerpt `sha256:8c9bd3c3345cf07ffa6815f7ec1a90485fe63e2b80e1724053327490204d780a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L2075-L2075) — lines `2075–2075`; excerpt `sha256:bf660f22b7c2b5ad1586f91c21fc4e625ed74e4ec29b524be165def32d7d016d`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:781](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L781-L781)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2125](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2125-L2125), [cite at paper/reasoning-parts/erdos1041/core.tex:2075](../../paper/reasoning-parts/erdos1041/core.tex#L2075-L2075)

<a id="source-source-e13ecb7c94852a"></a>

### [Representations of Real Numbers by Infinite Series](https://doi.org/10.1007/BFb0081642)

- Source id: `source-e13ecb7c94852a`
- Author or public identity: J. Galambos
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Background on rationality questions for Cantor series (Chapter II, §2.1, pp. 21–22).
- Source verification: `source\_verified` — The cited passages (Ch. II, §2.1, pp. 21-22; Ch. II, §2.1, pp. 21-22 (and Ch. II, §2.1 in the attribution paragraph)) were checked against the scan copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Ch. II, §2.1, pp. 21-22](https://doi.org/10.1007/BFb0081642)
- [Ch. II, §2.1, pp. 21-22 (and Ch. II, §2.1 in the attribution paragraph)](https://doi.org/10.1007/BFb0081642)
- [Reference and role retained from the attached paper; not independently reread in full in this revision.](https://doi.org/10.1007/BFb0081642)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3136-L3140) — lines `3136–3140`; excerpt `sha256:259feb71f707ecd3c171a22910b7c8c7271afda92cdb5fc376bb96e7b1e3a4c4`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3171-L3175) — lines `3171–3175`; excerpt `sha256:259feb71f707ecd3c171a22910b7c8c7271afda92cdb5fc376bb96e7b1e3a4c4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3136-L3140) — lines `3136–3140`; excerpt `sha256:259feb71f707ecd3c171a22910b7c8c7271afda92cdb5fc376bb96e7b1e3a4c4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1423-L1423) — lines `1423–1423`; excerpt `sha256:ad8298ac69c418e00f4fc3862912b0d4b44decd465a1ec66f04646c9f5d5ecfb`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1423-L1423) — lines `1423–1423`; excerpt `sha256:ad8298ac69c418e00f4fc3862912b0d4b44decd465a1ec66f04646c9f5d5ecfb`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1458](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1458-L1458), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2312](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2312-L2312), [cite at paper/reasoning-parts/erdos68/core.tex:1423](../../paper/reasoning-parts/erdos68/core.tex#L1423-L1423), [cite at paper/reasoning-parts/erdos68/core.tex:2277](../../paper/reasoning-parts/erdos68/core.tex#L2277-L2277)

<a id="source-source-e2bdd690015cad"></a>

### [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](https://doi.org/10.48550/arXiv.2306.15626)

- Source id: `source-e2bdd690015cad`
- Author or public identity: K. Yang, A. M. Swope, A. Gu, R. Chalamala, P. Song, S. Yu, S. Godil, R. Prenger, A. Anandkumar
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L700-L705) — lines `700–705`; excerpt `sha256:e1fb69819625ee4c623683e8876546bfaeba103a154bb24b05f891cf455291a5`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1226-L1228) — lines `1226–1228`; excerpt `sha256:5c3c73cac106465de37f6b0d206a52293b5061ddb965921d239f718eb722db0e`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1043](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1043-L1043)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:403](../../paper/systems/cold-clone-to-proof-receipt.tex#L403-L403), [cite at paper/systems/cold-clone-to-proof-receipt.tex:488](../../paper/systems/cold-clone-to-proof-receipt.tex#L488-L488)

<a id="source-source-e33bdf934f939f"></a>

### [On the irrationality of certain Ahmes series](https://users.renyi.hu/~p_erdos/1964-19.pdf)

- Source id: `source-e33bdf934f939f`
- Author or public identity: P. Erdős, E. G. Straus
- Kind: `literature`
- Problems: #243, #251
- Relationship and boundary: Classical LCM-weighted rationality criterion with a nonpositive upper limit (Theorem 3, p. 132), the comparator for the LCM corollary.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [286458 bytes; 5 pages, printed pp. 129–133. It remains a local](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [- \*\*Theorem 1 and proof:\*\* printed pp. 129–130. Under the displayed](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [- \*\*Intermediate criterion:\*\* printed p. 131, Theorem 2, together with the](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [- \*\*Theorem 3 and proof:\*\* printed p. 132 and continuing onto p. 133. The](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [large \`k\`. The source explicitly says the Theorem 1 hypotheses imply this](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [- \*\*Examples and end matter:\*\* printed pp. 132–133, Examples 1–3 give](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [The printed indexing in Theorem 3 is the relevant boundary for the note: the](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [one; this record follows the original printed theorem.](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [- The exact original theorem, its printed indexing, assumptions, conclusion,](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [mixed-sign or unbounded-negative regimes, or any release theorem about](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [The complete scanned article (printed pp. 129–133) was checked for Lean](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [declarations, the release's theorem names, an unrestricted proof of #243, and](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [any claim about the release's #249/#257 results; none occurs. Theorem 3 is](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [the source-aware exposition and its exact Theorem 3 locator.](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [The allowed outward statement is therefore: Erdős–Straus's original Theorem 3](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [plain citation (Ahmes-series terminology)](https://www.renyi.hu/~p_erdos/1964-19.pdf)
- [Theorem 3, p. 132](https://users.renyi.hu/~p_erdos/1964-19.pdf)
- [Historical Ahmes rigidity and the correctly indexed LCM expression.](https://users.renyi.hu/~p_erdos/1964-19.pdf)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1406-L1410) — lines `1406–1410`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4092-L4096) — lines `4092–4096`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3039-L3041) — lines `3039–3041`; excerpt `sha256:7cd258f662728fc8a7ab550dde219bad542c55e2520f19416bf3439de413de29`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4053-L4057) — lines `4053–4057`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L829-L829) — lines `829–829`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L829-L829) — lines `829–829`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L829-L829) — lines `829–829`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2997-L2999) — lines `2997–2999`; excerpt `sha256:7cd258f662728fc8a7ab550dde219bad542c55e2520f19416bf3439de413de29`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L644-L644) — lines `644–644`; excerpt `sha256:135bd438efff4d1cc9eb4aa85885a7a589e44741d435f5882864ba601bb76893`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L30-L32) — lines `30–32`; excerpt `sha256:1139eed2569eedcc245358cbde7bff884c8a36c06c78b0a38246a82257dae3ec`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:983](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L983-L983)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:868](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L868-L868), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2438](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2438-L2439), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2589](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2589-L2589), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3726](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3726-L3726), [cite at paper/reasoning-parts/erdos243/core.tex:829](../../paper/reasoning-parts/erdos243/core.tex#L829-L829), [cite at paper/reasoning-parts/erdos243/core.tex:2399](../../paper/reasoning-parts/erdos243/core.tex#L2399-L2400), [cite at paper/reasoning-parts/erdos243/core.tex:2550](../../paper/reasoning-parts/erdos243/core.tex#L2550-L2550), [cite at paper/reasoning-parts/erdos243/core.tex:3687](../../paper/reasoning-parts/erdos243/core.tex#L3687-L3687)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:686](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L686-L686), [cite at paper/reasoning-parts/erdos251/core.tex:644](../../paper/reasoning-parts/erdos251/core.tex#L644-L644)

<a id="source-source-e535117ac620e6"></a>

### [Log-convex and Stieltjes moment sequences](https://arxiv.org/abs/1612.04114v1)

- Source id: `source-e535117ac620e6`
- Author or public identity: Yi Wang, Bao-Xuan Zhu
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Both Hankel families at all ranks are required. Entrywise positivity and a finite list of leading minors are insufficient.
- Source verification: `source\_verified` — Complete supplied version 1; especially Lemma 2.1, p. 4, coefficientwise Stieltjes definitions in Section 3 and preservation results in Section 4.
- Local mapping: `not recorded`

Exact source locations:

- [Complete supplied version 1; especially Lemma 2.1, p. 4, coefficientwise Stieltjes definitions in Section 3 and preservation results in Section 4.](https://arxiv.org/abs/1612.04114v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1339-L1344) — lines `1339–1344`; excerpt `sha256:878e039506eed9cbdca4b85b0b81b72924aa12144ce61f35980e357fdec8b62e`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5353-L5358) — lines `5353–5358`; excerpt `sha256:f203205a4c16098f6ea390c2eb9ffeedc8e3c1bc649018114be1c761d0cbad7b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5322-L5327) — lines `5322–5327`; excerpt `sha256:f203205a4c16098f6ea390c2eb9ffeedc8e3c1bc649018114be1c761d0cbad7b`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1116](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1116-L1116)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2908](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2908-L2908), [cite at paper/reasoning-parts/erdos1049/core.tex:2877](../../paper/reasoning-parts/erdos1049/core.tex#L2877-L2877)
- `writing-mathematics-from-reviewed-revisions`: [cite at paper/exposition/parts/reading.tex:136](../../paper/exposition/parts/reading.tex#L136-L136)

<a id="source-source-e553241a97e580"></a>

### [Arithmetical investigations of a certain infinite product](https://numdam.org/item/CM_1994__91_2_175_0.pdf)

- Source id: `source-e553241a97e580`
- Author or public identity: P. Bundschuh, K. Väänänen
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Earlier rational-base sufficient region log b/log a \< 1/2 − 1/π² (Theorem 2); 31/4 lies outside it.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- \*\*Reading status:\*\* the complete source was read from its text layer and the rendered pages. The Numdam front matter is PDF page 1; printed pp. 175–199 are PDF pp. 2–26.](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [1. \*\*The infinite product and its series (printed pp. 175–176; PDF pp. 2–3).\*\* For an algebraic number field (K), a place (v), and an element (q) with (|q|\_v\>1) and (|q|\_w1) at every other infinite place, the paper defines](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [2. \*\*Qualitative linear-independence theorem (Theorem 1, printed p. 176; PDF p. 3).\*\* With (=(d h(q))/(d\_v|q|\_v)), (-q^j) for every positive integer (j), and (k3), the dimension over (K) of the span of (E\_q(),E'\_q(),,E\_q^ (k-1) ()) is at least](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [3. \*\*Lambert-type logarithmic derivative (printed p. 177; PDF p. 4).\*\* Logarithmic differentiation gives](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [4. \*\*Quantitative theorem (Theorem 2, printed p. 177; PDF p. 4; proof printed pp. 189–193 / PDF pp. 16–19).\*\* Under the stated hypotheses and (\<3/(2+3^ -2 )), the paper gives an effectively computable lower bound for nonzero linear forms (a\_0E\_q()+a\_1E'\_q()), with the improved (=-1) threshold (\<(1/2+^ -2 )^ -1 ). The bound is an irrationality-measure estimate, not a formalized theorem in this release.](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [5. \*\*The #1049 cited route at (q=7/2) (Theorem 2, printed p. 177; PDF p. 4).\*\* For (K= Q), (q=7/2), and (=-1), the absolute-height parameter is (= 7/(7/2)). The source’s improved threshold is equivalent to](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [- Section 1, printed pp. 179–181 (PDF pp. 5–7), constructs small linear forms using complex or Schnirelman integrals; Lemma 1 gives their asymptotic size.](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [- Section 2, printed pp. 182–188 (PDF pp. 8–14), clears denominators, controls polynomial degrees and valuations, and obtains Lemmas 2–3. Lemma 4 on printed p. 188 (PDF p. 14) is the Nesterenko-style dimension criterion used for Theorem 1.](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [- Section 3, printed pp. 189–193 (PDF pp. 16–19), proves the lower bound for two-term linear forms and hence Theorem 2.](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [- Section 4, printed pp. 193–198 (PDF pp. 20–25), constructs additional linear forms and completes the proof of Theorem 1 on printed pp. 197–198 (PDF pp. 24–25).](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [- The source is the authority for this analytic theorem and its stated hypotheses. No priority or novelty claim is made for the release’s elementary height inequality or for its separately formalized Lean statement.](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [p. 177](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [Thm. 2, p. 177](https://numdam.org/item/CM_1994__91_2_175_0.pdf)
- [Selected full text rechecked in pass 2: printed pp. 175--177, hypotheses and Theorem 2, including page images; conversion from lambda to log(b)/log(a). Not a complete proof audit.](https://numdam.org/item/CM_1994__91_2_175_0.pdf)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1263-L1267) — lines `1263–1267`; excerpt `sha256:e84ccbfd298ca45cdf1dc99cde6fa6c5c320db56fdd37d12d9716a81ae36f325`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5197-L5201) — lines `5197–5201`; excerpt `sha256:e84ccbfd298ca45cdf1dc99cde6fa6c5c320db56fdd37d12d9716a81ae36f325`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5166-L5170) — lines `5166–5170`; excerpt `sha256:e84ccbfd298ca45cdf1dc99cde6fa6c5c320db56fdd37d12d9716a81ae36f325`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:130](../../paper/1049/erdos-1049-rational-base-lambert.tex#L130-L130), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1059](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1059-L1059)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:126](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L126-L126), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:637](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L637-L637), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:847](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L847-L847), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:875](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L875-L875), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1161](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1161-L1161), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4057](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4057-L4057), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5039](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5039-L5039), [cite at paper/reasoning-parts/erdos1049/core.tex:95](../../paper/reasoning-parts/erdos1049/core.tex#L95-L95), [cite at paper/reasoning-parts/erdos1049/core.tex:606](../../paper/reasoning-parts/erdos1049/core.tex#L606-L606), [cite at paper/reasoning-parts/erdos1049/core.tex:816](../../paper/reasoning-parts/erdos1049/core.tex#L816-L816), [cite at paper/reasoning-parts/erdos1049/core.tex:844](../../paper/reasoning-parts/erdos1049/core.tex#L844-L844), [cite at paper/reasoning-parts/erdos1049/core.tex:1130](../../paper/reasoning-parts/erdos1049/core.tex#L1130-L1130), [cite at paper/reasoning-parts/erdos1049/core.tex:4026](../../paper/reasoning-parts/erdos1049/core.tex#L4026-L4026), [cite at paper/reasoning-parts/erdos1049/core.tex:5008](../../paper/reasoning-parts/erdos1049/core.tex#L5008-L5008)

<a id="source-source-e5f2924d82c59f"></a>

### [New irrationality measures for q-logarithms](https://doi.org/10.1090/S0025-5718-05-01812-0)

- Source id: `source-e5f2924d82c59f`
- Author or public identity: T. Matala-aho, K. Väänänen, W. Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Irrationality measures for q-logarithms at integer bases, cited for the neighbouring q-logarithm case.
- Source verification: `source\_verified` — The cited passages (abstract p. 879; introduction p. 880) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [abstract p. 879; introduction p. 880](https://doi.org/10.1090/S0025-5718-05-01812-0)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://doi.org/10.1090/S0025-5718-05-01812-0)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5250-L5257) — lines `5250–5257`; excerpt `sha256:ca3ad143147a5d2804f66fa9a2b445b365c705a19273a1ae8c77f2c257c09062`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5219-L5226) — lines `5219–5226`; excerpt `sha256:ca3ad143147a5d2804f66fa9a2b445b365c705a19273a1ae8c77f2c257c09062`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5032-L5032) — lines `5032–5032`; excerpt `sha256:a9816f01cbbbed3606bb3c7105e1f1bc81607266eee3e3bc860ed90c8624c684`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5063](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5063-L5063), [cite at paper/reasoning-parts/erdos1049/core.tex:5032](../../paper/reasoning-parts/erdos1049/core.tex#L5032-L5032)

<a id="source-source-e66e0693f05f0a"></a>

### [On the largest prime factor of n!+2^n−1](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.524.pdf)

- Source id: `source-e66e0693f05f0a`
- Author or public identity: Florian Luca, Igor E. Shparlinski
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Attached full text and publisher page images: §§1–2, Lemmas 2.1–2.3, pp. 860–862, and opening of §3 including (3.2), p. 863. Later global estimates not independently audited.
- Local mapping: `not recorded`

Exact source locations:

- [Attached full text and publisher page images: §§1–2, Lemmas 2.1–2.3, pp. 860–862, and opening of §3 including (3.2), p. 863. Later global estimates not independently audited.](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.524.pdf)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3188-L3192) — lines `3188–3192`; excerpt `sha256:301c9e11ac561f9aaaabc33c46f271f3f0cecc122a99db652c476daecd2fda2a`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3223-L3227) — lines `3223–3227`; excerpt `sha256:301c9e11ac561f9aaaabc33c46f271f3f0cecc122a99db652c476daecd2fda2a`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3188-L3192) — lines `3188–3192`; excerpt `sha256:301c9e11ac561f9aaaabc33c46f271f3f0cecc122a99db652c476daecd2fda2a`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1143](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1143-L1143), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1145](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1145-L1145), [cite at paper/reasoning-parts/erdos68/core.tex:1108](../../paper/reasoning-parts/erdos68/core.tex#L1108-L1108), [cite at paper/reasoning-parts/erdos68/core.tex:1110](../../paper/reasoning-parts/erdos68/core.tex#L1110-L1110)

<a id="source-source-e6716218a1ac07"></a>

### [National Institute of Standards and Technology](https://csrc.nist.gov/projects/hash-functions)

- Source id: `source-e6716218a1ac07`
- Author or public identity: National Institute of Standards, Technology
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1356-L1361) — lines `1356–1361`; excerpt `sha256:8f4293a0a02295b79306f2dd39994ae87fe5e3c104ae2b67eeec226a473b145e`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:605](../../docs/papers/mirror/plectis-public-system.tex#L605-L605)

<a id="source-source-e7f2f796dbcdb6"></a>

### [A new proof of Nishioka's theorem in Mahler's method](https://comptes-rendus.academie-sciences.fr/mathematique/articles/10.5802/crmath.458/)

- Source id: `source-e7f2f796dbcdb6`
- Author or public identity: Boris Adamczewski, Colin Faverjon
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Accessible one-variable value/lifting theorem interface; explicitly credit Nishioka for the earlier theorem.
- Source verification: `source\_verified` — Journal metadata, introductory definitions, Theorems 1 and 2 and attribution on pp. 1011--1012; not a complete proof audit.
- Local mapping: `not recorded`

Exact source locations:

- [Theorems 1 and 2, p. 1012; functional system and regular-point definition, pp. 1011--1012](https://comptes-rendus.academie-sciences.fr/mathematique/articles/10.5802/crmath.458/)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4517-L4521) — lines `4517–4521`; excerpt `sha256:66c2a5257f58be1672dd0343ef38da2c5d2f46e01935b51c3b7cec7dcf17b0ea`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4459-L4463) — lines `4459–4463`; excerpt `sha256:66c2a5257f58be1672dd0343ef38da2c5d2f46e01935b51c3b7cec7dcf17b0ea`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3648](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3648-L3648), [cite at paper/reasoning-parts/erdos269/core.tex:3590](../../paper/reasoning-parts/erdos269/core.tex#L3590-L3590)

<a id="source-source-e99ce64694b554"></a>

### [AI contributions to Erdős problems](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems)

- Source id: `source-e99ce64694b554`
- Author or public identity: Terence Tao
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by both public systems papers as the existing public, hand-edited community register of AI contributions to the Erdős problems; the contribution protocol is meant to feed it with returns that carry evidence class, roles, and a checkable boundary.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1732-L1737) — lines `1732–1737`; excerpt `sha256:4fa78969a75193c23aeb06cdd0323df94e0a5887673d1bf5c44d740748d12774`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1197-L1201) — lines `1197–1201`; excerpt `sha256:fea9fc446cc883ee74a3abe2b9d747aa1da68232d0315a8d8bef6e40e8b574ed`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1051](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1051-L1051)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:1097](../../paper/systems/open-source-mathematics-strategy.tex#L1097-L1097)

<a id="source-source-eaeb7980382323"></a>

### [Mahler's method in several variables and finite automata](https://annals.math.princeton.edu/2026/204-2/p01)

- Source id: `source-eaeb7980382323`
- Author or public identity: Boris Adamczewski, Colin Faverjon
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Multivariate analytic route: requires a Mahler system, regular evaluation and admissible transformation-point data.
- Source verification: `source\_verified` — Official journal metadata checked; author manuscript sections defining the systems and assumptions read. Older 52-page arXiv v1 has different numbering; journal proof text not independently obtained.
- Local mapping: `not recorded`

Exact source locations:

- [Author revised 68-page manuscript: Sections 3 and 5, Definition 3.2, Theorem 3.3, Corollary 3.5](https://annals.math.princeton.edu/2026/204-2/p01)

Public implementation or evidence coordinates:

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1089-L1095) — lines `1089–1095`; excerpt `sha256:f0b413584f891c1a725c23699a9efae2e7cbaba89e97347422243d21325f0020`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4521-L4527) — lines `4521–4527`; excerpt `sha256:f0b413584f891c1a725c23699a9efae2e7cbaba89e97347422243d21325f0020`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4463-L4469) — lines `4463–4469`; excerpt `sha256:f0b413584f891c1a725c23699a9efae2e7cbaba89e97347422243d21325f0020`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1001](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1001-L1001)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3651](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3651-L3651), [cite at paper/reasoning-parts/erdos269/core.tex:3593](../../paper/reasoning-parts/erdos269/core.tex#L3593-L3593)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1952](../../paper/synthesis/optimal-sparse-perturbations.tex#L1952-L1952)

<a id="source-source-eca9e699590922"></a>

### [On the binary digits of the Erdős--Borwein constant](https://arxiv.org/abs/2605.24160v1)

- Source id: `source-eca9e699590922`
- Author or public identity: J. M. Campbell
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Proof (Theorem 1) that the block 11 occurs infinitely often in the binary expansion of the constant, answering Crandall's question.
- Source verification: `source\_verified` — The cited passages (Theorem 1, p. 12) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 1, p. 12](https://arxiv.org/abs/2605.24160v1)
- [Theorem 1, p. 12 (v1), as recorded in the supplied long paper.](https://arxiv.org/pdf/2605.24160v1)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5406-L5412) — lines `5406–5412`; excerpt `sha256:cdaff80cd6c7f5f1646ee2c7a858ab106e0225c3e87b92ca3df2858826a27e1e`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L976-L976) — lines `976–976`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [lean/Erdos249257/CampbellShiftSynchronization.lean](../../lean/Erdos249257/CampbellShiftSynchronization.lean#L4-L22) — lines `4–22`; excerpt `sha256:d517c238bb94dca26752a32c4273074633c39a9b8af3551e069cb7a282081388`
- [lean/Erdos249257/CampbellShiftSynchronization.lean](../../lean/Erdos249257/CampbellShiftSynchronization.lean#L294-L299) — lines `294–299`; excerpt `sha256:a33a451732d6d625372bccee6302e08dfdb1ec94ea88b2bb9013d5eff55197d4`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9682-L9688) — lines `9682–9688`; excerpt `sha256:a764b921cc13bcb1cc2ca1ce687e7493ad39d0ad55326278645b6b44ec94cfdc`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9482-L9488) — lines `9482–9488`; excerpt `sha256:a764b921cc13bcb1cc2ca1ce687e7493ad39d0ad55326278645b6b44ec94cfdc`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2242](../../paper/archive/erdos249-257-main-paper.tex#L2242-L2243)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1484](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1484-L1484), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1284](../../paper/reasoning-parts/erdos257/a257_front.tex#L1284-L1284)

<a id="source-source-ee991edd431d57"></a>

### [Erdős #243: working report](https://erdosproblemaday.com/report/243)

- Source id: `source-ee991edd431d57`
- Author or public identity: P. White with Claude (Anthropic)
- Kind: `website\_contribution`
- Problems: #243
- Relationship and boundary: Dated public working report of 12 August 2026 carrying the same finite-negative-mass criterion in pseudo-greedy coordinates and the flat-transient construction.
- Source verification: `source\_verified` — The cited passages ("A global termination criterion"; "Flat-transient theorem") were checked against the downloaded copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- ["A global termination criterion"](https://erdosproblemaday.com/report/243)
- ["Flat-transient theorem"](https://erdosproblemaday.com/report/243)
- [Dated AI-assisted working-report comparison.](https://erdosproblemaday.com/report/243)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1437-L1441) — lines `1437–1441`; excerpt `sha256:40aecd254891fc812f0e8980ec61fe681a524880f510bb6cfc26f94b02d1b732`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4130-L4134) — lines `4130–4134`; excerpt `sha256:40aecd254891fc812f0e8980ec61fe681a524880f510bb6cfc26f94b02d1b732`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4091-L4095) — lines `4091–4095`; excerpt `sha256:40aecd254891fc812f0e8980ec61fe681a524880f510bb6cfc26f94b02d1b732`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:779](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L779-L779)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2712](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2712-L2712), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3263](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3263-L3263), [cite at paper/reasoning-parts/erdos243/core.tex:2673](../../paper/reasoning-parts/erdos243/core.tex#L2673-L2673), [cite at paper/reasoning-parts/erdos243/core.tex:3224](../../paper/reasoning-parts/erdos243/core.tex#L3224-L3224)

<a id="source-source-eeff3fa685af8a"></a>

### [Uber die asymptotische Verteilung reeller Zahlen mod 1](https://doi.org/10.1007/BF01181156)

- Source id: `source-eeff3fa685af8a`
- Author or public identity: I. Schoenberg
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Primary source for the continuous limiting distribution of phi(n)/n used by the bad-cofactor budget.
- Source verification: `source\_verified` — The cited passages (Section 17, p. 193) were checked against the journal scan copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Section 17, p. 193](https://doi.org/10.1007/BF01181156)
- [Distribution of totient ratios, not fine dyadic phase anti-concentration.](https://doi.org/10.1007/BF01181156)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10348-L10353) — lines `10348–10353`; excerpt `sha256:32599e7a2120d5129deed6138e89e7ebef17cd091f20f82776fde8449312e5ca`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10156-L10161) — lines `10156–10161`; excerpt `sha256:32599e7a2120d5129deed6138e89e7ebef17cd091f20f82776fde8449312e5ca`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8284](../../paper/249/erdos249-totient-reasoning-surface.tex#L8284-L8284), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8092](../../paper/reasoning-parts/erdos249/a249_front.tex#L8092-L8092)

<a id="source-source-ef6233b59b95cb"></a>

### [Rational numbers with odd greedy expansion of fixed length](https://arxiv.org/abs/2309.07280)

- Source id: `source-ef6233b59b95cb`
- Author or public identity: J. Louwsma, J. Martino
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Reciprocal-sum valuation formula (Lemma 4.1, p. 10); the maximal prime-power survival test is its top valuation layer.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Lemma 4.1, printed/PDF p. 10: for positive integers x\_1,…,x\_m and prime p, gives the exact p-adic valuation formula for σ\_{m−1}(x\_1,…,x\_m) in terms of v\_p(x\_1⋯x\_m), W\_p=max\_i v\_p(x\_i), and the normalized residual sum.](https://arxiv.org/abs/2309.07280)
- [Proof of Lemma 4.1, printed/PDF p. 10: factors the common p-power from the elementary-symmetric-polynomial sum to obtain the valuation identity.](https://arxiv.org/abs/2309.07280)
- [Lemma 4.1, p. 10](https://arxiv.org/abs/2309.07280v1)
- [Primary arXiv PDF: Lemma 4.1 and its proof read; page image checked. The current survival criterion is its finite reciprocal-sum specialisation.](https://arxiv.org/abs/2309.07280v1)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3128-L3132) — lines `3128–3132`; excerpt `sha256:56545f01462da2d6bd59af54b4c105a4e78489461a9719ab3c6db971299941ef`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3163-L3167) — lines `3163–3167`; excerpt `sha256:56545f01462da2d6bd59af54b4c105a4e78489461a9719ab3c6db971299941ef`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3128-L3132) — lines `3128–3132`; excerpt `sha256:56545f01462da2d6bd59af54b4c105a4e78489461a9719ab3c6db971299941ef`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L813-L813) — lines `813–813`; excerpt `sha256:7a549791ed341c1373f0b0c9b40e13b147f3aa3b9484ded64b1ef2f2a94aefa9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L813-L813) — lines `813–813`; excerpt `sha256:7a549791ed341c1373f0b0c9b40e13b147f3aa3b9484ded64b1ef2f2a94aefa9`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:848](../../paper/68/erdos68-factorial-reasoning-surface.tex#L848-L848), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2327](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2327-L2327), [cite at paper/reasoning-parts/erdos68/core.tex:813](../../paper/reasoning-parts/erdos68/core.tex#L813-L813), [cite at paper/reasoning-parts/erdos68/core.tex:2292](../../paper/reasoning-parts/erdos68/core.tex#L2292-L2292)

<a id="source-source-endpoint2026-logarithmic-repair"></a>

### The logarithmic endpoint fails under arithmetic sampling

- Source id: `source-endpoint2026-logarithmic-repair`
- Author or public identity: Plectis working note
- Kind: `literature`
- Problems: #257
- Relationship and boundary: AI-assisted ordinary proof note dated 17 September 2026 (not published). Its Theorem 1, Corollary 3 and Proposition 4 are the source of the finite-functional arithmetic counterexample, cover-cost separation, and initial-interval bound in the #257 papers, which give the proofs in full and state this origin. Independent review and fresh Lean verification are outstanding.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L858-L858) — lines `858–858`; excerpt `sha256:2b4bc5fe17fd8e238debc2df722a5d5ae84b5416fb38720f4a94b13b2f06e216`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9202-L9202) — lines `9202–9202`; excerpt `sha256:ec7c5a5f4b94d4c2488e3f5a57b5af9b264fc4f248b588252be6eb05d0e88fe2`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9002-L9002) — lines `9002–9002`; excerpt `sha256:ec7c5a5f4b94d4c2488e3f5a57b5af9b264fc4f248b588252be6eb05d0e88fe2`

<a id="source-source-evertse-ferretti-2013-author2012"></a>

### [A further improvement of the quantitative Subspace Theorem](https://pub.math.leidenuniv.nl/~evertsejh/10-subspace.pdf)

- Source id: `source-evertse-ferretti-2013-author2012`
- Author or public identity: Jan-Hendrik Evertse, Roberto Ferretti
- Kind: `literature`
- Problems: #257, #1049
- Relationship and boundary: The normalized number-field Subspace Theorem and product-formula height conventions supply the external theorem for the separated-cut proof. The new conjugate estimates and hyperplane exclusion are local ordinary arguments; qualitative finiteness only is used.
- Source verification: `source\_verified` — The named primary passage and the stated local use were checked on 29 September 2026; not a full-paper review or novelty judgment.
- Local mapping: `exact\_bibliographic\_use` — Round8 manuscript transfer; ordinary proof and citation authority remain separate.

Exact source locations:

- [Author version dated 3 May 2012, section1.1 equation(1.1) and section2.1.](https://pub.math.leidenuniv.nl/~evertsejh/10-subspace.pdf)

Public implementation or evidence coordinates:

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2308-L2314) — lines `2308–2314`; excerpt `sha256:47977a6056cdfc3896fa8809315451f7388750fbf3c2c4dc8cecc22c8db23ce3`
- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L1348-L1348) — lines `1348–1348`; excerpt `sha256:96ba3449869250ee797a74c61af26bb684a11fdafa259cc3adebbfc6c0c854c7`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1348](../../paper/synthesis/optimal-sparse-perturbations.tex#L1348-L1348)

<a id="source-source-f0af8e6f36727f"></a>

### [Four-point distortion theorem for complex polynomials](https://arxiv.org/abs/1301.3985v1)

- Source id: `source-f0af8e6f36727f`
- Author or public identity: Vladimir N. Dubinin
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 1 p. 2](https://arxiv.org/abs/1301.3985v1)
- [Proof pp. 3–4](https://arxiv.org/abs/1301.3985v1)
- [Corollary 4 pp. 5–6](https://arxiv.org/abs/1301.3985v1)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1246-L1249) — lines `1246–1249`; excerpt `sha256:a2ea0b0d9fe464fd26b77c94c6b482f3c945b98a5fd53c85d7624d1728340989`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5497-L5500) — lines `5497–5500`; excerpt `sha256:a2ea0b0d9fe464fd26b77c94c6b482f3c945b98a5fd53c85d7624d1728340989`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5447-L5450) — lines `5447–5450`; excerpt `sha256:a2ea0b0d9fe464fd26b77c94c6b482f3c945b98a5fd53c85d7624d1728340989`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1130](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1130-L1130)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:5130](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5130-L5130), [cite at paper/reasoning-parts/erdos1041/core.tex:5080](../../paper/reasoning-parts/erdos1041/core.tex#L5080-L5080)

<a id="source-source-f1a42898642b5f"></a>

### [Additive congruences with factorials modulo a prime](https://arxiv.org/html/2508.12127v1)

- Source id: `source-f1a42898642b5f`
- Author or public identity: Moubariz Z. Garaev, Julio C. Pardo
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Full-text introduction and Theorems 1.1–1.3 read in arXiv HTML. The global representation/value-set role is all that is used. Journal metadata corroborated by AMS indexed publisher PDF; direct fetch returned 403.
- Local mapping: `not recorded`

Exact source locations:

- [Full-text introduction and Theorems 1.1–1.3 read in arXiv HTML. The global representation/value-set role is all that is used. Journal metadata corroborated by AMS indexed publisher PDF; direct fetch returned 403.](https://arxiv.org/html/2508.12127v1)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3239-L3243) — lines `3239–3243`; excerpt `sha256:9840d0a92d94f920800cfb600e645cca774371293151ecea13c66a6cce76d3c8`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3204-L3208) — lines `3204–3208`; excerpt `sha256:9840d0a92d94f920800cfb600e645cca774371293151ecea13c66a6cce76d3c8`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1983](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1983-L1983), [cite at paper/reasoning-parts/erdos68/core.tex:1948](../../paper/reasoning-parts/erdos68/core.tex#L1948-L1948)

<a id="source-source-f1c687cb5e9ae4"></a>

### [Remarks on irrationality of q-harmonic series](https://doi.org/10.1007/s002290200249)

- Source id: `source-f1c687cb5e9ae4`
- Author or public identity: W. Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Reciprocal-interval, summatory-totient and trigamma argument (proof of Lemma 1, p. 466) used in the papers' proofs of the cyclotomic limits.
- Source verification: `source\_verified` — The cited passages (Lemma 1, p. 466; Lemma 1, p. 466) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Lemma 1, p. 466](https://doi.org/10.1007/s002290200249)
- [Lemma 1, p. 466](https://doi.org/10.1007/s002290200249)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://doi.org/10.1007/s002290200249)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1267-L1271) — lines `1267–1271`; excerpt `sha256:985c11e75c32024f7b85ea003ea9eddbd077703fea826834a3b574b6cc2d115c`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5201-L5205) — lines `5201–5205`; excerpt `sha256:985c11e75c32024f7b85ea003ea9eddbd077703fea826834a3b574b6cc2d115c`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5170-L5174) — lines `5170–5174`; excerpt `sha256:985c11e75c32024f7b85ea003ea9eddbd077703fea826834a3b574b6cc2d115c`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:872](../../paper/1049/erdos-1049-rational-base-lambert.tex#L872-L872)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:285](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L285-L285), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:509](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L509-L509), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:5110](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5110-L5110), [cite at paper/reasoning-parts/erdos1049/core.tex:254](../../paper/reasoning-parts/erdos1049/core.tex#L254-L254), [cite at paper/reasoning-parts/erdos1049/core.tex:478](../../paper/reasoning-parts/erdos1049/core.tex#L478-L478), [cite at paper/reasoning-parts/erdos1049/core.tex:5079](../../paper/reasoning-parts/erdos1049/core.tex#L5079-L5079)

<a id="source-source-f213b302ada43a"></a>

### [NIST Digital Library of Mathematical Functions, §1.12(ii) Convergents](https://dlmf.nist.gov/1.12)

- Source id: `source-f213b302ada43a`
- Author or public identity: Unknown
- Kind: `website\_contribution`
- Problems: #68
- Relationship and boundary: Standard continued-fraction recurrences, determinant identity and prefix transformation used to turn the common prefix into the denominator bound; the numerical outputs are the project's computation.
- Source verification: `source\_verified` — The cited passages (§1.12(ii), (1.12.5)-(1.12.7), (1.12.20)-(1.12.21); §1.12(ii), (1.12.5)-(1.12.7), (1.12.20)-(1.12.21)) were checked against the downloaded copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [§1.12(ii), (1.12.5)-(1.12.7), (1.12.20)-(1.12.21)](https://dlmf.nist.gov/1.12)
- [§1.12(ii), (1.12.5)-(1.12.7), (1.12.20)-(1.12.21)](https://dlmf.nist.gov/1.12)
- [§1.12(ii), convergent recurrences, determinant and fractional transformation, equations (1.12.5)–(1.12.7), (1.12.20)–(1.12.21). Page accessed 16 September 2026.](https://dlmf.nist.gov/1.12)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3180-L3184) — lines `3180–3184`; excerpt `sha256:d0240691fa5956d3f42d0e151a25cfaa8d0a16e7b1cc510ba6b9ef168ed084dc`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3215-L3219) — lines `3215–3219`; excerpt `sha256:d0240691fa5956d3f42d0e151a25cfaa8d0a16e7b1cc510ba6b9ef168ed084dc`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3180-L3184) — lines `3180–3184`; excerpt `sha256:d0240691fa5956d3f42d0e151a25cfaa8d0a16e7b1cc510ba6b9ef168ed084dc`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1926](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1926-L1926), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1955](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1955-L1955), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2330](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2330-L2330), [cite at paper/reasoning-parts/erdos68/core.tex:1891](../../paper/reasoning-parts/erdos68/core.tex#L1891-L1891), [cite at paper/reasoning-parts/erdos68/core.tex:1920](../../paper/reasoning-parts/erdos68/core.tex#L1920-L1920), [cite at paper/reasoning-parts/erdos68/core.tex:2295](../../paper/reasoning-parts/erdos68/core.tex#L2295-L2295)

<a id="source-source-f2a047037bae55"></a>

### [Reproducibility Badging and Definitions](https://doi.org/10.3789/niso-rp-31-2021)

- Source id: `source-f2a047037bae55`
- Author or public identity: National Information Standards Organization.
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1340-L1346) — lines `1340–1346`; excerpt `sha256:afa42db0c4dfb2114be595de4a2efc8acb377b5e1bb8f446e52f2791f475b1eb`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:434](../../docs/papers/mirror/plectis-public-system.tex#L434-L434)

<a id="source-source-f300911fb03a5c"></a>

### [A Short Path Joining Two Zeros Inside a Polynomial Lemniscate](https://shtuka123.github.io/1041/main.pdf)

- Source id: `source-f300911fb03a5c`
- Author or public identity: shtuka
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Manuscript on the unrestricted problem whose Proposition 12 tree budget the papers refute with the Cassini example.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1167-L1171) — lines `1167–1171`; excerpt `sha256:372ad8d3f82ff0212ee04c7dd5a7269a56a5c9a52cae45f7d05245ccae260a87`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5428-L5437) — lines `5428–5437`; excerpt `sha256:72a88e5a23c5730b248edc8d8bc104d1818c8c71ea25dbdd60a7c6074bb79d61`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5378-L5387) — lines `5378–5387`; excerpt `sha256:72a88e5a23c5730b248edc8d8bc104d1818c8c71ea25dbdd60a7c6074bb79d61`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4348-L4348) — lines `4348–4348`; excerpt `sha256:636651adc41018ae6f90faa70e4010583deaa28671fcc1c916acccd02f62d5c8`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4348-L4348) — lines `4348–4348`; excerpt `sha256:636651adc41018ae6f90faa70e4010583deaa28671fcc1c916acccd02f62d5c8`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1066](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1066-L1066)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4395](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4395-L4395), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4398](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4398-L4398), [cite at paper/reasoning-parts/erdos1041/core.tex:4345](../../paper/reasoning-parts/erdos1041/core.tex#L4345-L4345), [cite at paper/reasoning-parts/erdos1041/core.tex:4348](../../paper/reasoning-parts/erdos1041/core.tex#L4348-L4348)

<a id="source-source-f42f9e04743a4c"></a>

### [A conditional proof of the irrationality of ∑\_{n≥1} p\_n 2^{−n} under a uniform Hardy–Littlewood prime-tuples conjecture](https://github.com/beetree/math_erdos_251)

- Source id: `source-f42f9e04743a4c`
- Author or public identity: J. Land
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Public research draft of 5 September 2026 proving irrationality under Kuperberg's conjecture.
- Source verification: `source\_verified` — The cited passages (Theorem 2; Conjecture 1 and Theorem 2) were checked against the research draft dated 5 September 2026 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 2](https://github.com/beetree/math_erdos_251)
- [Conjecture 1 and Theorem 2](https://github.com/beetree/math_erdos_251)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3053-L3055) — lines `3053–3055`; excerpt `sha256:82eaf36e749d94b9bc85e72cb6decbd8b7ce392b18e1edb0f50d7c491ba8f4cf`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3011-L3013) — lines `3011–3013`; excerpt `sha256:82eaf36e749d94b9bc85e72cb6decbd8b7ce392b18e1edb0f50d7c491ba8f4cf`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L446-L446) — lines `446–446`; excerpt `sha256:160a2b014966aaf70cba2fb38dd6be86a729335f10185109e6e77f49fbcedee2`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2069-L2069) — lines `2069–2069`; excerpt `sha256:ad49b5aa94a8d9963ee6dcb001d2d84dc32e0776315128832b860e41fd3a9cf0`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L822-L824) — lines `822–824`; excerpt `sha256:82eaf36e749d94b9bc85e72cb6decbd8b7ce392b18e1edb0f50d7c491ba8f4cf`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:486](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L486-L486)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:488](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L488-L488), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2112](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2112-L2112), [cite at paper/reasoning-parts/erdos251/core.tex:446](../../paper/reasoning-parts/erdos251/core.tex#L446-L446), [cite at paper/reasoning-parts/erdos251/core.tex:2070](../../paper/reasoning-parts/erdos251/core.tex#L2070-L2070)

<a id="source-source-f4ad17717c8fd4"></a>

### [Sparse Polynomial-Weighted Expansions](https://arxiv.org/abs/2606.24972v4)

- Source id: `source-f4ad17717c8fd4`
- Author or public identity: Han Wang
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: The archival joint manuscript cites an earlier version under the title Positive dyadic density for rational weighted binary expansions. The tracked source closure verifies version 4, Sparse Polynomial-Weighted Expansions, by Han Wang alone; its polynomial-weighted expansion theorem is not a result about Erdős #249 or #257.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- Printed p. 1 gives the title, sole author “HAN WANG”, arXiv version/date,](https://arxiv.org/abs/2606.24972v4)
- [consequence of this source's theorem, not as a result about Erdős #249 or](https://arxiv.org/abs/2606.24972v4)
- [- Printed p. 2, Theorem 1.1 (“Polynomial-window density”), states that for an](https://arxiv.org/abs/2606.24972v4)
- [- Printed p. 3, Corollary 1.2 (“Density and gaps”), states the positive lower](https://arxiv.org/abs/2606.24972v4)
- [sparse-support consequence. Printed p. 3, Lemma 2.1 (“Carries and gaps”),](https://arxiv.org/abs/2606.24972v4)
- [- Printed p. 5, Lemma 2.4 (“Polynomial locking”), gives the rational polynomial](https://arxiv.org/abs/2606.24972v4)
- [Printed p. 5, its proof records the determinant/divisibility step used to](https://arxiv.org/abs/2606.24972v4)
- [- Printed p. 6, equation (7), gives the normalized leading-coefficient map](https://arxiv.org/abs/2606.24972v4)
- [\`mu -\> b^g mu - 1\`; Lemma 2.5 gives the interior/exterior dichotomy and the](https://arxiv.org/abs/2606.24972v4)
- [at-most-one interior successor-gap statement. Printed p. 6, Proposition 3.1](https://arxiv.org/abs/2606.24972v4)
- [- Printed p. 10, the proof of Theorem 1.1 combines the preceding estimates and](https://arxiv.org/abs/2606.24972v4)
- [lines 162–183 contain the source theorem corresponding to printed p. 2,](https://arxiv.org/abs/2606.24972v4)
- [- The printed p. 1 classification and keywords identify the source as Erdős](https://arxiv.org/abs/2606.24972v4)
- [#249 or #257 as a target. The printed p. 2 Theorem 1.1 is conditional on](https://arxiv.org/abs/2606.24972v4)
- [- Printed p. 3, Corollary 1.2 records the source's binary-linear consequence](https://arxiv.org/abs/2606.24972v4)
- [series of #249 or all infinite-support subseries of #257. Printed pp. 5–10](https://arxiv.org/abs/2606.24972v4)
- [theorem to those problems.](https://arxiv.org/abs/2606.24972v4)
- [- The source's final disclosure on printed p. 10 describes AI assistance and](https://arxiv.org/abs/2606.24972v4)
- [a formalisation commit for this source's theorem. It contains no peer-review,](https://arxiv.org/abs/2606.24972v4)
- [boundary, not unresolved implications of its theorem.](https://arxiv.org/abs/2606.24972v4)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5392-L5397) — lines `5392–5397`; excerpt `sha256:4caf7a23e043524edc0b28f6c56ff51ffc65fbd8e9bcea766fda7d8bd0b07263`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:912](../../paper/archive/erdos249-257-main-paper.tex#L912-L912), [cite at paper/archive/erdos249-257-main-paper.tex:4671](../../paper/archive/erdos249-257-main-paper.tex#L4671-L4671), [cite at paper/archive/erdos249-257-main-paper.tex:4706](../../paper/archive/erdos249-257-main-paper.tex#L4706-L4706)

<a id="source-source-f67bf9959aa230"></a>

### [A determinantal approach to irrationality](https://doi.org/10.1007/s00365-016-9333-7)

- Source id: `source-f67bf9959aa230`
- Author or public identity: W. Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Reference for Heine's expansion of a Hankel determinant of moments (Section 2, (2)–(5)).
- Source verification: `source\_verified` — The cited passages (Sec. 2, (2)--(5), pp. 2--3; Sec. 2, (2)--(5), pp. 2--3) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Sec. 2, (2)--(5), pp. 2--3](https://doi.org/10.1007/s00365-016-9333-7)
- [Sec. 2, (2)--(5), pp. 2--3](https://doi.org/10.1007/s00365-016-9333-7)
- [Full text consulted, especially Section 2, (2)--(5), pp. 2--3 and the arithmetic criterion.](https://doi.org/10.1007/s00365-016-9333-7)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1293-L1298) — lines `1293–1298`; excerpt `sha256:76708e9e1ba9cb5b881eb2f319d5a6bf94dc5132c846fc6c1ebd51aef0fb72d4`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5222-L5227) — lines `5222–5227`; excerpt `sha256:6e2271ffb0543bc3fdc177f643ec7c22e54002e1c42ef7828bffd0cf406d75df`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5191-L5196) — lines `5191–5196`; excerpt `sha256:6e2271ffb0543bc3fdc177f643ec7c22e54002e1c42ef7828bffd0cf406d75df`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:93](../../paper/1049/erdos-1049-rational-base-lambert.tex#L93-L93)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1757](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1757-L1757), [cite at paper/reasoning-parts/erdos1049/core.tex:1726](../../paper/reasoning-parts/erdos1049/core.tex#L1726-L1726)

<a id="source-source-f6e839bcb8a60f"></a>

### [Secure Hash Standard](https://doi.org/10.6028/NIST.FIPS.180-4)

- Source id: `source-f6e839bcb8a60f`
- Author or public identity: National Institute of Standards and Technology
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1351-L1356) — lines `1351–1356`; excerpt `sha256:53b40a353a433ace78f48f685ef15ac1819dc844bcf364ec37ff3b127cdfeaba`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:596](../../docs/papers/mirror/plectis-public-system.tex#L596-L596), [cite at docs/papers/mirror/plectis-public-system.tex:599](../../docs/papers/mirror/plectis-public-system.tex#L599-L599), [cite at docs/papers/mirror/plectis-public-system.tex:616](../../docs/papers/mirror/plectis-public-system.tex#L616-L616)

<a id="source-source-f6ee6890db85d9"></a>

### [Linear independence of certain Lambert series](https://doi.org/10.1090/S0002-9939-2014-12102-2)

- Source id: `source-f6ee6890db85d9`
- Author or public identity: Florian Luca, Yohei Tachiya
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Original antecedent to the later Chowla--Erdos refinement.
- Source verification: `source\_verified` — Original metadata checked on author publication list and in Duverney--Tachiya 2019 references; AMS full text unavailable.
- Local mapping: `not recorded`

Exact source locations:

- [Luca author publication list, 2014](https://doi.org/10.1090/S0002-9939-2014-12102-2)
- [Duverney--Tachiya 2019, reference 10](https://doi.org/10.1090/S0002-9939-2014-12102-2)

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1693-L1699) — lines `1693–1699`; excerpt `sha256:6c20454741356816e2d6d22e0fde01df4c611d7435ed3814f610e86ef368a80d`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9707-L9713) — lines `9707–9713`; excerpt `sha256:6c20454741356816e2d6d22e0fde01df4c611d7435ed3814f610e86ef368a80d`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9507-L9513) — lines `9507–9513`; excerpt `sha256:6c20454741356816e2d6d22e0fde01df4c611d7435ed3814f610e86ef368a80d`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1010](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1010-L1010)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9540](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9540-L9540), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9340](../../paper/reasoning-parts/erdos257/a257_front.tex#L9340-L9340)

<a id="source-source-f9fd9214c9ef11"></a>

### [Rational approximations to a q-analogue of π and some other q-series](https://doi.org/10.1007/978-3-211-74280-8_6)

- Source id: `source-f9fd9214c9ef11`
- Author or public identity: P. Bundschuh, W. Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Padé-type approximations underlying Zudilin's 2016 Hankel determinant.
- Source verification: `source\_verified` — The cited passages ((no locator; credited through Zudilin 2016 Sec. 2, p. 3)) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [(no locator; credited through Zudilin 2016 Sec. 2, p. 3)](https://doi.org/10.1007/978-3-211-74280-8_6)
- [Retained from the supplied manuscript; not newly represented as a full-text audit in this pass.](https://doi.org/10.1007/978-3-211-74280-8_6)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5231-L5236) — lines `5231–5236`; excerpt `sha256:bd1db09a836b7bae7294afc1da1a7ae1ba135a083600d289e0dd8b45d24c10e4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5200-L5205) — lines `5200–5205`; excerpt `sha256:bd1db09a836b7bae7294afc1da1a7ae1ba135a083600d289e0dd8b45d24c10e4`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1462](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1462-L1462), [cite at paper/reasoning-parts/erdos1049/core.tex:1431](../../paper/reasoning-parts/erdos1049/core.tex#L1431-L1431)

<a id="source-source-fb4194cadb150b"></a>

### [Generalized bases for the real numbers](https://www.fq.math.ca/Scanned/4-3/fridy.pdf)

- Source id: `source-fb4194cadb150b`
- Author or public identity: J. A. Fridy
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Variable-digit interval filling (Lemma, p. 194) behind the covering step; its overlap condition is the inequality the papers prove directly, without Fridy's monotone weights.
- Source verification: `source\_verified` — The cited passages (Lemma, p. 194 (twice: related work and the sparse proof); Lemma, p. 194 (related work and the interval-retention step)) were checked against the journal scan with OCR layer (Fibonacci Quart. 4(3), 193-201) copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Lemma, p. 194 (twice: related work and the sparse proof)](https://www.fq.math.ca/Scanned/4-3/fridy.pdf)
- [Lemma, p. 194 (related work and the interval-retention step)](https://www.fq.math.ca/Scanned/4-3/fridy.pdf)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L816-L818) — lines `816–818`; excerpt `sha256:2efe0e466de39d202e8f4b37c4f1254922fdfb071f848b688d6e85dd4f4cfff4`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3045-L3047) — lines `3045–3047`; excerpt `sha256:509f2c022f6bb16fcc6561688a6ee2a68568c8655480a3a52794977fbfd3eeec`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3003-L3005) — lines `3003–3005`; excerpt `sha256:509f2c022f6bb16fcc6561688a6ee2a68568c8655480a3a52794977fbfd3eeec`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:69](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L69-L69)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:381](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L381-L381), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:588](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L588-L588), [cite at paper/reasoning-parts/erdos251/core.tex:339](../../paper/reasoning-parts/erdos251/core.tex#L339-L339), [cite at paper/reasoning-parts/erdos251/core.tex:546](../../paper/reasoning-parts/erdos251/core.tex#L546-L546)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:877](../../paper/synthesis/optimal-sparse-perturbations.tex#L877-L877), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1012](../../paper/synthesis/optimal-sparse-perturbations.tex#L1012-L1012), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1852](../../paper/synthesis/optimal-sparse-perturbations.tex#L1852-L1852), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1969](../../paper/synthesis/optimal-sparse-perturbations.tex#L1969-L1969)

<a id="source-source-fb64da05c3acc7"></a>

### [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](https://doi.org/10.1007/s00209-006-0939-5)

- Source id: `source-fb64da05c3acc7`
- Author or public identity: Moubariz Z. Garaev, Florian Luca, Igor E. Shparlinski
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `source\_verified` — Supplied full text consulted at introduction, Theorem 1 and rational-shift argument; no conditioned-fibre conclusion extracted.
- Local mapping: `not recorded`

Exact source locations:

- [Supplied full text consulted at introduction, Theorem 1 and rational-shift argument; no conditioned-fibre conclusion extracted.](https://doi.org/10.1007/s00209-006-0939-5)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3227-L3231) — lines `3227–3231`; excerpt `sha256:913a7268d821938b55f3e6c38752a0db175dd6dca90b4edd9be62c706db57416`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3192-L3196) — lines `3192–3196`; excerpt `sha256:913a7268d821938b55f3e6c38752a0db175dd6dca90b4edd9be62c706db57416`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1972](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1972-L1972), [cite at paper/reasoning-parts/erdos68/core.tex:1937](../../paper/reasoning-parts/erdos68/core.tex#L1937-L1937)

<a id="source-source-fcf73a15ff9c7c"></a>

### [Arithmetic properties of certain functions in several variables III](https://doi.org/10.1017/S0004972700022978)

- Source id: `source-fcf73a15ff9c7c`
- Author or public identity: J. H. Loxton, A. J. van der Poorten
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Original Hecke–Mahler value theorem (Theorem 8, p. 40) for the case used in the two-prime deduction.
- Source verification: `source\_verified` — The cited passages (Theorem 8, p. 40; Theorem 8, p. 40 (two places)) were checked against the journal copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Theorem 8, p. 40](https://doi.org/10.1017/S0004972700022978)
- [Theorem 8, p. 40 (two places)](https://doi.org/10.1017/S0004972700022978)
- [Theorem 8, p. 40 (inherited pinpoint; attribution also checked in Bugeaud–Laurent)](https://doi.org/10.1017/s0004972700022978)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4466-L4469) — lines `4466–4469`; excerpt `sha256:c0c58cb7c064ff51cdf457f20ba15d04a78eb43f30bbf3764f9162de257e6a00`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1042-L1045) — lines `1042–1045`; excerpt `sha256:c0c58cb7c064ff51cdf457f20ba15d04a78eb43f30bbf3764f9162de257e6a00`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4408-L4411) — lines `4408–4411`; excerpt `sha256:c0c58cb7c064ff51cdf457f20ba15d04a78eb43f30bbf3764f9162de257e6a00`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L83-L83) — lines `83–83`; excerpt `sha256:072346b11faedd93181d1f5ba983b7885b1d5fd9b4292dcfa07310184ac025ab`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L83-L83) — lines `83–83`; excerpt `sha256:072346b11faedd93181d1f5ba983b7885b1d5fd9b4292dcfa07310184ac025ab`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:707](../../paper/269/erdos-269-three-prime-running-lcm.tex#L707-L707)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:141](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L141-L141), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:590](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L590-L590), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1346](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1346-L1346), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3903](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3903-L3903), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:4397](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4397-L4397), [cite at paper/reasoning-parts/erdos269/core.tex:83](../../paper/reasoning-parts/erdos269/core.tex#L83-L83), [cite at paper/reasoning-parts/erdos269/core.tex:532](../../paper/reasoning-parts/erdos269/core.tex#L532-L532), [cite at paper/reasoning-parts/erdos269/core.tex:1288](../../paper/reasoning-parts/erdos269/core.tex#L1288-L1288), [cite at paper/reasoning-parts/erdos269/core.tex:3845](../../paper/reasoning-parts/erdos269/core.tex#L3845-L3845), [cite at paper/reasoning-parts/erdos269/core.tex:4339](../../paper/reasoning-parts/erdos269/core.tex#L4339-L4339)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1291](../../paper/synthesis/optimal-sparse-perturbations.tex#L1291-L1291)

<a id="source-source-habiro-2004-cyclotomic"></a>

### [Cyclotomic completions of polynomial rings](https://ems.press/content/serial-article-files/40881)

- Source id: `source-habiro-2004-cyclotomic`
- Author or public identity: Kazuo Habiro
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Taylor-map injectivity is an exact statement in the cyclotomic-completion setting. It is compared with, not applied to, the local construction preserving prescribed finite jets and radial smoothness. The local theorem does not preserve an entire Taylor series.
- Source verification: `source\_verified` — The named primary passage and the stated local use were checked on 29 September 2026; not a full-paper review or novelty judgment.
- Local mapping: `exact\_bibliographic\_use` — Round8 manuscript transfer; ordinary proof and citation authority remain separate.

Exact source locations:

- [Journal edition, Publ.RIMS40(2004), Theorem5.2, printedp1138.](https://ems.press/content/serial-article-files/40881)

Public implementation or evidence coordinates:

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10436-L10441) — lines `10436–10441`; excerpt `sha256:5ab6928799e39a4d3e26716ecba39c7c67a800837b04a83ce236837f3eae312d`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L7656-L7656) — lines `7656–7656`; excerpt `sha256:6137621520080ad6f0ea38d5b86775d92fec7d19b870807a765fdfd728e9362c`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L10244-L10249) — lines `10244–10249`; excerpt `sha256:5ab6928799e39a4d3e26716ecba39c7c67a800837b04a83ce236837f3eae312d`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7464-L7464) — lines `7464–7464`; excerpt `sha256:6137621520080ad6f0ea38d5b86775d92fec7d19b870807a765fdfd728e9362c`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7656](../../paper/249/erdos249-totient-reasoning-surface.tex#L7656-L7656), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7464](../../paper/reasoning-parts/erdos249/a249_front.tex#L7464-L7464)

<a id="source-source-kozhan-vaktnas-2407-13946v1"></a>

### [Christoffel transform and multiple orthogonal polynomials](https://arxiv.org/abs/2407.13946v1)

- Source id: `source-kozhan-vaktnas-2407.13946v1`
- Author or public identity: Rostyslav Kozhan, Marcus Vaktnäs
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Polynomial reweighting of a moment functional is existing Christoffel-transform machinery. The local specialization multiplies the positive atomic mass by 1-qx; the calibrated value and exact denominator estimates are separate local arguments.
- Source verification: `source\_verified` — The named primary passage and the stated local use were checked on 29 September 2026; not a full-paper review or novelty judgment.
- Local mapping: `exact\_bibliographic\_use` — Round8 manuscript transfer; ordinary proof and citation authority remain separate.

Exact source locations:

- [Version1 introduction equations(3)-(4), with moment-functionals in section2.3.](https://arxiv.org/abs/2407.13946v1)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5344-L5348) — lines `5344–5348`; excerpt `sha256:284f2b11997d11abbeb3afe292b15bc5217f0f0f9edf5787e81581abdf458efa`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2767-L2767) — lines `2767–2767`; excerpt `sha256:e45056ad57ac969b6825cff487af5bde054739cf76036caa64219404edfb82fe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5313-L5317) — lines `5313–5317`; excerpt `sha256:284f2b11997d11abbeb3afe292b15bc5217f0f0f9edf5787e81581abdf458efa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2736-L2736) — lines `2736–2736`; excerpt `sha256:e45056ad57ac969b6825cff487af5bde054739cf76036caa64219404edfb82fe`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2767](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2767-L2767), [cite at paper/reasoning-parts/erdos1049/core.tex:2736](../../paper/reasoning-parts/erdos1049/core.tex#L2736-L2736)

<a id="source-source-le-intersective-0910-1880"></a>

### [Intersective polynomials and the primes](https://arxiv.org/abs/0910.1880v1)

- Source id: `source-le-intersective-0910-1880`
- Author or public identity: Thai Hoang Lê
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited for the modular-root definition of intersectivity. Its arXiv v1 introduction lists Q=(x²−2)(x²−3)(x²−6) as intersective; the synthesis paper's modulo-8 calculation corrects that printed example and proves its own shift-family criterion.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [p. 1, Theorem 3 and the printed Q example in the following paragraph](https://arxiv.org/pdf/0910.1880v1)

Public implementation or evidence coordinates:

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2109-L2113) — lines `2109–2113`; excerpt `sha256:5404323f44e0bf7745e5f12de10c65654b41f753d8706832e970ae20416d06be`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1799](../../paper/synthesis/optimal-sparse-perturbations.tex#L1799-L1799), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1826](../../paper/synthesis/optimal-sparse-perturbations.tex#L1826-L1826)

<a id="source-source-mishra-quadratic-2102-08379"></a>

### [Polynomials consisting of quadratic factors with roots modulo any positive integer](https://arxiv.org/abs/2102.08379)

- Source id: `source-mishra-quadratic-2102-08379`
- Author or public identity: Bhawesh Mishra
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Lists the rootless polynomial (x²−13)(x²−17)(x²−221) with roots modulo every positive integer; the unit-root and shift-family deductions are proved in the synthesis paper.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Example 1, p. 5 of the preprint](https://arxiv.org/pdf/2102.08379)

Public implementation or evidence coordinates:

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2117-L2121) — lines `2117–2121`; excerpt `sha256:3d65436d31201d414ea230e03345193de1bd649376c50acdc800ef0e44b497c7`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1808](../../paper/synthesis/optimal-sparse-perturbations.tex#L1808-L1808)

<a id="source-source-rice-pintersective-1111-6559"></a>

### [Sárközy's theorem for P-intersective polynomials](https://arxiv.org/abs/1111.6559)

- Source id: `source-rice-pintersective-1111-6559`
- Author or public identity: Alex Rice
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited for unit-root, prime-argument intersectivity terminology; the synthesis paper proves the selected-shift equivalence independently.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [§1.2, Definition 1 and following Remark on P-intersectivity](https://arxiv.org/pdf/1111.6559)

Public implementation or evidence coordinates:

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2113-L2117) — lines `2113–2117`; excerpt `sha256:dd7f0d46e967844319c928981d430ccea291c9ca3135f81eb0cc7cfe494ff39b`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1801](../../paper/synthesis/optimal-sparse-perturbations.tex#L1801-L1801)

<a id="source-source-vinroot-2010-multivariate-rogers-szego"></a>

### [Multivariate Rogers-Szego polynomials and flags in finite vector spaces](https://arxiv.org/abs/1011.0984)

- Source id: `source-vinroot-2010-multivariate-rogers-szego`
- Author or public identity: C. Ryan Vinroot
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Supplies the name and combinatorial identification of the finite sums R\_k^(r) used in long1049:prop:rogers-factorisation: the sum of all q-multinomial coefficients of degree k and length r, equal to the multivariate Rogers-Szego polynomial at unit arguments, a Galois number for r=2 and a flag count for r=3. The factorisation of the 2016 moment weights through those sums is proved in the long record, not taken from this source.
- Source verification: `bibliography\_only` — The arXiv abstract page for 1011.0984v1 was read on 20 September 2026 and confirms the title, author, single version, submission date, and the two identifications cited (q-multinomial coefficient sums as flag counts; a recursion generalising the Galois numbers). The full text was not read, and no proof in the source is certified here. The source is used for naming and identification only.
- Local mapping: `exact\_bibliographic\_use` — Exact local bibliography key and single in-text citation located in the long reasoning record.

Exact source locations:

- [Abstract (v1, 3 November 2010): recursion for the multivariate Rogers-Szego polynomials; the sum of all q-multinomial coefficients of degree n and length m counts flags of length m-1 in an n-dimensional space over F\_q, with a recursion generalising the Galois numbers.](https://arxiv.org/abs/1011.0984)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5367-L5374) — lines `5367–5374`; excerpt `sha256:737d5477a37bdfbe338d30af01c736674dfc46101542dd73448f0906325c87ee`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5398-L5405) — lines `5398–5405`; excerpt `sha256:737d5477a37bdfbe338d30af01c736674dfc46101542dd73448f0906325c87ee`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:350](../../paper/1049/erdos-1049-rational-base-lambert.tex#L350-L350)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2005](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2005-L2005), [cite at paper/reasoning-parts/erdos1049/core.tex:1974](../../paper/reasoning-parts/erdos1049/core.tex#L1974-L1974)

<a id="source-source-zudilin-determinantal-1507-05697v2"></a>

### [A determinantal approach to irrationality (arXiv v2)](https://arxiv.org/abs/1507.05697v2)

- Source id: `source-zudilin-determinantal-1507.05697v2`
- Author or public identity: Wadim Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: The determinantal criterion requires successive denominator divisibility in addition to positive moment and analytic bounds. The local rank-two residual625 refutes replacing that divisibility by numerical ordering; it does not refute the source criterion. Existing Heine-expansion citations remain pinned separately to v1.
- Source verification: `source\_verified` — The named primary passage and the stated local use were checked on 29 September 2026; not a full-paper review or novelty judgment.
- Local mapping: `exact\_bibliographic\_use` — Round8 manuscript transfer; ordinary proof and citation authority remain separate.

Exact source locations:

- [Version2 section1 Propositions1-2, hypothesis(e) delta\_n divides delta\_(n+1), and section2 determinant clearing.](https://arxiv.org/abs/1507.05697v2)

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5227-L5231) — lines `5227–5231`; excerpt `sha256:4e24fef998f109ce93696a8d9d04b5a1a6af4b7a9e8b88bd4ccee7a4154cfd88`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2753-L2753) — lines `2753–2753`; excerpt `sha256:7a145aa9594fa020d57e86e4eea374a60a878af8c1b11118e150c4a10410fe93`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L5196-L5200) — lines `5196–5200`; excerpt `sha256:4e24fef998f109ce93696a8d9d04b5a1a6af4b7a9e8b88bd4ccee7a4154cfd88`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2722-L2722) — lines `2722–2722`; excerpt `sha256:7a145aa9594fa020d57e86e4eea374a60a878af8c1b11118e150c4a10410fe93`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2753](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2753-L2753), [cite at paper/reasoning-parts/erdos1049/core.tex:2722](../../paper/reasoning-parts/erdos1049/core.tex#L2722-L2722)

## Coverage requiring review

These gaps are shown explicitly so the catalogue cannot be mistaken for complete historical knowledge.

- Registered papers scanned: `24`; TeX source files scanned after local includes: `98`.
- Citation keys without a local bibliography definition: `0`
- Bibliography entries without a curated source link: `119`
- Lean lexical candidates awaiting review: `827`
- Unresolved local TeX includes: `0`

Machine-readable inventories, hashes, unresolved keys, and lexical candidates: [source-attribution-index.json](source-attribution-index.json).
