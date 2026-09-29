<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Source attributions

_Generated from the authored source registry; do not hand-edit._

This index shows which public sources informed which papers, problems, Lean-facing records, and implemented changes. Source credit does not establish proof, novelty, endorsement, peer review, or complete historical coverage.

Private correspondence appears only under a neutral anonymous identity until public naming is confirmed. Its email, mailbox location, message text, and private evidence remain outside this repository.

## Coverage and anonymous implementation credits

The registry contains `309` curated sources across `22` registered papers and `1903` Lean library files.

Source review states: `bibliography_only`: `96`; `existing_source_closure`: `31`; `external_claim_unverified`: `1`; `implemented_advice`: `3`; `source_verified`: `178`.

Bibliography coverage records attribution already present in the corpus. A `bibliography_only` record still needs direct source-passage verification; a completed lexical review does not certify a source-to-theorem correspondence.

Implemented advice whose identity is awaiting confirmation:

- [Formalization classification and cheap inspection advice](#source-correspondence-001) — Implemented advice to classify each selected result, expose exact statements, proof provenance, novelty status, sorry count, axiom budget, and boundaries in formalization.yaml, and to provide a cheap Comparator inspection route with an altered-statement rejection fixture. The current public surface has evolved beyond the original interface count; the durable implementation is the manifest-plus-Comparator pattern and its explicit scope ceiling.
- [Theorem-first packaging and literature-comparison advice](#source-correspondence-002) — Implemented advice to lead with the exact finite-level rank and basis, give the CRT/Dirichlet-style independence mechanism, compare the result precisely with Allouche–Shallit, Coons, Martin, and adjacent k-kernel literature, and link a minimal Lean entry. The paper states the exact rank k^e+1 and basis, records that Coons already proved non-k-regularity and Martin supplies a broader external affine-independence antecedent while the public Lean proof establishes all-base independence separately, and keeps the unbounded #249 irrationality endpoint open. No proof verification, novelty judgment, or progress-on-parent-problem judgment is attributed to the correspondent.
- [Prior-art comparison advice](#source-correspondence-003) — Implemented a received pointer by comparing the cited q-Apéry construction with the #1049 rational-base programme. The public source closure verifies that the paper targets the same Lambert value, identifies the q-WZ operator and the integer-base denominator-clearing boundary, and credits both published authors in the ordinary literature row. The local Lean module separately proves that Van Assche’s different moving diagonal has a nonzero n=0 residual for the cited operator. This correspondence row credits only the private prior-art pointer; it does not claim the correspondent checked the comparison, calculations, Lean, or #1049 mathematics.

- Unmatched citation keys: `0`
- Bibliography entries awaiting curated links: `94`
- Lean candidates awaiting review: `793` (`3` direct URL/DOI/arXiv rows; `1644` surname/key rows; categories may overlap).

## Browse by problem

- **Erdős #1041**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates), [Formalization classification and cheap inspection advice](#source-correspondence-001), [Degree-seven total-variation counterexample for polynomial lemniscates](#source-erdos1041-ani-degree-seven-candidate-counterexample), [Independent check of candidate degree-seven counterexample](#source-erdos1041-morluto-independent-check), [Quartic case of Erdős #1041](#source-erdos1041-pendyala-quartic), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [A Markov-type inequality for arbitrary plane continua](#source-eremenko-2007-markov-type-inequality-plane-continua), [An extremal problem for polynomials](#source-eremenko-lempert-1994-extremal-problem-for-polynomials), [Comb functions](#source-eremenko-yuditskii-2012-comb-functions), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [The maximal length of the Erdős–Herzog–Piranian lemniscate in high…](#source-source-0e12f93aeac487), [Lemniscates and inequalities for the logarithmic capacities of cont…](#source-source-2a86f52125aec0), [Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zu…](#source-source-2ec6bf87654604), [Bad Polynomials for Newton's Method](#source-source-318ee5e7cf6d74), [The area of polynomial images and preimages](#source-source-40bc4064b92788), [Three refinements for the lemniscate-path programme](#source-source-45037c29c04bed), [Length functions of lemniscates](#source-source-57fe330e419648), [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff), [Critical points and values of complex polynomials](#source-source-7ac8693558c1a2), [On the length of lemniscates](#source-source-7f1f2a3fd9238c), [A bound for Smale's mean value conjecture for complex polynomials](#source-source-818467bc1cb170), [Shortest paths in polynomial lemniscate sublevel sets and a problem…](#source-source-8710374c3e8c9f), [The arc length of the lemniscate |p(z)|=1](#source-source-89b9a294db76bb), [Computing the Newtonian Graph](#source-source-92b0dfb67f5009), [A Degree-Four Lemniscate Path Theorem](#source-source-951f70d8dfc418), [Number of Components of Polynomial Lemniscates: A Problem of Erdős,…](#source-source-97b4e6a82335a7), [Two-dimensional shapes and lemniscates](#source-source-9e37cc2fe7db3e), [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec), [Inequalities for critical values of polynomials](#source-source-b10b965e63a00d), [Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichun…](#source-source-b4b0f2811b1d2d), [Some inequalities for polynomials and rational functions associated…](#source-source-dcbe400c96be59), [Four-point distortion theorem for complex polynomials](#source-source-f0af8e6f36727f), [A Short Path Joining Two Zeros Inside a Polynomial Lemniscate](#source-source-f300911fb03a5c)
- **Erdős #1049**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Prior-art comparison advice](#source-correspondence-003), [Retrieval of Chowla 1947 original scan](#source-erdos1049-bloom-chowla-scan-retrieval), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #1049](#source-formal-conjectures-adapter-problem-1049), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [A problem about Mahler functions](#source-source-0a6b8c93371570), [Stieltjes moment sequences of polynomials](#source-source-0f46dee5024c66), [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [À propos de la série ∑\_{n≥1} x^n/(q^n−1)](#source-source-169c3d67838965), [On a permutation group related to ζ(2)](#source-source-176d35cb60b651), [On the non-quadraticity of values of the q-exponential function and…](#source-source-22ef36d016ca81), [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62), [On powers of Stieltjes moment sequences, II](#source-source-2a10c7287879c3), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [A determinant identity for moments of orthogonal polynomials that i…](#source-source-3479bad7869d7c), [Common Factors in Fraction-Free Matrix Decompositions](#source-source-39e4fc546549fd), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [Lattice paths and branched continued fractions: An infinite sequenc…](#source-source-490b1875016ea4), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Calculation of Gauss Quadrature Rules](#source-source-53a2a9c4a9e7c2), [NIST Digital Library of Mathematical Functions, Eq. 17.2.37](#source-source-5857f9959e7529), [On an incomplete argument of Erdős on the irrationality of Lambert…](#source-source-5911448b65fdf9), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [On the irrationality of ∑ 1/(q^n+r)](#source-source-62f9190aeb7d34), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [Arithmetical functions and irrationality of Lambert series](#source-source-6cfe654e650970), [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b), [Smith normal form in combinatorics](#source-source-91756d895a28a8), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Zero Coefficients of Rational Power Series and Rational Lambert Series](#source-source-aa2d5c249362f1), [On the irrationality of generalized q-logarithm](#source-source-ae9859af28fdcd), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [Continued-fraction characterization of Stieltjes moment sequences w…](#source-source-c61a0cf3f328ce), [Irrationality proof of certain Lambert series using little q-Jacobi…](#source-source-ca19e504149107), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94), [Some New Applications of the Subspace Theorem](#source-source-corvaja-zannier-2002-subspace), [FormalConjectures.ErdosProblems.1049](#source-source-d7a43109c64c0c), [Log-convex and Stieltjes moment sequences](#source-source-e535117ac620e6), [Arithmetical investigations of a certain infinite product](#source-source-e553241a97e580), [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f), [A further improvement of the quantitative Subspace Theorem](#source-source-evertse-ferretti-2013-author2012), [Remarks on irrationality of q-harmonic series](#source-source-f1c687cb5e9ae4), [A determinantal approach to irrationality](#source-source-f67bf9959aa230), [Rational approximations to a q-analogue of π and some other q-series](#source-source-f9fd9214c9ef11), [Christoffel transform and multiple orthogonal polynomials](#source-source-kozhan-vaktnas-2407-13946v1), [Multivariate Rogers-Szego polynomials and flags in finite vector sp…](#source-source-vinroot-2010-multivariate-rogers-szego), [A determinantal approach to irrationality (arXiv v2)](#source-source-zudilin-determinantal-1507-05697v2)
- **Erdős #243**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Koizumi pseudo-greedy equivalence and computation pointer](#source-erdos243-kovac-koizumi-pointer), [Rational-tail deterministic pair recurrence and open-boundary reduc…](#source-erdos243-tao-tail-pair-recurrence), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Irrationality exponents of certain fast converging series of ration…](#source-source-0f03e2dab0b8c2), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [FormalConjectures.ErdosProblems.243](#source-source-1713b9ad6350bd), [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641), [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62), [Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partia…](#source-source-2a3af2a360bb15), [A theorem on irrationality of infinite series and applications](#source-source-318b37ba5af2eb), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [On the irrationality of polynomial Cantor series](#source-source-77ddbf43e364f7), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Irrationality of the reciprocal sum of doubly exponential sequences](#source-source-86d1745e2d139b), [Chebotarëv and his density theorem](#source-source-abedb02f9939e5), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [{Digital Library of Mathematical Functions}, {Section} 5.11(iii): R…](#source-source-b95bf142df7fb5), [Irrationality Criteria for Series by Erdős and Straus](#source-source-c6e97d89c9fa5f), [On the rationality of Cantor and Ahmes series](#source-source-cbaba7aeeb0f71), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f), [Erdős #243: working report](#source-source-ee991edd431d57)
- **Erdős #249**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Theorem-first packaging and literature-comparison advice](#source-correspondence-002), [Möbius-transform identity for the binary totient constant](#source-erdos249-fan-mobius-transform), [Irrationality of the n=2^m sparse totient subseries](#source-erdos249-rafik-sparse-power-two-subseries), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #249](#source-formal-conjectures-adapter-problem-249), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891), [Erdős–Gál lacunary-series law of the iterated logarithm (two-part s…](#source-proposed-direct-7f278004ad452a), [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c), [Note on normal numbers](#source-proposed-direct-f7f90747134dba), [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da), [On asymptotic distributions of arithmetical functions](#source-source-0e9b7210b29d99), [On the set of partial sums of an infinite series](#source-source-0ecb074e507b86), [Answer to An infinite sum based on the mod-parity of Euler's totien…](#source-source-0f61ad0796acdf), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Simultaneous inequalities among values of the Euler phi-function](#source-source-11b46a0435368f), [A survey of gcd-sum functions](#source-source-22ce74d28ddb49), [Regular sequences and the joint spectral radius](#source-source-296ff41148fff7), [On a curious property of vulgar fractions](#source-source-2aa4970cfda278), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [On the law of the iterated logarithm. I](#source-source-39690ee8e07b0c), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [A dynamical proof of the van der Corput inequality](#source-source-3d300ccd5e4cbb), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [The ring of k -regular sequences](#source-source-5752bb5009e4de), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Integer sequences and periodic points](#source-source-5cac1ad51acb12), [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [Modular functions and transcendence questions](#source-source-6346eeeac5036d), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [How to prove that a sequence is not automatic](#source-source-6b460d123159d9), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [Comment and formula added to OEIS A256936 (revisions 28 and 31)](#source-source-71037224a1dd7c), [(Non)automaticity of number theoretic functions](#source-source-741da55b02c5a9), [On the complexity of algebraic numbers I. Expansions in integer bases](#source-source-7c8ba4ea6eea79), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [The Lambert series factorization theorem](#source-source-8935df46fb4693), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [Comment on Erdős Problem #249](#source-source-99c2f3cb190b95), [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81), [Multiplicative functions and k-automatic sequences](#source-source-a0d109b4492fba), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [Transcendence of generating functions whose coefficients are multip…](#source-source-b791f5b49e0da6), [Smooth numbers: computational number theory and beyond](#source-source-bc5d16b84e62c7), [The Fourier transform of functions of the greatest common divisor](#source-source-c786f202d47318), [(Non)Automaticity of number theoretic functions (arXiv v3)](#source-source-coons-nonautomaticity-0810-3709v3), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [On the binary digits of the Erdős--Borwein constant](#source-source-eca9e699590922), [Uber die asymptotische Verteilung reeller Zahlen mod 1](#source-source-eeff3fa685af8a), [Sparse Polynomial-Weighted Expansions](#source-source-f4ad17717c8fd4), [Cyclotomic completions of polynomial rings](#source-source-habiro-2004-cyclotomic)
- **Erdős #251**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Schlage-Puchta Theorem 2 literature pointer](#source-erdos251-alfaiz-schlage-puchta-pointer), [Counterexample to Erdős variable-denominator expectation](#source-erdos251-kovac-variable-denominator-counterexample), [Conditional #251 proof under Kuperberg Conjecture 1.3 and Lean form…](#source-erdos251-land-conditional-proof-lean), [Prime-gap summation-by-parts equivalence and conditional route](#source-erdos251-tao-prime-gap-equivalence), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #251](#source-formal-conjectures-adapter-problem-251), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Multiplicative Number Theory I: Classical Theory](#source-source-0aca0e5e4e03c0), [On the Erdős problem #251](#source-source-0ec7ca07508557), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Beweis eines Satzes von Tschebyschef](#source-source-20c650f8cf3744), [Erdős Problems discussion thread #251](#source-source-21738452dcb95c), [On the largest prime factors of n and n+1](#source-source-27575f46a101c1), [Multigeometric sequences and Cantorvals](#source-source-2b0038d2c239f5), [Sur certaines séries à valeur irrationnelle](#source-source-2ee394177d0f38), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [Sums of singular series along arithmetic progressions and with smoo…](#source-source-450aed97015b8f), [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Continued Fractions](#source-source-5ee5f85bd606ee), [Subsum sets: intervals, Cantor sets, and Cantorvals](#source-source-63a234b13e4427), [Small gaps between primes](#source-source-6564b203677735), [On Kakeya Conditions for Achievement Sets](#source-source-6d8837bbc174ce), [Achievement sets -- current results and open problems](#source-source-77333436a9e579), [Achievable Cantorvals almost without reversed Kakeya conditions](#source-source-779915b8355ac1), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Sums of singular series with large sets and the tail of the distrib…](#source-source-811205223e0788), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3), [Variants of the Selberg sieve, and bounded intervals containing man…](#source-source-91aa380a16dba9), [Local gap statistics, telescoping, and normality](#source-source-9a38b2d8b0dada), [Ford circles, continued fractions, and best approximation of the se…](#source-source-9b23918ce33c38), [FormalConjectures.ErdosProblems.251](#source-source-b202a3f125817d), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [More on Kakeya Conditions for Achievement Sets](#source-source-b46f8a083b4271), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001), [Bounded gaps between primes](#source-source-c32d672658410d), [The Poisson Tail Conjecture for primes in short intervals](#source-source-c9b987093aaf4e), [On a new condition implying that an achievement set is a Cantorval…](#source-source-ce27d27dd5ec77), [Long gaps between primes](#source-source-d3995db1508bc9), [The irrationality of some number theoretical series](#source-source-d471eacdba0f87), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [Partitions with prescribed sum of reciprocals: asymptotic bounds](#source-source-dbbc7de069eeee), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f), [A conditional proof of the irrationality of ∑\_{n≥1} p\_n 2^{−n} unde…](#source-source-f42f9e04743a4c), [Generalized bases for the real numbers](#source-source-fb4194cadb150b)
- **Erdős #257**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Earlier variants, interval-filling negative variant, and fat-Cantor…](#source-erdos257-kovac-context-bundle), [Older Erdős and Borwein attribution for even/odd supports](#source-erdos257-kovac-older-special-case-attribution), [Period-two Lambert theorem applied to even and odd supports](#source-erdos257-tang-tachiya-period-two), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #257](#source-formal-conjectures-adapter-problem-257), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Diophantine Problems for q-Zeta Values](#source-proposed-direct-0ef4f73f93ceed), [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [Divisor-bounded multiplicative functions in short intervals](#source-proposed-direct-6c67db53ef5f8c), [The critical-window profile for d\_k in short intervals](#source-proposed-direct-6f90767d1d01dd), [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da), [On the set of partial sums of an infinite series](#source-source-0ecb074e507b86), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [On a curious property of vulgar fractions](#source-source-2aa4970cfda278), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [Some problems and results on the irrationality of the sum of infini…](#source-source-43a734be32736f), [FormalConjectures.ErdosProblems.257](#source-source-4bb571f8383293), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [The ring of k -regular sequences](#source-source-5752bb5009e4de), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [Modular functions and transcendence questions](#source-source-6346eeeac5036d), [Subsum sets: intervals, Cantor sets, and Cantorvals](#source-source-63a234b13e4427), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Über beliebige Teilsummen absolut konvergenter Reihen](#source-source-691e9cc3c46273), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [(Non)automaticity of number theoretic functions](#source-source-741da55b02c5a9), [Achievement sets -- current results and open problems](#source-source-77333436a9e579), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3), [The Lambert series factorization theorem](#source-source-8935df46fb4693), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [Irrationality of Lambert series associated with a periodic sequence](#source-source-9ce84321e202f1), [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94), [Some New Applications of the Subspace Theorem](#source-source-corvaja-zannier-2002-subspace), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [On the binary digits of the Erdős--Borwein constant](#source-source-eca9e699590922), [The logarithmic endpoint fails under arithmetic sampling](#source-source-endpoint2026-logarithmic-repair), [A further improvement of the quantitative Subspace Theorem](#source-source-evertse-ferretti-2013-author2012), [Sparse Polynomial-Weighted Expansions](#source-source-f4ad17717c8fd4), [Linear independence of certain Lambert series](#source-source-f6ee6890db85d9)
- **Erdős #269**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Infinite-prime-set irrationality proof and correction chain](#source-erdos269-fan-infinite-p-proof-repair), [Two-prime Hecke–Mahler factorisation and transcendence disclosure](#source-erdos269-fan-two-prime-disclosure), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [The Prime Number Theorem](#source-source-06457731c60720), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [On the irrationality of Cantor and Ahmes series](#source-source-1a7535a5e17a8c), [Comment on Erdős Problem #269](#source-source-21cdeefea4c8ec), [Letter to the Editor](#source-source-22aba734190d65), [Transcendence of Hecke–Mahler Series](#source-source-29bdada58b414a), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Sur le développement en fraction continue d'un nombre choisi au hasard](#source-source-5270112e32002d), [FormalConjectures.ErdosProblems.269](#source-source-573a79feb36d47), [Continued Fractions](#source-source-5ee5f85bd606ee), [On the set of points of convergence of a lacunary trigonometric ser…](#source-source-62ee65065db497), [Strongly complete sets and a conjecture of Erdős](#source-source-71fb76f6e1363b), [On the irrationality of polynomial Cantor series](#source-source-77ddbf43e364f7), [On the number of positive integers ≤ x and free of prime factors \> y](#source-source-78565c625f0ea3), [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](#source-source-7a9657920d576b), [On the complexity of algebraic numbers I. Expansions in integer bases](#source-source-7c8ba4ea6eea79), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Smith normal form in combinatorics](#source-source-91756d895a28a8), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [On the arithmetic properties of complex values of Hecke-Mahler seri…](#source-source-9c2776b87b1155), [On integers generated by a finite number of fixed primes](#source-source-ab6d6d6b890f57), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [Transcendence and continued fraction expansion of values of Hecke--…](#source-source-b9d7160919621f), [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380), [Irrationality Criteria for Series by Erdős and Straus](#source-source-c6e97d89c9fa5f), [A new proof of Nishioka's theorem in Mahler's method](#source-source-e7f2f796dbcdb6), [Mahler's method in several variables and finite automata](#source-source-eaeb7980382323), [Arithmetic properties of certain functions in several variables III](#source-source-fcf73a15ff9c7c)
- **Erdős #68**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #68](#source-formal-conjectures-adapter-problem-68), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [On the sequence $n!$ mod $p$](#source-source-02fc1f0e6f0418), [Lower bounds for some value sets over finite fields: incidence geom…](#source-source-04603f785c9e7f), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674), [An improved point-line incidence bound over arbitrary fields](#source-source-29cbac966b8b76), [On equal products of consecutive integers](#source-source-3068a3586a5e8b), [Character sums and congruences with n!](#source-source-34b520c561ee3c), [Factorial residues modulo a prime: beyond the square-root bound](#source-source-365c2b5cf46ebe), [On the greatest and least prime factors of n!+1](#source-source-3fb9e4907eec24), [Some problems and results on the irrationality of the sum of infini…](#source-source-43a734be32736f), [On the irrationality of certain 2-adic zeta values](#source-source-5122572a1e7312), [On the largest prime divisor of n!+1](#source-source-57adfd0cdcd8c2), [Prime divisors of shifted factorials](#source-source-5f85fb0bd75b8b), [A geometric proof that e is irrational and a new measure of its irr…](#source-source-6a5bf83735fdef), [Distribution of factorials modulo $p$](#source-source-724fef812699b7), [The product of consecutive integers is never a power](#source-source-7d923cace5602a), [Über die einfachen Zahlensysteme](#source-source-8ac37c92429a46), [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [On the irrationality of certain p-adic zeta values](#source-source-b3b7518e07e159), [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5), [On Equal Products of Consecutive Integers](#source-source-b6d577df139d85), [On the irrationality of factorial series](#source-source-c835bc94aad831), [On the greatest and least prime factors of n!+1 , II](#source-source-d1710db60eae06), [Representations of Real Numbers by Infinite Series](#source-source-e13ecb7c94852a), [On the largest prime factor of n!+2^n−1](#source-source-e66e0693f05f0a), [Rational numbers with odd greedy expansion of fixed length](#source-source-ef6233b59b95cb), [Additive congruences with factorials modulo a prime](#source-source-f1a42898642b5f), [NIST Digital Library of Mathematical Functions, §1.12(ii) Convergents](#source-source-f213b302ada43a), [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](#source-source-fb64da05c3acc7)

<details>
<summary>Browse alphabetically by author or public identity</summary>


- **A mathematician (name withheld pending confirmation)**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Theorem-first packaging and literature-comparison advice](#source-correspondence-002), [Prior-art comparison advice](#source-correspondence-003)
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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1254-L1255) — lines `1254–1255`; excerpt `sha256:e6c89924a4cd473044338ab4fc20aab3daf6d1b197c0f08b9472a7eb66e2f7cd`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:867](../../paper/systems/claim-faithful-publication-systems-paper.tex#L867-L867)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1240-L1243) — lines `1240–1243`; excerpt `sha256:389f1072e7710565d0ac22458d1649687336a06f23358534558210550d8c9d02`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:864](../../paper/systems/claim-faithful-publication-systems-paper.tex#L864-L864)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1058-L1061) — lines `1058–1061`; excerpt `sha256:069ff384c13f55f042ef0e445571c6ee28f771d27e9e80ae21ed97ffbf0c2689`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:853](../../paper/systems/claim-faithful-publication-systems-paper.tex#L853-L853)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1063-L1067) — lines `1063–1067`; excerpt `sha256:89a8572972941dbe073d1556d617df2e0a8d68508abbb26e667f054aa22542c9`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:864](../../paper/systems/claim-faithful-publication-systems-paper.tex#L864-L864)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1248-L1251) — lines `1248–1251`; excerpt `sha256:3a38116bdc9ac7954a4da9c52e66825e7c058d6e89d5d407cbaa402c7e2c6d4a`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:864](../../paper/systems/claim-faithful-publication-systems-paper.tex#L864-L864)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1251-L1254) — lines `1251–1254`; excerpt `sha256:78dd6ea8e8ef43d29d302fc8b5de01969a7254476ce7b4f61f7082ea5b1bdea9`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:867](../../paper/systems/claim-faithful-publication-systems-paper.tex#L867-L867)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1054-L1058) — lines `1054–1058`; excerpt `sha256:e32354d6e9dce5beea0bd7639fc428e29239061b36285063968f4c6b438d2b27`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:853](../../paper/systems/claim-faithful-publication-systems-paper.tex#L853-L853)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1238-L1240) — lines `1238–1240`; excerpt `sha256:be814ce4951f2905b8004c7408ab43e90833c53c2d9b14a310a0db0a25ef9a49`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:856](../../paper/systems/claim-faithful-publication-systems-paper.tex#L856-L856)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1139-L1142) — lines `1139–1142`; excerpt `sha256:d26896e824fc6ec4be1ca9fa58e0870913de11aaddf21f73f81231cffa1984d4`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:867](../../paper/systems/claim-faithful-publication-systems-paper.tex#L867-L867)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1067-L1070) — lines `1067–1070`; excerpt `sha256:57b56b3dc98f87e01830ec9d8ad0f84c00156ef9828cf7682e76d145c0ecf451`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:853](../../paper/systems/claim-faithful-publication-systems-paper.tex#L853-L853)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1061-L1063) — lines `1061–1063`; excerpt `sha256:2d82072ecac5b1ee63f9196038f8571e3f41c077968642287239a708bf0838ac`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:856](../../paper/systems/claim-faithful-publication-systems-paper.tex#L856-L856)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L924-L930) — lines `924–930`; excerpt `sha256:bfae70e92b17ff0eb46d5a89787ab01a60a09ee1c2fa3385ddf8b2ff8854f038`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5324-L5330) — lines `5324–5330`; excerpt `sha256:26d60d27d7d495f7259334fef196a51735ac5030652cb8728846fed7b1146393`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5280-L5286) — lines `5280–5286`; excerpt `sha256:26d60d27d7d495f7259334fef196a51735ac5030652cb8728846fed7b1146393`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:778](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L778-L778)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4293](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4293-L4293), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4296](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4296-L4296), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4364](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4364-L4364), [cite at paper/reasoning-parts/erdos1041/core.tex:4249](../../paper/reasoning-parts/erdos1041/core.tex#L4249-L4249), [cite at paper/reasoning-parts/erdos1041/core.tex:4252](../../paper/reasoning-parts/erdos1041/core.tex#L4252-L4252), [cite at paper/reasoning-parts/erdos1041/core.tex:4320](../../paper/reasoning-parts/erdos1041/core.tex#L4320-L4320)

<a id="source-correspondence-001"></a>

### Formalization classification and cheap inspection advice

- Source id: `correspondence-001`
- Author or public identity: A mathematician (name withheld pending confirmation)
- Kind: `correspondence`
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
- [docs/EXTERNAL\_VERIFICATION.md](../../docs/EXTERNAL_VERIFICATION.md#L4-L14) — lines `4–14`; excerpt `sha256:d38bbf38909250ed6425efc908bf466dd7da14f8cbd8020fdd3021ef1548b592`

<a id="source-correspondence-002"></a>

### Theorem-first packaging and literature-comparison advice

- Source id: `correspondence-002`
- Author or public identity: A mathematician (name withheld pending confirmation)
- Kind: `correspondence`
- Problems: #249
- Relationship and boundary: Implemented advice to lead with the exact finite-level rank and basis, give the CRT/Dirichlet-style independence mechanism, compare the result precisely with Allouche–Shallit, Coons, Martin, and adjacent k-kernel literature, and link a minimal Lean entry. The paper states the exact rank k^e+1 and basis, records that Coons already proved non-k-regularity and Martin supplies a broader external affine-independence antecedent while the public Lean proof establishes all-base independence separately, and keeps the unbounded #249 irrationality endpoint open. No proof verification, novelty judgment, or progress-on-parent-problem judgment is attributed to the correspondent.
- Source verification: `implemented\_advice` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- Private correspondence retained by maintainer; identity withheld pending confirmation.

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L21-L23) — lines `21–23`; excerpt `sha256:88b60a7e65dd8caa239cb470e4423911058629e75c0bb69c7656677329f9429a`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L62-L62) — lines `62–62`; excerpt `sha256:b6ce0fb599e9bf02898ae89ea89e3bf47a7a31efcaab7ffbe2a9e2aaaae8ab8c`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L61-L61) — lines `61–61`; excerpt `sha256:c1960cd50c0146b008839691c83ef53220ec6bdf251ce3c02d30ff006670e01a`
- [lean/Erdos249257/TotientMahlerDefect.lean](../../lean/Erdos249257/TotientMahlerDefect.lean#L935-L1145) — lines `935–1145`; excerpt `sha256:e4bbeef9407526e58653fc7ed307d51530c41af7bd6d225f36388486dc845a6e`
- [formalization.yaml](../../formalization.yaml#L159-L216) — lines `159–216`; excerpt `sha256:b323e9a098414f61b29469d542453a446713a6650efbe384accb4d657f9a1e7e`
- [docs/EXTERNAL\_VERIFICATION.md](../../docs/EXTERNAL_VERIFICATION.md#L534-L544) — lines `534–544`; excerpt `sha256:cb49ade0a57a20d0355d24a8ebc443b2be0b82e0f3c2bdd61f361abe2913a17b`

<a id="source-correspondence-003"></a>

### Prior-art comparison advice

- Source id: `correspondence-003`
- Author or public identity: A mathematician (name withheld pending confirmation)
- Kind: `correspondence`
- Problems: #1049
- Relationship and boundary: Implemented a received pointer by comparing the cited q-Apéry construction with the #1049 rational-base programme. The public source closure verifies that the paper targets the same Lambert value, identifies the q-WZ operator and the integer-base denominator-clearing boundary, and credits both published authors in the ordinary literature row. The local Lean module separately proves that Van Assche’s different moving diagonal has a nonzero n=0 residual for the cited operator. This correspondence row credits only the private prior-art pointer; it does not claim the correspondent checked the comparison, calculations, Lean, or #1049 mathematics.
- Source verification: `implemented\_advice` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- Private correspondence retained by maintainer; identity withheld pending confirmation.

Public implementation or evidence coordinates:

- [docs/primary-sources/reciprocal-tail/amdeberhan-zeilberger-1998-q-apery-source-closure.md](../../docs/primary-sources/reciprocal-tail/amdeberhan-zeilberger-1998-q-apery-source-closure.md#L1-L41) — lines `1–41`; excerpt `sha256:2dd1c6e867a779af56358ca64dc97076e8c0c4f4fe8db1128aed5624673e206b`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L846-L846) — lines `846–846`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L389-L393) — lines `389–393`; excerpt `sha256:c9f8d191bbf7d39a3e75436d9d7036604d3f396d1223d6f8d505668cafc4971e`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L1-L100) — lines `1–100`; excerpt `sha256:2869c3db2da5857a4c9fc56be272d52f5a7b1242f3633bd8ed0b01f0da016724`

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
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1106-L1108) — lines `1106–1108`; excerpt `sha256:4e4234729ca246120c50642f617d7062a456fa5a1f0900f82ed49b3a7e16a132`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:953](../../paper/systems/claim-faithful-publication-systems-paper.tex#L953-L953)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L276-L276) — lines `276–276`; excerpt `sha256:564fef3b1c83b587c34b3db58f1f89d199d9b9f7fccafdea2fbbe0766f05f34a`
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
- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5441-L5452) — lines `5441–5452`; excerpt `sha256:f4a1bd463f398d1bcf67d88f273df4a9fc0dc2d42efadf85db1519f432cadfb5`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L837-L841) — lines `837–841`; excerpt `sha256:b901a58ca5f4fa10b5877f77546cf4c15ae0e086b4ea3be59376b1a5cbe7b336`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2981-L2985) — lines `2981–2985`; excerpt `sha256:fd3671803715497848f50b7e406b351a3c0b3100358db5c0e7912563aefc2384`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1269-L1272) — lines `1269–1272`; excerpt `sha256:4d4235c9f8595425346cd8f2ad0afc169ccb1bbc0fba3996d6af5ec8a919f0f7`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4040-L4043) — lines `4040–4043`; excerpt `sha256:1dca12f343679fed7cbdd1c9c2c6875092a3fc3a72e5f2d5a7e3c53e88c81bad`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L620-L622) — lines `620–622`; excerpt `sha256:005880e8a0c24af82bd80baf86e412679544e057c8fc1dd3cb8974df9821931f`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2921-L2923) — lines `2921–2923`; excerpt `sha256:005880e8a0c24af82bd80baf86e412679544e057c8fc1dd3cb8974df9821931f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4228-L4231) — lines `4228–4231`; excerpt `sha256:537273daefc24b11ce4957528c7e9ccf4d6f1dded43341bd70c16ddf413cbaec`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1043-L1046) — lines `1043–1046`; excerpt `sha256:1f96b54624b74012e10f2b0eb737b72d04c0a867978035159fb1c8d591f76534`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L865-L867) — lines `865–867`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5234-L5236) — lines `5234–5236`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1068-L1072) — lines `1068–1072`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4949-L4953) — lines `4949–4953`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1671-L1676) — lines `1671–1676`; excerpt `sha256:bb8050123710e542e010c55df517209f1e56e938a1655ebb63df13ec2e2c8c44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5190-L5192) — lines `5190–5192`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L48-L48) — lines `48–48`; excerpt `sha256:39b01ef53f651e61857928eaa6e3fcd4e9d3905f467040c640112f06aed89e75`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4918-L4922) — lines `4918–4922`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L32-L32) — lines `32–32`; excerpt `sha256:4b64e09024256b353df29c3a5a534206fcc391d86cbc2811fdc4722cfb6d1d96`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L32-L32) — lines `32–32`; excerpt `sha256:4b64e09024256b353df29c3a5a534206fcc391d86cbc2811fdc4722cfb6d1d96`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4001-L4004) — lines `4001–4004`; excerpt `sha256:1dca12f343679fed7cbdd1c9c2c6875092a3fc3a72e5f2d5a7e3c53e88c81bad`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L39-L39) — lines `39–39`; excerpt `sha256:291771799f1e1c8a9a0b43391570fd9b02e3836c3944d9938c7a8118de5e6afb`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L37-L37) — lines `37–37`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L39-L39) — lines `39–39`; excerpt `sha256:291771799f1e1c8a9a0b43391570fd9b02e3836c3944d9938c7a8118de5e6afb`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2880-L2882) — lines `2880–2882`; excerpt `sha256:005880e8a0c24af82bd80baf86e412679544e057c8fc1dd3cb8974df9821931f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L24-L24) — lines `24–24`; excerpt `sha256:d538a4c45ccfa82fa63fdd158d662620db6780ba048b39e23d15f5c6393443b8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L24-L24) — lines `24–24`; excerpt `sha256:d538a4c45ccfa82fa63fdd158d662620db6780ba048b39e23d15f5c6393443b8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L24-L24) — lines `24–24`; excerpt `sha256:d538a4c45ccfa82fa63fdd158d662620db6780ba048b39e23d15f5c6393443b8`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4177-L4180) — lines `4177–4180`; excerpt `sha256:537273daefc24b11ce4957528c7e9ccf4d6f1dded43341bd70c16ddf413cbaec`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:a70f5c34effd84c3fbdebb08f7c02886f19fea4ea5a96f7f4cadf1eef3d5c97b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:a70f5c34effd84c3fbdebb08f7c02886f19fea4ea5a96f7f4cadf1eef3d5c97b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:a70f5c34effd84c3fbdebb08f7c02886f19fea4ea5a96f7f4cadf1eef3d5c97b`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2946-L2950) — lines `2946–2950`; excerpt `sha256:fd3671803715497848f50b7e406b351a3c0b3100358db5c0e7912563aefc2384`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L27-L27) — lines `27–27`; excerpt `sha256:170789f848d7f281c8706ecc14826b85c56cbb95549d73fab6df1df6b540b6d0`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4949-L4953) — lines `4949–4953`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4918-L4922) — lines `4918–4922`; excerpt `sha256:c3bb3c4929a9278950209981b07b4c49dc93d8a276eb91c9c4a3e33a7142151e`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1100-L1103) — lines `1100–1103`; excerpt `sha256:62c7f30e6e69a9518a78ce54ec17705c85fe324ecc02ed5ab901a96123bb8909`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1042-L1044) — lines `1042–1044`; excerpt `sha256:1ac5357f10c02faa48f742246381cd200e43461ec7bf1ad931f1b9be3964b97b`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:105](../../paper/systems/claim-faithful-publication-systems-paper.tex#L105-L105), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:950](../../paper/systems/claim-faithful-publication-systems-paper.tex#L950-L950)
- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:64](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L64-L64)
- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1020](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1020-L1020)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:70](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L70-L70)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:590](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L590-L590)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1028](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1028-L1028)
- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:50](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L50-L50)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:92](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L92-L92), [cite at paper/reasoning-parts/erdos1041/core.tex:48](../../paper/reasoning-parts/erdos1041/core.tex#L48-L48)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:63](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L63-L63), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4701](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4701-L4701), [cite at paper/reasoning-parts/erdos1049/core.tex:32](../../paper/reasoning-parts/erdos1049/core.tex#L32-L32), [cite at paper/reasoning-parts/erdos1049/core.tex:4670](../../paper/reasoning-parts/erdos1049/core.tex#L4670-L4670)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:78](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L78-L78), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:814](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L814-L814), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3645](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3645-L3645), [cite at paper/reasoning-parts/erdos243/core.tex:39](../../paper/reasoning-parts/erdos243/core.tex#L39-L39), [cite at paper/reasoning-parts/erdos243/core.tex:775](../../paper/reasoning-parts/erdos243/core.tex#L775-L775), [cite at paper/reasoning-parts/erdos243/core.tex:3606](../../paper/reasoning-parts/erdos243/core.tex#L3606-L3606)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:197](../../paper/archive/erdos249-257-main-paper.tex#L197-L197), [cite at paper/archive/erdos249-257-main-paper.tex:4524](../../paper/archive/erdos249-257-main-paper.tex#L4524-L4524)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:65](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L65-L65), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2002](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2002-L2002), [cite at paper/reasoning-parts/erdos251/core.tex:24](../../paper/reasoning-parts/erdos251/core.tex#L24-L24), [cite at paper/reasoning-parts/erdos251/core.tex:1961](../../paper/reasoning-parts/erdos251/core.tex#L1961-L1961)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:105](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L105-L105), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3668](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3668-L3668), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3687](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3687-L3687), [cite at paper/reasoning-parts/erdos269/core.tex:54](../../paper/reasoning-parts/erdos269/core.tex#L54-L54), [cite at paper/reasoning-parts/erdos269/core.tex:3617](../../paper/reasoning-parts/erdos269/core.tex#L3617-L3617), [cite at paper/reasoning-parts/erdos269/core.tex:3636](../../paper/reasoning-parts/erdos269/core.tex#L3636-L3636)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:62](../../paper/68/erdos68-factorial-reasoning-surface.tex#L62-L62), [cite at paper/reasoning-parts/erdos68/core.tex:27](../../paper/reasoning-parts/erdos68/core.tex#L27-L27)
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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L918-L924) — lines `918–924`; excerpt `sha256:9b66ac2741824a4fb126ce6c85cdddc7806daa4534b4f393e06ebf1a210dbd9c`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5318-L5324) — lines `5318–5324`; excerpt `sha256:23a731c181be1a3d3f4f814b84774f68a8a5b6bcebb7b8717ac21e9917899da5`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5274-L5280) — lines `5274–5280`; excerpt `sha256:23a731c181be1a3d3f4f814b84774f68a8a5b6bcebb7b8717ac21e9917899da5`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:823](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L823-L823)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2276](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2276-L2276), [cite at paper/reasoning-parts/erdos1041/core.tex:2232](../../paper/reasoning-parts/erdos1041/core.tex#L2232-L2232)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L913-L918) — lines `913–918`; excerpt `sha256:a3161ac11344fd8199bdbbb63800da9443a64e2a1d3fdd2007366848b954d26f`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5313-L5318) — lines `5313–5318`; excerpt `sha256:2ca5100ac1e4e768257b05ac88a40e2a04ae625930bbba2c8e7c147703d176a6`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5269-L5274) — lines `5269–5274`; excerpt `sha256:2ca5100ac1e4e768257b05ac88a40e2a04ae625930bbba2c8e7c147703d176a6`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:822](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L822-L822)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2274](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2274-L2274), [cite at paper/reasoning-parts/erdos1041/core.tex:2230](../../paper/reasoning-parts/erdos1041/core.tex#L2230-L2230)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L909-L913) — lines `909–913`; excerpt `sha256:97ed6ed938a762a7aa078c24d5e27afbbef833b6e4baddc2c4ebde5eff3f4607`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5309-L5313) — lines `5309–5313`; excerpt `sha256:42b99f9986d17fa7c89618f299bdc5940ef3f67b0a8129937e2dcd5521a15379`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5265-L5269) — lines `5265–5269`; excerpt `sha256:42b99f9986d17fa7c89618f299bdc5940ef3f67b0a8129937e2dcd5521a15379`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:678](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L678-L678)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2259](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2259-L2259), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2267](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2267-L2267), [cite at paper/reasoning-parts/erdos1041/core.tex:2215](../../paper/reasoning-parts/erdos1041/core.tex#L2215-L2215), [cite at paper/reasoning-parts/erdos1041/core.tex:2223](../../paper/reasoning-parts/erdos1041/core.tex#L2223-L2223)

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
- Relationship and boundary: Direct paper citations exist for #243, #251, #269, #1049. Local compatibility declarations exist for #68, #249, #251, #257, #1049. No exact #1041 Formal Conjectures reuse/citation was found; absence is a coverage boundary, not negative authority.
- Source verification: `source\_verified` — The cited webpage/source identity, displayed authorship, date, and quoted claim were directly checked. This does not certify the mathematics or imply local adoption.
- Local mapping: `coverage\_audit` — Derived from exact cited paths and adapter declarations.

Exact source locations:

- [Repository-level formal statement corpus](https://github.com/google-deepmind/formal-conjectures)

Public implementation or evidence coordinates:

- [research/adapters/FormalConjecturesAdapter.lean](../../research/adapters/FormalConjecturesAdapter.lean#L10-L42) — lines `10–42`; excerpt `sha256:a09ac08e4260951af6627cc74ccc029207e6497eb1840a65bda22888010525ed`
- [lakefile.toml](../../lakefile.toml#L67-L79) — lines `67–79`; excerpt `sha256:831b7c7270f57c8606e4effd1314f87cfd4b9ad0eee57b89a546b5457b16aa78`

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
- [CITATION.cff](../../CITATION.cff#L174-L188) — lines `174–188`; excerpt `sha256:20ed248984e0372fbfcc616d3d61f895f70cb37bf9a5e14498b7618a6f5f137b`

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
- [CITATION.cff](../../CITATION.cff#L189-L193) — lines `189–193`; excerpt `sha256:b732cf902522394d45614cbb39c73530e2cde6315917ace5f34708b2e268bdb8`

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1243-L1248) — lines `1243–1248`; excerpt `sha256:ac245ce2f2ef2f2b58c37f9d6208461ebddbd9910d265d81108a7b2a80ee0c8d`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:864](../../paper/systems/claim-faithful-publication-systems-paper.tex#L864-L864)

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

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L879-L879) — lines `879–879`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1181-L1181) — lines `1181–1181`; excerpt `sha256:603c399e18eec54e4b76bcb455d51b93adf56ce7a26e699ca50aa8527aaa25fa`

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

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1116-L1116) — lines `1116–1116`; excerpt `sha256:bd3042b8bb213124b09edd0ae290bc793d67b690b4f3eaa43e75f1389ed209f9`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L257-L257) — lines `257–257`; excerpt `sha256:6c51e4cac6bf83888f322c8e9f4ef1bd38f2f03de7d73982b83ec5b7a1b72c1b`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1432-L1436) — lines `1432–1436`; excerpt `sha256:1d98da1cc9acba9dff63b689605b7402eee23c5f2cea8e887c7c18989b40d0d1`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L499-L499) — lines `499–499`; excerpt `sha256:1ed1ce69c8bf73f3362ff5a2aca04fe7d02e4cc4dbe0784bc0f09ca0a22ad778`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9502-L9511) — lines `9502–9511`; excerpt `sha256:29419ac25750a3ca44cb2c1c49ac4bd44f6206b9eff9cc840572a0d12a962f43`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9302-L9311) — lines `9302–9311`; excerpt `sha256:29419ac25750a3ca44cb2c1c49ac4bd44f6206b9eff9cc840572a0d12a962f43`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:378](../../paper/249/erdos-249-binary-totient-series.tex#L378-L378)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:257](../../paper/257/erdos-257-mersenne-support-subseries.tex#L257-L257)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:630](../../paper/249/erdos249-totient-reasoning-surface.tex#L630-L630), [cite at paper/249/erdos249-totient-reasoning-surface.tex:636](../../paper/249/erdos249-totient-reasoning-surface.tex#L636-L636), [cite at paper/249/erdos249-totient-reasoning-surface.tex:638](../../paper/249/erdos249-totient-reasoning-surface.tex#L638-L638), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:438](../../paper/reasoning-parts/erdos249/a249_front.tex#L438-L438), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:444](../../paper/reasoning-parts/erdos249/a249_front.tex#L444-L444), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:446](../../paper/reasoning-parts/erdos249/a249_front.tex#L446-L446)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:699](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L699-L699), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:499](../../paper/reasoning-parts/erdos257/a257_front.tex#L499-L499)

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

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7997-L7997) — lines `7997–7997`; excerpt `sha256:bad452dab3a80d026ba2b9d6aca2caf78d90b3a49add7f6d1955eef4c220342f`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10057-L10063) — lines `10057–10063`; excerpt `sha256:f37eea22c3c2e50c9106c29e8480d8c2ab20d0f3f59a7faec27317f14c9ea473`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9865-L9871) — lines `9865–9871`; excerpt `sha256:f37eea22c3c2e50c9106c29e8480d8c2ab20d0f3f59a7faec27317f14c9ea473`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10063-L10069) — lines `10063–10069`; excerpt `sha256:e35aaa04403be003a4b96499d83a53616643be3a1bc6ec591562551be6db9bf5`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9871-L9877) — lines `9871–9877`; excerpt `sha256:e35aaa04403be003a4b96499d83a53616643be3a1bc6ec591562551be6db9bf5`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10069-L10076) — lines `10069–10076`; excerpt `sha256:4ca7b4c0db1de3a40807dc6214421cb78ee688d52511a96a2204550ee24c19a4`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9877-L9884) — lines `9877–9884`; excerpt `sha256:4ca7b4c0db1de3a40807dc6214421cb78ee688d52511a96a2204550ee24c19a4`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9549-L9554) — lines `9549–9554`; excerpt `sha256:0b4989fd169ff765ea3d5b38ef8e6aea0f4cd59a60283d86861edd55ca023917`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9349-L9354) — lines `9349–9354`; excerpt `sha256:0b4989fd169ff765ea3d5b38ef8e6aea0f4cd59a60283d86861edd55ca023917`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8189](../../paper/249/erdos249-totient-reasoning-surface.tex#L8189-L8189), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8192](../../paper/249/erdos249-totient-reasoning-surface.tex#L8192-L8192), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8194](../../paper/249/erdos249-totient-reasoning-surface.tex#L8194-L8194), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7997](../../paper/reasoning-parts/erdos249/a249_front.tex#L7997-L7997), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8000](../../paper/reasoning-parts/erdos249/a249_front.tex#L8000-L8000), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8002](../../paper/reasoning-parts/erdos249/a249_front.tex#L8002-L8002)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7986](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7986-L7986), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7786](../../paper/reasoning-parts/erdos257/a257_front.tex#L7786-L7786)

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

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L81-L81) — lines `81–81`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L722-L728) — lines `722–728`; excerpt `sha256:a8cf6f2cdc8cb0b26a0a37cb8141e5828d7e67bf0a8de5e636412840e1a2f1b7`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10031-L10037) — lines `10031–10037`; excerpt `sha256:1e409fb0093faa23ebcc4e5651da0b5eac48a708ad25c90724afa7a140769712`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9839-L9845) — lines `9839–9845`; excerpt `sha256:1e409fb0093faa23ebcc4e5651da0b5eac48a708ad25c90724afa7a140769712`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:608](../../paper/249/erdos-249-binary-totient-series.tex#L608-L608)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9889](../../paper/249/erdos249-totient-reasoning-surface.tex#L9889-L9889), [cite at paper/249/erdos249-totient-reasoning-surface.tex:9891](../../paper/249/erdos249-totient-reasoning-surface.tex#L9891-L9891), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9697](../../paper/reasoning-parts/erdos249/a249_front.tex#L9697-L9697), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9699](../../paper/reasoning-parts/erdos249/a249_front.tex#L9699-L9699)

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

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L7786-L7786) — lines `7786–7786`; excerpt `sha256:d50e57ea55fd331cc5fcd2f60b7cbbe4f74bdfad5ed5d507e3e2607f34a7aae6`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9554-L9558) — lines `9554–9558`; excerpt `sha256:c5c4489e4688d8773d399bf748456a2ae9b05460c54f6faafd532fa836da5957`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9354-L9358) — lines `9354–9358`; excerpt `sha256:c5c4489e4688d8773d399bf748456a2ae9b05460c54f6faafd532fa836da5957`

Paper citation usages:

- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7988](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7988-L7988), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7788](../../paper/reasoning-parts/erdos257/a257_front.tex#L7788-L7788)

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

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L7786-L7786) — lines `7786–7786`; excerpt `sha256:d50e57ea55fd331cc5fcd2f60b7cbbe4f74bdfad5ed5d507e3e2607f34a7aae6`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9558-L9562) — lines `9558–9562`; excerpt `sha256:6d0851d07c69f2ae700a812b4b5fc31762d09234debac02cca0ca4ff63212261`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9358-L9362) — lines `9358–9362`; excerpt `sha256:6d0851d07c69f2ae700a812b4b5fc31762d09234debac02cca0ca4ff63212261`

Paper citation usages:

- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7990](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7990-L7990), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7790](../../paper/reasoning-parts/erdos257/a257_front.tex#L7790-L7790)

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

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7729-L7729) — lines `7729–7729`; excerpt `sha256:df8b5a08361a8b2709dbfbc190e9e72f41b2ef5c5874a6274b6c15c70054b621`

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

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L8172-L8172) — lines `8172–8172`; excerpt `sha256:be78c26f277d33338d36a1396ef173f2016a8d8cd7654b87697206f4f4ceb081`

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1096-L1098) — lines `1096–1098`; excerpt `sha256:deb96a200b13f5e87c5d0fd551fcbcf9b199c27d94d72de6039982177c546346`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:356](../../paper/systems/claim-faithful-publication-systems-paper.tex#L356-L356)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1098-L1100) — lines `1098–1100`; excerpt `sha256:a524c5a22e5fbacade3320260e08f8d57395a112937206a765495b6dfc73eafb`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:356](../../paper/systems/claim-faithful-publication-systems-paper.tex#L356-L356)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3081-L3085) — lines `3081–3085`; excerpt `sha256:bddcb7495409ba674f37573e14998a223896847e01c9d7d112a430f0cca41d03`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3046-L3050) — lines `3046–3050`; excerpt `sha256:bddcb7495409ba674f37573e14998a223896847e01c9d7d112a430f0cca41d03`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1740](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1740-L1740), [cite at paper/reasoning-parts/erdos68/core.tex:1705](../../paper/reasoning-parts/erdos68/core.tex#L1705-L1705)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3069-L3073) — lines `3069–3073`; excerpt `sha256:a14aa06f222d10c851dd2bfa10beea5352390803145dcffcbdd0759d84e41498`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3034-L3038) — lines `3034–3038`; excerpt `sha256:a14aa06f222d10c851dd2bfa10beea5352390803145dcffcbdd0759d84e41498`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1750](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1750-L1750), [cite at paper/reasoning-parts/erdos68/core.tex:1715](../../paper/reasoning-parts/erdos68/core.tex#L1715-L1715)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4256-L4259) — lines `4256–4259`; excerpt `sha256:0db3df8cac9eaa008e4ba1fc69bf370097ffa91fb0e512033da28a1cab6e2dbc`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4205-L4208) — lines `4205–4208`; excerpt `sha256:0db3df8cac9eaa008e4ba1fc69bf370097ffa91fb0e512033da28a1cab6e2dbc`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L149-L149) — lines `149–149`; excerpt `sha256:a48dbfded735816b42a100262684c9bca03496f8812e5b3646266716ccf5cc33`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:200](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L200-L200), [cite at paper/reasoning-parts/erdos269/core.tex:149](../../paper/reasoning-parts/erdos269/core.tex#L149-L149)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4888-L4897) — lines `4888–4897`; excerpt `sha256:559ea13819baf75b04cc9d7303f6c7c0c031c962cc19c07bc95ad20eac0a8832`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4857-L4866) — lines `4857–4866`; excerpt `sha256:559ea13819baf75b04cc9d7303f6c7c0c031c962cc19c07bc95ad20eac0a8832`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4330-L4330) — lines `4330–4330`; excerpt `sha256:255e468ab972fcdcc21a815a58d107099746c2882b841d319f2239751a44e4fe`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4361](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4361-L4361), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4767](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4767-L4767), [cite at paper/reasoning-parts/erdos1049/core.tex:4330](../../paper/reasoning-parts/erdos1049/core.tex#L4330-L4330), [cite at paper/reasoning-parts/erdos1049/core.tex:4736](../../paper/reasoning-parts/erdos1049/core.tex#L4736-L4736)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L616-L618) — lines `616–618`; excerpt `sha256:d266a1d3a0fa072bc043987dc7748df23076e1f5a520e7d5041e49ad2509fad6`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2434-L2434) — lines `2434–2434`; excerpt `sha256:19cfb014840fa377aa38df9849019ad015dd70327f7bf8e708af471ac52e8466`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2393-L2393) — lines `2393–2393`; excerpt `sha256:19cfb014840fa377aa38df9849019ad015dd70327f7bf8e708af471ac52e8466`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2911-L2913) — lines `2911–2913`; excerpt `sha256:b7e63e9f291863fbd6b9fd3c4dc4951de337b3fe54505a8871c92d96d21d90a9`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2870-L2872) — lines `2870–2872`; excerpt `sha256:b7e63e9f291863fbd6b9fd3c4dc4951de337b3fe54505a8871c92d96d21d90a9`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:300](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L300-L300)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:670](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L670-L670), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1401](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1401-L1401), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1466](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1466-L1466), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2141](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2141-L2141), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2434](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2434-L2434), [cite at paper/reasoning-parts/erdos251/core.tex:629](../../paper/reasoning-parts/erdos251/core.tex#L629-L629), [cite at paper/reasoning-parts/erdos251/core.tex:1360](../../paper/reasoning-parts/erdos251/core.tex#L1360-L1360), [cite at paper/reasoning-parts/erdos251/core.tex:1425](../../paper/reasoning-parts/erdos251/core.tex#L1425-L1425), [cite at paper/reasoning-parts/erdos251/core.tex:2100](../../paper/reasoning-parts/erdos251/core.tex#L2100-L2100), [cite at paper/reasoning-parts/erdos251/core.tex:2393](../../paper/reasoning-parts/erdos251/core.tex#L2393-L2393)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5400-L5409) — lines `5400–5409`; excerpt `sha256:94ae85ad39b40622ea590cddfc409ecb93f19d077df9ec9c6ab543560d0d1a1a`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L879-L879) — lines `879–879`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2250](../../paper/archive/erdos249-257-main-paper.tex#L2250-L2250)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5305-L5309) — lines `5305–5309`; excerpt `sha256:7968722d9338768846f85bc2ef2063b55804e78527ad41a2e77023c434d04535`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5261-L5265) — lines `5261–5265`; excerpt `sha256:7968722d9338768846f85bc2ef2063b55804e78527ad41a2e77023c434d04535`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1579-L1579) — lines `1579–1579`; excerpt `sha256:adaee106fc9f14bfa32c5f6ab3ba20afe848ed080f83389485ba7fbd8b3be932`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1623](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1623-L1623), [cite at paper/reasoning-parts/erdos1041/core.tex:1579](../../paper/reasoning-parts/erdos1041/core.tex#L1579-L1579)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10047-L10051) — lines `10047–10051`; excerpt `sha256:2ffe3c91d993950605f8bf070b0a5a11ffc1f8ef39055137701039e8577a8e67`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9855-L9859) — lines `9855–9859`; excerpt `sha256:2ffe3c91d993950605f8bf070b0a5a11ffc1f8ef39055137701039e8577a8e67`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8034](../../paper/249/erdos249-totient-reasoning-surface.tex#L8034-L8034), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7842](../../paper/reasoning-parts/erdos249/a249_front.tex#L7842-L7842)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L424-L427) — lines `424–427`; excerpt `sha256:de76425fbfedc49c7c1333d6ff6b6755d0f608d87b83bcebc6b9c6d27c0db50d`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2925-L2927) — lines `2925–2927`; excerpt `sha256:1565fef6512ed60adfcce853ce390a078eea05be1ecd50bcf8d12b0b2b596645`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2884-L2886) — lines `2884–2886`; excerpt `sha256:1565fef6512ed60adfcce853ce390a078eea05be1ecd50bcf8d12b0b2b596645`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L385-L385) — lines `385–385`; excerpt `sha256:f0be293a894eaec58b1c7ed38efb4953996ef87f9ac22c7627561bf7e65657c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L385-L385) — lines `385–385`; excerpt `sha256:f0be293a894eaec58b1c7ed38efb4953996ef87f9ac22c7627561bf7e65657c8`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:426](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L426-L426), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1769](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1769-L1769), [cite at paper/reasoning-parts/erdos251/core.tex:385](../../paper/reasoning-parts/erdos251/core.tex#L385-L385), [cite at paper/reasoning-parts/erdos251/core.tex:1728](../../paper/reasoning-parts/erdos251/core.tex#L1728-L1728)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5335-L5338) — lines `5335–5338`; excerpt `sha256:888488ef48fd0e622a7a10d9a3365f11c2438983c6865da31232ee81ad07c437`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1112-L1112) — lines `1112–1112`; excerpt `sha256:2f13d854d17862e3e84cfe8260e36f3e508b7165189455204d23c133aeac237e`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:5071](../../paper/archive/erdos249-257-main-paper.tex#L5071-L5071), [cite at paper/archive/erdos249-257-main-paper.tex:5111](../../paper/archive/erdos249-257-main-paper.tex#L5111-L5111)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1282-L1288) — lines `1282–1288`; excerpt `sha256:c6ad3b74ba433b2451bb8a22ac558445aec5cb56ecfef0b9118236d8dbc841ac`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4058-L4064) — lines `4058–4064`; excerpt `sha256:c6ad3b74ba433b2451bb8a22ac558445aec5cb56ecfef0b9118236d8dbc841ac`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4019-L4025) — lines `4019–4025`; excerpt `sha256:c6ad3b74ba433b2451bb8a22ac558445aec5cb56ecfef0b9118236d8dbc841ac`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:841](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L841-L841)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:874](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L874-L874), [cite at paper/reasoning-parts/erdos243/core.tex:835](../../paper/reasoning-parts/erdos243/core.tex#L835-L835)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3021-L3025) — lines `3021–3025`; excerpt `sha256:de382823fb7376836cf48c1a4705162b30877bceecea105e5ba9fd991dc8dcc9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2986-L2990) — lines `2986–2990`; excerpt `sha256:de382823fb7376836cf48c1a4705162b30877bceecea105e5ba9fd991dc8dcc9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2012-L2012) — lines `2012–2012`; excerpt `sha256:c6c8cf9b68fb541c95c305abe93492fb959422799957e770844d1c594c99ab29`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2012-L2012) — lines `2012–2012`; excerpt `sha256:c6c8cf9b68fb541c95c305abe93492fb959422799957e770844d1c594c99ab29`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2012-L2012) — lines `2012–2012`; excerpt `sha256:c6c8cf9b68fb541c95c305abe93492fb959422799957e770844d1c594c99ab29`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2047](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2047-L2047), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2446](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2446-L2446), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2458](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2458-L2458), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2460](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2460-L2460), [cite at paper/reasoning-parts/erdos68/core.tex:2012](../../paper/reasoning-parts/erdos68/core.tex#L2012-L2012), [cite at paper/reasoning-parts/erdos68/core.tex:2411](../../paper/reasoning-parts/erdos68/core.tex#L2411-L2411), [cite at paper/reasoning-parts/erdos68/core.tex:2423](../../paper/reasoning-parts/erdos68/core.tex#L2423-L2423), [cite at paper/reasoning-parts/erdos68/core.tex:2425](../../paper/reasoning-parts/erdos68/core.tex#L2425-L2425)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5008-L5011) — lines `5008–5011`; excerpt `sha256:e321a18827767ed58cdd1dd982eeeb9a39803cd37871901a8449163cbd346499`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4977-L4980) — lines `4977–4980`; excerpt `sha256:e321a18827767ed58cdd1dd982eeeb9a39803cd37871901a8449163cbd346499`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2603](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2603-L2603), [cite at paper/reasoning-parts/erdos1049/core.tex:2572](../../paper/reasoning-parts/erdos1049/core.tex#L2572-L2572)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L703-L707) — lines `703–707`; excerpt `sha256:117bd3171f2e021774f4f9022ede7b0664bac13a6e9e4ac082ac520ce020f436`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9962-L9966) — lines `9962–9966`; excerpt `sha256:fb74fd71f49bc3b483f5ac1feed5de8f28b2cb86a5c35567b0628c644acf4527`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9770-L9774) — lines `9770–9774`; excerpt `sha256:fb74fd71f49bc3b483f5ac1feed5de8f28b2cb86a5c35567b0628c644acf4527`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:381](../../paper/249/erdos-249-binary-totient-series.tex#L381-L381)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:642](../../paper/249/erdos249-totient-reasoning-surface.tex#L642-L642), [cite at paper/249/erdos249-totient-reasoning-surface.tex:9877](../../paper/249/erdos249-totient-reasoning-surface.tex#L9877-L9877), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:450](../../paper/reasoning-parts/erdos249/a249_front.tex#L450-L450), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9685](../../paper/reasoning-parts/erdos249/a249_front.tex#L9685-L9685)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5315-L5318) — lines `5315–5318`; excerpt `sha256:89ad0eb6d9dac773cb478c008d67b4ac6ad8b50cdf587f23feda6a8d1825acf6`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1239-L1243) — lines `1239–1243`; excerpt `sha256:8d04873393ce01957978e7bf822e3411f2a23947e1a44f04f81a2db2f17c6332`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3999-L4003) — lines `3999–4003`; excerpt `sha256:8d04873393ce01957978e7bf822e3411f2a23947e1a44f04f81a2db2f17c6332`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L719-L722) — lines `719–722`; excerpt `sha256:e79adb56b67cd11616132762fbeadb6b20811b0217440e25c49e7a4f695da264`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L596-L598) — lines `596–598`; excerpt `sha256:22cefc7058ffe04e57c206b77700b9b9eb94a7db94b2cb2d8367e3e36b8da144`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2881-L2883) — lines `2881–2883`; excerpt `sha256:44c67147da17a5a42fe794398401c5f1d3beb10fb6f1b30933e004aa1a164fd5`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4219-L4222) — lines `4219–4222`; excerpt `sha256:8466f5a9dd4ced1a4f291d5d67e847f3b2fca1cf34f259ca712ff23fe61bbc42`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1034-L1037) — lines `1034–1037`; excerpt `sha256:8466f5a9dd4ced1a4f291d5d67e847f3b2fca1cf34f259ca712ff23fe61bbc42`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3960-L3964) — lines `3960–3964`; excerpt `sha256:8d04873393ce01957978e7bf822e3411f2a23947e1a44f04f81a2db2f17c6332`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L37-L37) — lines `37–37`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2840-L2842) — lines `2840–2842`; excerpt `sha256:44c67147da17a5a42fe794398401c5f1d3beb10fb6f1b30933e004aa1a164fd5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L25-L25) — lines `25–25`; excerpt `sha256:9ac9f5c746a4ed69413e2f364cc0753ee3aa969eb39b5d87a0c1c8e8d6797e46`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4168-L4171) — lines `4168–4171`; excerpt `sha256:8466f5a9dd4ced1a4f291d5d67e847f3b2fca1cf34f259ca712ff23fe61bbc42`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L53-L53) — lines `53–53`; excerpt `sha256:89b37a0d3340796c5590d761a39d83444f6987ea56bf2f2eaf180f3f1f9e9178`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9984-L9988) — lines `9984–9988`; excerpt `sha256:727de5144fdf771c479a2e03e7b875cffecf9400543450974b25f25aced90f03`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9792-L9796) — lines `9792–9796`; excerpt `sha256:727de5144fdf771c479a2e03e7b875cffecf9400543450974b25f25aced90f03`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1074-L1077) — lines `1074–1077`; excerpt `sha256:1b937681bd73e372ca1eb2a058ee0578cb99d388132d9fdc186e9ec9fc03e58b`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:942](../../paper/systems/claim-faithful-publication-systems-paper.tex#L942-L942)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:68](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L68-L68)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:119](../../paper/249/erdos-249-binary-totient-series.tex#L119-L119)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:46](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L46-L46)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:93](../../paper/269/erdos-269-three-prime-running-lcm.tex#L93-L93)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:76](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L76-L76), [cite at paper/reasoning-parts/erdos243/core.tex:37](../../paper/reasoning-parts/erdos243/core.tex#L37-L37)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:193](../../paper/archive/erdos249-257-main-paper.tex#L193-L193), [cite at paper/archive/erdos249-257-main-paper.tex:194](../../paper/archive/erdos249-257-main-paper.tex#L194-L194)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:273](../../paper/249/erdos249-totient-reasoning-surface.tex#L273-L273), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:81](../../paper/reasoning-parts/erdos249/a249_front.tex#L81-L81)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:66](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L66-L66), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:448](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L448-L448), [cite at paper/reasoning-parts/erdos251/core.tex:25](../../paper/reasoning-parts/erdos251/core.tex#L25-L25), [cite at paper/reasoning-parts/erdos251/core.tex:407](../../paper/reasoning-parts/erdos251/core.tex#L407-L407)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:104](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L104-L104), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3715](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3715-L3715), [cite at paper/reasoning-parts/erdos269/core.tex:53](../../paper/reasoning-parts/erdos269/core.tex#L53-L53), [cite at paper/reasoning-parts/erdos269/core.tex:3664](../../paper/reasoning-parts/erdos269/core.tex#L3664-L3664)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:72](../../paper/synthesis/optimal-sparse-perturbations.tex#L72-L72), [cite at paper/synthesis/optimal-sparse-perturbations.tex:858](../../paper/synthesis/optimal-sparse-perturbations.tex#L858-L858)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L699-L703) — lines `699–703`; excerpt `sha256:5c07b90db96e384410ed6cbfa6f0a0260dd341520e919d4e5654581d25bb3b5c`
- [lean/Erdos249257/AllBaseTotientKernel.lean](../../lean/Erdos249257/AllBaseTotientKernel.lean#L4-L61) — lines `4–61`; excerpt `sha256:a7583f78b57fbb25305024044671d8303e0dfd61da003f0de23f3c82ca558fb4`
- [lean/Erdos249257/AllBaseTotientKernel.lean](../../lean/Erdos249257/AllBaseTotientKernel.lean#L642-L644) — lines `642–644`; excerpt `sha256:f2847f43a004d01715e61f5510732df2e0014e197cb1796803035180a98f88f6`
- [lean/Erdos249257/TotientKernelConditional.lean](../../lean/Erdos249257/TotientKernelConditional.lean#L5-L18) — lines `5–18`; excerpt `sha256:bb1cbd9adcabf879040179a1dda4145da0903770eb95510584365a88131340ba`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L88-L88) — lines `88–88`; excerpt `sha256:0b9c9251af21e6eeb9177cb4f168d77d98fe8e2be6e6f70f8029efd8b0ef9375`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9958-L9962) — lines `9958–9962`; excerpt `sha256:c97e654465265fb62b6de801d7921a842ace01171d8790c26144b859fefa809c`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9766-L9770) — lines `9766–9770`; excerpt `sha256:c97e654465265fb62b6de801d7921a842ace01171d8790c26144b859fefa809c`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:928](../../paper/systems/claim-faithful-publication-systems-paper.tex#L928-L928)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:103](../../paper/249/erdos-249-binary-totient-series.tex#L103-L103), [cite at paper/249/erdos-249-binary-totient-series.tex:282](../../paper/249/erdos-249-binary-totient-series.tex#L282-L282), [cite at paper/249/erdos-249-binary-totient-series.tex:634](../../paper/249/erdos-249-binary-totient-series.tex#L634-L634)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:280](../../paper/249/erdos249-totient-reasoning-surface.tex#L280-L280), [cite at paper/249/erdos249-totient-reasoning-surface.tex:6826](../../paper/249/erdos249-totient-reasoning-surface.tex#L6826-L6826), [cite at paper/249/erdos249-totient-reasoning-surface.tex:6921](../../paper/249/erdos249-totient-reasoning-surface.tex#L6921-L6921), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:88](../../paper/reasoning-parts/erdos249/a249_front.tex#L88-L88), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6634](../../paper/reasoning-parts/erdos249/a249_front.tex#L6634-L6634), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6729](../../paper/reasoning-parts/erdos249/a249_front.tex#L6729-L6729)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1041-L1047) — lines `1041–1047`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4836-L4842) — lines `4836–4842`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4805-L4811) — lines `4805–4811`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36) — lines `36–36`; excerpt `sha256:19cf4ce893b8009053c16f93767c730c7f1c57ac0b5342be1c68f24283b43d3d`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L879-L879) — lines `879–879`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1181-L1181) — lines `1181–1181`; excerpt `sha256:603c399e18eec54e4b76bcb455d51b93adf56ce7a26e699ca50aa8527aaa25fa`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L8-L36) — lines `8–36`; excerpt `sha256:580a0329d38f93ac21807ae3e4b5576bc7cc0a60f32dc890b169224bff93a983`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L121-L143) — lines `121–143`; excerpt `sha256:9cbb2521fc20ab9b5f2b1ef19d400d7a4706ab42e437b60f3d445f245666ebab`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L312-L317) — lines `312–317`; excerpt `sha256:9d8f3b2b1f69665003c2e2e1011aa3ab2153e1279df369928b397383f2c62c70`
- [lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean](../../lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L8-L15) — lines `8–15`; excerpt `sha256:944f0e0e804396ce17b086bb0755d7c33ca82e608e624be2a2542fcd18124e82`
- [lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean](../../lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L72-L79) — lines `72–79`; excerpt `sha256:519814e5b5744e92c8a9dc9ac2c0c0fd009c2f4c5e71df7e3e2af9a3034f730a`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9537-L9543) — lines `9537–9543`; excerpt `sha256:b26157f8e2462fe6a9cb317178ca1aa00c80c57d6b9c2a7ae528d32e670113ad`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9337-L9343) — lines `9337–9343`; excerpt `sha256:b26157f8e2462fe6a9cb317178ca1aa00c80c57d6b9c2a7ae528d32e670113ad`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:148](../../paper/1049/erdos-1049-rational-base-lambert.tex#L148-L148), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:511](../../paper/1049/erdos-1049-rational-base-lambert.tex#L511-L511), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:514](../../paper/1049/erdos-1049-rational-base-lambert.tex#L514-L514), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:565](../../paper/1049/erdos-1049-rational-base-lambert.tex#L565-L565), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:596](../../paper/1049/erdos-1049-rational-base-lambert.tex#L596-L596), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:608](../../paper/1049/erdos-1049-rational-base-lambert.tex#L608-L608), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:618](../../paper/1049/erdos-1049-rational-base-lambert.tex#L618-L618), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:624](../../paper/1049/erdos-1049-rational-base-lambert.tex#L624-L624), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:696](../../paper/1049/erdos-1049-rational-base-lambert.tex#L696-L696), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:801](../../paper/1049/erdos-1049-rational-base-lambert.tex#L801-L801), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:882](../../paper/1049/erdos-1049-rational-base-lambert.tex#L882-L882)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:67](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L67-L67), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:164](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L164-L164), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:196](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L196-L196), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:207](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L207-L207), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:241](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L241-L241), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:263](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L263-L263), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:288](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L288-L288), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:302](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L302-L302), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:305](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L305-L305), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:338](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L338-L338), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:478](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L478-L478), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:513](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L513-L514), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:835](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L835-L835), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:848](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L848-L848), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1138](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1138-L1138), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1147](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1147-L1147), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1278](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1278-L1278), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2971](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2971-L2971), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3132](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3132-L3132), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3457](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3457-L3457), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4640](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4640-L4640), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4682](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4682-L4682), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4726](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4726-L4726), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4727](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4727-L4727), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4732](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4732-L4732), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4887](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4887-L4887), [cite at paper/reasoning-parts/erdos1049/core.tex:36](../../paper/reasoning-parts/erdos1049/core.tex#L36-L36), [cite at paper/reasoning-parts/erdos1049/core.tex:133](../../paper/reasoning-parts/erdos1049/core.tex#L133-L133), [cite at paper/reasoning-parts/erdos1049/core.tex:165](../../paper/reasoning-parts/erdos1049/core.tex#L165-L165), [cite at paper/reasoning-parts/erdos1049/core.tex:176](../../paper/reasoning-parts/erdos1049/core.tex#L176-L176), [cite at paper/reasoning-parts/erdos1049/core.tex:210](../../paper/reasoning-parts/erdos1049/core.tex#L210-L210), [cite at paper/reasoning-parts/erdos1049/core.tex:232](../../paper/reasoning-parts/erdos1049/core.tex#L232-L232), [cite at paper/reasoning-parts/erdos1049/core.tex:257](../../paper/reasoning-parts/erdos1049/core.tex#L257-L257), [cite at paper/reasoning-parts/erdos1049/core.tex:271](../../paper/reasoning-parts/erdos1049/core.tex#L271-L271), [cite at paper/reasoning-parts/erdos1049/core.tex:274](../../paper/reasoning-parts/erdos1049/core.tex#L274-L274), [cite at paper/reasoning-parts/erdos1049/core.tex:307](../../paper/reasoning-parts/erdos1049/core.tex#L307-L307), [cite at paper/reasoning-parts/erdos1049/core.tex:447](../../paper/reasoning-parts/erdos1049/core.tex#L447-L447), [cite at paper/reasoning-parts/erdos1049/core.tex:482](../../paper/reasoning-parts/erdos1049/core.tex#L482-L483), [cite at paper/reasoning-parts/erdos1049/core.tex:804](../../paper/reasoning-parts/erdos1049/core.tex#L804-L804), [cite at paper/reasoning-parts/erdos1049/core.tex:817](../../paper/reasoning-parts/erdos1049/core.tex#L817-L817), [cite at paper/reasoning-parts/erdos1049/core.tex:1107](../../paper/reasoning-parts/erdos1049/core.tex#L1107-L1107), [cite at paper/reasoning-parts/erdos1049/core.tex:1116](../../paper/reasoning-parts/erdos1049/core.tex#L1116-L1116), [cite at paper/reasoning-parts/erdos1049/core.tex:1247](../../paper/reasoning-parts/erdos1049/core.tex#L1247-L1247), [cite at paper/reasoning-parts/erdos1049/core.tex:2940](../../paper/reasoning-parts/erdos1049/core.tex#L2940-L2940), [cite at paper/reasoning-parts/erdos1049/core.tex:3101](../../paper/reasoning-parts/erdos1049/core.tex#L3101-L3101), [cite at paper/reasoning-parts/erdos1049/core.tex:3426](../../paper/reasoning-parts/erdos1049/core.tex#L3426-L3426), [cite at paper/reasoning-parts/erdos1049/core.tex:4609](../../paper/reasoning-parts/erdos1049/core.tex#L4609-L4609), [cite at paper/reasoning-parts/erdos1049/core.tex:4651](../../paper/reasoning-parts/erdos1049/core.tex#L4651-L4651), [cite at paper/reasoning-parts/erdos1049/core.tex:4695](../../paper/reasoning-parts/erdos1049/core.tex#L4695-L4695), [cite at paper/reasoning-parts/erdos1049/core.tex:4696](../../paper/reasoning-parts/erdos1049/core.tex#L4696-L4696), [cite at paper/reasoning-parts/erdos1049/core.tex:4701](../../paper/reasoning-parts/erdos1049/core.tex#L4701-L4701), [cite at paper/reasoning-parts/erdos1049/core.tex:4856](../../paper/reasoning-parts/erdos1049/core.tex#L4856-L4856)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1381](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1381-L1381), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7323](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7323-L7323), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1181](../../paper/reasoning-parts/erdos257/a257_front.tex#L1181-L1181), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7123](../../paper/reasoning-parts/erdos257/a257_front.tex#L7123-L7123)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:949](../../paper/synthesis/optimal-sparse-perturbations.tex#L949-L949)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4874-L4881) — lines `4874–4881`; excerpt `sha256:2e85c59828644ad3c8fb345c8b459c4f9c86946c02a53b466028be600adf3dcf`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4843-L4850) — lines `4843–4850`; excerpt `sha256:2e85c59828644ad3c8fb345c8b459c4f9c86946c02a53b466028be600adf3dcf`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L799-L799) — lines `799–799`; excerpt `sha256:fbce7f2db65bdd8d9f109301fb1bc86d09291626cd9714baf8b44fb0defea1c4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L799-L799) — lines `799–799`; excerpt `sha256:fbce7f2db65bdd8d9f109301fb1bc86d09291626cd9714baf8b44fb0defea1c4`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:830](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L830-L830), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4677](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4677-L4677), [cite at paper/reasoning-parts/erdos1049/core.tex:799](../../paper/reasoning-parts/erdos1049/core.tex#L799-L799), [cite at paper/reasoning-parts/erdos1049/core.tex:4646](../../paper/reasoning-parts/erdos1049/core.tex#L4646-L4646)

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

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4043-L4048) — lines `4043–4048`; excerpt `sha256:1aefcf6f7f768fe29af3e6054e3b0cd92df53c67a5b2082873142c699135431c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4004-L4009) — lines `4004–4009`; excerpt `sha256:1aefcf6f7f768fe29af3e6054e3b0cd92df53c67a5b2082873142c699135431c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L940-L940) — lines `940–940`; excerpt `sha256:adfa536049be0e74065800037ce0ba5a0d022d83f1cf5dfdd9d4c0dda34e205f`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L979-L979) — lines `979–979`; excerpt `sha256:adfa536049be0e74065800037ce0ba5a0d022d83f1cf5dfdd9d4c0dda34e205f`

Paper citation usages:

- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:979](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L979-L979), [cite at paper/reasoning-parts/erdos243/core.tex:940](../../paper/reasoning-parts/erdos243/core.tex#L940-L940)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4897-L4902) — lines `4897–4902`; excerpt `sha256:b75b67635c18f80de0c876644a0d855886ffebd57e78291c56d2b76c6f5fe91f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4866-L4871) — lines `4866–4871`; excerpt `sha256:b75b67635c18f80de0c876644a0d855886ffebd57e78291c56d2b76c6f5fe91f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L3096-L3096) — lines `3096–3096`; excerpt `sha256:7d171ed1577013457353cdde13d778d34a71fbed4c861b7ce3d975c634196d90`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L3096-L3096) — lines `3096–3096`; excerpt `sha256:7d171ed1577013457353cdde13d778d34a71fbed4c861b7ce3d975c634196d90`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3127](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3127-L3127), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4645](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4645-L4645), [cite at paper/reasoning-parts/erdos1049/core.tex:3096](../../paper/reasoning-parts/erdos1049/core.tex#L3096-L3096), [cite at paper/reasoning-parts/erdos1049/core.tex:4614](../../paper/reasoning-parts/erdos1049/core.tex#L4614-L4614)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1062-L1065) — lines `1062–1065`; excerpt `sha256:102b617cbf408f358626ce785399d55baf63d64228a12995ce76a5747cad8bfb`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4278-L4281) — lines `4278–4281`; excerpt `sha256:d7d4cedfe807acd8fbf6994b4c4ea185099dead717184730b0485ff8e4adf7fe`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4227-L4230) — lines `4227–4230`; excerpt `sha256:d7d4cedfe807acd8fbf6994b4c4ea185099dead717184730b0485ff8e4adf7fe`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:354](../../paper/269/erdos-269-three-prime-running-lcm.tex#L354-L354), [cite at paper/269/erdos-269-three-prime-running-lcm.tex:587](../../paper/269/erdos-269-three-prime-running-lcm.tex#L587-L587)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:910](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L910-L910), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2393](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2393-L2393), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3734](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3734-L3734), [cite at paper/reasoning-parts/erdos269/core.tex:859](../../paper/reasoning-parts/erdos269/core.tex#L859-L859), [cite at paper/reasoning-parts/erdos269/core.tex:2342](../../paper/reasoning-parts/erdos269/core.tex#L2342-L2342), [cite at paper/reasoning-parts/erdos269/core.tex:3683](../../paper/reasoning-parts/erdos269/core.tex#L3683-L3683)

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

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4030-L4034) — lines `4030–4034`; excerpt `sha256:d1521927de67d3175dadffc4db2ca2b2786b8297ec43e4eec74b73a350d2d98c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3991-L3995) — lines `3991–3995`; excerpt `sha256:d1521927de67d3175dadffc4db2ca2b2786b8297ec43e4eec74b73a350d2d98c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2791-L2791) — lines `2791–2791`; excerpt `sha256:7031adbd8ee1ddab8aa252c4d2184fcfd608e6225a7ebbe27418145af8fd95d2`

Paper citation usages:

- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2830](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2830-L2830), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2834](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2834-L2834), [cite at paper/reasoning-parts/erdos243/core.tex:2791](../../paper/reasoning-parts/erdos243/core.tex#L2791-L2791), [cite at paper/reasoning-parts/erdos243/core.tex:2795](../../paper/reasoning-parts/erdos243/core.tex#L2795-L2795)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2887-L2889) — lines `2887–2889`; excerpt `sha256:e12f144375e5514cf3ca5b5c578990d0af610fa16c55c2bbfa94d6d3dc603533`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2846-L2848) — lines `2846–2848`; excerpt `sha256:e12f144375e5514cf3ca5b5c578990d0af610fa16c55c2bbfa94d6d3dc603533`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L630-L632) — lines `630–632`; excerpt `sha256:9f99ab4abb9eff1473257f6e3d761345f3ec4a6ed070161011aa5016e99df64b`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:245](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L245-L245)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2013](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2013-L2013), [cite at paper/reasoning-parts/erdos251/core.tex:1972](../../paper/reasoning-parts/erdos251/core.tex#L1972-L1972)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2923-L2925) — lines `2923–2925`; excerpt `sha256:2f37d7491f7db374d77d7036431632eaee02b51bfb55b4e5580d8a6e1a5e5239`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2882-L2884) — lines `2882–2884`; excerpt `sha256:2f37d7491f7db374d77d7036431632eaee02b51bfb55b4e5580d8a6e1a5e5239`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L322-L322) — lines `322–322`; excerpt `sha256:febeb70c1e1d0e553f1814d889d3b740a8e14147b23351b3b5af7b4df8b9ffd3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L322-L322) — lines `322–322`; excerpt `sha256:febeb70c1e1d0e553f1814d889d3b740a8e14147b23351b3b5af7b4df8b9ffd3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1912-L1912) — lines `1912–1912`; excerpt `sha256:12505b93fd9fe42cc2789467c5e348722fb0f6684320328f30690cdcc31c269c`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L622-L624) — lines `622–624`; excerpt `sha256:3221315fa09146b40ebe5676dd2da36df0ffdcf48a5f7e9dafca3ccc5ff205c8`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:348](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L348-L348)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:363](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L363-L363), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1954](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1954-L1954), [cite at paper/reasoning-parts/erdos251/core.tex:322](../../paper/reasoning-parts/erdos251/core.tex#L322-L322), [cite at paper/reasoning-parts/erdos251/core.tex:1913](../../paper/reasoning-parts/erdos251/core.tex#L1913-L1913)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4272-L4275) — lines `4272–4275`; excerpt `sha256:1e613e1240ad72300abf67c0d0bb0f8876f0fc68cf51b5a579626af38b8177e5`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1052-L1055) — lines `1052–1055`; excerpt `sha256:38d333be83004c73220542c256f0931ce00bb2390b3a5378c76418f76b198689`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4221-L4224) — lines `4221–4224`; excerpt `sha256:1e613e1240ad72300abf67c0d0bb0f8876f0fc68cf51b5a579626af38b8177e5`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L90-L90) — lines `90–90`; excerpt `sha256:af947109aab559bea882df279e8e9f19ecaf9561d6fded648d1ef904f80ea733`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L90-L90) — lines `90–90`; excerpt `sha256:af947109aab559bea882df279e8e9f19ecaf9561d6fded648d1ef904f80ea733`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L90-L90) — lines `90–90`; excerpt `sha256:af947109aab559bea882df279e8e9f19ecaf9561d6fded648d1ef904f80ea733`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L90-L90) — lines `90–90`; excerpt `sha256:af947109aab559bea882df279e8e9f19ecaf9561d6fded648d1ef904f80ea733`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1124-L1127) — lines `1124–1127`; excerpt `sha256:6974b157493799b4a7767f749fa6d8152750333b471355942174e4bfd947b461`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:939](../../paper/systems/claim-faithful-publication-systems-paper.tex#L939-L939)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:102](../../paper/269/erdos-269-three-prime-running-lcm.tex#L102-L102), [cite at paper/269/erdos-269-three-prime-running-lcm.tex:362](../../paper/269/erdos-269-three-prime-running-lcm.tex#L362-L362)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:141](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L141-L141), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1708](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1708-L1708), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3615](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3615-L3615), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3664](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3664-L3664), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3744](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3744-L3744), [cite at paper/reasoning-parts/erdos269/core.tex:90](../../paper/reasoning-parts/erdos269/core.tex#L90-L90), [cite at paper/reasoning-parts/erdos269/core.tex:1657](../../paper/reasoning-parts/erdos269/core.tex#L1657-L1657), [cite at paper/reasoning-parts/erdos269/core.tex:3564](../../paper/reasoning-parts/erdos269/core.tex#L3564-L3564), [cite at paper/reasoning-parts/erdos269/core.tex:3613](../../paper/reasoning-parts/erdos269/core.tex#L3613-L3613), [cite at paper/reasoning-parts/erdos269/core.tex:3693](../../paper/reasoning-parts/erdos269/core.tex#L3693-L3693)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1861](../../paper/synthesis/optimal-sparse-perturbations.tex#L1861-L1861)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4225-L4228) — lines `4225–4228`; excerpt `sha256:c96fc6ec675af873515b2c54bc711717a8fc43e0ef49d8237f9f330492b2bfa1`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1040-L1043) — lines `1040–1043`; excerpt `sha256:c96fc6ec675af873515b2c54bc711717a8fc43e0ef49d8237f9f330492b2bfa1`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4174-L4177) — lines `4174–4177`; excerpt `sha256:c96fc6ec675af873515b2c54bc711717a8fc43e0ef49d8237f9f330492b2bfa1`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L3642-L3642) — lines `3642–3642`; excerpt `sha256:8dbf333f1a138fb93ccef0608ac25e384cc5c3099760d92e2c9e99b5995e8837`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:81](../../paper/269/erdos-269-three-prime-running-lcm.tex#L81-L81)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:89](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L89-L89), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:470](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L470-L470), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3693](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3693-L3693), [cite at paper/reasoning-parts/erdos269/core.tex:38](../../paper/reasoning-parts/erdos269/core.tex#L38-L38), [cite at paper/reasoning-parts/erdos269/core.tex:419](../../paper/reasoning-parts/erdos269/core.tex#L419-L419), [cite at paper/reasoning-parts/erdos269/core.tex:3642](../../paper/reasoning-parts/erdos269/core.tex#L3642-L3642)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10008-L10013) — lines `10008–10013`; excerpt `sha256:6b26831b0198ae83ddcc51944fe34abc4a33f500ca85d17497481409ce3268b5`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9816-L9821) — lines `9816–9821`; excerpt `sha256:6b26831b0198ae83ddcc51944fe34abc4a33f500ca85d17497481409ce3268b5`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1770](../../paper/249/erdos249-totient-reasoning-surface.tex#L1770-L1771), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1578](../../paper/reasoning-parts/erdos249/a249_front.tex#L1578-L1579)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4867-L4874) — lines `4867–4874`; excerpt `sha256:037d8d669c712adb2ce488ddaad6988ca8a9e433e3271c97496d29be910f9ded`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4836-L4843) — lines `4836–4843`; excerpt `sha256:037d8d669c712adb2ce488ddaad6988ca8a9e433e3271c97496d29be910f9ded`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1102-L1109) — lines `1102–1109`; excerpt `sha256:f964675e399704b559c29b51eea44fc7fd16035cbb7bfee0f3491e3f1433945c`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:922](../../paper/1049/erdos-1049-rational-base-lambert.tex#L922-L922)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1434](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1434-L1434), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1436](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1436-L1436), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2865](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2865-L2865), [cite at paper/reasoning-parts/erdos1049/core.tex:1403](../../paper/reasoning-parts/erdos1049/core.tex#L1403-L1403), [cite at paper/reasoning-parts/erdos1049/core.tex:1405](../../paper/reasoning-parts/erdos1049/core.tex#L1405-L1405), [cite at paper/reasoning-parts/erdos1049/core.tex:2834](../../paper/reasoning-parts/erdos1049/core.tex#L2834-L2834)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L440-L445) — lines `440–445`; excerpt `sha256:1aaf5b626bbf92fab7b69d929e63d45171a17423eceba890691f509c0a872392`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2883-L2885) — lines `2883–2885`; excerpt `sha256:b4c77ac8d585a2bd2069a38e1c79a60b2fad942e48f3b3f28ef5324369021f67`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2842-L2844) — lines `2842–2844`; excerpt `sha256:b4c77ac8d585a2bd2069a38e1c79a60b2fad942e48f3b3f28ef5324369021f67`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L404-L404) — lines `404–404`; excerpt `sha256:6145f1750639419f2be2c1cc3dd58772864138a3bf33e3321107e49b5b3fd1b3`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:445](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L445-L445), [cite at paper/reasoning-parts/erdos251/core.tex:404](../../paper/reasoning-parts/erdos251/core.tex#L404-L404)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4914-L4918) — lines `4914–4918`; excerpt `sha256:009f0d973b996ec8f00395a65152d98054ea2ab49f230fdc01672a16b260f5cc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4883-L4887) — lines `4883–4887`; excerpt `sha256:009f0d973b996ec8f00395a65152d98054ea2ab49f230fdc01672a16b260f5cc`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4602](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4602-L4602), [cite at paper/reasoning-parts/erdos1049/core.tex:4571](../../paper/reasoning-parts/erdos1049/core.tex#L4571-L4571)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L692-L699) — lines `692–699`; excerpt `sha256:35232d77de2ddf4ba567da9e409016c66c0f5cf9a2043005e44829a8e3810ecb`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L623-L623) — lines `623–623`; excerpt `sha256:559a32bdd42dcc360fbcdc78de307cb8110fa700323e46aaf4f642fc6a1722b8`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L664-L664) — lines `664–664`; excerpt `sha256:3c3ce8b2e013386839dd33fce201b6bc5d5509a8fb97eab0f2da2406a1f45cb1`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L6712-L6712) — lines `6712–6712`; excerpt `sha256:c723c9121fa930c5c64b014b964f84584b03d698fff49666383cbf575a0e3068`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9952-L9958) — lines `9952–9958`; excerpt `sha256:de208be728552e87a1ec173f99d8429dd11fd4df8ecf144d7252710e5141acaa`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9760-L9766) — lines `9760–9766`; excerpt `sha256:de208be728552e87a1ec173f99d8429dd11fd4df8ecf144d7252710e5141acaa`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:623](../../paper/249/erdos-249-binary-totient-series.tex#L623-L623), [cite at paper/249/erdos-249-binary-totient-series.tex:665](../../paper/249/erdos-249-binary-totient-series.tex#L665-L665)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:6904](../../paper/249/erdos249-totient-reasoning-surface.tex#L6904-L6904), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6712](../../paper/reasoning-parts/erdos249/a249_front.tex#L6712-L6712)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1074-L1077) — lines `1074–1077`; excerpt `sha256:c38b879eb5217d10f2aed8b52d4612ade541384e4d3e5da0fc7060cf204a573b`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4299-L4302) — lines `4299–4302`; excerpt `sha256:c38b879eb5217d10f2aed8b52d4612ade541384e4d3e5da0fc7060cf204a573b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4248-L4251) — lines `4248–4251`; excerpt `sha256:c38b879eb5217d10f2aed8b52d4612ade541384e4d3e5da0fc7060cf204a573b`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1005](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1005-L1005)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3135](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3135-L3135), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3724](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3724-L3724), [cite at paper/reasoning-parts/erdos269/core.tex:3084](../../paper/reasoning-parts/erdos269/core.tex#L3084-L3084), [cite at paper/reasoning-parts/erdos269/core.tex:3673](../../paper/reasoning-parts/erdos269/core.tex#L3673-L3673)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3085-L3089) — lines `3085–3089`; excerpt `sha256:3aaa23b0ee5980d4b7a569cd8945d5e49ec49e7301ec40d1a5ab10ee81d75a3f`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3050-L3054) — lines `3050–3054`; excerpt `sha256:3aaa23b0ee5980d4b7a569cd8945d5e49ec49e7301ec40d1a5ab10ee81d75a3f`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1757](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1757-L1757), [cite at paper/reasoning-parts/erdos68/core.tex:1722](../../paper/reasoning-parts/erdos68/core.tex#L1722-L1722)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1114-L1118) — lines `1114–1118`; excerpt `sha256:67bdfa0d9c73d3ef9074f492e01b18101ff6ce673d7d7e006e7add28eefa7c93`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4999-L5003) — lines `4999–5003`; excerpt `sha256:67bdfa0d9c73d3ef9074f492e01b18101ff6ce673d7d7e006e7add28eefa7c93`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4968-L4972) — lines `4968–4972`; excerpt `sha256:67bdfa0d9c73d3ef9074f492e01b18101ff6ce673d7d7e006e7add28eefa7c93`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:918](../../paper/1049/erdos-1049-rational-base-lambert.tex#L918-L918)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2502](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2502-L2502), [cite at paper/reasoning-parts/erdos1049/core.tex:2471](../../paper/reasoning-parts/erdos1049/core.tex#L2471-L2471)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1248-L1253) — lines `1248–1253`; excerpt `sha256:0b698c4756fa8f99456ed34f52b4cf9be3600160caf3f3dec408e04cc0d7d111`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4015-L4020) — lines `4015–4020`; excerpt `sha256:0b698c4756fa8f99456ed34f52b4cf9be3600160caf3f3dec408e04cc0d7d111`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3976-L3981) — lines `3976–3981`; excerpt `sha256:0b698c4756fa8f99456ed34f52b4cf9be3600160caf3f3dec408e04cc0d7d111`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:502](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L502-L502), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:672](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L672-L672)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1422](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1422-L1422), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1801](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1801-L1801), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2885](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2885-L2885), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3158](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3158-L3158), [cite at paper/reasoning-parts/erdos243/core.tex:1383](../../paper/reasoning-parts/erdos243/core.tex#L1383-L1383), [cite at paper/reasoning-parts/erdos243/core.tex:1762](../../paper/reasoning-parts/erdos243/core.tex#L1762-L1762), [cite at paper/reasoning-parts/erdos243/core.tex:2846](../../paper/reasoning-parts/erdos243/core.tex#L2846-L2846), [cite at paper/reasoning-parts/erdos243/core.tex:3119](../../paper/reasoning-parts/erdos243/core.tex#L3119-L3119)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5264-L5270) — lines `5264–5270`; excerpt `sha256:2bbaf57338864a16529f3ab7d08eeeff8fb2358b4fafc7034087e3c4761985ee`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5220-L5226) — lines `5220–5226`; excerpt `sha256:2bbaf57338864a16529f3ab7d08eeeff8fb2358b4fafc7034087e3c4761985ee`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L965-L970) — lines `965–970`; excerpt `sha256:b596c679afdf485909e77c3fe5c891b6e74ed84091d4e552b784d92fb5a71aff`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:785](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L785-L785)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4387](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4387-L4387), [cite at paper/reasoning-parts/erdos1041/core.tex:4343](../../paper/reasoning-parts/erdos1041/core.tex#L4343-L4343)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5338-L5341) — lines `5338–5341`; excerpt `sha256:de50551571b8b9704ef2811a545a407c263e582e69b12f840cbb9d96750d359e`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2382](../../paper/archive/erdos249-257-main-paper.tex#L2382-L2382)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L508-L510) — lines `508–510`; excerpt `sha256:362d881ea52f611773702813f66d486fe4770940533ad01c07ba24d964ad5b46`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2941-L2943) — lines `2941–2943`; excerpt `sha256:3ba50a821565d47f20a7cf904fc3290b1f3c5126a28229eafe3917129456236e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2900-L2902) — lines `2900–2902`; excerpt `sha256:3ba50a821565d47f20a7cf904fc3290b1f3c5126a28229eafe3917129456236e`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:510](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L510-L510), [cite at paper/reasoning-parts/erdos251/core.tex:469](../../paper/reasoning-parts/erdos251/core.tex#L469-L469)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L935-L941) — lines `935–941`; excerpt `sha256:550b981b3e8c869d0df50cfb0dea1be1b90d0f2ad814088a1f8a1a3ac9ffade8`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5222-L5228) — lines `5222–5228`; excerpt `sha256:81544feb2d8e4a8dc89d7c14926bbdc17f7c170e2812d2e600bc764613620048`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5178-L5184) — lines `5178–5184`; excerpt `sha256:81544feb2d8e4a8dc89d7c14926bbdc17f7c170e2812d2e600bc764613620048`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L589-L589) — lines `589–589`; excerpt `sha256:e9af8055987c041e602fc36e4a30d002d7968c9be42fc2308fabbfc5f03eda0d`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L589-L589) — lines `589–589`; excerpt `sha256:e9af8055987c041e602fc36e4a30d002d7968c9be42fc2308fabbfc5f03eda0d`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L2007-L2007) — lines `2007–2007`; excerpt `sha256:513d9455ccd8f11d7bcdd4c503ae02528701d9a1e8bef30b6c9cb257b35a2b5f`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:570](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L570-L570)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1051](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1051-L1051), [cite at paper/reasoning-parts/erdos1041/core.tex:1007](../../paper/reasoning-parts/erdos1041/core.tex#L1007-L1007)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L594-L596) — lines `594–596`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2879-L2881) — lines `2879–2881`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2838-L2840) — lines `2838–2840`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L25-L25) — lines `25–25`; excerpt `sha256:9ac9f5c746a4ed69413e2f364cc0753ee3aa969eb39b5d87a0c1c8e8d6797e46`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L25-L25) — lines `25–25`; excerpt `sha256:9ac9f5c746a4ed69413e2f364cc0753ee3aa969eb39b5d87a0c1c8e8d6797e46`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L25-L25) — lines `25–25`; excerpt `sha256:9ac9f5c746a4ed69413e2f364cc0753ee3aa969eb39b5d87a0c1c8e8d6797e46`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:46](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L46-L46)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:66](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L66-L66), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:415](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L415-L415), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:429](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L429-L429), [cite at paper/reasoning-parts/erdos251/core.tex:25](../../paper/reasoning-parts/erdos251/core.tex#L25-L25), [cite at paper/reasoning-parts/erdos251/core.tex:374](../../paper/reasoning-parts/erdos251/core.tex#L374-L374), [cite at paper/reasoning-parts/erdos251/core.tex:388](../../paper/reasoning-parts/erdos251/core.tex#L388-L388)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3093-L3097) — lines `3093–3097`; excerpt `sha256:0237824e9b1bc6846e06ebc8479034b15e0574bcf800f0b614d1d0a682ca52bb`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3058-L3062) — lines `3058–3062`; excerpt `sha256:0237824e9b1bc6846e06ebc8479034b15e0574bcf800f0b614d1d0a682ca52bb`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1865](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1865-L1865), [cite at paper/reasoning-parts/erdos68/core.tex:1830](../../paper/reasoning-parts/erdos68/core.tex#L1830-L1830)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5383-L5391) — lines `5383–5391`; excerpt `sha256:64ec02486225f54bf2dfac8b56940d1a93a770185477df524459a057b87a721e`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1425-L1432) — lines `1425–1432`; excerpt `sha256:0ef99b680f15dcdcdc4890932040fe1bad3f3ee018e801c7204dea8bae0d1b51`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L969-L969) — lines `969–969`; excerpt `sha256:e8f0eb9c08b32d040eb9d382b55721fcbada06cfa90efaa2936a851eae07396b`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L879-L879) — lines `879–879`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8271-L8271) — lines `8271–8271`; excerpt `sha256:53ca69e59ff43d0292ca42e7954e5800d1314c64e4be23c03c224c016e357b49`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8431-L8431) — lines `8431–8431`; excerpt `sha256:1197efd3480c3d18971ff7587e64c3696907146bd64660e41bda3a5ac9fbd8f2`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8821-L8821) — lines `8821–8821`; excerpt `sha256:b02d5126a31d6f516b011882cd7b77604eb511797cbc09d89912554f44c242e9`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L835-L835) — lines `835–835`; excerpt `sha256:9221d992894d2f2ad88d52adc3a37360730affc1220f1d1730cef4677b6f31ce`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L835-L835) — lines `835–835`; excerpt `sha256:9221d992894d2f2ad88d52adc3a37360730affc1220f1d1730cef4677b6f31ce`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L835-L835) — lines `835–835`; excerpt `sha256:9221d992894d2f2ad88d52adc3a37360730affc1220f1d1730cef4677b6f31ce`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L499-L499) — lines `499–499`; excerpt `sha256:1ed1ce69c8bf73f3362ff5a2aca04fe7d02e4cc4dbe0784bc0f09ca0a22ad778`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4929-L4936) — lines `4929–4936`; excerpt `sha256:d84745edafcc3ae3ed868569f0e1e327404f0c2a6ff86a0c327422d4a6ddbebd`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4898-L4905) — lines `4898–4905`; excerpt `sha256:d84745edafcc3ae3ed868569f0e1e327404f0c2a6ff86a0c327422d4a6ddbebd`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9511-L9526) — lines `9511–9526`; excerpt `sha256:639844231444857a119025ab8e330a05e28514cf1dc9e9c65fdc92da1d687928`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9311-L9326) — lines `9311–9326`; excerpt `sha256:639844231444857a119025ab8e330a05e28514cf1dc9e9c65fdc92da1d687928`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1083-L1090) — lines `1083–1090`; excerpt `sha256:1efaad4cfc934457449068fdeec1040f4a4c014a88951973ae9338a1d554132d`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:234](../../paper/systems/claim-faithful-publication-systems-paper.tex#L234-L234)
- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:962](../../paper/1049/erdos-1049-rational-base-lambert.tex#L962-L962)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:255](../../paper/257/erdos-257-mersenne-support-subseries.tex#L255-L255), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:697](../../paper/257/erdos-257-mersenne-support-subseries.tex#L697-L697), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:835](../../paper/257/erdos-257-mersenne-support-subseries.tex#L835-L835)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4629](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4629-L4629), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4630](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4630-L4630), [cite at paper/reasoning-parts/erdos1049/core.tex:4598](../../paper/reasoning-parts/erdos1049/core.tex#L4598-L4598), [cite at paper/reasoning-parts/erdos1049/core.tex:4599](../../paper/reasoning-parts/erdos1049/core.tex#L4599-L4599)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:749](../../paper/archive/erdos249-257-main-paper.tex#L749-L749)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1383](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1383-L1383), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3188](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3188-L3188), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1183](../../paper/reasoning-parts/erdos257/a257_front.tex#L1183-L1183), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2988](../../paper/reasoning-parts/erdos257/a257_front.tex#L2988-L2988)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1992](../../paper/synthesis/optimal-sparse-perturbations.tex#L1992-L1993)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1230-L1235) — lines `1230–1235`; excerpt `sha256:ee897c806cc6764f8001bdbab28ecd44a7ae784f93c8b76cdca0c229578e334b`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3990-L3995) — lines `3990–3995`; excerpt `sha256:ee897c806cc6764f8001bdbab28ecd44a7ae784f93c8b76cdca0c229578e334b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3951-L3956) — lines `3951–3956`; excerpt `sha256:ee897c806cc6764f8001bdbab28ecd44a7ae784f93c8b76cdca0c229578e334b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L1556-L1556) — lines `1556–1556`; excerpt `sha256:2df19ae3d0b16a50ae460b309f4d509936436c1b79c214baa753b21bb87891dd`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:837](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L837-L837)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:888](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L888-L889), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1595](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1595-L1595), [cite at paper/reasoning-parts/erdos243/core.tex:849](../../paper/reasoning-parts/erdos243/core.tex#L849-L850), [cite at paper/reasoning-parts/erdos243/core.tex:1556](../../paper/reasoning-parts/erdos243/core.tex#L1556-L1556)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5247-L5252) — lines `5247–5252`; excerpt `sha256:620501b65c595f397bcb8546b8f32f2dc7376a436f617b51b629ce031def07e1`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5203-L5208) — lines `5203–5208`; excerpt `sha256:620501b65c595f397bcb8546b8f32f2dc7376a436f617b51b629ce031def07e1`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4082-L4082) — lines `4082–4082`; excerpt `sha256:018d096210a7ffec3eb82decf527d824cd58c2bd4eb4f692250cc5c4b2b8caa9`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4126](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4126-L4126), [cite at paper/reasoning-parts/erdos1041/core.tex:4082](../../paper/reasoning-parts/erdos1041/core.tex#L4082-L4082)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4979-L4984) — lines `4979–4984`; excerpt `sha256:58eae42e166b8f8a536b9cfe4c4577e41e70667815b654f00bc6a6c1c848d0dc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4948-L4953) — lines `4948–4953`; excerpt `sha256:58eae42e166b8f8a536b9cfe4c4577e41e70667815b654f00bc6a6c1c848d0dc`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2731](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2731-L2731), [cite at paper/reasoning-parts/erdos1049/core.tex:2700](../../paper/reasoning-parts/erdos1049/core.tex#L2700-L2700)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3001-L3005) — lines `3001–3005`; excerpt `sha256:0758379961a43fb0431ee76d95c75e47c003353f90b6a707964f44a842f3ea87`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2966-L2970) — lines `2966–2970`; excerpt `sha256:0758379961a43fb0431ee76d95c75e47c003353f90b6a707964f44a842f3ea87`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L980-L980) — lines `980–980`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L980-L980) — lines `980–980`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L980-L980) — lines `980–980`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L980-L980) — lines `980–980`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L897-L901) — lines `897–901`; excerpt `sha256:25aaa19e96eb7b41573f74f4702b9cbc37b54a817dc5039af5bd04f243600052`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:652](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L652-L652)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1015](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1015-L1015), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1817](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1817-L1817), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2168](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2168-L2168), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2528](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2528-L2528), [cite at paper/reasoning-parts/erdos68/core.tex:980](../../paper/reasoning-parts/erdos68/core.tex#L980-L980), [cite at paper/reasoning-parts/erdos68/core.tex:1782](../../paper/reasoning-parts/erdos68/core.tex#L1782-L1782), [cite at paper/reasoning-parts/erdos68/core.tex:2133](../../paper/reasoning-parts/erdos68/core.tex#L2133-L2133), [cite at paper/reasoning-parts/erdos68/core.tex:2493](../../paper/reasoning-parts/erdos68/core.tex#L2493-L2493)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3061-L3065) — lines `3061–3065`; excerpt `sha256:c81f5719e7e0059427c6fe7295699d3523c4215f7fe430b755be834cb594cfe9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3026-L3030) — lines `3026–3030`; excerpt `sha256:c81f5719e7e0059427c6fe7295699d3523c4215f7fe430b755be834cb594cfe9`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1742](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1742-L1742), [cite at paper/reasoning-parts/erdos68/core.tex:1707](../../paper/reasoning-parts/erdos68/core.tex#L1707-L1707)

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
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1130-L1133) — lines `1130–1133`; excerpt `sha256:c9a36ce66934887ca2d845c1c21fdca445b85d85fda8067ad6a244acf9f4fbe6`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:148](../../paper/systems/claim-faithful-publication-systems-paper.tex#L148-L148), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:811](../../paper/systems/claim-faithful-publication-systems-paper.tex#L811-L811)
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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10084-L10088) — lines `10084–10088`; excerpt `sha256:e8efab4ceb7a738eebd6f794631df1b61792fb0a00d2d6d557380dd4e37f9c41`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9892-L9896) — lines `9892–9896`; excerpt `sha256:e8efab4ceb7a738eebd6f794631df1b61792fb0a00d2d6d557380dd4e37f9c41`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7921](../../paper/249/erdos249-totient-reasoning-surface.tex#L7921-L7921), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7729](../../paper/reasoning-parts/erdos249/a249_front.tex#L7729-L7729)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5019-L5025) — lines `5019–5025`; excerpt `sha256:bd367f3dba72019c86ec01aacbc2dc2ba3af36d5b42d189d2c16647299c55964`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4988-L4994) — lines `4988–4994`; excerpt `sha256:bd367f3dba72019c86ec01aacbc2dc2ba3af36d5b42d189d2c16647299c55964`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2858](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2858-L2858), [cite at paper/reasoning-parts/erdos1049/core.tex:2827](../../paper/reasoning-parts/erdos1049/core.tex#L2827-L2827)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5358-L5363) — lines `5358–5363`; excerpt `sha256:b3f91ee983a8672978d0cb4683a9eac57121a743ff8449aa943c718486e5f24d`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1072-L1078) — lines `1072–1078`; excerpt `sha256:f7f8625de08bee4472f7198ac41b6132a598c68fb4f2c5d046fbf4555082ef4d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4343-L4343) — lines `4343–4343`; excerpt `sha256:9c2a91a02fdf0d919533a27cf6d9347afee25f7427ccbde7d620a561bd32d9e8`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4374-L4374) — lines `4374–4374`; excerpt `sha256:9c2a91a02fdf0d919533a27cf6d9347afee25f7427ccbde7d620a561bd32d9e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4922-L4928) — lines `4922–4928`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4953-L4959) — lines `4953–4959`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L739-L743) — lines `739–743`; excerpt `sha256:a596a5a3ab90688c2d2e40605ef4e488e6632133e5a12a5f09f3821c37ac1dbd`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10099-L10103) — lines `10099–10103`; excerpt `sha256:a596a5a3ab90688c2d2e40605ef4e488e6632133e5a12a5f09f3821c37ac1dbd`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9907-L9911) — lines `9907–9911`; excerpt `sha256:a596a5a3ab90688c2d2e40605ef4e488e6632133e5a12a5f09f3821c37ac1dbd`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4953-L4959) — lines `4953–4959`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4922-L4928) — lines `4922–4928`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:969](../../paper/1049/erdos-1049-rational-base-lambert.tex#L969-L969)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:645](../../paper/249/erdos-249-binary-totient-series.tex#L645-L645)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4301](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4301-L4301), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4896](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4896-L4896), [cite at paper/reasoning-parts/erdos1049/core.tex:4270](../../paper/reasoning-parts/erdos1049/core.tex#L4270-L4270), [cite at paper/reasoning-parts/erdos1049/core.tex:4865](../../paper/reasoning-parts/erdos1049/core.tex#L4865-L4865)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3192](../../paper/archive/erdos249-257-main-paper.tex#L3192-L3192)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9906](../../paper/249/erdos249-totient-reasoning-surface.tex#L9906-L9906), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9714](../../paper/reasoning-parts/erdos249/a249_front.tex#L9714-L9714)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10051-L10057) — lines `10051–10057`; excerpt `sha256:5ea3e979eefb577068ea145beb2c4d5913b323a0f5a413f315280b716ec5eb58`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9859-L9865) — lines `9859–9865`; excerpt `sha256:5ea3e979eefb577068ea145beb2c4d5913b323a0f5a413f315280b716ec5eb58`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7813](../../paper/249/erdos249-totient-reasoning-surface.tex#L7813-L7813), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7621](../../paper/reasoning-parts/erdos249/a249_front.tex#L7621-L7621)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L881-L885) — lines `881–885`; excerpt `sha256:01afe33226c434943312f632a5b1272516885eec61dfda3c99448c38f71ab1f1`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3045-L3049) — lines `3045–3049`; excerpt `sha256:01afe33226c434943312f632a5b1272516885eec61dfda3c99448c38f71ab1f1`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3010-L3014) — lines `3010–3014`; excerpt `sha256:01afe33226c434943312f632a5b1272516885eec61dfda3c99448c38f71ab1f1`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:393](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L393-L393)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:946](../../paper/68/erdos68-factorial-reasoning-surface.tex#L946-L946), [cite at paper/reasoning-parts/erdos68/core.tex:911](../../paper/reasoning-parts/erdos68/core.tex#L911-L911)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5228-L5234) — lines `5228–5234`; excerpt `sha256:428989f59406f939d2c86c6f7824295f410f97de0a786684b7faeddbd01f4a71`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5184-L5190) — lines `5184–5190`; excerpt `sha256:428989f59406f939d2c86c6f7824295f410f97de0a786684b7faeddbd01f4a71`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L891-L897) — lines `891–897`; excerpt `sha256:cd02a3f4bd4ab2831d4e82f0258f2e99b98627ee1ba71dc7fcd33aaae61f7342`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:114](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L114-L114), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:570](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L570-L570)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:633](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L633-L633), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1051](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1051-L1051), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1174](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1174-L1174), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1343](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1343-L1343), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1416](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1416-L1416), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1595](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1595-L1595), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1595](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1595-L1595), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1920](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1920-L1920), [cite at paper/reasoning-parts/erdos1041/core.tex:589](../../paper/reasoning-parts/erdos1041/core.tex#L589-L589), [cite at paper/reasoning-parts/erdos1041/core.tex:1007](../../paper/reasoning-parts/erdos1041/core.tex#L1007-L1007), [cite at paper/reasoning-parts/erdos1041/core.tex:1130](../../paper/reasoning-parts/erdos1041/core.tex#L1130-L1130), [cite at paper/reasoning-parts/erdos1041/core.tex:1299](../../paper/reasoning-parts/erdos1041/core.tex#L1299-L1299), [cite at paper/reasoning-parts/erdos1041/core.tex:1372](../../paper/reasoning-parts/erdos1041/core.tex#L1372-L1372), [cite at paper/reasoning-parts/erdos1041/core.tex:1551](../../paper/reasoning-parts/erdos1041/core.tex#L1551-L1551), [cite at paper/reasoning-parts/erdos1041/core.tex:1551](../../paper/reasoning-parts/erdos1041/core.tex#L1551-L1551), [cite at paper/reasoning-parts/erdos1041/core.tex:1876](../../paper/reasoning-parts/erdos1041/core.tex#L1876-L1876)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1288-L1294) — lines `1288–1294`; excerpt `sha256:94123b672bbe246ca5a1da5c42f627ccc32ae5d9d6727e40019a7798db0120de`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4064-L4070) — lines `4064–4070`; excerpt `sha256:94123b672bbe246ca5a1da5c42f627ccc32ae5d9d6727e40019a7798db0120de`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4025-L4031) — lines `4025–4031`; excerpt `sha256:94123b672bbe246ca5a1da5c42f627ccc32ae5d9d6727e40019a7798db0120de`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L626-L628) — lines `626–628`; excerpt `sha256:06af722f0c1d5bd1dbdd7a2c42574299caad3b8bfea7faed51cebc591365c44c`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2931-L2933) — lines `2931–2933`; excerpt `sha256:828f4da9714361921bc80071c0a1ee81ffb2c4cd7328ba82c26137466ef09a38`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2890-L2892) — lines `2890–2892`; excerpt `sha256:828f4da9714361921bc80071c0a1ee81ffb2c4cd7328ba82c26137466ef09a38`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10122-L10126) — lines `10122–10126`; excerpt `sha256:7ec6c33f36b32e11bbec81e8c966173b30a2c50d056c1ab9103fffc5afc23d94`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L7295-L7295) — lines `7295–7295`; excerpt `sha256:b5f7725d9d9b224c30c605af2ec45cbedb389b6e64791915712d49c8c2ee5bd0`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9930-L9934) — lines `9930–9934`; excerpt `sha256:7ec6c33f36b32e11bbec81e8c966173b30a2c50d056c1ab9103fffc5afc23d94`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7103-L7103) — lines `7103–7103`; excerpt `sha256:b5f7725d9d9b224c30c605af2ec45cbedb389b6e64791915712d49c8c2ee5bd0`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1047](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1047-L1047), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1099](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1099-L1099)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:66](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L66-L66), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:202](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L202-L202)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:967](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L967-L967), [cite at paper/reasoning-parts/erdos243/core.tex:928](../../paper/reasoning-parts/erdos243/core.tex#L928-L928)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7295](../../paper/249/erdos249-totient-reasoning-surface.tex#L7295-L7295), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7103](../../paper/reasoning-parts/erdos249/a249_front.tex#L7103-L7103)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:279](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L279-L279), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:465](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L465-L465), [cite at paper/reasoning-parts/erdos251/core.tex:238](../../paper/reasoning-parts/erdos251/core.tex#L238-L238), [cite at paper/reasoning-parts/erdos251/core.tex:424](../../paper/reasoning-parts/erdos251/core.tex#L424-L424)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1455-L1458) — lines `1455–1458`; excerpt `sha256:8fe2d89da58a1e4e231d39f70b8dc5e5e218e128f6a1964d09e9a63a746e2b0a`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2985-L2989) — lines `2985–2989`; excerpt `sha256:b938d408a670bde68b8522a01fa71ee3a1b30b4fbb78368431f5fb9cded5f0f9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2950-L2954) — lines `2950–2954`; excerpt `sha256:b938d408a670bde68b8522a01fa71ee3a1b30b4fbb78368431f5fb9cded5f0f9`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:714](../../paper/257/erdos-257-mersenne-support-subseries.tex#L714-L714)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2045](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2045-L2045), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2177](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2177-L2177), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2439](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2439-L2439), [cite at paper/reasoning-parts/erdos68/core.tex:2010](../../paper/reasoning-parts/erdos68/core.tex#L2010-L2010), [cite at paper/reasoning-parts/erdos68/core.tex:2142](../../paper/reasoning-parts/erdos68/core.tex#L2142-L2142), [cite at paper/reasoning-parts/erdos68/core.tex:2404](../../paper/reasoning-parts/erdos68/core.tex#L2404-L2404)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L961-L965) — lines `961–965`; excerpt `sha256:6ea06c00bd0618e69c51b088f55e4fd1b6441571dde55b8bda3d1dc3d28d3e67`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5350-L5354) — lines `5350–5354`; excerpt `sha256:906433dd170c41415919219e15b60b8e1b97efac405ace13999d8cc6451fa785`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5306-L5310) — lines `5306–5310`; excerpt `sha256:906433dd170c41415919219e15b60b8e1b97efac405ace13999d8cc6451fa785`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:638](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L638-L638), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:718](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L718-L718), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:812](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L812-L812)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1376](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1376-L1376), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2121](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2121-L2121), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3090](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3090-L3090), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3787](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3787-L3787), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3912](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3912-L3912), [cite at paper/reasoning-parts/erdos1041/core.tex:1332](../../paper/reasoning-parts/erdos1041/core.tex#L1332-L1332), [cite at paper/reasoning-parts/erdos1041/core.tex:2077](../../paper/reasoning-parts/erdos1041/core.tex#L2077-L2077), [cite at paper/reasoning-parts/erdos1041/core.tex:3046](../../paper/reasoning-parts/erdos1041/core.tex#L3046-L3046), [cite at paper/reasoning-parts/erdos1041/core.tex:3743](../../paper/reasoning-parts/erdos1041/core.tex#L3743-L3743), [cite at paper/reasoning-parts/erdos1041/core.tex:3868](../../paper/reasoning-parts/erdos1041/core.tex#L3868-L3868)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2943-L2945) — lines `2943–2945`; excerpt `sha256:c13202ba0e0b2c61e1309389eeaf97212f8f3b05eea87b49c4ad2e8748454dc3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2902-L2904) — lines `2902–2904`; excerpt `sha256:c13202ba0e0b2c61e1309389eeaf97212f8f3b05eea87b49c4ad2e8748454dc3`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:548](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L548-L548), [cite at paper/reasoning-parts/erdos251/core.tex:507](../../paper/reasoning-parts/erdos251/core.tex#L507-L507)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5011-L5019) — lines `5011–5019`; excerpt `sha256:17a9f0c77da491dc851c4a65e945725b1c61e75da287cb94849f3bb840ee6c33`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4980-L4988) — lines `4980–4988`; excerpt `sha256:17a9f0c77da491dc851c4a65e945725b1c61e75da287cb94849f3bb840ee6c33`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2603](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2603-L2603), [cite at paper/reasoning-parts/erdos1049/core.tex:2572](../../paper/reasoning-parts/erdos1049/core.tex#L2572-L2572)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10109-L10116) — lines `10109–10116`; excerpt `sha256:c412b56a71492694abbd8a4bb30d4b12dd25d5050689bc96bb8d162c095f07c6`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9917-L9924) — lines `9917–9924`; excerpt `sha256:c412b56a71492694abbd8a4bb30d4b12dd25d5050689bc96bb8d162c095f07c6`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L534-L535) — lines `534–535`; excerpt `sha256:247c067f39becf8fb56e126e3b8f9082fe2ff5beedfff0856ec406a7f8bb7975`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2933-L2935) — lines `2933–2935`; excerpt `sha256:6e5c026e217aafc0c8b121d5e6586f0139ff79cbf8c2871b89cdc840c4041993`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2892-L2894) — lines `2892–2894`; excerpt `sha256:6e5c026e217aafc0c8b121d5e6586f0139ff79cbf8c2871b89cdc840c4041993`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9914](../../paper/249/erdos249-totient-reasoning-surface.tex#L9914-L9914), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9722](../../paper/reasoning-parts/erdos249/a249_front.tex#L9722-L9722)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:535](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L535-L535), [cite at paper/reasoning-parts/erdos251/core.tex:494](../../paper/reasoning-parts/erdos251/core.tex#L494-L494)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1446-L1451) — lines `1446–1451`; excerpt `sha256:25cf3513f78fba977dc2a6cefb4a67e70b7815d304207cbac09e637aaa5db383`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1377](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1377-L1377)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5391-L5395) — lines `5391–5395`; excerpt `sha256:e74d62894afb08f0bf9f352f2a81f1d8436fc4947ccc8847ea8044e669d88d61`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4008-L4015) — lines `4008–4015`; excerpt `sha256:cc6aca2237133e921cd97b74d25252bfe07f4ac85f0f29888f9c09d741fbe072`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L604-L606) — lines `604–606`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2899-L2901) — lines `2899–2901`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1440-L1444) — lines `1440–1444`; excerpt `sha256:da365fb3627d4a62500ab14506a5fa9a7c61368c1f67b75982752d2ba474ccc5`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4259-L4262) — lines `4259–4262`; excerpt `sha256:854363997d348b739079081250c9280b18fc2f8b82b9e98cfd71f3fe5d758fdf`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4942-L4949) — lines `4942–4949`; excerpt `sha256:31734bb5dbd8d4b44ac368c926cf6ce72c577a3e05d74dab77682764ee7da3da`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4911-L4918) — lines `4911–4918`; excerpt `sha256:31734bb5dbd8d4b44ac368c926cf6ce72c577a3e05d74dab77682764ee7da3da`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4624-L4624) — lines `4624–4624`; excerpt `sha256:1102bfe9b1f75f0d5960a2f3d22f55f277c362853922162565b2ad5506af83b9`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3969-L3976) — lines `3969–3976`; excerpt `sha256:cc6aca2237133e921cd97b74d25252bfe07f4ac85f0f29888f9c09d741fbe072`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L910-L910) — lines `910–910`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L910-L910) — lines `910–910`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L910-L910) — lines `910–910`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2858-L2860) — lines `2858–2860`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L243-L243) — lines `243–243`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4208-L4211) — lines `4208–4211`; excerpt `sha256:854363997d348b739079081250c9280b18fc2f8b82b9e98cfd71f3fe5d758fdf`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L134-L134) — lines `134–134`; excerpt `sha256:3abef61fe6288d78d30765ceaf472ba30b63436843d7f7cb71bd57725ce6dfa1`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L81-L81) — lines `81–81`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1112-L1112) — lines `1112–1112`; excerpt `sha256:2f13d854d17862e3e84cfe8260e36f3e508b7165189455204d23c133aeac237e`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L603-L613) — lines `603–613`; excerpt `sha256:c989aa24e7d0cd4a81a2207dea6e4647a9e1d349d2fb8a86a8fcd45cc9386fd7`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L67-L67) — lines `67–67`; excerpt `sha256:50d32f90b65fd0005fb2987ffe3dda549379dfbd5da510242ea70b71dd44cacd`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L67-L67) — lines `67–67`; excerpt `sha256:50d32f90b65fd0005fb2987ffe3dda549379dfbd5da510242ea70b71dd44cacd`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L243-L243) — lines `243–243`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L243-L243) — lines `243–243`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L243-L243) — lines `243–243`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L284-L284) — lines `284–284`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L284-L284) — lines `284–284`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L284-L284) — lines `284–284`; excerpt `sha256:c42aedd2b096572a99b7eb98dee02ac62548a548a8b12d108891131c690bd548`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10025-L10031) — lines `10025–10031`; excerpt `sha256:aa7e7a743f9042755d99379ed9c411c18d6b86186718b25aa42a57c133a0f41e`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9833-L9839) — lines `9833–9839`; excerpt `sha256:aa7e7a743f9042755d99379ed9c411c18d6b86186718b25aa42a57c133a0f41e`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L604-L606) — lines `604–606`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1086-L1089) — lines `1086–1089`; excerpt `sha256:9c3c5db10d94904b54c40a45565db137f38253e6cc98c36fb7f0446f37302911`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:67](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L67-L67)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:951](../../paper/257/erdos-257-mersenne-support-subseries.tex#L951-L951)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1014](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1014-L1014)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4655](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4655-L4655), [cite at paper/reasoning-parts/erdos1049/core.tex:4624](../../paper/reasoning-parts/erdos1049/core.tex#L4624-L4624)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:949](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L949-L949), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:952](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L952-L952), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:961](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L961-L961), [cite at paper/reasoning-parts/erdos243/core.tex:910](../../paper/reasoning-parts/erdos243/core.tex#L910-L910), [cite at paper/reasoning-parts/erdos243/core.tex:913](../../paper/reasoning-parts/erdos243/core.tex#L913-L913), [cite at paper/reasoning-parts/erdos243/core.tex:922](../../paper/reasoning-parts/erdos243/core.tex#L922-L922)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:835](../../paper/archive/erdos249-257-main-paper.tex#L835-L835), [cite at paper/archive/erdos249-257-main-paper.tex:836](../../paper/archive/erdos249-257-main-paper.tex#L836-L836), [cite at paper/archive/erdos249-257-main-paper.tex:2157](../../paper/archive/erdos249-257-main-paper.tex#L2157-L2157), [cite at paper/archive/erdos249-257-main-paper.tex:4676](../../paper/archive/erdos249-257-main-paper.tex#L4676-L4676), [cite at paper/archive/erdos249-257-main-paper.tex:5067](../../paper/archive/erdos249-257-main-paper.tex#L5067-L5067), [cite at paper/archive/erdos249-257-main-paper.tex:5113](../../paper/archive/erdos249-257-main-paper.tex#L5113-L5113)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9882](../../paper/249/erdos249-totient-reasoning-surface.tex#L9882-L9882), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9690](../../paper/reasoning-parts/erdos249/a249_front.tex#L9690-L9690)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:284](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L284-L284), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:474](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L474-L474), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:569](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L569-L569), [cite at paper/reasoning-parts/erdos251/core.tex:243](../../paper/reasoning-parts/erdos251/core.tex#L243-L243), [cite at paper/reasoning-parts/erdos251/core.tex:433](../../paper/reasoning-parts/erdos251/core.tex#L433-L433), [cite at paper/reasoning-parts/erdos251/core.tex:528](../../paper/reasoning-parts/erdos251/core.tex#L528-L528)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9086](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9086-L9086), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:8886](../../paper/reasoning-parts/erdos257/a257_front.tex#L8886-L8886)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:185](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L185-L185), [cite at paper/reasoning-parts/erdos269/core.tex:134](../../paper/reasoning-parts/erdos269/core.tex#L134-L134)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:885](../../paper/synthesis/optimal-sparse-perturbations.tex#L885-L885), [cite at paper/synthesis/optimal-sparse-perturbations.tex:912](../../paper/synthesis/optimal-sparse-perturbations.tex#L912-L912), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1019](../../paper/synthesis/optimal-sparse-perturbations.tex#L1019-L1019), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1035](../../paper/synthesis/optimal-sparse-perturbations.tex#L1035-L1035), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1858](../../paper/synthesis/optimal-sparse-perturbations.tex#L1858-L1858), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1977](../../paper/synthesis/optimal-sparse-perturbations.tex#L1977-L1977), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1980](../../paper/synthesis/optimal-sparse-perturbations.tex#L1980-L1980)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L873-L877) — lines `873–877`; excerpt `sha256:c1feb1fd30f80a42ea7b93c301207ea72abff8a1961dc7646ef336d6bf938b73`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3037-L3041) — lines `3037–3041`; excerpt `sha256:c1feb1fd30f80a42ea7b93c301207ea72abff8a1961dc7646ef336d6bf938b73`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3002-L3006) — lines `3002–3006`; excerpt `sha256:c1feb1fd30f80a42ea7b93c301207ea72abff8a1961dc7646ef336d6bf938b73`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:808](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L808-L808)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1115](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1115-L1115), [cite at paper/reasoning-parts/erdos68/core.tex:1080](../../paper/reasoning-parts/erdos68/core.tex#L1080-L1080)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4290-L4293) — lines `4290–4293`; excerpt `sha256:53305164d06918956b307b2a2bd9e37d95e4d93aff557246b8ebc65eee173fbd`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4239-L4242) — lines `4239–4242`; excerpt `sha256:53305164d06918956b307b2a2bd9e37d95e4d93aff557246b8ebc65eee173fbd`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2953](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2953-L2953), [cite at paper/reasoning-parts/erdos269/core.tex:2902](../../paper/reasoning-parts/erdos269/core.tex#L2902-L2902)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1123-L1127) — lines `1123–1127`; excerpt `sha256:3b958d96041c8d7357ca2a6320bad4a5c5dd5c24e66c13f3fdcb75343dfb1596`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5025-L5029) — lines `5025–5029`; excerpt `sha256:3b958d96041c8d7357ca2a6320bad4a5c5dd5c24e66c13f3fdcb75343dfb1596`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4994-L4998) — lines `4994–4998`; excerpt `sha256:3b958d96041c8d7357ca2a6320bad4a5c5dd5c24e66c13f3fdcb75343dfb1596`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:919](../../paper/1049/erdos-1049-rational-base-lambert.tex#L919-L919)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2726](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2726-L2726), [cite at paper/reasoning-parts/erdos1049/core.tex:2695](../../paper/reasoning-parts/erdos1049/core.tex#L2695-L2695)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4247-L4250) — lines `4247–4250`; excerpt `sha256:dad66e1d91ee56df1368adfe2ef9592eef350506274c14cc06dcf5ad03ef77ed`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4196-L4199) — lines `4196–4199`; excerpt `sha256:dad66e1d91ee56df1368adfe2ef9592eef350506274c14cc06dcf5ad03ef77ed`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L3701-L3701) — lines `3701–3701`; excerpt `sha256:70156aa149e95bc051830fe62c9e4dead62a9dfae84a47de933e386647c09bdb`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L3701-L3701) — lines `3701–3701`; excerpt `sha256:70156aa149e95bc051830fe62c9e4dead62a9dfae84a47de933e386647c09bdb`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3752-L3752) — lines `3752–3752`; excerpt `sha256:70156aa149e95bc051830fe62c9e4dead62a9dfae84a47de933e386647c09bdb`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3732](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3732-L3732), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3752](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3752-L3752), [cite at paper/reasoning-parts/erdos269/core.tex:3681](../../paper/reasoning-parts/erdos269/core.tex#L3681-L3681), [cite at paper/reasoning-parts/erdos269/core.tex:3701](../../paper/reasoning-parts/erdos269/core.tex#L3701-L3701)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5344-L5352) — lines `5344–5352`; excerpt `sha256:28fc1b15f89dedfd49214bfcd5a49cc05823f44376740a8e9ad7fc0e987fb378`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L684-L688) — lines `684–688`; excerpt `sha256:822cceaa2102882ca659544f6f24812353e6082e3f3fd963beaa90ce4be4a49a`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9942-L9947) — lines `9942–9947`; excerpt `sha256:1faa5900afcaadc94dc78596f20f82bc542cdeea10be862bbe3be3e9ca92f21f`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9750-L9755) — lines `9750–9755`; excerpt `sha256:1faa5900afcaadc94dc78596f20f82bc542cdeea10be862bbe3be3e9ca92f21f`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:61](../../paper/249/erdos-249-binary-totient-series.tex#L61-L61)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3184](../../paper/archive/erdos249-257-main-paper.tex#L3184-L3184)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8462](../../paper/249/erdos249-totient-reasoning-surface.tex#L8462-L8462), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8270](../../paper/reasoning-parts/erdos249/a249_front.tex#L8270-L8270)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L861-L865) — lines `861–865`; excerpt `sha256:00f686cb4c9f7ec34f4862095318a0388b914d486a42bca48ec232dec92aebc4`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3029-L3033) — lines `3029–3033`; excerpt `sha256:e82d9607acf436d2f4aa8d7afad731fa862ecbfa84e051d3b8579701aa30e049`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2994-L2998) — lines `2994–2998`; excerpt `sha256:e82d9607acf436d2f4aa8d7afad731fa862ecbfa84e051d3b8579701aa30e049`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L391-L391) — lines `391–391`; excerpt `sha256:3b3725b25d8e462319ac40a8ae1bb53225d1d9aa0e5d822a6ca8618d10aa1268`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L391-L391) — lines `391–391`; excerpt `sha256:3b3725b25d8e462319ac40a8ae1bb53225d1d9aa0e5d822a6ca8618d10aa1268`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L908-L908) — lines `908–908`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L908-L908) — lines `908–908`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L906-L906) — lines `906–906`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L908-L908) — lines `908–908`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:391](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L391-L391), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:407](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L407-L407)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:943](../../paper/68/erdos68-factorial-reasoning-surface.tex#L943-L943), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1027](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1027-L1027), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2171](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2171-L2171), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2174](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2174-L2174), [cite at paper/reasoning-parts/erdos68/core.tex:908](../../paper/reasoning-parts/erdos68/core.tex#L908-L908), [cite at paper/reasoning-parts/erdos68/core.tex:992](../../paper/reasoning-parts/erdos68/core.tex#L992-L992), [cite at paper/reasoning-parts/erdos68/core.tex:2136](../../paper/reasoning-parts/erdos68/core.tex#L2136-L2136), [cite at paper/reasoning-parts/erdos68/core.tex:2139](../../paper/reasoning-parts/erdos68/core.tex#L2139-L2139)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L953-L958) — lines `953–958`; excerpt `sha256:9976334d2d074f47b0f36053eafc88c2da992e02c4c4c2eb6956f0ecc319a48b`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5342-L5347) — lines `5342–5347`; excerpt `sha256:9976334d2d074f47b0f36053eafc88c2da992e02c4c4c2eb6956f0ecc319a48b`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5298-L5303) — lines `5298–5303`; excerpt `sha256:9976334d2d074f47b0f36053eafc88c2da992e02c4c4c2eb6956f0ecc319a48b`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:825](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L825-L825)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1497](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1497-L1497), [cite at paper/reasoning-parts/erdos1041/core.tex:1453](../../paper/reasoning-parts/erdos1041/core.tex#L1453-L1453)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4959-L4963) — lines `4959–4963`; excerpt `sha256:1f93dd63fdcecc1c50a9e4192bb21b88580fe393bef2b1a4a2bd32200489b8f2`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4928-L4932) — lines `4928–4932`; excerpt `sha256:1f93dd63fdcecc1c50a9e4192bb21b88580fe393bef2b1a4a2bd32200489b8f2`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1667](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1667-L1667), [cite at paper/reasoning-parts/erdos1049/core.tex:1636](../../paper/reasoning-parts/erdos1049/core.tex#L1636-L1636)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4918-L4923) — lines `4918–4923`; excerpt `sha256:8145c4e8df8a670bb4c71753052c607b975795318f4a6fdaaed256f6644f773f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4887-L4892) — lines `4887–4892`; excerpt `sha256:8145c4e8df8a670bb4c71753052c607b975795318f4a6fdaaed256f6644f773f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4587-L4587) — lines `4587–4587`; excerpt `sha256:4cba849220b6d89a05527440677a635fe05b976de1d3d125b3c7d9e3b37a61fe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4587-L4587) — lines `4587–4587`; excerpt `sha256:4cba849220b6d89a05527440677a635fe05b976de1d3d125b3c7d9e3b37a61fe`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1078-L1083) — lines `1078–1083`; excerpt `sha256:8d3a5a9309dacce42b935afcf56eac11bf777dafe926a5de5f7e5dbb71726aca`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:961](../../paper/1049/erdos-1049-rational-base-lambert.tex#L961-L961)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4618](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4618-L4618), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4621](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4621-L4621), [cite at paper/reasoning-parts/erdos1049/core.tex:4587](../../paper/reasoning-parts/erdos1049/core.tex#L4587-L4587), [cite at paper/reasoning-parts/erdos1049/core.tex:4590](../../paper/reasoning-parts/erdos1049/core.tex#L4590-L4590)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5307-L5310) — lines `5307–5310`; excerpt `sha256:20b0b33ebb4cd3cbf86a87600342b42670e722c45b2b8f83015e0c8f3160e9da`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1444-L1446) — lines `1444–1446`; excerpt `sha256:12e925bb796b6215db708d25b5d1ab1c5640c351e7f3683e2c91ae968206b259`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4804-L4808) — lines `4804–4808`; excerpt `sha256:cf446c3cbb0c405bcc80ec2c25d599a8a83cd781fed2f9312d32338c1383374d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4773-L4777) — lines `4773–4777`; excerpt `sha256:cf446c3cbb0c405bcc80ec2c25d599a8a83cd781fed2f9312d32338c1383374d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:e06d2e72d93c52fba3ae2473df2bb6b9f6ac53c8a0b97d7f71ed0ee9e7bcc574`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:e06d2e72d93c52fba3ae2473df2bb6b9f6ac53c8a0b97d7f71ed0ee9e7bcc574`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:e06d2e72d93c52fba3ae2473df2bb6b9f6ac53c8a0b97d7f71ed0ee9e7bcc574`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L2044-L2045) — lines `2044–2045`; excerpt `sha256:da5a2b6be594eb622f6493ba7b287897955792d0f4a849924d6977e44d0c48c1`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L879-L879) — lines `879–879`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
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
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9988-L9992) — lines `9988–9992`; excerpt `sha256:83ff6ef68815bf0b391a143e9e5336b1ff5b127bd0fbcac01ed9f7a399d02225`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9796-L9800) — lines `9796–9800`; excerpt `sha256:83ff6ef68815bf0b391a143e9e5336b1ff5b127bd0fbcac01ed9f7a399d02225`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9468-L9471) — lines `9468–9471`; excerpt `sha256:7a684bfaefd18d542b221d902849314551f3d7d7c0bdd860824a938e6896ecd7`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9268-L9271) — lines `9268–9271`; excerpt `sha256:7a684bfaefd18d542b221d902849314551f3d7d7c0bdd860824a938e6896ecd7`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:49](../../paper/257/erdos-257-mersenne-support-subseries.tex#L49-L49), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:690](../../paper/257/erdos-257-mersenne-support-subseries.tex#L690-L690)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:64](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L64-L64), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3477](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3477-L3477), [cite at paper/reasoning-parts/erdos1049/core.tex:33](../../paper/reasoning-parts/erdos1049/core.tex#L33-L33), [cite at paper/reasoning-parts/erdos1049/core.tex:3446](../../paper/reasoning-parts/erdos1049/core.tex#L3446-L3446)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:115](../../paper/archive/erdos249-257-main-paper.tex#L115-L115), [cite at paper/archive/erdos249-257-main-paper.tex:630](../../paper/archive/erdos249-257-main-paper.tex#L630-L630), [cite at paper/archive/erdos249-257-main-paper.tex:633](../../paper/archive/erdos249-257-main-paper.tex#L633-L633)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1690](../../paper/249/erdos249-totient-reasoning-surface.tex#L1690-L1690), [cite at paper/249/erdos249-totient-reasoning-surface.tex:1713](../../paper/249/erdos249-totient-reasoning-surface.tex#L1713-L1713), [cite at paper/249/erdos249-totient-reasoning-surface.tex:2633](../../paper/249/erdos249-totient-reasoning-surface.tex#L2633-L2633), [cite at paper/249/erdos249-totient-reasoning-surface.tex:5534](../../paper/249/erdos249-totient-reasoning-surface.tex#L5534-L5534), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7837](../../paper/249/erdos249-totient-reasoning-surface.tex#L7837-L7837), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7847](../../paper/249/erdos249-totient-reasoning-surface.tex#L7847-L7847), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1498](../../paper/reasoning-parts/erdos249/a249_front.tex#L1498-L1498), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1521](../../paper/reasoning-parts/erdos249/a249_front.tex#L1521-L1521), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:2441](../../paper/reasoning-parts/erdos249/a249_front.tex#L2441-L2441), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:5342](../../paper/reasoning-parts/erdos249/a249_front.tex#L5342-L5342), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7645](../../paper/reasoning-parts/erdos249/a249_front.tex#L7645-L7645), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7655](../../paper/reasoning-parts/erdos249/a249_front.tex#L7655-L7655)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1079](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1079-L1079), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1380](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1380-L1380), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2928](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2928-L2928), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:6810](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L6810-L6810), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:879](../../paper/reasoning-parts/erdos257/a257_front.tex#L879-L879), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1180](../../paper/reasoning-parts/erdos257/a257_front.tex#L1180-L1180), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2728](../../paper/reasoning-parts/erdos257/a257_front.tex#L2728-L2728), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:6610](../../paper/reasoning-parts/erdos257/a257_front.tex#L6610-L6610)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10080-L10084) — lines `10080–10084`; excerpt `sha256:77de149e1b9e4c1cbd9c39690b007e9959c56e7732149a19d644b96ce9c396c8`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9888-L9892) — lines `9888–9892`; excerpt `sha256:77de149e1b9e4c1cbd9c39690b007e9959c56e7732149a19d644b96ce9c396c8`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:4217](../../paper/249/erdos249-totient-reasoning-surface.tex#L4217-L4217), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:4025](../../paper/reasoning-parts/erdos249/a249_front.tex#L4025-L4025)

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
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1269-L1270) — lines `1269–1270`; excerpt `sha256:ed477db421c75bd2bf0fc9a8324059f75c74acbb2096b75ffc57c88c0fabd274`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:959](../../paper/systems/claim-faithful-publication-systems-paper.tex#L959-L959)
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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2897-L2899) — lines `2897–2899`; excerpt `sha256:46d4d39e3d51b2837c93b4e701c6caaf1022bcecb3c0b0c8dcc4e198022fc852`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2856-L2858) — lines `2856–2858`; excerpt `sha256:46d4d39e3d51b2837c93b4e701c6caaf1022bcecb3c0b0c8dcc4e198022fc852`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4293-L4296) — lines `4293–4296`; excerpt `sha256:3bb82e6b41bc7ebd606d251e5b57d3c92e82927c527268e1c978c3131c24c529`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4242-L4245) — lines `4242–4245`; excerpt `sha256:3bb82e6b41bc7ebd606d251e5b57d3c92e82927c527268e1c978c3131c24c529`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1216](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1216-L1216), [cite at paper/reasoning-parts/erdos251/core.tex:1175](../../paper/reasoning-parts/erdos251/core.tex#L1175-L1175)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2932](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2932-L2932), [cite at paper/reasoning-parts/erdos269/core.tex:2881](../../paper/reasoning-parts/erdos269/core.tex#L2881-L2881)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L865-L869) — lines `865–869`; excerpt `sha256:7eb810a856d8371d607b27c13d08cdb1e45b57dea452204683e677e9ad4ad61e`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3025-L3029) — lines `3025–3029`; excerpt `sha256:dd044dad6d56b9bf4fbea7b10c5f1541732d45804e9ab24eba3d70dc193802b7`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2990-L2994) — lines `2990–2994`; excerpt `sha256:dd044dad6d56b9bf4fbea7b10c5f1541732d45804e9ab24eba3d70dc193802b7`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L390-L390) — lines `390–390`; excerpt `sha256:f79753efe99565cb54902130359759280c3fe18d64ad7ada9e6b45359ab7373f`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L390-L390) — lines `390–390`; excerpt `sha256:f79753efe99565cb54902130359759280c3fe18d64ad7ada9e6b45359ab7373f`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L906-L906) — lines `906–906`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L906-L906) — lines `906–906`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L906-L906) — lines `906–906`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L906-L906) — lines `906–906`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:390](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L390-L390)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:941](../../paper/68/erdos68-factorial-reasoning-surface.tex#L941-L941), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1026](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1026-L1026), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2171](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2171-L2171), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2173](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2173-L2173), [cite at paper/reasoning-parts/erdos68/core.tex:906](../../paper/reasoning-parts/erdos68/core.tex#L906-L906), [cite at paper/reasoning-parts/erdos68/core.tex:991](../../paper/reasoning-parts/erdos68/core.tex#L991-L991), [cite at paper/reasoning-parts/erdos68/core.tex:2136](../../paper/reasoning-parts/erdos68/core.tex#L2136-L2136), [cite at paper/reasoning-parts/erdos68/core.tex:2138](../../paper/reasoning-parts/erdos68/core.tex#L2138-L2138)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5331-L5335) — lines `5331–5335`; excerpt `sha256:3a65bfeacf2ad8a25e0f67d84cbd49de341eed686e5744522532edb843972cc8`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L81-L81) — lines `81–81`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10013-L10020) — lines `10013–10020`; excerpt `sha256:168b06eeef0d655602ef10d79d4d5a2c298c562e5b09b730a812b94d0458d1a2`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9821-L9828) — lines `9821–9828`; excerpt `sha256:168b06eeef0d655602ef10d79d4d5a2c298c562e5b09b730a812b94d0458d1a2`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:500](../../paper/archive/erdos249-257-main-paper.tex#L500-L500), [cite at paper/archive/erdos249-257-main-paper.tex:4086](../../paper/archive/erdos249-257-main-paper.tex#L4086-L4086), [cite at paper/archive/erdos249-257-main-paper.tex:4785](../../paper/archive/erdos249-257-main-paper.tex#L4785-L4785)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1738](../../paper/249/erdos249-totient-reasoning-surface.tex#L1738-L1739), [cite at paper/249/erdos249-totient-reasoning-surface.tex:9885](../../paper/249/erdos249-totient-reasoning-surface.tex#L9885-L9885), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1546](../../paper/reasoning-parts/erdos249/a249_front.tex#L1546-L1547), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9693](../../paper/reasoning-parts/erdos249/a249_front.tex#L9693-L9693)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L867-L871) — lines `867–871`; excerpt `sha256:eacde95a2a008044b34dad3bc740d3a6e33953232b7364e5c222730a382b3f1e`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5236-L5240) — lines `5236–5240`; excerpt `sha256:b88bf461b59f2aca4fbd717fe1f7fae9a31ad41586223d8984be19883d35f1de`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5192-L5196) — lines `5192–5196`; excerpt `sha256:b88bf461b59f2aca4fbd717fe1f7fae9a31ad41586223d8984be19883d35f1de`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:ec216dae4e1ec5b7681eb4f14cd219fe516d1a80a356c7abe9b83c3727916844`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:ec216dae4e1ec5b7681eb4f14cd219fe516d1a80a356c7abe9b83c3727916844`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L33-L33) — lines `33–33`; excerpt `sha256:ec216dae4e1ec5b7681eb4f14cd219fe516d1a80a356c7abe9b83c3727916844`
- [lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean](../../lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean#L47-L52) — lines `47–52`; excerpt `sha256:33cfc2f7e37e3a2c10db006bdf734166bb372b874a1933fa3324a066b6552b44`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1103-L1106) — lines `1103–1106`; excerpt `sha256:1c7bbff8b9ecf2229080e8b8ba7833142628f64292e1aecef725441fa86f7ef9`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:950](../../paper/systems/claim-faithful-publication-systems-paper.tex#L950-L950)
- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:61](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L61-L61), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:677](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L677-L677)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:77](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L77-L77), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1646](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1646-L1646), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2238](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2238-L2238), [cite at paper/reasoning-parts/erdos1041/core.tex:33](../../paper/reasoning-parts/erdos1041/core.tex#L33-L33), [cite at paper/reasoning-parts/erdos1041/core.tex:1602](../../paper/reasoning-parts/erdos1041/core.tex#L1602-L1602), [cite at paper/reasoning-parts/erdos1041/core.tex:2194](../../paper/reasoning-parts/erdos1041/core.tex#L2194-L2194)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1065-L1068) — lines `1065–1068`; excerpt `sha256:a90c5dfbfb8e145cf527f538fca7dae79167bd3b9090eb55e85806bc4d0edba4`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4284-L4287) — lines `4284–4287`; excerpt `sha256:a90c5dfbfb8e145cf527f538fca7dae79167bd3b9090eb55e85806bc4d0edba4`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4233-L4236) — lines `4233–4236`; excerpt `sha256:a90c5dfbfb8e145cf527f538fca7dae79167bd3b9090eb55e85806bc4d0edba4`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:996](../../paper/269/erdos-269-three-prime-running-lcm.tex#L996-L996)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2075](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2075-L2075), [cite at paper/reasoning-parts/erdos269/core.tex:2024](../../paper/reasoning-parts/erdos269/core.tex#L2024-L2024)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4812-L4816) — lines `4812–4816`; excerpt `sha256:ba25c19782edca439fc59536016a13c5d36a33cd2f359c1c6f2080fb7a229a6d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4781-L4785) — lines `4781–4785`; excerpt `sha256:ba25c19782edca439fc59536016a13c5d36a33cd2f359c1c6f2080fb7a229a6d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4515-L4515) — lines `4515–4515`; excerpt `sha256:c2aaa0c462b306e178c3f673ec026c7a33d2885dc0bdb20b45061a7ba1d2ad52`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4546](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4546-L4546), [cite at paper/reasoning-parts/erdos1049/core.tex:4515](../../paper/reasoning-parts/erdos1049/core.tex#L4515-L4515)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5363-L5369) — lines `5363–5369`; excerpt `sha256:77bdb4aaccf3767207aeaa531daa9b36b72b6f99ea6282713f5fedd223ebf6a0`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L2440-L2440) — lines `2440–2440`; excerpt `sha256:4981ac14d5920d3c14f3419aeb71ae38c99632f3a948fda8a4f21229dd4514f8`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L2440-L2440) — lines `2440–2440`; excerpt `sha256:4981ac14d5920d3c14f3419aeb71ae38c99632f3a948fda8a4f21229dd4514f8`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L18396-L18404) — lines `18396–18404`; excerpt `sha256:6d631a23b443180906d917bb60d1a6c65c9fd2a705b5a9ed4ed4e026e91ae20d`
- [lean/Erdos249257/MersenneLambertLadder.lean](../../lean/Erdos249257/MersenneLambertLadder.lean#L15-L27) — lines `15–27`; excerpt `sha256:b17ccf4eb86418af3ba24ecd888e62fe5e23ef5fbf22c02f21fad26eef0562d0`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9998-L10003) — lines `9998–10003`; excerpt `sha256:786abf98fbd01e8ff40ec5a22574fff70c8c6565197a70a1b1cf5f71fbf62c38`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9806-L9811) — lines `9806–9811`; excerpt `sha256:786abf98fbd01e8ff40ec5a22574fff70c8c6565197a70a1b1cf5f71fbf62c38`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:529](../../paper/archive/erdos249-257-main-paper.tex#L529-L529), [cite at paper/archive/erdos249-257-main-paper.tex:560](../../paper/archive/erdos249-257-main-paper.tex#L560-L560)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:2632](../../paper/249/erdos249-totient-reasoning-surface.tex#L2632-L2632), [cite at paper/249/erdos249-totient-reasoning-surface.tex:3815](../../paper/249/erdos249-totient-reasoning-surface.tex#L3815-L3815), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:2440](../../paper/reasoning-parts/erdos249/a249_front.tex#L2440-L2440), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:3623](../../paper/reasoning-parts/erdos249/a249_front.tex#L3623-L3623)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1462-L1465) — lines `1462–1465`; excerpt `sha256:defd9a2ce501d09c198612d2849b08f6a067d1b43209958db0a0f1bc2c6a9fee`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9491-L9497) — lines `9491–9497`; excerpt `sha256:bfddd679ba6ccf3efd131b25b49729ba82e27339010d41e166fd995306f8494a`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9291-L9297) — lines `9291–9297`; excerpt `sha256:bfddd679ba6ccf3efd131b25b49729ba82e27339010d41e166fd995306f8494a`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L518-L519) — lines `518–519`; excerpt `sha256:4c4861d2cae484653a1e3d2ea0d051919da8b0b8cd404dba7e783d700375f2ff`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2949-L2951) — lines `2949–2951`; excerpt `sha256:17a384a1fdc66bdc50bfc789563acfc6b6e42f091c58ab6c6108261e4a3dd127`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2908-L2910) — lines `2908–2910`; excerpt `sha256:17a384a1fdc66bdc50bfc789563acfc6b6e42f091c58ab6c6108261e4a3dd127`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:945](../../paper/257/erdos-257-mersenne-support-subseries.tex#L945-L945), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1374](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1374-L1374)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:518](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L518-L518), [cite at paper/reasoning-parts/erdos251/core.tex:477](../../paper/reasoning-parts/erdos251/core.tex#L477-L477)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1312](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1312-L1312), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2307](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2307-L2307), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:5507](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L5507-L5507), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9417](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9417-L9417), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1112](../../paper/reasoning-parts/erdos257/a257_front.tex#L1112-L1112), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2107](../../paper/reasoning-parts/erdos257/a257_front.tex#L2107-L2107), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:5307](../../paper/reasoning-parts/erdos257/a257_front.tex#L5307-L5307), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9217](../../paper/reasoning-parts/erdos257/a257_front.tex#L9217-L9217)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L614-L616) — lines `614–616`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2909-L2911) — lines `2909–2911`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2868-L2870) — lines `2868–2870`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1897-L1897) — lines `1897–1897`; excerpt `sha256:1c353b92a6150c3c1fd31caf9ea67c600326deef9ecc2bd683a7fda752871261`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1898-L1898) — lines `1898–1898`; excerpt `sha256:b6e73fa3c5843b9322f980cfbc458e10518d0b0d75da433be27f464b8b1db2c8`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L21-L21) — lines `21–21`; excerpt `sha256:07dad1a6dbaa03c54631370154c906de91a50cd710b3b9c6e143f85e14b3c973`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L614-L616) — lines `614–616`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2909-L2911) — lines `2909–2911`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2868-L2870) — lines `2868–2870`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:553](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L553-L553)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1939](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1939-L1939), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1941](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1941-L1941), [cite at paper/reasoning-parts/erdos251/core.tex:1898](../../paper/reasoning-parts/erdos251/core.tex#L1898-L1898), [cite at paper/reasoning-parts/erdos251/core.tex:1900](../../paper/reasoning-parts/erdos251/core.tex#L1900-L1900)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5422-L5428) — lines `5422–5428`; excerpt `sha256:f3e98b048d91936f24d3575618c5935a8f710849e94afd0c3c7451115a89db41`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1436-L1440) — lines `1436–1440`; excerpt `sha256:b8aeba1b74c5004a308c7a77d0dacb7f303d2e1210da60dac512f3834b9dfb1d`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L969-L969) — lines `969–969`; excerpt `sha256:e8f0eb9c08b32d040eb9d382b55721fcbada06cfa90efaa2936a851eae07396b`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1870-L1870) — lines `1870–1870`; excerpt `sha256:65cd5e4e29d1cdc61e86b1fdfd3aa0da4bc9945beae2af9f53b372cd68363f58`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8082-L8082) — lines `8082–8082`; excerpt `sha256:15ac24d3bb2a60a3a8644dbaa74f8f7584e82afe96beea17331f198e477b3da8`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8437-L8437) — lines `8437–8437`; excerpt `sha256:7ddfabbfa80938c48b779f2b3418205424c4f3e925ef9cc11a07e77b0ce99902`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9141-L9146) — lines `9141–9146`; excerpt `sha256:c427aea096590bf4f8315ac8e13c2e92925eb10e1f02993b79815bfea6191556`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9651-L9656) — lines `9651–9656`; excerpt `sha256:01736f364c6af6f08a7498583610f9761ec3023900cdc6b3a5a25a416cccbf9e`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9526-L9537) — lines `9526–9537`; excerpt `sha256:3171372fd423eb3435f8b30446d71ac1de6f8b8a34d05c55191952194f66d6dd`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9326-L9337) — lines `9326–9337`; excerpt `sha256:3171372fd423eb3435f8b30446d71ac1de6f8b8a34d05c55191952194f66d6dd`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:674](../../paper/257/erdos-257-mersenne-support-subseries.tex#L674-L674)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:767](../../paper/archive/erdos249-257-main-paper.tex#L767-L768)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2151](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2151-L2151), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1951](../../paper/reasoning-parts/erdos257/a257_front.tex#L1951-L1951)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1860](../../paper/synthesis/optimal-sparse-perturbations.tex#L1860-L1860)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1490-L1497) — lines `1490–1497`; excerpt `sha256:9fb245c54bf24e5b9fefda94bc836f1a8dae5e0a9c852475ce12f264cb114471`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9581-L9587) — lines `9581–9587`; excerpt `sha256:e9c60c753e365223406c899dee816ed5743af3cc67081cc3002ceb4f8cf6b1da`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9381-L9387) — lines `9381–9387`; excerpt `sha256:e9c60c753e365223406c899dee816ed5743af3cc67081cc3002ceb4f8cf6b1da`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:944](../../paper/257/erdos-257-mersenne-support-subseries.tex#L944-L944)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9416](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9416-L9416), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9216](../../paper/reasoning-parts/erdos257/a257_front.tex#L9216-L9216)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:883](../../paper/synthesis/optimal-sparse-perturbations.tex#L883-L883), [cite at paper/synthesis/optimal-sparse-perturbations.tex:910](../../paper/synthesis/optimal-sparse-perturbations.tex#L910-L910), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1975](../../paper/synthesis/optimal-sparse-perturbations.tex#L1975-L1975)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L889-L893) — lines `889–893`; excerpt `sha256:fc6fd8468b61e2df565a66c6f80ada42f10c2a199342733fd32a56b58a37f741`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3057-L3061) — lines `3057–3061`; excerpt `sha256:e676e6cb0116aea00ea8f9c6ab98b451db00b3a8f7711be43649ec04855f1014`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3022-L3026) — lines `3022–3026`; excerpt `sha256:e676e6cb0116aea00ea8f9c6ab98b451db00b3a8f7711be43649ec04855f1014`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:579](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L579-L579)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1626](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1626-L1626), [cite at paper/reasoning-parts/erdos68/core.tex:1591](../../paper/reasoning-parts/erdos68/core.tex#L1591-L1591)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5376-L5383) — lines `5376–5383`; excerpt `sha256:690f1f58f32c3dd75fa57e5966f1e713460a42c814f9ab411c04c7e2183ee0b0`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4923-L4929) — lines `4923–4929`; excerpt `sha256:7edeec595003b28ac91040a61c50d3a57a5872bbc9871d704d9ba32a048e1a23`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4892-L4898) — lines `4892–4898`; excerpt `sha256:7edeec595003b28ac91040a61c50d3a57a5872bbc9871d704d9ba32a048e1a23`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4595-L4595) — lines `4595–4595`; excerpt `sha256:21196a6cc9019dd41d30945a6a3d9e8e466447c7c1830ee9e83704db25a0ef1f`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L11735-L11740) — lines `11735–11740`; excerpt `sha256:563923daea706e56c4f2e7175d13053380af2dc3a24ac50d9212c2b0b6d7634e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L12806-L12811) — lines `12806–12811`; excerpt `sha256:448131d83b624b6ce5520dce8ac090fcec58010089d33f41e6a4644fb0ca8a01`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L12962-L12969) — lines `12962–12969`; excerpt `sha256:85e296ca403f80f61aacb885a69266e7645176834ee36a40fbd6e9652cf62bce`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L13680-L13685) — lines `13680–13685`; excerpt `sha256:0de2a3ac66ecee1b3a0e617d573bb7de8678b3975f019984a2d7a83aa43ffbf9`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L14196-L14200) — lines `14196–14200`; excerpt `sha256:12fe3f3b9cef7b6405e234a689ac1e837abfeb24254cb43a2d6815961f8e0b30`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1465-L1471) — lines `1465–1471`; excerpt `sha256:e2ea1dec26aa5bc12b24ae324b5eec9758dfe18eef2464f06f2c610f65164b7d`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9480-L9491) — lines `9480–9491`; excerpt `sha256:dc3b6825148962fe6dcac631ca31bbed24b0c5d155adf89e2b13951655dda752`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9280-L9291) — lines `9280–9291`; excerpt `sha256:dc3b6825148962fe6dcac631ca31bbed24b0c5d155adf89e2b13951655dda752`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1372](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1372-L1372)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4626](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4626-L4626), [cite at paper/reasoning-parts/erdos1049/core.tex:4595](../../paper/reasoning-parts/erdos1049/core.tex#L4595-L4595)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:718](../../paper/archive/erdos249-257-main-paper.tex#L718-L718), [cite at paper/archive/erdos249-257-main-paper.tex:720](../../paper/archive/erdos249-257-main-paper.tex#L720-L720), [cite at paper/archive/erdos249-257-main-paper.tex:724](../../paper/archive/erdos249-257-main-paper.tex#L724-L724), [cite at paper/archive/erdos249-257-main-paper.tex:726](../../paper/archive/erdos249-257-main-paper.tex#L726-L726), [cite at paper/archive/erdos249-257-main-paper.tex:729](../../paper/archive/erdos249-257-main-paper.tex#L729-L729), [cite at paper/archive/erdos249-257-main-paper.tex:3853](../../paper/archive/erdos249-257-main-paper.tex#L3853-L3854), [cite at paper/archive/erdos249-257-main-paper.tex:3859](../../paper/archive/erdos249-257-main-paper.tex#L3859-L3859)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1083](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1083-L1083), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1086](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1086-L1086), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1192](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1192-L1192), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2259](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2259-L2259), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2286](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2286-L2286), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3020](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3020-L3020), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3051](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3051-L3051), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3055](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3055-L3055), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3176](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3176-L3176), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:6926](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L6926-L6926), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7083](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7083-L7083), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9408](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9408-L9408), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:883](../../paper/reasoning-parts/erdos257/a257_front.tex#L883-L883), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:886](../../paper/reasoning-parts/erdos257/a257_front.tex#L886-L886), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:992](../../paper/reasoning-parts/erdos257/a257_front.tex#L992-L992), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2059](../../paper/reasoning-parts/erdos257/a257_front.tex#L2059-L2059), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2086](../../paper/reasoning-parts/erdos257/a257_front.tex#L2086-L2086), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2820](../../paper/reasoning-parts/erdos257/a257_front.tex#L2820-L2820), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2851](../../paper/reasoning-parts/erdos257/a257_front.tex#L2851-L2851), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2855](../../paper/reasoning-parts/erdos257/a257_front.tex#L2855-L2855), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2976](../../paper/reasoning-parts/erdos257/a257_front.tex#L2976-L2976), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:6726](../../paper/reasoning-parts/erdos257/a257_front.tex#L6726-L6726), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:6883](../../paper/reasoning-parts/erdos257/a257_front.tex#L6883-L6883), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9208](../../paper/reasoning-parts/erdos257/a257_front.tex#L9208-L9208)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1162-L1165) — lines `1162–1165`; excerpt `sha256:b82d8ed1c80672ed82ae452a87448ac398ce482d8717aebd2d8eb1d7b21c714d`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:822](../../paper/systems/claim-faithful-publication-systems-paper.tex#L822-L822)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L733-L739) — lines `733–739`; excerpt `sha256:baac1f8ff06d86954ea6fb3d6ea4be3f7ba3e7cc9c207ea61e4e3d1c42db53d0`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10093-L10099) — lines `10093–10099`; excerpt `sha256:baac1f8ff06d86954ea6fb3d6ea4be3f7ba3e7cc9c207ea61e4e3d1c42db53d0`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9901-L9907) — lines `9901–9907`; excerpt `sha256:baac1f8ff06d86954ea6fb3d6ea4be3f7ba3e7cc9c207ea61e4e3d1c42db53d0`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:627](../../paper/249/erdos-249-binary-totient-series.tex#L627-L627)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:288](../../paper/249/erdos249-totient-reasoning-surface.tex#L288-L289), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:96](../../paper/reasoning-parts/erdos249/a249_front.tex#L96-L97)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5369-L5376) — lines `5369–5376`; excerpt `sha256:5a1a511c5f97e370e3878ea3ba811d494255649a47bf397f5ba6a6bc5538a1f3`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L18614-L18619) — lines `18614–18619`; excerpt `sha256:1ddc9c03c740ef6c475f6cab866ca8afd592972f666408305d7d85b4399ccba6`
- [lean/Erdos249257/GcdMomentCalculus.lean](../../lean/Erdos249257/GcdMomentCalculus.lean#L31-L37) — lines `31–37`; excerpt `sha256:df63d9348b43000b662da16518b601491c3fd177be47b864cb61bf0db772b86c`
- [lean/Erdos249257/GcdMomentCalculus.lean](../../lean/Erdos249257/GcdMomentCalculus.lean#L210-L216) — lines `210–216`; excerpt `sha256:f2f4533d57864d5d1c1ccb3b19e15365cab99d16e5b432b8737687af0eb24265`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9992-L9998) — lines `9992–9998`; excerpt `sha256:d225e8a6b24e1aa1895e5b08441a48c78042c267387c9e1c0073591e2991cb37`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9800-L9806) — lines `9800–9806`; excerpt `sha256:d225e8a6b24e1aa1895e5b08441a48c78042c267387c9e1c0073591e2991cb37`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1096-L1102) — lines `1096–1102`; excerpt `sha256:4ce4046469794790aba2dd446aea947f73b80cbd8f7aa313de40dda280a3a9ef`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4969-L4975) — lines `4969–4975`; excerpt `sha256:ae062de55b96a5c30b121b0f18d20452951075be7688d2b736a0ddcd2277483b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4938-L4944) — lines `4938–4944`; excerpt `sha256:ae062de55b96a5c30b121b0f18d20452951075be7688d2b736a0ddcd2277483b`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:906](../../paper/1049/erdos-1049-rational-base-lambert.tex#L906-L906)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1206](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1206-L1206), [cite at paper/reasoning-parts/erdos1049/core.tex:1175](../../paper/reasoning-parts/erdos1049/core.tex#L1175-L1175)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3970](../../paper/archive/erdos249-257-main-paper.tex#L3970-L3971)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1754](../../paper/249/erdos249-totient-reasoning-surface.tex#L1754-L1754), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1562](../../paper/reasoning-parts/erdos249/a249_front.tex#L1562-L1562)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4994-L4999) — lines `4994–4999`; excerpt `sha256:4948c1fb7d6744d97873f78ed67c6b8f64ed69d62dfe299bf8c4335148a7d850`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4963-L4968) — lines `4963–4968`; excerpt `sha256:4948c1fb7d6744d97873f78ed67c6b8f64ed69d62dfe299bf8c4335148a7d850`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4632](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4632-L4632), [cite at paper/reasoning-parts/erdos1049/core.tex:4601](../../paper/reasoning-parts/erdos1049/core.tex#L4601-L4601)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2953-L2955) — lines `2953–2955`; excerpt `sha256:4b2c462e9156fcefa9deab67573f0793906c11306432364ce53464dbb6c19538`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2912-L2914) — lines `2912–2914`; excerpt `sha256:4b2c462e9156fcefa9deab67573f0793906c11306432364ce53464dbb6c19538`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:523](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L523-L523), [cite at paper/reasoning-parts/erdos251/core.tex:482](../../paper/reasoning-parts/erdos251/core.tex#L482-L482)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L713-L716) — lines `713–716`; excerpt `sha256:56a8f02f756379e8b9f86571b2146e088317bf4d41df88c247647efa76da475f`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9976-L9980) — lines `9976–9980`; excerpt `sha256:bb9e02a0cb308737040e1d9af54ab2a42d227d1dbf584528d1d8763f1f2fe1e1`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9784-L9788) — lines `9784–9788`; excerpt `sha256:bb9e02a0cb308737040e1d9af54ab2a42d227d1dbf584528d1d8763f1f2fe1e1`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:495](../../paper/249/erdos-249-binary-totient-series.tex#L495-L495)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1601](../../paper/249/erdos249-totient-reasoning-surface.tex#L1601-L1601), [cite at paper/249/erdos249-totient-reasoning-surface.tex:9589](../../paper/249/erdos249-totient-reasoning-surface.tex#L9589-L9589), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1409](../../paper/reasoning-parts/erdos249/a249_front.tex#L1409-L1409), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9397](../../paper/reasoning-parts/erdos249/a249_front.tex#L9397-L9397)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4287-L4290) — lines `4287–4290`; excerpt `sha256:4fd45772ff7add1f64a2a0aceb707abf3ec134b84b8189985e359c4a31876a7b`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1068-L1071) — lines `1068–1071`; excerpt `sha256:89365f17cd5c9375bfee104214e4355cd14808bfdc25bae5d0d57d71698246ad`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4236-L4239) — lines `4236–4239`; excerpt `sha256:4fd45772ff7add1f64a2a0aceb707abf3ec134b84b8189985e359c4a31876a7b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2026-L2026) — lines `2026–2026`; excerpt `sha256:b87bb3e4a7af82e9910a8693bb635b75f50fdfb4e5b86a06543454c0545aca25`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L997-L997) — lines `997–997`; excerpt `sha256:961bd6a78ce8cda3c09ee72527f5bbe134663f8001e53d1a5ffa9a9db34eea5a`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:997](../../paper/269/erdos-269-three-prime-running-lcm.tex#L997-L997)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2077](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2077-L2077), [cite at paper/reasoning-parts/erdos269/core.tex:2026](../../paper/reasoning-parts/erdos269/core.tex#L2026-L2026)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3077-L3081) — lines `3077–3081`; excerpt `sha256:a48ddc588b042ca4c1ef063504be6dd2e3c0c0d8f6ce9a6a0b3fe1989375c081`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3042-L3046) — lines `3042–3046`; excerpt `sha256:a48ddc588b042ca4c1ef063504be6dd2e3c0c0d8f6ce9a6a0b3fe1989375c081`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1737](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1737-L1737), [cite at paper/reasoning-parts/erdos68/core.tex:1702](../../paper/reasoning-parts/erdos68/core.tex#L1702-L1702)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5352-L5358) — lines `5352–5358`; excerpt `sha256:4a7aa0cbb0dba5d29390adbbc95554c796fb3eee93f2efae803d6c97270c9768`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L688-L692) — lines `688–692`; excerpt `sha256:3a615d5188e3c811f81c9421c1fae9cae57aa51eaecc361017b08887fd690350`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L61-L61) — lines `61–61`; excerpt `sha256:c1960cd50c0146b008839691c83ef53220ec6bdf251ce3c02d30ff006670e01a`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L62-L62) — lines `62–62`; excerpt `sha256:b6ce0fb599e9bf02898ae89ea89e3bf47a7a31efcaab7ffbe2a9e2aaaae8ab8c`
- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L166-L166) — lines `166–166`; excerpt `sha256:3260d5a1253a2750f8cda31532306f204142e47cb4ce3964043dff2fdb598f14`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L256-L256) — lines `256–256`; excerpt `sha256:48a3dc935a9efd4f525b4196ade8751cfd054cab2285d0b3acf1c074f18578f9`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L84-L84) — lines `84–84`; excerpt `sha256:cb49a811183c00893bef1ffc247d63d3efebe505db66c5ea17d14f12b750a7bf`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L84-L84) — lines `84–84`; excerpt `sha256:cb49a811183c00893bef1ffc247d63d3efebe505db66c5ea17d14f12b750a7bf`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L256-L256) — lines `256–256`; excerpt `sha256:48a3dc935a9efd4f525b4196ade8751cfd054cab2285d0b3acf1c074f18578f9`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9947-L9952) — lines `9947–9952`; excerpt `sha256:5cedcebcfca20ab63e92ba4441d035c85b0a632e564a43408ffe6b79fe30ae48`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9755-L9760) — lines `9755–9760`; excerpt `sha256:5cedcebcfca20ab63e92ba4441d035c85b0a632e564a43408ffe6b79fe30ae48`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:925](../../paper/systems/claim-faithful-publication-systems-paper.tex#L925-L925)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:62](../../paper/249/erdos-249-binary-totient-series.tex#L62-L62), [cite at paper/249/erdos-249-binary-totient-series.tex:618](../../paper/249/erdos-249-binary-totient-series.tex#L618-L618)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3187](../../paper/archive/erdos249-257-main-paper.tex#L3187-L3187)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:276](../../paper/249/erdos249-totient-reasoning-surface.tex#L276-L276), [cite at paper/249/erdos249-totient-reasoning-surface.tex:6823](../../paper/249/erdos249-totient-reasoning-surface.tex#L6823-L6823), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8467](../../paper/249/erdos249-totient-reasoning-surface.tex#L8467-L8467), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:84](../../paper/reasoning-parts/erdos249/a249_front.tex#L84-L84), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6631](../../paper/reasoning-parts/erdos249/a249_front.tex#L6631-L6631), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8275](../../paper/reasoning-parts/erdos249/a249_front.tex#L8275-L8275)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L517-L517) — lines `517–517`; excerpt `sha256:8d5dd05c085a4fd98e3f503d81e2c85f42cafdb7ab70462763044bc5e7a1c380`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2937-L2939) — lines `2937–2939`; excerpt `sha256:61ad353ab13c9df0f317f4f72d599dc10397c01254ccf1035a02cf84853d8304`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2896-L2898) — lines `2896–2898`; excerpt `sha256:61ad353ab13c9df0f317f4f72d599dc10397c01254ccf1035a02cf84853d8304`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9587-L9593) — lines `9587–9593`; excerpt `sha256:e118982ef9fb8a4e691c79683424d1b891a905dfc8672b0a0f1e9237f5fb3d99`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9387-L9393) — lines `9387–9393`; excerpt `sha256:e118982ef9fb8a4e691c79683424d1b891a905dfc8672b0a0f1e9237f5fb3d99`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:517](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L517-L517), [cite at paper/reasoning-parts/erdos251/core.tex:476](../../paper/reasoning-parts/erdos251/core.tex#L476-L476)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9418](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9418-L9418), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9218](../../paper/reasoning-parts/erdos257/a257_front.tex#L9218-L9218)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L511-L512) — lines `511–512`; excerpt `sha256:b7acbadf514865bc634e221a2b56c30a420e8adc4a8760dde974814e250b0456`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2939-L2941) — lines `2939–2941`; excerpt `sha256:a876ac96db99087a07bfa49f869f9990f286e49a52310ceab8423d7980641577`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2898-L2900) — lines `2898–2900`; excerpt `sha256:a876ac96db99087a07bfa49f869f9990f286e49a52310ceab8423d7980641577`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:512](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L512-L512), [cite at paper/reasoning-parts/erdos251/core.tex:471](../../paper/reasoning-parts/erdos251/core.tex#L471-L471)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1276-L1282) — lines `1276–1282`; excerpt `sha256:fdc72e5f8bd263e4a323f5c9a3cde8b9b721106fee45e5666a814b1163e3a605`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4052-L4058) — lines `4052–4058`; excerpt `sha256:fdc72e5f8bd263e4a323f5c9a3cde8b9b721106fee45e5666a814b1163e3a605`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4013-L4019) — lines `4013–4019`; excerpt `sha256:fdc72e5f8bd263e4a323f5c9a3cde8b9b721106fee45e5666a814b1163e3a605`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1071-L1074) — lines `1071–1074`; excerpt `sha256:45604844b23b875721c499f1d941719928dcc2b6bb269b97c8564702e5d3051b`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4296-L4299) — lines `4296–4299`; excerpt `sha256:45604844b23b875721c499f1d941719928dcc2b6bb269b97c8564702e5d3051b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4245-L4248) — lines `4245–4248`; excerpt `sha256:45604844b23b875721c499f1d941719928dcc2b6bb269b97c8564702e5d3051b`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1045](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1045-L1045), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1093](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1093-L1093)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:999](../../paper/269/erdos-269-three-prime-running-lcm.tex#L999-L999)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:784](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L784-L784), [cite at paper/reasoning-parts/erdos243/core.tex:745](../../paper/reasoning-parts/erdos243/core.tex#L745-L745)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2436](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2436-L2436), [cite at paper/reasoning-parts/erdos269/core.tex:2385](../../paper/reasoning-parts/erdos269/core.tex#L2385-L2385)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4253-L4256) — lines `4253–4256`; excerpt `sha256:5eafead45851c5d9d3dbc7e8333b2811c3bfb396c82d092e088a35955fc4a00e`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4202-L4205) — lines `4202–4205`; excerpt `sha256:5eafead45851c5d9d3dbc7e8333b2811c3bfb396c82d092e088a35955fc4a00e`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L130-L130) — lines `130–130`; excerpt `sha256:46b167725fbe089dbde15bd1c1125d18dbd277b79357403bbf40c73a4a9a1c6c`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:181](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L181-L181), [cite at paper/reasoning-parts/erdos269/core.tex:130](../../paper/reasoning-parts/erdos269/core.tex#L130-L130)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4822-L4828) — lines `4822–4828`; excerpt `sha256:d5178dbf9e857836e9898ea177d620546af9d24a1826f669a5c173ec6dea9c58`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4791-L4797) — lines `4791–4797`; excerpt `sha256:d5178dbf9e857836e9898ea177d620546af9d24a1826f669a5c173ec6dea9c58`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4529-L4529) — lines `4529–4529`; excerpt `sha256:e85a60b5f00cd26f892425661c3e141ada248c650f76fa1bbab1b0d4d117a642`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L88-L95) — lines `88–95`; excerpt `sha256:2223d196ea50c7aa4910ff7135c17302d35865756bc58597c18dfb8b05e931ac`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4560](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4560-L4560), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4581](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4581-L4581), [cite at paper/reasoning-parts/erdos1049/core.tex:4529](../../paper/reasoning-parts/erdos1049/core.tex#L4529-L4529), [cite at paper/reasoning-parts/erdos1049/core.tex:4550](../../paper/reasoning-parts/erdos1049/core.tex#L4550-L4550)

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
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1093-L1096) — lines `1093–1096`; excerpt `sha256:06650ad7fd498dc3411f33be1c9fa8d899b3b07e13190cc806400263d07a88c8`
- [docs/research-commons/rounds/round7/README.md](../../docs/research-commons/rounds/round7/README.md#L56-L60) — lines `56–60`; excerpt `sha256:1d66252ee7cb6baaf5065f96ec3ab4dad3e7296eca6d2c98ed0d5c7e41e08a97`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:819](../../paper/systems/claim-faithful-publication-systems-paper.tex#L819-L819)
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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1077-L1080) — lines `1077–1080`; excerpt `sha256:b9e2249bc4d01297697400d9029b3c8e7883b75d69de50546f4bde27319bc74f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4302-L4305) — lines `4302–4305`; excerpt `sha256:b9e2249bc4d01297697400d9029b3c8e7883b75d69de50546f4bde27319bc74f`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4251-L4254) — lines `4251–4254`; excerpt `sha256:b9e2249bc4d01297697400d9029b3c8e7883b75d69de50546f4bde27319bc74f`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1006](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1006-L1006)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3196](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3196-L3196), [cite at paper/reasoning-parts/erdos269/core.tex:3145](../../paper/reasoning-parts/erdos269/core.tex#L3145-L3145)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L958-L961) — lines `958–961`; excerpt `sha256:6aaf6da69e5a056c56565ce65b93dc9624cd8a22480a7b32eacbb405f875508a`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5347-L5350) — lines `5347–5350`; excerpt `sha256:6aaf6da69e5a056c56565ce65b93dc9624cd8a22480a7b32eacbb405f875508a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5303-L5306) — lines `5303–5306`; excerpt `sha256:6aaf6da69e5a056c56565ce65b93dc9624cd8a22480a7b32eacbb405f875508a`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:717](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L717-L717)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3085](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3085-L3085), [cite at paper/reasoning-parts/erdos1041/core.tex:3041](../../paper/reasoning-parts/erdos1041/core.tex#L3041-L3041)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10076-L10080) — lines `10076–10080`; excerpt `sha256:48c8f377367df5c421434058ed0f1e7474c781ee36061cf7ab0d39eda785c36d`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9884-L9888) — lines `9884–9888`; excerpt `sha256:48c8f377367df5c421434058ed0f1e7474c781ee36061cf7ab0d39eda785c36d`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1092-L1096) — lines `1092–1096`; excerpt `sha256:2d8e8e60c166ca01ea9461e45af9157b2f035c8a50a7d38749db5dbf50c5e728`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4311-L4315) — lines `4311–4315`; excerpt `sha256:ef78f91a2a53616a917a9b8d574a5da55953d5024938b45990e8decb1515b07b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4260-L4264) — lines `4260–4264`; excerpt `sha256:ef78f91a2a53616a917a9b8d574a5da55953d5024938b45990e8decb1515b07b`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1007](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1007-L1007)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8364](../../paper/249/erdos249-totient-reasoning-surface.tex#L8364-L8364), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8172](../../paper/reasoning-parts/erdos249/a249_front.tex#L8172-L8172)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3318](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3318-L3318), [cite at paper/reasoning-parts/erdos269/core.tex:3267](../../paper/reasoning-parts/erdos269/core.tex#L3267-L3267)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3097-L3101) — lines `3097–3101`; excerpt `sha256:ea1e57fc8df0e5e2dc90fc296ae5b3eb8139cdc0ae9ec706f448b795a1933541`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3062-L3066) — lines `3062–3066`; excerpt `sha256:ea1e57fc8df0e5e2dc90fc296ae5b3eb8139cdc0ae9ec706f448b795a1933541`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1860](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1860-L1860), [cite at paper/reasoning-parts/erdos68/core.tex:1825](../../paper/reasoning-parts/erdos68/core.tex#L1825-L1825)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5310-L5315) — lines `5310–5315`; excerpt `sha256:87ad1ba0f311b57b61a187d8e3c5bf6b16922e8b73a12590b746f135bbf6f48f`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1451-L1455) — lines `1451–1455`; excerpt `sha256:4ea0575269b0cc301d69524665b7d6cb05120bcbba9460851e9fa2718c3cafec`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L139-L139) — lines `139–139`; excerpt `sha256:991b168a6e80106e87c200dde8f2bf29239f5928740465826640d6a7ebc1b93e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L10768-L10777) — lines `10768–10777`; excerpt `sha256:162189e1cf0c892075ed7cffb8ef885d1d9da766b3f16a7a6ae07d5c83afc90e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9741-L9741) — lines `9741–9741`; excerpt `sha256:cdc7c634e30bd34ca3a9b807193c3645b42bcbe20c8c45508b70001c4eae795d`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L118-L118) — lines `118–118`; excerpt `sha256:01df466ef33f3331dd51f69f00dedfeff5bb3b531cc2f0419a20f89e666af5c5`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L339-L339) — lines `339–339`; excerpt `sha256:991b168a6e80106e87c200dde8f2bf29239f5928740465826640d6a7ebc1b93e`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L118-L118) — lines `118–118`; excerpt `sha256:01df466ef33f3331dd51f69f00dedfeff5bb3b531cc2f0419a20f89e666af5c5`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L146-L146) — lines `146–146`; excerpt `sha256:e3872dd726142058db24d451b073eb106f0d6e35aea52bb385f849574ba5ce02`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1059-L1062) — lines `1059–1062`; excerpt `sha256:38cd73fc723cb87858bf5ad1ff85bc3a6aed38bc336429f816ee84816442c7d9`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4275-L4278) — lines `4275–4278`; excerpt `sha256:38cd73fc723cb87858bf5ad1ff85bc3a6aed38bc336429f816ee84816442c7d9`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4224-L4227) — lines `4224–4227`; excerpt `sha256:38cd73fc723cb87858bf5ad1ff85bc3a6aed38bc336429f816ee84816442c7d9`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2891-L2893) — lines `2891–2893`; excerpt `sha256:f27417f97884dcd2e5140620cdfa45a7fbcbc3cec44992f67d8feb50d91f535c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2850-L2852) — lines `2850–2852`; excerpt `sha256:f27417f97884dcd2e5140620cdfa45a7fbcbc3cec44992f67d8feb50d91f535c`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9471-L9480) — lines `9471–9480`; excerpt `sha256:23b75d9385f4d7c31ec74d72a39ca533b7b4c020d60c4718af8894c4ba6f4ed4`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9271-L9280) — lines `9271–9280`; excerpt `sha256:23b75d9385f4d7c31ec74d72a39ca533b7b4c020d60c4718af8894c4ba6f4ed4`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1272-L1276) — lines `1272–1276`; excerpt `sha256:7534aa59bb234c308a55714341b32d4a03d5c73d5381c36bf619a6d8cdc5e0c4`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4048-L4052) — lines `4048–4052`; excerpt `sha256:7534aa59bb234c308a55714341b32d4a03d5c73d5381c36bf619a6d8cdc5e0c4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4009-L4013) — lines `4009–4013`; excerpt `sha256:7534aa59bb234c308a55714341b32d4a03d5c73d5381c36bf619a6d8cdc5e0c4`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:228](../../paper/systems/claim-faithful-publication-systems-paper.tex#L228-L228)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1043](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1043-L1043), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1090](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1090-L1090)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:50](../../paper/257/erdos-257-mersenne-support-subseries.tex#L50-L50), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:118](../../paper/257/erdos-257-mersenne-support-subseries.tex#L118-L118), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:757](../../paper/257/erdos-257-mersenne-support-subseries.tex#L757-L757), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:770](../../paper/257/erdos-257-mersenne-support-subseries.tex#L770-L770), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1371](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1371-L1371)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:353](../../paper/269/erdos-269-three-prime-running-lcm.tex#L353-L353), [cite at paper/269/erdos-269-three-prime-running-lcm.tex:586](../../paper/269/erdos-269-three-prime-running-lcm.tex#L586-L586)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:779](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L779-L779), [cite at paper/reasoning-parts/erdos243/core.tex:740](../../paper/reasoning-parts/erdos243/core.tex#L740-L740)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:705](../../paper/archive/erdos249-257-main-paper.tex#L705-L705)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1794](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1794-L1794), [cite at paper/reasoning-parts/erdos251/core.tex:1753](../../paper/reasoning-parts/erdos251/core.tex#L1753-L1753)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1081](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1081-L1081), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:881](../../paper/reasoning-parts/erdos257/a257_front.tex#L881-L881)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:909](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L909-L909), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2388](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2388-L2388), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3733](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3733-L3733), [cite at paper/reasoning-parts/erdos269/core.tex:858](../../paper/reasoning-parts/erdos269/core.tex#L858-L858), [cite at paper/reasoning-parts/erdos269/core.tex:2337](../../paper/reasoning-parts/erdos269/core.tex#L2337-L2337), [cite at paper/reasoning-parts/erdos269/core.tex:3682](../../paper/reasoning-parts/erdos269/core.tex#L3682-L3682)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:944](../../paper/synthesis/optimal-sparse-perturbations.tex#L944-L944)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5294-L5299) — lines `5294–5299`; excerpt `sha256:fbbf29db45c62cfa84769c87ea4dfb6dcbc312a557a3335deb161872d3ae4d44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5250-L5255) — lines `5250–5255`; excerpt `sha256:fbbf29db45c62cfa84769c87ea4dfb6dcbc312a557a3335deb161872d3ae4d44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1577-L1577) — lines `1577–1577`; excerpt `sha256:9b744f2b7f5621dd470311a82aeee2e8b051a79200911c2b6b0f3b283301c6d6`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L904-L909) — lines `904–909`; excerpt `sha256:03547751579bddb06550186cbd4cd5363e790e059ff80b147b313232f2329016`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:820](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L820-L820)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1621](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1621-L1621), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2271](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2271-L2271), [cite at paper/reasoning-parts/erdos1041/core.tex:1577](../../paper/reasoning-parts/erdos1041/core.tex#L1577-L1577), [cite at paper/reasoning-parts/erdos1041/core.tex:2227](../../paper/reasoning-parts/erdos1041/core.tex#L2227-L2227)

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
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1262-L1264) — lines `1262–1264`; excerpt `sha256:2791c8042dc468854cefb24a74e27b8ce018aa3c98bb4987cd94e39599e9c97d`
- [docs/research-commons/rounds/round7/README.md](../../docs/research-commons/rounds/round7/README.md#L61-L64) — lines `61–64`; excerpt `sha256:874b2be52514deae844bef1f44fcbc81dfb88cf010c98a26bf6bc0cfa4dae767`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:142](../../paper/systems/claim-faithful-publication-systems-paper.tex#L142-L142), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:733](../../paper/systems/claim-faithful-publication-systems-paper.tex#L733-L733)
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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L606-L608) — lines `606–608`; excerpt `sha256:5cfb10540069185577d738da52c429d1b74a4f8ce94c54018d941550c730eeaf`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2901-L2903) — lines `2901–2903`; excerpt `sha256:5cfb10540069185577d738da52c429d1b74a4f8ce94c54018d941550c730eeaf`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2860-L2862) — lines `2860–2862`; excerpt `sha256:5cfb10540069185577d738da52c429d1b74a4f8ce94c54018d941550c730eeaf`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:318](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L318-L318)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:379](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L379-L379), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:546](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L546-L546), [cite at paper/reasoning-parts/erdos251/core.tex:338](../../paper/reasoning-parts/erdos251/core.tex#L338-L338), [cite at paper/reasoning-parts/erdos251/core.tex:505](../../paper/reasoning-parts/erdos251/core.tex#L505-L505)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L945-L950) — lines `945–950`; excerpt `sha256:dd81dda92210816aa997d12725fdd2b3d2f7a70097cbd438d5ef8102c0c13e44`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5334-L5339) — lines `5334–5339`; excerpt `sha256:dd81dda92210816aa997d12725fdd2b3d2f7a70097cbd438d5ef8102c0c13e44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5290-L5295) — lines `5290–5295`; excerpt `sha256:dd81dda92210816aa997d12725fdd2b3d2f7a70097cbd438d5ef8102c0c13e44`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:116](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L116-L116)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4967](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4967-L4967), [cite at paper/reasoning-parts/erdos1041/core.tex:4923](../../paper/reasoning-parts/erdos1041/core.tex#L4923-L4923)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1263-L1269) — lines `1263–1269`; excerpt `sha256:eb7d5ec7e254bbf424e424d7b70e149f642ec316eed5ca8d2357045a54b32cc6`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4034-L4040) — lines `4034–4040`; excerpt `sha256:eb7d5ec7e254bbf424e424d7b70e149f642ec316eed5ca8d2357045a54b32cc6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3995-L4001) — lines `3995–4001`; excerpt `sha256:eb7d5ec7e254bbf424e424d7b70e149f642ec316eed5ca8d2357045a54b32cc6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L183-L183) — lines `183–183`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:115](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L115-L115), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:142](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L142-L142), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:424](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L424-L424), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:562](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L562-L562), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:992](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L992-L993)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:222](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L222-L222), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:797](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L797-L797), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:817](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L817-L817), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:897](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L897-L897), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:903](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L903-L903), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:914](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L914-L914), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:927](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L927-L927), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:928](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L928-L928), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:930](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L930-L930), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:936](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L936-L936), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1013](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1013-L1013), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2327](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2327-L2327), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2336](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2336-L2336), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2361](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2361-L2361), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2409](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2409-L2409), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2469](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2469-L2469), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2785](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2785-L2785), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2789](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2789-L2789), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3091](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3091-L3091), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3172](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3172-L3172), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3173](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3173-L3173), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3477](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3477-L3477), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3480](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3480-L3480), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3486](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3486-L3486), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3865](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3865-L3866), [cite at paper/reasoning-parts/erdos243/core.tex:183](../../paper/reasoning-parts/erdos243/core.tex#L183-L183), [cite at paper/reasoning-parts/erdos243/core.tex:758](../../paper/reasoning-parts/erdos243/core.tex#L758-L758), [cite at paper/reasoning-parts/erdos243/core.tex:778](../../paper/reasoning-parts/erdos243/core.tex#L778-L778), [cite at paper/reasoning-parts/erdos243/core.tex:858](../../paper/reasoning-parts/erdos243/core.tex#L858-L858), [cite at paper/reasoning-parts/erdos243/core.tex:864](../../paper/reasoning-parts/erdos243/core.tex#L864-L864), [cite at paper/reasoning-parts/erdos243/core.tex:875](../../paper/reasoning-parts/erdos243/core.tex#L875-L875), [cite at paper/reasoning-parts/erdos243/core.tex:888](../../paper/reasoning-parts/erdos243/core.tex#L888-L888), [cite at paper/reasoning-parts/erdos243/core.tex:889](../../paper/reasoning-parts/erdos243/core.tex#L889-L889), [cite at paper/reasoning-parts/erdos243/core.tex:891](../../paper/reasoning-parts/erdos243/core.tex#L891-L891), [cite at paper/reasoning-parts/erdos243/core.tex:897](../../paper/reasoning-parts/erdos243/core.tex#L897-L897), [cite at paper/reasoning-parts/erdos243/core.tex:974](../../paper/reasoning-parts/erdos243/core.tex#L974-L974), [cite at paper/reasoning-parts/erdos243/core.tex:2288](../../paper/reasoning-parts/erdos243/core.tex#L2288-L2288), [cite at paper/reasoning-parts/erdos243/core.tex:2297](../../paper/reasoning-parts/erdos243/core.tex#L2297-L2297), [cite at paper/reasoning-parts/erdos243/core.tex:2322](../../paper/reasoning-parts/erdos243/core.tex#L2322-L2322), [cite at paper/reasoning-parts/erdos243/core.tex:2370](../../paper/reasoning-parts/erdos243/core.tex#L2370-L2370), [cite at paper/reasoning-parts/erdos243/core.tex:2430](../../paper/reasoning-parts/erdos243/core.tex#L2430-L2430), [cite at paper/reasoning-parts/erdos243/core.tex:2746](../../paper/reasoning-parts/erdos243/core.tex#L2746-L2746), [cite at paper/reasoning-parts/erdos243/core.tex:2750](../../paper/reasoning-parts/erdos243/core.tex#L2750-L2750), [cite at paper/reasoning-parts/erdos243/core.tex:3052](../../paper/reasoning-parts/erdos243/core.tex#L3052-L3052), [cite at paper/reasoning-parts/erdos243/core.tex:3133](../../paper/reasoning-parts/erdos243/core.tex#L3133-L3133), [cite at paper/reasoning-parts/erdos243/core.tex:3134](../../paper/reasoning-parts/erdos243/core.tex#L3134-L3134), [cite at paper/reasoning-parts/erdos243/core.tex:3438](../../paper/reasoning-parts/erdos243/core.tex#L3438-L3438), [cite at paper/reasoning-parts/erdos243/core.tex:3441](../../paper/reasoning-parts/erdos243/core.tex#L3441-L3441), [cite at paper/reasoning-parts/erdos243/core.tex:3447](../../paper/reasoning-parts/erdos243/core.tex#L3447-L3447), [cite at paper/reasoning-parts/erdos243/core.tex:3826](../../paper/reasoning-parts/erdos243/core.tex#L3826-L3827)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L880-L886) — lines `880–886`; excerpt `sha256:82d28a8215cfaad9830f9c69ac73ab8a39b6b8fde4ba10c62ec7be6337dc3ff0`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:830](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L830-L830)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L476-L477) — lines `476–477`; excerpt `sha256:acd0118c6668b66ae11eee7978ef8959e8909aa7c6b93b4273df7e0a9fefef1b`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2917-L2919) — lines `2917–2919`; excerpt `sha256:9418f72235db07cc6cd7f1772c2ce7a82d075de7ad72f5c574173c93b1d28da6`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2876-L2878) — lines `2876–2878`; excerpt `sha256:9418f72235db07cc6cd7f1772c2ce7a82d075de7ad72f5c574173c93b1d28da6`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L477-L477) — lines `477–477`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L436-L436) — lines `436–436`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L436-L436) — lines `436–436`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L477-L477) — lines `477–477`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L477-L477) — lines `477–477`; excerpt `sha256:27664e2d08b6fb20dfc62202daee1413c336ba690dbaa227d4c709ed0901752e`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1497-L1503) — lines `1497–1503`; excerpt `sha256:08841993ec7ee7aa859d0a63801cb36c9d22ae35f6f155707172b3fa7712308a`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9600-L9609) — lines `9600–9609`; excerpt `sha256:d09ac96b0131bd7dfc76f01dbf0e7d50ec3b4558035379307812584b13065d36`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9400-L9409) — lines `9400–9409`; excerpt `sha256:d09ac96b0131bd7dfc76f01dbf0e7d50ec3b4558035379307812584b13065d36`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:718](../../paper/257/erdos-257-mersenne-support-subseries.tex#L718-L718)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:477](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L477-L477), [cite at paper/reasoning-parts/erdos251/core.tex:436](../../paper/reasoning-parts/erdos251/core.tex#L436-L436)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9093](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9093-L9093), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:8893](../../paper/reasoning-parts/erdos257/a257_front.tex#L8893-L8893)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1858](../../paper/synthesis/optimal-sparse-perturbations.tex#L1858-L1858), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1859](../../paper/synthesis/optimal-sparse-perturbations.tex#L1859-L1859), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1978](../../paper/synthesis/optimal-sparse-perturbations.tex#L1978-L1978)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5328-L5331) — lines `5328–5331`; excerpt `sha256:2cc1d6adac4a799350b2f110f64e22883a9a6da730739cce9c316980e35947b3`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L81-L81) — lines `81–81`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10020-L10025) — lines `10020–10025`; excerpt `sha256:68764d4d7a89374c4c04bae75c94f6c2e0e288f6e20da9c4a285948259753998`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9828-L9833) — lines `9828–9833`; excerpt `sha256:68764d4d7a89374c4c04bae75c94f6c2e0e288f6e20da9c4a285948259753998`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:497](../../paper/archive/erdos249-257-main-paper.tex#L497-L497), [cite at paper/archive/erdos249-257-main-paper.tex:498](../../paper/archive/erdos249-257-main-paper.tex#L498-L498), [cite at paper/archive/erdos249-257-main-paper.tex:4085](../../paper/archive/erdos249-257-main-paper.tex#L4085-L4085), [cite at paper/archive/erdos249-257-main-paper.tex:4784](../../paper/archive/erdos249-257-main-paper.tex#L4784-L4784)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9884](../../paper/249/erdos249-totient-reasoning-surface.tex#L9884-L9884), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9692](../../paper/reasoning-parts/erdos249/a249_front.tex#L9692-L9692)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5289-L5294) — lines `5289–5294`; excerpt `sha256:2eb3162258360253b5cf7a590c5d7eefeabfb1b4633350ee641a14035d11359c`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5245-L5250) — lines `5245–5250`; excerpt `sha256:2eb3162258360253b5cf7a590c5d7eefeabfb1b4633350ee641a14035d11359c`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1576-L1576) — lines `1576–1576`; excerpt `sha256:5b6b0635f8d7bc8209166c68611d1605127309d1ef4997e63819762365a6909a`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1620](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1620-L1620), [cite at paper/reasoning-parts/erdos1041/core.tex:1576](../../paper/reasoning-parts/erdos1041/core.tex#L1576-L1576)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L841-L845) — lines `841–845`; excerpt `sha256:495e90612bc48250f516ad11282d20ee19e249325363e3dd38cfe59a6de6a6c5`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2993-L2997) — lines `2993–2997`; excerpt `sha256:495e90612bc48250f516ad11282d20ee19e249325363e3dd38cfe59a6de6a6c5`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2958-L2962) — lines `2958–2962`; excerpt `sha256:495e90612bc48250f516ad11282d20ee19e249325363e3dd38cfe59a6de6a6c5`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1225-L1225) — lines `1225–1225`; excerpt `sha256:05ae035c98ef1be04452fd7e72676d785c26a101271763e5bf6acf84902d1963`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1225-L1225) — lines `1225–1225`; excerpt `sha256:05ae035c98ef1be04452fd7e72676d785c26a101271763e5bf6acf84902d1963`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:726](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L726-L726)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1260](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1260-L1260), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2157](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2157-L2157), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2336](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2336-L2336), [cite at paper/reasoning-parts/erdos68/core.tex:1225](../../paper/reasoning-parts/erdos68/core.tex#L1225-L1225), [cite at paper/reasoning-parts/erdos68/core.tex:2122](../../paper/reasoning-parts/erdos68/core.tex#L2122-L2122), [cite at paper/reasoning-parts/erdos68/core.tex:2301](../../paper/reasoning-parts/erdos68/core.tex#L2301-L2301)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1058-L1063) — lines `1058–1063`; excerpt `sha256:3e8d9bba274ba0d1fa7883a36808baad3612c511dcd54421d1fb5d61d279fd1e`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4989-L4994) — lines `4989–4994`; excerpt `sha256:f56843a81f14f05368c09617997aad73fc6b35003af9f80f751f87b4ad29611f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4958-L4963) — lines `4958–4963`; excerpt `sha256:f56843a81f14f05368c09617997aad73fc6b35003af9f80f751f87b4ad29611f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4262-L4266) — lines `4262–4266`; excerpt `sha256:e828b32afe869265193334410009d5198e4188e0ff2dbfb72332db658f289473`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1787-L1787) — lines `1787–1787`; excerpt `sha256:16452cca21c31d1c0ed13a43089946f8ae7c468e95a04481e8bfeb79ff69f18c`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4211-L4215) — lines `4211–4215`; excerpt `sha256:e828b32afe869265193334410009d5198e4188e0ff2dbfb72332db658f289473`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L1736-L1736) — lines `1736–1736`; excerpt `sha256:16452cca21c31d1c0ed13a43089946f8ae7c468e95a04481e8bfeb79ff69f18c`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:937](../../paper/1049/erdos-1049-rational-base-lambert.tex#L937-L937)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4173](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4173-L4173), [cite at paper/reasoning-parts/erdos1049/core.tex:4142](../../paper/reasoning-parts/erdos1049/core.tex#L4142-L4142)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1787](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1787-L1787), [cite at paper/reasoning-parts/erdos269/core.tex:1736](../../paper/reasoning-parts/erdos269/core.tex#L1736-L1736)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L632-L634) — lines `632–634`; excerpt `sha256:4ef9d8671b8ce392778e642dc0289749457d7d772ade16d4e14764d4b2b041dd`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2947-L2949) — lines `2947–2949`; excerpt `sha256:b91b61385dc89f0e6767647854a990d52e4590e0b3e52ac921e4d46e37c4a36b`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2906-L2908) — lines `2906–2908`; excerpt `sha256:b91b61385dc89f0e6767647854a990d52e4590e0b3e52ac921e4d46e37c4a36b`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:553](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L553-L553), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:556](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L556-L556)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1943](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1943-L1943), [cite at paper/reasoning-parts/erdos251/core.tex:1902](../../paper/reasoning-parts/erdos251/core.tex#L1902-L1902)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L886-L891) — lines `886–891`; excerpt `sha256:ed2e1d97e25042a1c3cc333a2f890caed82f4b663b8b32c55aee9808f3380583`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5252-L5257) — lines `5252–5257`; excerpt `sha256:bfa2ad242e4a6f037e19e479a20a53b503839419b0cda9e5daa5e3cb598fe13a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5208-L5213) — lines `5208–5213`; excerpt `sha256:bfa2ad242e4a6f037e19e479a20a53b503839419b0cda9e5daa5e3cb598fe13a`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:748](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L748-L748)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4121](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4121-L4121), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4127](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4127-L4127), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4129](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4129-L4129), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4140](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4140-L4140), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4185](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4185-L4185), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4219](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4219-L4219), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4382](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4382-L4382), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4837](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4837-L4837), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4841](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4841-L4841), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4845](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4845-L4845), [cite at paper/reasoning-parts/erdos1041/core.tex:4077](../../paper/reasoning-parts/erdos1041/core.tex#L4077-L4077), [cite at paper/reasoning-parts/erdos1041/core.tex:4083](../../paper/reasoning-parts/erdos1041/core.tex#L4083-L4083), [cite at paper/reasoning-parts/erdos1041/core.tex:4085](../../paper/reasoning-parts/erdos1041/core.tex#L4085-L4085), [cite at paper/reasoning-parts/erdos1041/core.tex:4096](../../paper/reasoning-parts/erdos1041/core.tex#L4096-L4096), [cite at paper/reasoning-parts/erdos1041/core.tex:4141](../../paper/reasoning-parts/erdos1041/core.tex#L4141-L4141), [cite at paper/reasoning-parts/erdos1041/core.tex:4175](../../paper/reasoning-parts/erdos1041/core.tex#L4175-L4175), [cite at paper/reasoning-parts/erdos1041/core.tex:4338](../../paper/reasoning-parts/erdos1041/core.tex#L4338-L4338), [cite at paper/reasoning-parts/erdos1041/core.tex:4793](../../paper/reasoning-parts/erdos1041/core.tex#L4793-L4793), [cite at paper/reasoning-parts/erdos1041/core.tex:4797](../../paper/reasoning-parts/erdos1041/core.tex#L4797-L4797), [cite at paper/reasoning-parts/erdos1041/core.tex:4801](../../paper/reasoning-parts/erdos1041/core.tex#L4801-L4801)

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
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1142-L1144) — lines `1142–1144`; excerpt `sha256:9f7cd13126bc86bb2e14538da4a22cac99dbf4eaaabadfd3aba8c94ea897364f`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:142](../../paper/systems/claim-faithful-publication-systems-paper.tex#L142-L142)
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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L875-L880) — lines `875–880`; excerpt `sha256:de6f7f3e7ce0991e2f6ce37362689f9baf718419396e29df27966f24fa9d4a1f`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5279-L5284) — lines `5279–5284`; excerpt `sha256:47c15ddd8236ce68dd0ecbf6270bce0d6213cbaaf1750e780da87c87894d6230`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5235-L5240) — lines `5235–5240`; excerpt `sha256:47c15ddd8236ce68dd0ecbf6270bce0d6213cbaaf1750e780da87c87894d6230`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L50-L50) — lines `50–50`; excerpt `sha256:8cd1420d63ac6dba85e07a367f50e3b3fbcbda60ea0f87fa3c34a8351bb2ee01`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L50-L50) — lines `50–50`; excerpt `sha256:8cd1420d63ac6dba85e07a367f50e3b3fbcbda60ea0f87fa3c34a8351bb2ee01`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L50-L50) — lines `50–50`; excerpt `sha256:8cd1420d63ac6dba85e07a367f50e3b3fbcbda60ea0f87fa3c34a8351bb2ee01`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:74](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L74-L74)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:94](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L94-L94), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1712](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1712-L1712), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2971](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2971-L2971), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2972](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2972-L2972), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3050](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3050-L3050), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3052](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3052-L3052), [cite at paper/reasoning-parts/erdos1041/core.tex:50](../../paper/reasoning-parts/erdos1041/core.tex#L50-L50), [cite at paper/reasoning-parts/erdos1041/core.tex:1668](../../paper/reasoning-parts/erdos1041/core.tex#L1668-L1668), [cite at paper/reasoning-parts/erdos1041/core.tex:2927](../../paper/reasoning-parts/erdos1041/core.tex#L2927-L2927), [cite at paper/reasoning-parts/erdos1041/core.tex:2928](../../paper/reasoning-parts/erdos1041/core.tex#L2928-L2928), [cite at paper/reasoning-parts/erdos1041/core.tex:3006](../../paper/reasoning-parts/erdos1041/core.tex#L3006-L3006), [cite at paper/reasoning-parts/erdos1041/core.tex:3008](../../paper/reasoning-parts/erdos1041/core.tex#L3008-L3008)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5322-L5325) — lines `5322–5325`; excerpt `sha256:a2986b3c4ad5444edff29257bbeccf1dbda70fa87ceb63468d3192cdd636ac3b`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4816-L4822) — lines `4816–4822`; excerpt `sha256:62e9f12c9446297c621f7f486af4e1739cd6b6e5b979419191df4d31b8bb4cdc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4785-L4791) — lines `4785–4791`; excerpt `sha256:62e9f12c9446297c621f7f486af4e1739cd6b6e5b979419191df4d31b8bb4cdc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4546-L4546) — lines `4546–4546`; excerpt `sha256:5fd985589a096c7284944042b00248690d1d7fceed1258356a6e91864e8e051c`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4577](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4577-L4577), [cite at paper/reasoning-parts/erdos1049/core.tex:4546](../../paper/reasoning-parts/erdos1049/core.tex#L4546-L4546)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:642](../../paper/archive/erdos249-257-main-paper.tex#L642-L642)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5240-L5247) — lines `5240–5247`; excerpt `sha256:ac93a1f2c5c87957117830efd99688e57dc988e65987811c68128cdf2f71aa9f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5196-L5203) — lines `5196–5203`; excerpt `sha256:ac93a1f2c5c87957117830efd99688e57dc988e65987811c68128cdf2f71aa9f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4242-L4242) — lines `4242–4242`; excerpt `sha256:789975730662255be1953f14644da72f9bee1ce16a61867e38c8b7ddd266fcb5`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4286](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4286-L4286), [cite at paper/reasoning-parts/erdos1041/core.tex:4242](../../paper/reasoning-parts/erdos1041/core.tex#L4242-L4242)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4250-L4253) — lines `4250–4253`; excerpt `sha256:24eacdd006d27f46e0ea49feb1a0b92cc03b5cd554204a5ff82c31aef527f7d2`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4199-L4202) — lines `4199–4202`; excerpt `sha256:24eacdd006d27f46e0ea49feb1a0b92cc03b5cd554204a5ff82c31aef527f7d2`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L148-L148) — lines `148–148`; excerpt `sha256:714f7e7837698f5625120d30f22eb2fd6a2f960836d9458c5bd06eb68baabd97`
- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5325-L5328) — lines `5325–5328`; excerpt `sha256:d83b8379aa5d3a8d993822c9518436371502939df5b9c449f945ffb60730454b`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:495](../../paper/archive/erdos249-257-main-paper.tex#L495-L495), [cite at paper/archive/erdos249-257-main-paper.tex:4084](../../paper/archive/erdos249-257-main-paper.tex#L4084-L4084), [cite at paper/archive/erdos249-257-main-paper.tex:4678](../../paper/archive/erdos249-257-main-paper.tex#L4678-L4678), [cite at paper/archive/erdos249-257-main-paper.tex:4782](../../paper/archive/erdos249-257-main-paper.tex#L4782-L4782)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:199](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L199-L199), [cite at paper/reasoning-parts/erdos269/core.tex:148](../../paper/reasoning-parts/erdos269/core.tex#L148-L148)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L716-L719) — lines `716–719`; excerpt `sha256:2fd518712f78c5863c24df2988af2303d5d5610ce069a736fcb6f69c30c4d37b`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9980-L9984) — lines `9980–9984`; excerpt `sha256:6f68ca842cab80e0e80859b0448d856556a74a77fbf2793f408455173289681c`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9788-L9792) — lines `9788–9792`; excerpt `sha256:6f68ca842cab80e0e80859b0448d856556a74a77fbf2793f408455173289681c`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:496](../../paper/249/erdos-249-binary-totient-series.tex#L496-L496)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1603](../../paper/249/erdos249-totient-reasoning-surface.tex#L1603-L1603), [cite at paper/249/erdos249-totient-reasoning-surface.tex:9591](../../paper/249/erdos249-totient-reasoning-surface.tex#L9591-L9591), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1411](../../paper/reasoning-parts/erdos249/a249_front.tex#L1411-L1411), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9399](../../paper/reasoning-parts/erdos249/a249_front.tex#L9399-L9399)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L319-L319) — lines `319–319`; excerpt `sha256:7e61b42ea68ba67af8f394d8ccf905ab7a64c0866af88228cdd70633340422fa`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L624-L626) — lines `624–626`; excerpt `sha256:a68775eea867950e9742ad93dd4089e04252a31cf488340177ac456e7b57c84f`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L372-L372) — lines `372–372`; excerpt `sha256:3411ca8b06103cfe9c649bff064c056e7f9e43045265fcc7e8409ac7f0236feb`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2929-L2931) — lines `2929–2931`; excerpt `sha256:a68775eea867950e9742ad93dd4089e04252a31cf488340177ac456e7b57c84f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L331-L331) — lines `331–331`; excerpt `sha256:3411ca8b06103cfe9c649bff064c056e7f9e43045265fcc7e8409ac7f0236feb`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2888-L2890) — lines `2888–2890`; excerpt `sha256:a68775eea867950e9742ad93dd4089e04252a31cf488340177ac456e7b57c84f`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:319](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L319-L319)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:372](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L372-L372), [cite at paper/reasoning-parts/erdos251/core.tex:331](../../paper/reasoning-parts/erdos251/core.tex#L331-L331)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2915-L2917) — lines `2915–2917`; excerpt `sha256:2bdb1af734a1c86a2ea7603f390d84d3309c1d1abf8a8f4eb21930714a5a0c9d`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2874-L2876) — lines `2874–2876`; excerpt `sha256:2bdb1af734a1c86a2ea7603f390d84d3309c1d1abf8a8f4eb21930714a5a0c9d`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1217](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1217-L1217), [cite at paper/reasoning-parts/erdos251/core.tex:1176](../../paper/reasoning-parts/erdos251/core.tex#L1176-L1176)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4315-L4320) — lines `4315–4320`; excerpt `sha256:4d3c475c2dd44a15da10bb68d05eedaa5bb7ef373c98a81bf0994e003e8022e6`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4264-L4269) — lines `4264–4269`; excerpt `sha256:4d3c475c2dd44a15da10bb68d05eedaa5bb7ef373c98a81bf0994e003e8022e6`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3420](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3420-L3420), [cite at paper/reasoning-parts/erdos269/core.tex:3369](../../paper/reasoning-parts/erdos269/core.tex#L3369-L3369)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1471-L1477) — lines `1471–1477`; excerpt `sha256:3f90c9c82f80686f1efe4c911cd5f754201a1464c150d626d59690b5e96927f9`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9562-L9568) — lines `9562–9568`; excerpt `sha256:3f90c9c82f80686f1efe4c911cd5f754201a1464c150d626d59690b5e96927f9`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9362-L9368) — lines `9362–9368`; excerpt `sha256:3f90c9c82f80686f1efe4c911cd5f754201a1464c150d626d59690b5e96927f9`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1372](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1372-L1372)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1191](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1191-L1191), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9408](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9408-L9408), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:991](../../paper/reasoning-parts/erdos257/a257_front.tex#L991-L991), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9208](../../paper/reasoning-parts/erdos257/a257_front.tex#L9208-L9208)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5341-L5344) — lines `5341–5344`; excerpt `sha256:3ac7773843e9a2678e1438fae3c683df643a9de180d07f049ef248f6010429ec`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:4090](../../paper/archive/erdos249-257-main-paper.tex#L4090-L4090)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L897-L904) — lines `897–904`; excerpt `sha256:0b086dc6c508b56a163e9e87eadee8f83406883c0bb951c90f8c3195b296ef03`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5257-L5264) — lines `5257–5264`; excerpt `sha256:ff50af06cc617795c60c2ca89ddaec781a6c4593028140edc22775c58cb3e3a9`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5213-L5220) — lines `5213–5220`; excerpt `sha256:ff50af06cc617795c60c2ca89ddaec781a6c4593028140edc22775c58cb3e3a9`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:112](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L112-L112)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:435](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L435-L435), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:638](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L638-L638), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1534](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1534-L1534), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1651](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1651-L1651), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1777](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1777-L1777), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3810](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3810-L3810), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4287](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4287-L4287), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4383](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4383-L4383), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4433](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4433-L4433), [cite at paper/reasoning-parts/erdos1041/core.tex:391](../../paper/reasoning-parts/erdos1041/core.tex#L391-L391), [cite at paper/reasoning-parts/erdos1041/core.tex:594](../../paper/reasoning-parts/erdos1041/core.tex#L594-L594), [cite at paper/reasoning-parts/erdos1041/core.tex:1490](../../paper/reasoning-parts/erdos1041/core.tex#L1490-L1490), [cite at paper/reasoning-parts/erdos1041/core.tex:1607](../../paper/reasoning-parts/erdos1041/core.tex#L1607-L1607), [cite at paper/reasoning-parts/erdos1041/core.tex:1733](../../paper/reasoning-parts/erdos1041/core.tex#L1733-L1733), [cite at paper/reasoning-parts/erdos1041/core.tex:3766](../../paper/reasoning-parts/erdos1041/core.tex#L3766-L3766), [cite at paper/reasoning-parts/erdos1041/core.tex:4243](../../paper/reasoning-parts/erdos1041/core.tex#L4243-L4243), [cite at paper/reasoning-parts/erdos1041/core.tex:4339](../../paper/reasoning-parts/erdos1041/core.tex#L4339-L4339), [cite at paper/reasoning-parts/erdos1041/core.tex:4389](../../paper/reasoning-parts/erdos1041/core.tex#L4389-L4389)

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
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1133-L1136) — lines `1133–1136`; excerpt `sha256:8390940285e5ebe3fa348b34c283e57cd010fdfb08dc84dbd79db8071c51e094`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:819](../../paper/systems/claim-faithful-publication-systems-paper.tex#L819-L819)
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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L728-L733) — lines `728–733`; excerpt `sha256:1afac1390d37599a1aabc74b5e4f00b9c13fe3b5510b23747164aafc5cabb79f`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10088-L10093) — lines `10088–10093`; excerpt `sha256:1afac1390d37599a1aabc74b5e4f00b9c13fe3b5510b23747164aafc5cabb79f`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9896-L9901) — lines `9896–9901`; excerpt `sha256:1afac1390d37599a1aabc74b5e4f00b9c13fe3b5510b23747164aafc5cabb79f`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:107](../../paper/249/erdos-249-binary-totient-series.tex#L107-L107)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:285](../../paper/249/erdos249-totient-reasoning-surface.tex#L285-L285), [cite at paper/249/erdos249-totient-reasoning-surface.tex:287](../../paper/249/erdos249-totient-reasoning-surface.tex#L287-L287), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:93](../../paper/reasoning-parts/erdos249/a249_front.tex#L93-L93), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:95](../../paper/reasoning-parts/erdos249/a249_front.tex#L95-L95)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5299-L5305) — lines `5299–5305`; excerpt `sha256:bcdad75ad0ef6a705b6fe89763d0da02f0663ec648798c57bec9c5455264dc47`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5255-L5261) — lines `5255–5261`; excerpt `sha256:bcdad75ad0ef6a705b6fe89763d0da02f0663ec648798c57bec9c5455264dc47`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1574-L1574) — lines `1574–1574`; excerpt `sha256:8f0116d285182c3169d8171b8d13c4c752a018a50c51df8dfd0a78fe648e1fe0`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1618](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1618-L1618), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1622](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1622-L1622), [cite at paper/reasoning-parts/erdos1041/core.tex:1574](../../paper/reasoning-parts/erdos1041/core.tex#L1574-L1574), [cite at paper/reasoning-parts/erdos1041/core.tex:1578](../../paper/reasoning-parts/erdos1041/core.tex#L1578-L1578)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3009-L3013) — lines `3009–3013`; excerpt `sha256:3a26f5bc4eb9c2426ec95588f15ecf2d22cd99dd0ae4aa88e40f0d69fe5e8750`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2974-L2978) — lines `2974–2978`; excerpt `sha256:3a26f5bc4eb9c2426ec95588f15ecf2d22cd99dd0ae4aa88e40f0d69fe5e8750`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1229-L1229) — lines `1229–1229`; excerpt `sha256:5139a5f6ebb95c3e704baeace6907b8ca37b7f8ea44fd4d7e73ced8285e38c76`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1229-L1229) — lines `1229–1229`; excerpt `sha256:5139a5f6ebb95c3e704baeace6907b8ca37b7f8ea44fd4d7e73ced8285e38c76`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L849-L853) — lines `849–853`; excerpt `sha256:e8cae7318c8c143094d52d1da99fd4dda7271236e256e02a746de55f05d72d67`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:86](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L86-L86)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1264](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1264-L1264), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2159](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2159-L2159), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2387](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2387-L2387), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2394](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2394-L2394), [cite at paper/reasoning-parts/erdos68/core.tex:1229](../../paper/reasoning-parts/erdos68/core.tex#L1229-L1229), [cite at paper/reasoning-parts/erdos68/core.tex:2124](../../paper/reasoning-parts/erdos68/core.tex#L2124-L2124), [cite at paper/reasoning-parts/erdos68/core.tex:2352](../../paper/reasoning-parts/erdos68/core.tex#L2352-L2352), [cite at paper/reasoning-parts/erdos68/core.tex:2359](../../paper/reasoning-parts/erdos68/core.tex#L2359-L2359)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4936-L4942) — lines `4936–4942`; excerpt `sha256:547a282df5e35d2d260581efbb9d6958a6a3bf47c2d9a4d9b39949fd65e27f76`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4905-L4911) — lines `4905–4911`; excerpt `sha256:547a282df5e35d2d260581efbb9d6958a6a3bf47c2d9a4d9b39949fd65e27f76`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4334-L4334) — lines `4334–4334`; excerpt `sha256:54e3d1ef752ffcb54e8ee1bfe7534ff85b97adcfec7a02daa218a664d09cd7f7`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4334-L4334) — lines `4334–4334`; excerpt `sha256:54e3d1ef752ffcb54e8ee1bfe7534ff85b97adcfec7a02daa218a664d09cd7f7`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4334-L4334) — lines `4334–4334`; excerpt `sha256:54e3d1ef752ffcb54e8ee1bfe7534ff85b97adcfec7a02daa218a664d09cd7f7`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4365](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4365-L4365), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4529](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4529-L4529), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4534](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4534-L4534), [cite at paper/reasoning-parts/erdos1049/core.tex:4334](../../paper/reasoning-parts/erdos1049/core.tex#L4334-L4334), [cite at paper/reasoning-parts/erdos1049/core.tex:4498](../../paper/reasoning-parts/erdos1049/core.tex#L4498-L4498), [cite at paper/reasoning-parts/erdos1049/core.tex:4503](../../paper/reasoning-parts/erdos1049/core.tex#L4503-L4503)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1080-L1083) — lines `1080–1083`; excerpt `sha256:56c3313573f1c66b97e759caddfa08857ff02beecce742ca74aa60516751dfb8`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4305-L4308) — lines `4305–4308`; excerpt `sha256:56c3313573f1c66b97e759caddfa08857ff02beecce742ca74aa60516751dfb8`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4254-L4257) — lines `4254–4257`; excerpt `sha256:56c3313573f1c66b97e759caddfa08857ff02beecce742ca74aa60516751dfb8`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1013](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1013-L1013)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:181](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L181-L181), [cite at paper/reasoning-parts/erdos269/core.tex:130](../../paper/reasoning-parts/erdos269/core.tex#L130-L130)

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

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4024-L4030) — lines `4024–4030`; excerpt `sha256:114c6c590cc9d93a8ef21180697160ce21e5fd0ef2e6801cfa8c3bd3dc16e78c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3985-L3991) — lines `3985–3991`; excerpt `sha256:114c6c590cc9d93a8ef21180697160ce21e5fd0ef2e6801cfa8c3bd3dc16e78c`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1257-L1263) — lines `1257–1263`; excerpt `sha256:4a2a8e4fc977c8352311e72ae7979c821e66a3545b5d72c4ade3b36bc5e51666`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:288](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L288-L288)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:360](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L360-L360), [cite at paper/reasoning-parts/erdos243/core.tex:321](../../paper/reasoning-parts/erdos243/core.tex#L321-L321)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1047-L1058) — lines `1047–1058`; excerpt `sha256:ded7a6e73c64eb888bff8d92fdf9045c0912b78b36a09aaf5d4f28ab76caf53f`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4842-L4853) — lines `4842–4853`; excerpt `sha256:28607cac7b070bebdf820b61863c3daadc81c336a532ef5ffb850e0444467fbe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4811-L4822) — lines `4811–4822`; excerpt `sha256:28607cac7b070bebdf820b61863c3daadc81c336a532ef5ffb850e0444467fbe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L802-L802) — lines `802–802`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L802-L802) — lines `802–802`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L802-L802) — lines `802–802`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L802-L802) — lines `802–802`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L802-L802) — lines `802–802`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L802-L802) — lines `802–802`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L3-L12) — lines `3–12`; excerpt `sha256:2c6a0d27c905ea48c1f25e9aa96f3007e323409c7b093d69e63e5d6389c5dd78`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L294-L341) — lines `294–341`; excerpt `sha256:079ff692126bd3e4d34f548fea370a492cd0c13ef7f93ce3fb3dd3ad6697e51f`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L1373-L1380) — lines `1373–1380`; excerpt `sha256:00ffa8698a1534c856de8c5358848f0e1631280815d61cd62dccca5b31c96703`
- [lean/ErdosProblems/Erdos1049/AdelicHeightBridge.lean](../../lean/ErdosProblems/Erdos1049/AdelicHeightBridge.lean#L177-L184) — lines `177–184`; excerpt `sha256:48cded238c23f3b69267c7634831949873ba61edbfc1d81d7be4e4f53a9dfa1f`
- [lean/ErdosProblems/Erdos1049/AllRow/Producer.lean](../../lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L139-L144) — lines `139–144`; excerpt `sha256:d91ba4591cce7012da8fb4b68e2c502744e2a86cbff69f02ac661f05bbbc77f0`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L675-L679) — lines `675–679`; excerpt `sha256:f4bd612442f7360245d4b631cbdc499c687fc3d6d13818a39db22dc67e091077`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:113](../../paper/1049/erdos-1049-rational-base-lambert.tex#L113-L113), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:134](../../paper/1049/erdos-1049-rational-base-lambert.tex#L134-L134), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:417](../../paper/1049/erdos-1049-rational-base-lambert.tex#L417-L417), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:880](../../paper/1049/erdos-1049-rational-base-lambert.tex#L880-L880)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:69](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L69-L69), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:833](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L833-L833), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1434](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1434-L1434), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1437](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1437-L1437), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1454](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1454-L1454), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1465](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1465-L1465), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1489](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1489-L1489), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1780](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1780-L1780), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2465](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2465-L2465), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4666](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4666-L4666), [cite at paper/reasoning-parts/erdos1049/core.tex:38](../../paper/reasoning-parts/erdos1049/core.tex#L38-L38), [cite at paper/reasoning-parts/erdos1049/core.tex:802](../../paper/reasoning-parts/erdos1049/core.tex#L802-L802), [cite at paper/reasoning-parts/erdos1049/core.tex:1403](../../paper/reasoning-parts/erdos1049/core.tex#L1403-L1403), [cite at paper/reasoning-parts/erdos1049/core.tex:1406](../../paper/reasoning-parts/erdos1049/core.tex#L1406-L1406), [cite at paper/reasoning-parts/erdos1049/core.tex:1423](../../paper/reasoning-parts/erdos1049/core.tex#L1423-L1423), [cite at paper/reasoning-parts/erdos1049/core.tex:1434](../../paper/reasoning-parts/erdos1049/core.tex#L1434-L1434), [cite at paper/reasoning-parts/erdos1049/core.tex:1458](../../paper/reasoning-parts/erdos1049/core.tex#L1458-L1458), [cite at paper/reasoning-parts/erdos1049/core.tex:1749](../../paper/reasoning-parts/erdos1049/core.tex#L1749-L1749), [cite at paper/reasoning-parts/erdos1049/core.tex:2434](../../paper/reasoning-parts/erdos1049/core.tex#L2434-L2434), [cite at paper/reasoning-parts/erdos1049/core.tex:4635](../../paper/reasoning-parts/erdos1049/core.tex#L4635-L4635)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1226-L1230) — lines `1226–1230`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3986-L3990) — lines `3986–3990`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3947-L3951) — lines `3947–3951`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L792-L792) — lines `792–792`; excerpt `sha256:ed7a349b06c0fa968d6eac74252e7f637f42e8018159ddf7e209ad4a3fae8037`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L792-L792) — lines `792–792`; excerpt `sha256:ed7a349b06c0fa968d6eac74252e7f637f42e8018159ddf7e209ad4a3fae8037`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3013-L3017) — lines `3013–3017`; excerpt `sha256:82a9d3633d44a7f0d1eb428949e60377edee33c29aa6e38e5941bceb6b962b77`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2978-L2982) — lines `2978–2982`; excerpt `sha256:82a9d3633d44a7f0d1eb428949e60377edee33c29aa6e38e5941bceb6b962b77`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2008-L2008) — lines `2008–2008`; excerpt `sha256:29422f1117ddf0cfe478b48719a3b1d57db703b18e788e0dd9e85d0344241384`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2008-L2008) — lines `2008–2008`; excerpt `sha256:29422f1117ddf0cfe478b48719a3b1d57db703b18e788e0dd9e85d0344241384`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2008-L2008) — lines `2008–2008`; excerpt `sha256:29422f1117ddf0cfe478b48719a3b1d57db703b18e788e0dd9e85d0344241384`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:839](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L839-L839)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:831](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L831-L831), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1669](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1669-L1669), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3620](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3620-L3620), [cite at paper/reasoning-parts/erdos243/core.tex:792](../../paper/reasoning-parts/erdos243/core.tex#L792-L792), [cite at paper/reasoning-parts/erdos243/core.tex:1630](../../paper/reasoning-parts/erdos243/core.tex#L1630-L1630), [cite at paper/reasoning-parts/erdos243/core.tex:3581](../../paper/reasoning-parts/erdos243/core.tex#L3581-L3581)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2043](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2043-L2043), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2427](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2427-L2427), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2430](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2430-L2430), [cite at paper/reasoning-parts/erdos68/core.tex:2008](../../paper/reasoning-parts/erdos68/core.tex#L2008-L2008), [cite at paper/reasoning-parts/erdos68/core.tex:2392](../../paper/reasoning-parts/erdos68/core.tex#L2392-L2392), [cite at paper/reasoning-parts/erdos68/core.tex:2395](../../paper/reasoning-parts/erdos68/core.tex#L2395-L2395)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L941-L945) — lines `941–945`; excerpt `sha256:e71562d62b7120e70fe7b834f65baa80911382d9eec508f8396928584ab1dacf`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5330-L5334) — lines `5330–5334`; excerpt `sha256:e71562d62b7120e70fe7b834f65baa80911382d9eec508f8396928584ab1dacf`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5286-L5290) — lines `5286–5290`; excerpt `sha256:e71562d62b7120e70fe7b834f65baa80911382d9eec508f8396928584ab1dacf`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:714](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L714-L714), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:784](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L784-L784)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3068](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3068-L3068), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4386](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4386-L4386), [cite at paper/reasoning-parts/erdos1041/core.tex:3024](../../paper/reasoning-parts/erdos1041/core.tex#L3024-L3024), [cite at paper/reasoning-parts/erdos1041/core.tex:4342](../../paper/reasoning-parts/erdos1041/core.tex#L4342-L4342)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2927-L2929) — lines `2927–2929`; excerpt `sha256:8724712f34a0b9289550c3ab049d6a1ee5927433c0a4731b5a6cab0280040067`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2886-L2888) — lines `2886–2888`; excerpt `sha256:8724712f34a0b9289550c3ab049d6a1ee5927433c0a4731b5a6cab0280040067`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L515-L515) — lines `515–515`; excerpt `sha256:afde66f79f7325fc6e5739cbb7f5cf67d57b23b919e011448cce112b14fd5df0`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L594-L596) — lines `594–596`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L556-L556) — lines `556–556`; excerpt `sha256:afde66f79f7325fc6e5739cbb7f5cf67d57b23b919e011448cce112b14fd5df0`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:556](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L556-L556), [cite at paper/reasoning-parts/erdos251/core.tex:515](../../paper/reasoning-parts/erdos251/core.tex#L515-L515)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5318-L5322) — lines `5318–5322`; excerpt `sha256:ef4a3136894b8a7edf6c08674740c39ae6802868494e203a59f1f0b740884aad`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L833-L837) — lines `833–837`; excerpt `sha256:b630a0f0ca592293699970eda53a16eea623a9f1d81f881c6dc903179a78eeec`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2977-L2981) — lines `2977–2981`; excerpt `sha256:b630a0f0ca592293699970eda53a16eea623a9f1d81f881c6dc903179a78eeec`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1243-L1248) — lines `1243–1248`; excerpt `sha256:78f98ff5782c3f26518953792349ad37efb90e1c262886d330c17b9bd9667677`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4003-L4008) — lines `4003–4008`; excerpt `sha256:eaf6cb9470a050bc0ac5978773ab824fd5e2486d1c128ad600ecc049ec5e1863`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L598-L600) — lines `598–600`; excerpt `sha256:d48a3b5fc1a3db1218dc2cebafed7ac30142d5ecb2e63f7fecff1e2a5c569695`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2885-L2887) — lines `2885–2887`; excerpt `sha256:33443e1df07646c816cedeb1eb59f9662fa5abee19c5b12c98dc3dbea83c505f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4222-L4225) — lines `4222–4225`; excerpt `sha256:a170cdfc562020c04faf65c58a81863df6e925b08eae36eba6e3fe186dbf1eb0`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1037-L1040) — lines `1037–1040`; excerpt `sha256:a170cdfc562020c04faf65c58a81863df6e925b08eae36eba6e3fe186dbf1eb0`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1029-L1033) — lines `1029–1033`; excerpt `sha256:46dc589925f18c98a38b701dc32978cf7bf47298f8b19fc97e2d6eb3b37ddaf2`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4808-L4812) — lines `4808–4812`; excerpt `sha256:5dc4499ba85b2a90c1b7eeae654d404e424be3f9aa288c8eaf30e698ab7cf0e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4777-L4781) — lines `4777–4781`; excerpt `sha256:5dc4499ba85b2a90c1b7eeae654d404e424be3f9aa288c8eaf30e698ab7cf0e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L31-L31) — lines `31–31`; excerpt `sha256:8b386bf7b02b221ab9f461321f419a2f93a0a03e8d35da223eb91f401a4655e5`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3964-L3969) — lines `3964–3969`; excerpt `sha256:eaf6cb9470a050bc0ac5978773ab824fd5e2486d1c128ad600ecc049ec5e1863`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L37-L37) — lines `37–37`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L37-L37) — lines `37–37`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2844-L2846) — lines `2844–2846`; excerpt `sha256:33443e1df07646c816cedeb1eb59f9662fa5abee19c5b12c98dc3dbea83c505f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L26-L26) — lines `26–26`; excerpt `sha256:626083ad8fe32513999d7b51bd99f24ffcd6a8a982d19d34d4cffaf234f372b5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L26-L26) — lines `26–26`; excerpt `sha256:626083ad8fe32513999d7b51bd99f24ffcd6a8a982d19d34d4cffaf234f372b5`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4171-L4174) — lines `4171–4174`; excerpt `sha256:a170cdfc562020c04faf65c58a81863df6e925b08eae36eba6e3fe186dbf1eb0`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L53-L53) — lines `53–53`; excerpt `sha256:89b37a0d3340796c5590d761a39d83444f6987ea56bf2f2eaf180f3f1f9e9178`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L53-L53) — lines `53–53`; excerpt `sha256:89b37a0d3340796c5590d761a39d83444f6987ea56bf2f2eaf180f3f1f9e9178`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L53-L53) — lines `53–53`; excerpt `sha256:89b37a0d3340796c5590d761a39d83444f6987ea56bf2f2eaf180f3f1f9e9178`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2942-L2946) — lines `2942–2946`; excerpt `sha256:b630a0f0ca592293699970eda53a16eea623a9f1d81f881c6dc903179a78eeec`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L23-L23) — lines `23–23`; excerpt `sha256:eedf58c8921c99e121942c72f945730fb30f151860f8a859f47e2254e6ba7731`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:143](../../paper/1049/erdos-1049-rational-base-lambert.tex#L143-L143)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:69](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L69-L69)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:47](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L47-L47)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:93](../../paper/269/erdos-269-three-prime-running-lcm.tex#L93-L93)
- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:49](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L49-L49)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:62](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L62-L62), [cite at paper/reasoning-parts/erdos1049/core.tex:31](../../paper/reasoning-parts/erdos1049/core.tex#L31-L31)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:76](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L76-L76), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:814](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L814-L814), [cite at paper/reasoning-parts/erdos243/core.tex:37](../../paper/reasoning-parts/erdos243/core.tex#L37-L37), [cite at paper/reasoning-parts/erdos243/core.tex:775](../../paper/reasoning-parts/erdos243/core.tex#L775-L775)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:193](../../paper/archive/erdos249-257-main-paper.tex#L193-L193), [cite at paper/archive/erdos249-257-main-paper.tex:195](../../paper/archive/erdos249-257-main-paper.tex#L195-L195)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:67](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L67-L67), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:420](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L420-L420), [cite at paper/reasoning-parts/erdos251/core.tex:26](../../paper/reasoning-parts/erdos251/core.tex#L26-L26), [cite at paper/reasoning-parts/erdos251/core.tex:379](../../paper/reasoning-parts/erdos251/core.tex#L379-L379)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:104](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L104-L104), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3685](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3685-L3685), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3721](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3721-L3721), [cite at paper/reasoning-parts/erdos269/core.tex:53](../../paper/reasoning-parts/erdos269/core.tex#L53-L53), [cite at paper/reasoning-parts/erdos269/core.tex:3634](../../paper/reasoning-parts/erdos269/core.tex#L3634-L3634), [cite at paper/reasoning-parts/erdos269/core.tex:3670](../../paper/reasoning-parts/erdos269/core.tex#L3670-L3670)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:58](../../paper/68/erdos68-factorial-reasoning-surface.tex#L58-L58), [cite at paper/reasoning-parts/erdos68/core.tex:23](../../paper/reasoning-parts/erdos68/core.tex#L23-L23)
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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L869-L873) — lines `869–873`; excerpt `sha256:eb4b28f73e685f8395aaa64be8cef4676a9807d8e5c53e9480cb7c0132a381f6`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3033-L3037) — lines `3033–3037`; excerpt `sha256:eb4b28f73e685f8395aaa64be8cef4676a9807d8e5c53e9480cb7c0132a381f6`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2998-L3002) — lines `2998–3002`; excerpt `sha256:eb4b28f73e685f8395aaa64be8cef4676a9807d8e5c53e9480cb7c0132a381f6`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L806-L806) — lines `806–806`; excerpt `sha256:cf9f47bed15acad9ba6b2de721781ee969de7a90ce6fad2f985b7d5332437051`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L806-L806) — lines `806–806`; excerpt `sha256:cf9f47bed15acad9ba6b2de721781ee969de7a90ce6fad2f985b7d5332437051`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L806-L806) — lines `806–806`; excerpt `sha256:cf9f47bed15acad9ba6b2de721781ee969de7a90ce6fad2f985b7d5332437051`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L806-L806) — lines `806–806`; excerpt `sha256:cf9f47bed15acad9ba6b2de721781ee969de7a90ce6fad2f985b7d5332437051`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1076-L1076) — lines `1076–1076`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1076-L1076) — lines `1076–1076`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1076-L1076) — lines `1076–1076`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:806](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L806-L806), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:807](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L807-L807)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1111](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1111-L1111), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1112](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1112-L1112), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1114](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1114-L1114), [cite at paper/reasoning-parts/erdos68/core.tex:1076](../../paper/reasoning-parts/erdos68/core.tex#L1076-L1076), [cite at paper/reasoning-parts/erdos68/core.tex:1077](../../paper/reasoning-parts/erdos68/core.tex#L1077-L1077), [cite at paper/reasoning-parts/erdos68/core.tex:1079](../../paper/reasoning-parts/erdos68/core.tex#L1079-L1079)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3073-L3077) — lines `3073–3077`; excerpt `sha256:3505a37c28e494a2a50e4fe25e04a275f47dea02e877ed8c2299dbfd058f927a`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3038-L3042) — lines `3038–3042`; excerpt `sha256:3505a37c28e494a2a50e4fe25e04a275f47dea02e877ed8c2299dbfd058f927a`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1735](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1735-L1735), [cite at paper/reasoning-parts/erdos68/core.tex:1700](../../paper/reasoning-parts/erdos68/core.tex#L1700-L1700)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L523-L524) — lines `523–524`; excerpt `sha256:4129ae8a548eb28a7e3432bbf4bbcc912b7dd61b2142446ce4caac2e976ce178`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2951-L2953) — lines `2951–2953`; excerpt `sha256:4d23f3968fb1ccd53933b23fc840988fd48072550d470fc5a28559b929df023f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2910-L2912) — lines `2910–2912`; excerpt `sha256:4d23f3968fb1ccd53933b23fc840988fd48072550d470fc5a28559b929df023f`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:524](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L524-L524), [cite at paper/reasoning-parts/erdos251/core.tex:483](../../paper/reasoning-parts/erdos251/core.tex#L483-L483)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5354-L5358) — lines `5354–5358`; excerpt `sha256:7634243bb1a190b0aeb3ad7cffcd772a6f9cb9cb1e54e1b3ea7d5bf9c9b18a25`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5310-L5314) — lines `5310–5314`; excerpt `sha256:7634243bb1a190b0aeb3ad7cffcd772a6f9cb9cb1e54e1b3ea7d5bf9c9b18a25`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3087](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3087-L3087), [cite at paper/reasoning-parts/erdos1041/core.tex:3043](../../paper/reasoning-parts/erdos1041/core.tex#L3043-L3043)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5428-L5434) — lines `5428–5434`; excerpt `sha256:693e1e0134f09226af4a4f04bb1f50d763c2bc0c40320ed6d730242cab1263bf`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L610-L612) — lines `610–612`; excerpt `sha256:ad96b93897cb722f9a63aa344b11a333231b11971c032d6bf1a0781e0d6ded9f`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2905-L2907) — lines `2905–2907`; excerpt `sha256:ad96b93897cb722f9a63aa344b11a333231b11971c032d6bf1a0781e0d6ded9f`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1676-L1681) — lines `1676–1681`; excerpt `sha256:10b82bb930fe79ac10a4ea88fdca0fe6cef302ef6284568b8ea7a1bd56f969d0`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2864-L2866) — lines `2864–2866`; excerpt `sha256:ad96b93897cb722f9a63aa344b11a333231b11971c032d6bf1a0781e0d6ded9f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L81-L81) — lines `81–81`; excerpt `sha256:8e56484cbb8a2a51938d6d95f9eb16930424134d3eb232b2a1c1323f9489b0f2`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1070-L1074) — lines `1070–1074`; excerpt `sha256:a79650c0f50caca8446521a3613124f26f30878a82d4d43715c4bfc4f1b646d1`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:114](../../paper/systems/claim-faithful-publication-systems-paper.tex#L114-L114), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:727](../../paper/systems/claim-faithful-publication-systems-paper.tex#L727-L727)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:567](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L567-L567)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3773](../../paper/archive/erdos249-257-main-paper.tex#L3773-L3773)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1980](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1980-L1980), [cite at paper/reasoning-parts/erdos251/core.tex:1939](../../paper/reasoning-parts/erdos251/core.tex#L1939-L1939)
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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3089-L3093) — lines `3089–3093`; excerpt `sha256:e3b1d19fa4854f7153d25ef24896c1b7f697c819f9574977485c2759ead98276`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3054-L3058) — lines `3054–3058`; excerpt `sha256:e3b1d19fa4854f7153d25ef24896c1b7f697c819f9574977485c2759ead98276`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1864](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1864-L1864), [cite at paper/reasoning-parts/erdos68/core.tex:1829](../../paper/reasoning-parts/erdos68/core.tex#L1829-L1829)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L743-L749) — lines `743–749`; excerpt `sha256:6cb7dcabcbc0e388ffa8e2348251a577293e5169688f4aaaffac1b8ae868d1ea`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10103-L10109) — lines `10103–10109`; excerpt `sha256:e10593522712515931ddcbaa7131d36a55628516394338e405b737d442819636`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9911-L9917) — lines `9911–9917`; excerpt `sha256:e10593522712515931ddcbaa7131d36a55628516394338e405b737d442819636`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:648](../../paper/249/erdos-249-binary-totient-series.tex#L648-L648)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9908](../../paper/249/erdos249-totient-reasoning-surface.tex#L9908-L9908), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9716](../../paper/reasoning-parts/erdos249/a249_front.tex#L9716-L9716)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1299-L1302) — lines `1299–1302`; excerpt `sha256:10c3199fda8e6b96e9871391653c60d86629257f2027c73dec8028c99d52a01a`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4075-L4078) — lines `4075–4078`; excerpt `sha256:68ea153c3563a568a2f8dd959b99f6641b703032a1460306b051df5a3a19d4f9`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4036-L4039) — lines `4036–4039`; excerpt `sha256:68ea153c3563a568a2f8dd959b99f6641b703032a1460306b051df5a3a19d4f9`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1051](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1051-L1051)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:608](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L608-L608), [cite at paper/reasoning-parts/erdos243/core.tex:569](../../paper/reasoning-parts/erdos243/core.tex#L569-L569)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4266-L4269) — lines `4266–4269`; excerpt `sha256:3566f4017e8d66bd416398ee1ff4829b468fbfc27cdd460a22f7d3c1443a3892`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1046-L1049) — lines `1046–1049`; excerpt `sha256:3566f4017e8d66bd416398ee1ff4829b468fbfc27cdd460a22f7d3c1443a3892`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4215-L4218) — lines `4215–4218`; excerpt `sha256:3566f4017e8d66bd416398ee1ff4829b468fbfc27cdd460a22f7d3c1443a3892`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:83a2da03f72cdfe7d20a66a82e8d957584ade075bfcbcc042444582792ef211e`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L95-L95) — lines `95–95`; excerpt `sha256:83a2da03f72cdfe7d20a66a82e8d957584ade075bfcbcc042444582792ef211e`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:419](../../paper/269/erdos-269-three-prime-running-lcm.tex#L419-L419)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:146](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L146-L146), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:409](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L409-L409), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1213](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1213-L1213), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1490](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1490-L1490), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3707](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3707-L3707), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:4199](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4199-L4199), [cite at paper/reasoning-parts/erdos269/core.tex:95](../../paper/reasoning-parts/erdos269/core.tex#L95-L95), [cite at paper/reasoning-parts/erdos269/core.tex:358](../../paper/reasoning-parts/erdos269/core.tex#L358-L358), [cite at paper/reasoning-parts/erdos269/core.tex:1162](../../paper/reasoning-parts/erdos269/core.tex#L1162-L1162), [cite at paper/reasoning-parts/erdos269/core.tex:1439](../../paper/reasoning-parts/erdos269/core.tex#L1439-L1439), [cite at paper/reasoning-parts/erdos269/core.tex:3656](../../paper/reasoning-parts/erdos269/core.tex#L3656-L3656), [cite at paper/reasoning-parts/erdos269/core.tex:4148](../../paper/reasoning-parts/erdos269/core.tex#L4148-L4148)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1083-L1086) — lines `1083–1086`; excerpt `sha256:4882a3b299d75653e0733b29ff553b0c30bef3f7e4584c239baa2dc69d719f05`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4308-L4311) — lines `4308–4311`; excerpt `sha256:d2de58d8a1aef218af5e1cbe7a8d2d2e6c1b7fa33cca90bcee80d5265ac4b37f`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4257-L4260) — lines `4257–4260`; excerpt `sha256:d2de58d8a1aef218af5e1cbe7a8d2d2e6c1b7fa33cca90bcee80d5265ac4b37f`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1013](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1013-L1013)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:183](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L183-L183), [cite at paper/reasoning-parts/erdos269/core.tex:132](../../paper/reasoning-parts/erdos269/core.tex#L132-L132)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10037-L10042) — lines `10037–10042`; excerpt `sha256:3b4314143d0179f0e80db37bd37b8d4c9238a3d5a98cff4c888fcdf15fd2d416`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9845-L9850) — lines `9845–9850`; excerpt `sha256:3b4314143d0179f0e80db37bd37b8d4c9238a3d5a98cff4c888fcdf15fd2d416`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8022](../../paper/249/erdos249-totient-reasoning-surface.tex#L8022-L8022), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8023](../../paper/249/erdos249-totient-reasoning-surface.tex#L8023-L8023), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7830](../../paper/reasoning-parts/erdos249/a249_front.tex#L7830-L7830), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7831](../../paper/reasoning-parts/erdos249/a249_front.tex#L7831-L7831)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L618-L620) — lines `618–620`; excerpt `sha256:5bb26410e95839b64ea4bf5f23b0e11414c0841dab9afdc4a31c006cc4754751`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2919-L2921) — lines `2919–2921`; excerpt `sha256:5bb26410e95839b64ea4bf5f23b0e11414c0841dab9afdc4a31c006cc4754751`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2878-L2880) — lines `2878–2880`; excerpt `sha256:5bb26410e95839b64ea4bf5f23b0e11414c0841dab9afdc4a31c006cc4754751`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L21-L21) — lines `21–21`; excerpt `sha256:07dad1a6dbaa03c54631370154c906de91a50cd710b3b9c6e143f85e14b3c973`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:552](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L552-L552)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1936](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1936-L1936), [cite at paper/reasoning-parts/erdos251/core.tex:1895](../../paper/reasoning-parts/erdos251/core.tex#L1895-L1895)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1118-L1123) — lines `1118–1123`; excerpt `sha256:8b16aa8ce3f46b281fb40b2e16b106525ac072214009c4f43d3751d3148a85ef`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5003-L5008) — lines `5003–5008`; excerpt `sha256:e0b4d65450b872a2ec9473172bcabec68557987449286f48db42d3c226f70988`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4972-L4977) — lines `4972–4977`; excerpt `sha256:e0b4d65450b872a2ec9473172bcabec68557987449286f48db42d3c226f70988`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:917](../../paper/1049/erdos-1049-rational-base-lambert.tex#L917-L917)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2673](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2673-L2673), [cite at paper/reasoning-parts/erdos1049/core.tex:2642](../../paper/reasoning-parts/erdos1049/core.tex#L2642-L2642)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4281-L4284) — lines `4281–4284`; excerpt `sha256:fc54218ee2caf5338f8576a083a77ebf02ded7474aabe6fadbda0c33f1624c08`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4230-L4233) — lines `4230–4233`; excerpt `sha256:fc54218ee2caf5338f8576a083a77ebf02ded7474aabe6fadbda0c33f1624c08`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1294-L1299) — lines `1294–1299`; excerpt `sha256:24a478d3e71a9e5ce6ab2dcf8084cf9ba533270acd0b15cdfd19710d0c338733`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4070-L4075) — lines `4070–4075`; excerpt `sha256:24a478d3e71a9e5ce6ab2dcf8084cf9ba533270acd0b15cdfd19710d0c338733`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4031-L4036) — lines `4031–4036`; excerpt `sha256:24a478d3e71a9e5ce6ab2dcf8084cf9ba533270acd0b15cdfd19710d0c338733`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1089-L1092) — lines `1089–1092`; excerpt `sha256:997988654d9ef70ccc079da055de714cc3514f6ed4822ee4b84eab7c073da669`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1049](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1049-L1049), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1096](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1096-L1096)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1000](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1000-L1000)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:986](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L986-L986), [cite at paper/reasoning-parts/erdos243/core.tex:947](../../paper/reasoning-parts/erdos243/core.tex#L947-L947)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2395](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2395-L2395), [cite at paper/reasoning-parts/erdos269/core.tex:2344](../../paper/reasoning-parts/erdos269/core.tex#L2344-L2344)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1458-L1462) — lines `1458–1462`; excerpt `sha256:156df176c039566fa6a406e54730ac45e0fabbf03ff99eaeb3b08442cc0945c5`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:717](../../paper/257/erdos-257-mersenne-support-subseries.tex#L717-L717)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10003-L10008) — lines `10003–10008`; excerpt `sha256:cda83ebde02e28a432b8ceb19002a8a337d3c75febb082deef2e12df21f76d3e`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9811-L9816) — lines `9811–9816`; excerpt `sha256:cda83ebde02e28a432b8ceb19002a8a337d3c75febb082deef2e12df21f76d3e`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:2526](../../paper/249/erdos249-totient-reasoning-surface.tex#L2526-L2526), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:2334](../../paper/reasoning-parts/erdos249/a249_front.tex#L2334-L2334)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3017-L3021) — lines `3017–3021`; excerpt `sha256:1c1ed4ef4c6101db50bde9f966d63761d20c722b5a1a19916cb663d42ee249fd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2982-L2986) — lines `2982–2986`; excerpt `sha256:1c1ed4ef4c6101db50bde9f966d63761d20c722b5a1a19916cb663d42ee249fd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2449-L2449) — lines `2449–2449`; excerpt `sha256:eaef0eb562b2565c4e6cca9b9e2071d569a2d058ca3df8fe1a95c3b9fbbe116f`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L853-L857) — lines `853–857`; excerpt `sha256:3875de59e714310957e9a10579cc224e98e345c01f4ca934900cb9d1bd7e5c4a`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:83](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L83-L83)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1156](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1156-L1157), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2163](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2163-L2164), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2484](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2484-L2484), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2487](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2487-L2487), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2495](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2495-L2495), [cite at paper/reasoning-parts/erdos68/core.tex:1121](../../paper/reasoning-parts/erdos68/core.tex#L1121-L1122), [cite at paper/reasoning-parts/erdos68/core.tex:2128](../../paper/reasoning-parts/erdos68/core.tex#L2128-L2129), [cite at paper/reasoning-parts/erdos68/core.tex:2449](../../paper/reasoning-parts/erdos68/core.tex#L2449-L2449), [cite at paper/reasoning-parts/erdos68/core.tex:2452](../../paper/reasoning-parts/erdos68/core.tex#L2452-L2452), [cite at paper/reasoning-parts/erdos68/core.tex:2460](../../paper/reasoning-parts/erdos68/core.tex#L2460-L2460)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2945-L2947) — lines `2945–2947`; excerpt `sha256:e6fc69e63673756998024749e72cb913b9a0094933c34fd8e81d93f0eeca483e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2904-L2906) — lines `2904–2906`; excerpt `sha256:e6fc69e63673756998024749e72cb913b9a0094933c34fd8e81d93f0eeca483e`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:550](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L550-L550), [cite at paper/reasoning-parts/erdos251/core.tex:509](../../paper/reasoning-parts/erdos251/core.tex#L509-L509)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4908-L4914) — lines `4908–4914`; excerpt `sha256:b6b59c3f516fe753628de797f741e46ad1554bcd562427e309cfd40f794a23f8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4877-L4883) — lines `4877–4883`; excerpt `sha256:b6b59c3f516fe753628de797f741e46ad1554bcd562427e309cfd40f794a23f8`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4599](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4599-L4599), [cite at paper/reasoning-parts/erdos1049/core.tex:4568](../../paper/reasoning-parts/erdos1049/core.tex#L4568-L4568)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1235-L1239) — lines `1235–1239`; excerpt `sha256:8a847cb8c6d7ed0d59130cbc1d2e6cc75ca5363d7b766e4b4549f87e237f59d6`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3995-L3999) — lines `3995–3999`; excerpt `sha256:8a847cb8c6d7ed0d59130cbc1d2e6cc75ca5363d7b766e4b4549f87e237f59d6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3956-L3960) — lines `3956–3960`; excerpt `sha256:8a847cb8c6d7ed0d59130cbc1d2e6cc75ca5363d7b766e4b4549f87e237f59d6`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:819](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L819-L819), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:837](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L837-L837)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:820](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L820-L820), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1596](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1596-L1596), [cite at paper/reasoning-parts/erdos243/core.tex:781](../../paper/reasoning-parts/erdos243/core.tex#L781-L781), [cite at paper/reasoning-parts/erdos243/core.tex:1557](../../paper/reasoning-parts/erdos243/core.tex#L1557-L1557)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4902-L4908) — lines `4902–4908`; excerpt `sha256:caca3710f524135671e299fa1162e5d77947646ae83681362b020268b6f0aac0`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4871-L4877) — lines `4871–4877`; excerpt `sha256:caca3710f524135671e299fa1162e5d77947646ae83681362b020268b6f0aac0`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L815-L815) — lines `815–815`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L815-L815) — lines `815–815`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L815-L815) — lines `815–815`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L815-L815) — lines `815–815`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L4-L13) — lines `4–13`; excerpt `sha256:9e02e269f490c0d8ee088d184d3cf2b53af45d9b0144a4623c9110e7230e7af9`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L19-L32) — lines `19–32`; excerpt `sha256:ed4a3e5b020b06b3f16f2771e4c9518cf5e0c23e46e275e30a93b5b498f5db23`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L58-L62) — lines `58–62`; excerpt `sha256:6fab9c0293d1ca17fe26b54f24d0f7366711b09b71d8f6e869df1315fb5c2dbc`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1483-L1490) — lines `1483–1490`; excerpt `sha256:c67b14d05ad70fe87ae10882e6666f671b4fb879b6ad3b2ac2f9cd21da8d1764`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9574-L9581) — lines `9574–9581`; excerpt `sha256:c67b14d05ad70fe87ae10882e6666f671b4fb879b6ad3b2ac2f9cd21da8d1764`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9374-L9381) — lines `9374–9381`; excerpt `sha256:c67b14d05ad70fe87ae10882e6666f671b4fb879b6ad3b2ac2f9cd21da8d1764`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1090-L1096) — lines `1090–1096`; excerpt `sha256:72d40703f422b4e9c77e9b7f7d1db51028590dcfa3b80e0dfd26187887ef7b98`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:905](../../paper/1049/erdos-1049-rational-base-lambert.tex#L905-L905)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:886](../../paper/257/erdos-257-mersenne-support-subseries.tex#L886-L886)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:846](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L846-L846), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2480](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2480-L2480), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4550](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4550-L4550), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4554](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4554-L4554), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4576](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4576-L4576), [cite at paper/reasoning-parts/erdos1049/core.tex:815](../../paper/reasoning-parts/erdos1049/core.tex#L815-L815), [cite at paper/reasoning-parts/erdos1049/core.tex:2449](../../paper/reasoning-parts/erdos1049/core.tex#L2449-L2449), [cite at paper/reasoning-parts/erdos1049/core.tex:4519](../../paper/reasoning-parts/erdos1049/core.tex#L4519-L4519), [cite at paper/reasoning-parts/erdos1049/core.tex:4523](../../paper/reasoning-parts/erdos1049/core.tex#L4523-L4523), [cite at paper/reasoning-parts/erdos1049/core.tex:4545](../../paper/reasoning-parts/erdos1049/core.tex#L4545-L4545)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9412](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9412-L9412), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9212](../../paper/reasoning-parts/erdos257/a257_front.tex#L9212-L9212)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L527-L528) — lines `527–528`; excerpt `sha256:593651151526dd9c60804cafcb6f765f4f855a943dd88f568cbe7e65e48b06fe`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2955-L2957) — lines `2955–2957`; excerpt `sha256:6287f2e5f5563289d4064e0d820c7d7f4d40b15e0efeaa8af2f7bf000182a58a`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2914-L2916) — lines `2914–2916`; excerpt `sha256:6287f2e5f5563289d4064e0d820c7d7f4d40b15e0efeaa8af2f7bf000182a58a`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:528](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L528-L528), [cite at paper/reasoning-parts/erdos251/core.tex:487](../../paper/reasoning-parts/erdos251/core.tex#L487-L487)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10126-L10130) — lines `10126–10130`; excerpt `sha256:2f294b2503d2448477ab88b5f01e57b82be38261f6866fa51e12cb42fdaf1931`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L7412-L7412) — lines `7412–7412`; excerpt `sha256:ea2c18fcbd108947a85f0c7ad3832b7c5a50121404e6ee760f1a053d967d615f`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9934-L9938) — lines `9934–9938`; excerpt `sha256:2f294b2503d2448477ab88b5f01e57b82be38261f6866fa51e12cb42fdaf1931`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7220-L7220) — lines `7220–7220`; excerpt `sha256:ea2c18fcbd108947a85f0c7ad3832b7c5a50121404e6ee760f1a053d967d615f`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7412](../../paper/249/erdos249-totient-reasoning-surface.tex#L7412-L7412), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7220](../../paper/reasoning-parts/erdos249/a249_front.tex#L7220-L7220)

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

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2215-L2220) — lines `2215–2220`; excerpt `sha256:de88340cc2b28c69940b64cf1bcdbf90dd118bb326ff5edd71abe0001f11021c`
- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L1356-L1356) — lines `1356–1356`; excerpt `sha256:c5730ed1aecc44a1cef58487cebc75be161e05aa5a960b5dcbb3825e6b92cf96`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1288](../../paper/synthesis/optimal-sparse-perturbations.tex#L1288-L1288), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1356](../../paper/synthesis/optimal-sparse-perturbations.tex#L1356-L1356)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5415-L5422) — lines `5415–5422`; excerpt `sha256:93d139a71e461686d30e06c7802e159563a317a1df01f8e655071348c500dd47`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2257](../../paper/archive/erdos249-257-main-paper.tex#L2257-L2257)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3005-L3009) — lines `3005–3009`; excerpt `sha256:3460ef54d7c16f79f21ea0acd344175689e099e53fd07f95423bbc149ab01fcc`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2970-L2974) — lines `2970–2974`; excerpt `sha256:3460ef54d7c16f79f21ea0acd344175689e099e53fd07f95423bbc149ab01fcc`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L875-L875) — lines `875–875`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L875-L875) — lines `875–875`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L875-L875) — lines `875–875`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [lean/ErdosProblems/Erdos68/PrimeZeroBranch.lean](../../lean/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3134-L3139) — lines `3134–3139`; excerpt `sha256:c866f4949ed4ad3259541be1ab078fcd2c3b951e2dcb35d831286f21d4ff0dae`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L893-L897) — lines `893–897`; excerpt `sha256:3347ae470eba67fe218dfc8f10a1ac6bcff33e960f9653c66d0f9c00f480a123`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:651](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L651-L651)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:910](../../paper/68/erdos68-factorial-reasoning-surface.tex#L910-L910), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1805](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1805-L1805), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1852](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1852-L1852), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1856](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1856-L1856), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2155](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2155-L2155), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2777](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2777-L2777), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2778](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2778-L2778), [cite at paper/reasoning-parts/erdos68/core.tex:875](../../paper/reasoning-parts/erdos68/core.tex#L875-L875), [cite at paper/reasoning-parts/erdos68/core.tex:1770](../../paper/reasoning-parts/erdos68/core.tex#L1770-L1770), [cite at paper/reasoning-parts/erdos68/core.tex:1817](../../paper/reasoning-parts/erdos68/core.tex#L1817-L1817), [cite at paper/reasoning-parts/erdos68/core.tex:1821](../../paper/reasoning-parts/erdos68/core.tex#L1821-L1821), [cite at paper/reasoning-parts/erdos68/core.tex:2120](../../paper/reasoning-parts/erdos68/core.tex#L2120-L2120), [cite at paper/reasoning-parts/erdos68/core.tex:2742](../../paper/reasoning-parts/erdos68/core.tex#L2742-L2742), [cite at paper/reasoning-parts/erdos68/core.tex:2743](../../paper/reasoning-parts/erdos68/core.tex#L2743-L2743)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1282-L1284) — lines `1282–1284`; excerpt `sha256:c66e4c643708ca23615d9d6c9473c802267b432d3f477cb5deb758c7fb5f7d69`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:805](../../paper/systems/claim-faithful-publication-systems-paper.tex#L805-L805)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L600-L602) — lines `600–602`; excerpt `sha256:7d4b3edd3f0259421dd8a74baf144d917da4ddfbfce902474872b62fbe04ff8c`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2893-L2895) — lines `2893–2895`; excerpt `sha256:7d4b3edd3f0259421dd8a74baf144d917da4ddfbfce902474872b62fbe04ff8c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2852-L2854) — lines `2852–2854`; excerpt `sha256:7d4b3edd3f0259421dd8a74baf144d917da4ddfbfce902474872b62fbe04ff8c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L931-L931) — lines `931–931`; excerpt `sha256:fb59e0780e408bca1499f60eeea9ba2361376ec468ffa18034717c0b6bfa9c53`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1905-L1905) — lines `1905–1905`; excerpt `sha256:eaaaa84d309b1a0c1d56fc36e531a59a4fa33af5709a256b9b48f214908ca467`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L22-L22) — lines `22–22`; excerpt `sha256:6fe10d86cfbff9e425bdd6578dd696a5a4e58cae9a09bb6b9e1d399e6bd9e791`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:554](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L554-L554)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:970](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L970-L970), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1947](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1947-L1947), [cite at paper/reasoning-parts/erdos251/core.tex:929](../../paper/reasoning-parts/erdos251/core.tex#L929-L929), [cite at paper/reasoning-parts/erdos251/core.tex:1906](../../paper/reasoning-parts/erdos251/core.tex#L1906-L1906)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2913-L2915) — lines `2913–2915`; excerpt `sha256:1a14b5dab89311efa51f08c6a1083aa9a70ec67efa331a3a3b2b5c065768d4e5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2872-L2874) — lines `2872–2874`; excerpt `sha256:1a14b5dab89311efa51f08c6a1083aa9a70ec67efa331a3a3b2b5c065768d4e5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L377-L377) — lines `377–377`; excerpt `sha256:f299553286b4320e16b47eddc966a0712f4f7aa504c996308e3b4654f6115f5e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L377-L377) — lines `377–377`; excerpt `sha256:f299553286b4320e16b47eddc966a0712f4f7aa504c996308e3b4654f6115f5e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L377-L377) — lines `377–377`; excerpt `sha256:f299553286b4320e16b47eddc966a0712f4f7aa504c996308e3b4654f6115f5e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1246-L1253) — lines `1246–1253`; excerpt `sha256:5f6919f6f6f0d056ce159d53b5e9796ab4e2ae6a3e46c34b596e2ae84458afac`
- [lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean](../../lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L7-L23) — lines `7–23`; excerpt `sha256:321f1f193ba6cea89edee0e703684bdf6234e2bc38d8b5dc53a6395d1b42cf33`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L628-L630) — lines `628–630`; excerpt `sha256:a3a48dc0af2ce0549ba6c3e9eea30a30f6e3554c01f26cebd6566dc236f816dc`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:279](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L279-L279), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:287](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L287-L287), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:451](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L451-L451)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:418](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L418-L418), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:453](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L453-L453), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:460](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L460-L460), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1289](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1289-L1289), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1394](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1394-L1394), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1406](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1406-L1406), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1450](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1450-L1450), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1459](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1459-L1459), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1518](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1518-L1518), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1525](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1525-L1525), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1971](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1971-L1971), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2136](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2136-L2136), [cite at paper/reasoning-parts/erdos251/core.tex:377](../../paper/reasoning-parts/erdos251/core.tex#L377-L377), [cite at paper/reasoning-parts/erdos251/core.tex:412](../../paper/reasoning-parts/erdos251/core.tex#L412-L412), [cite at paper/reasoning-parts/erdos251/core.tex:419](../../paper/reasoning-parts/erdos251/core.tex#L419-L419), [cite at paper/reasoning-parts/erdos251/core.tex:1248](../../paper/reasoning-parts/erdos251/core.tex#L1248-L1248), [cite at paper/reasoning-parts/erdos251/core.tex:1353](../../paper/reasoning-parts/erdos251/core.tex#L1353-L1353), [cite at paper/reasoning-parts/erdos251/core.tex:1365](../../paper/reasoning-parts/erdos251/core.tex#L1365-L1365), [cite at paper/reasoning-parts/erdos251/core.tex:1409](../../paper/reasoning-parts/erdos251/core.tex#L1409-L1409), [cite at paper/reasoning-parts/erdos251/core.tex:1418](../../paper/reasoning-parts/erdos251/core.tex#L1418-L1418), [cite at paper/reasoning-parts/erdos251/core.tex:1477](../../paper/reasoning-parts/erdos251/core.tex#L1477-L1477), [cite at paper/reasoning-parts/erdos251/core.tex:1484](../../paper/reasoning-parts/erdos251/core.tex#L1484-L1484), [cite at paper/reasoning-parts/erdos251/core.tex:1930](../../paper/reasoning-parts/erdos251/core.tex#L1930-L1930), [cite at paper/reasoning-parts/erdos251/core.tex:2095](../../paper/reasoning-parts/erdos251/core.tex#L2095-L2095)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4963-L4969) — lines `4963–4969`; excerpt `sha256:fd04dc6525552320cb5e54a12e8e0739172ac9163ecf01bedfd7dcf7a6485be2`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4932-L4938) — lines `4932–4938`; excerpt `sha256:fd04dc6525552320cb5e54a12e8e0739172ac9163ecf01bedfd7dcf7a6485be2`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4760-L4760) — lines `4760–4760`; excerpt `sha256:a687d79281dfe79c9bc043998a9b0da79a7a7066f72571d9b7a84107de6bf44d`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4791-L4791) — lines `4791–4791`; excerpt `sha256:a687d79281dfe79c9bc043998a9b0da79a7a7066f72571d9b7a84107de6bf44d`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4791](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4791-L4791), [cite at paper/reasoning-parts/erdos1049/core.tex:4760](../../paper/reasoning-parts/erdos1049/core.tex#L4760-L4760)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5434-L5441) — lines `5434–5441`; excerpt `sha256:add18eb59b9977acb225b85709240b860573b28552d807c45eec7058c8a77d79`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L612-L614) — lines `612–614`; excerpt `sha256:d72e98994bd66ed7b43de80a46537b74234c2d45f82d4b6ff1a1a24103ce7117`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2907-L2909) — lines `2907–2909`; excerpt `sha256:d72e98994bd66ed7b43de80a46537b74234c2d45f82d4b6ff1a1a24103ce7117`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2866-L2868) — lines `2866–2868`; excerpt `sha256:d72e98994bd66ed7b43de80a46537b74234c2d45f82d4b6ff1a1a24103ce7117`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1939-L1939) — lines `1939–1939`; excerpt `sha256:6c9614868ad6ac591604ecab3aefeeaeb3a729ddb735225be25d197b9e9d3c0f`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:114](../../paper/systems/claim-faithful-publication-systems-paper.tex#L114-L114), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:727](../../paper/systems/claim-faithful-publication-systems-paper.tex#L727-L727)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:568](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L568-L568)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3775](../../paper/archive/erdos249-257-main-paper.tex#L3775-L3775)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1980](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1980-L1980), [cite at paper/reasoning-parts/erdos251/core.tex:1939](../../paper/reasoning-parts/erdos251/core.tex#L1939-L1939)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L492-L495) — lines `492–495`; excerpt `sha256:a46579d416d03f380705b4e9553347ab0b66c9e1ec6b4d3a84ac0f5a246008c1`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2935-L2937) — lines `2935–2937`; excerpt `sha256:0ff84f114bce1e696b9859dc6944ea26811f851d98955e2f5cf233d48165ac05`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2894-L2896) — lines `2894–2896`; excerpt `sha256:0ff84f114bce1e696b9859dc6944ea26811f851d98955e2f5cf233d48165ac05`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:495](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L495-L495), [cite at paper/reasoning-parts/erdos251/core.tex:454](../../paper/reasoning-parts/erdos251/core.tex#L454-L454)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L930-L935) — lines `930–935`; excerpt `sha256:ada915f17a1ed537b753f4f88aa73ca8631254a748c99e5c556dd0dcde0016c1`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5284-L5289) — lines `5284–5289`; excerpt `sha256:8c9bd3c3345cf07ffa6815f7ec1a90485fe63e2b80e1724053327490204d780a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5240-L5245) — lines `5240–5245`; excerpt `sha256:8c9bd3c3345cf07ffa6815f7ec1a90485fe63e2b80e1724053327490204d780a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1994-L1994) — lines `1994–1994`; excerpt `sha256:bf660f22b7c2b5ad1586f91c21fc4e625ed74e4ec29b524be165def32d7d016d`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:575](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L575-L575)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2038](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2038-L2038), [cite at paper/reasoning-parts/erdos1041/core.tex:1994](../../paper/reasoning-parts/erdos1041/core.tex#L1994-L1994)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L845-L849) — lines `845–849`; excerpt `sha256:f959bb68cc06d5c8fc21e17f7becd84211e2f55bf7f57c01f14dae8f0a569649`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2997-L3001) — lines `2997–3001`; excerpt `sha256:259feb71f707ecd3c171a22910b7c8c7271afda92cdb5fc376bb96e7b1e3a4c4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2962-L2966) — lines `2962–2966`; excerpt `sha256:259feb71f707ecd3c171a22910b7c8c7271afda92cdb5fc376bb96e7b1e3a4c4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1226-L1226) — lines `1226–1226`; excerpt `sha256:ad8298ac69c418e00f4fc3862912b0d4b44decd465a1ec66f04646c9f5d5ecfb`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1226-L1226) — lines `1226–1226`; excerpt `sha256:ad8298ac69c418e00f4fc3862912b0d4b44decd465a1ec66f04646c9f5d5ecfb`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:85](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L85-L85)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1261](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1261-L1261), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2160](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2160-L2160), [cite at paper/reasoning-parts/erdos68/core.tex:1226](../../paper/reasoning-parts/erdos68/core.tex#L1226-L1226), [cite at paper/reasoning-parts/erdos68/core.tex:2125](../../paper/reasoning-parts/erdos68/core.tex#L2125-L2125)

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
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1159-L1161) — lines `1159–1161`; excerpt `sha256:5c3c73cac106465de37f6b0d206a52293b5061ddb965921d239f718eb722db0e`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:755](../../paper/systems/claim-faithful-publication-systems-paper.tex#L755-L755)
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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1222-L1226) — lines `1222–1226`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3982-L3986) — lines `3982–3986`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2889-L2891) — lines `2889–2891`; excerpt `sha256:7cd258f662728fc8a7ab550dde219bad542c55e2520f19416bf3439de413de29`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3943-L3947) — lines `3943–3947`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L767-L767) — lines `767–767`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L767-L767) — lines `767–767`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L767-L767) — lines `767–767`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2848-L2850) — lines `2848–2850`; excerpt `sha256:7cd258f662728fc8a7ab550dde219bad542c55e2520f19416bf3439de413de29`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L528-L528) — lines `528–528`; excerpt `sha256:135bd438efff4d1cc9eb4aa85885a7a589e44741d435f5882864ba601bb76893`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L30-L32) — lines `30–32`; excerpt `sha256:1139eed2569eedcc245358cbde7bff884c8a36c06c78b0a38246a82257dae3ec`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:816](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L816-L816)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:806](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L806-L806), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2325](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2325-L2326), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2473](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2473-L2473), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3615](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3615-L3615), [cite at paper/reasoning-parts/erdos243/core.tex:767](../../paper/reasoning-parts/erdos243/core.tex#L767-L767), [cite at paper/reasoning-parts/erdos243/core.tex:2286](../../paper/reasoning-parts/erdos243/core.tex#L2286-L2287), [cite at paper/reasoning-parts/erdos243/core.tex:2434](../../paper/reasoning-parts/erdos243/core.tex#L2434-L2434), [cite at paper/reasoning-parts/erdos243/core.tex:3576](../../paper/reasoning-parts/erdos243/core.tex#L3576-L3576)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:569](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L569-L569), [cite at paper/reasoning-parts/erdos251/core.tex:528](../../paper/reasoning-parts/erdos251/core.tex#L528-L528)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1109-L1114) — lines `1109–1114`; excerpt `sha256:878e039506eed9cbdca4b85b0b81b72924aa12144ce61f35980e357fdec8b62e`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4984-L4989) — lines `4984–4989`; excerpt `sha256:f203205a4c16098f6ea390c2eb9ffeedc8e3c1bc649018114be1c761d0cbad7b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4953-L4958) — lines `4953–4958`; excerpt `sha256:f203205a4c16098f6ea390c2eb9ffeedc8e3c1bc649018114be1c761d0cbad7b`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:916](../../paper/1049/erdos-1049-rational-base-lambert.tex#L916-L916)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2582](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2582-L2582), [cite at paper/reasoning-parts/erdos1049/core.tex:2551](../../paper/reasoning-parts/erdos1049/core.tex#L2551-L2551)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1033-L1037) — lines `1033–1037`; excerpt `sha256:e84ccbfd298ca45cdf1dc99cde6fa6c5c320db56fdd37d12d9716a81ae36f325`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4828-L4832) — lines `4828–4832`; excerpt `sha256:e84ccbfd298ca45cdf1dc99cde6fa6c5c320db56fdd37d12d9716a81ae36f325`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4797-L4801) — lines `4797–4801`; excerpt `sha256:e84ccbfd298ca45cdf1dc99cde6fa6c5c320db56fdd37d12d9716a81ae36f325`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:5c955cffe3f917b2bdd49ab1e2c3c923e754d64fd159f4452cd5726135089931`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:868](../../paper/1049/erdos-1049-rational-base-lambert.tex#L868-L868)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:85](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L85-L85), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:607](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L607-L607), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:815](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L815-L815), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:843](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L843-L843), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1130](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1130-L1130), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3706](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3706-L3706), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4659](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4659-L4659), [cite at paper/reasoning-parts/erdos1049/core.tex:54](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54), [cite at paper/reasoning-parts/erdos1049/core.tex:576](../../paper/reasoning-parts/erdos1049/core.tex#L576-L576), [cite at paper/reasoning-parts/erdos1049/core.tex:784](../../paper/reasoning-parts/erdos1049/core.tex#L784-L784), [cite at paper/reasoning-parts/erdos1049/core.tex:812](../../paper/reasoning-parts/erdos1049/core.tex#L812-L812), [cite at paper/reasoning-parts/erdos1049/core.tex:1099](../../paper/reasoning-parts/erdos1049/core.tex#L1099-L1099), [cite at paper/reasoning-parts/erdos1049/core.tex:3675](../../paper/reasoning-parts/erdos1049/core.tex#L3675-L3675), [cite at paper/reasoning-parts/erdos1049/core.tex:4628](../../paper/reasoning-parts/erdos1049/core.tex#L4628-L4628)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4881-L4888) — lines `4881–4888`; excerpt `sha256:ca3ad143147a5d2804f66fa9a2b445b365c705a19273a1ae8c77f2c257c09062`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4850-L4857) — lines `4850–4857`; excerpt `sha256:ca3ad143147a5d2804f66fa9a2b445b365c705a19273a1ae8c77f2c257c09062`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4652-L4652) — lines `4652–4652`; excerpt `sha256:a9816f01cbbbed3606bb3c7105e1f1bc81607266eee3e3bc860ed90c8624c684`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4683](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4683-L4683), [cite at paper/reasoning-parts/erdos1049/core.tex:4652](../../paper/reasoning-parts/erdos1049/core.tex#L4652-L4652)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L885-L889) — lines `885–889`; excerpt `sha256:6d0b157c1bad243c1cdb9d1a9e0b30105bc3e63f1061acabf6c3d01f0b057b0e`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3049-L3053) — lines `3049–3053`; excerpt `sha256:301c9e11ac561f9aaaabc33c46f271f3f0cecc122a99db652c476daecd2fda2a`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3014-L3018) — lines `3014–3018`; excerpt `sha256:301c9e11ac561f9aaaabc33c46f271f3f0cecc122a99db652c476daecd2fda2a`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:408](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L408-L408)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1062](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1062-L1062), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1064](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1064-L1064), [cite at paper/reasoning-parts/erdos68/core.tex:1027](../../paper/reasoning-parts/erdos68/core.tex#L1027-L1027), [cite at paper/reasoning-parts/erdos68/core.tex:1029](../../paper/reasoning-parts/erdos68/core.tex#L1029-L1029)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4320-L4324) — lines `4320–4324`; excerpt `sha256:66c2a5257f58be1672dd0343ef38da2c5d2f46e01935b51c3b7cec7dcf17b0ea`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4269-L4273) — lines `4269–4273`; excerpt `sha256:66c2a5257f58be1672dd0343ef38da2c5d2f46e01935b51c3b7cec7dcf17b0ea`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3447](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3447-L3447), [cite at paper/reasoning-parts/erdos269/core.tex:3396](../../paper/reasoning-parts/erdos269/core.tex#L3396-L3396)

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
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1136-L1139) — lines `1136–1139`; excerpt `sha256:b286b09fb9c90ba4049a0069fa8b7698b73f4799d2b73fac1a54fdceef20a7d8`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:828](../../paper/systems/claim-faithful-publication-systems-paper.tex#L828-L828)
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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1096-L1102) — lines `1096–1102`; excerpt `sha256:f0b413584f891c1a725c23699a9efae2e7cbaba89e97347422243d21325f0020`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4324-L4330) — lines `4324–4330`; excerpt `sha256:f0b413584f891c1a725c23699a9efae2e7cbaba89e97347422243d21325f0020`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4273-L4279) — lines `4273–4279`; excerpt `sha256:f0b413584f891c1a725c23699a9efae2e7cbaba89e97347422243d21325f0020`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:1008](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1008-L1008)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3450](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3450-L3450), [cite at paper/reasoning-parts/erdos269/core.tex:3399](../../paper/reasoning-parts/erdos269/core.tex#L3399-L3399)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1958](../../paper/synthesis/optimal-sparse-perturbations.tex#L1958-L1958)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5409-L5415) — lines `5409–5415`; excerpt `sha256:cdaff80cd6c7f5f1646ee2c7a858ab106e0225c3e87b92ca3df2858826a27e1e`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L879-L879) — lines `879–879`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [lean/Erdos249257/CampbellShiftSynchronization.lean](../../lean/Erdos249257/CampbellShiftSynchronization.lean#L4-L22) — lines `4–22`; excerpt `sha256:d517c238bb94dca26752a32c4273074633c39a9b8af3551e069cb7a282081388`
- [lean/Erdos249257/CampbellShiftSynchronization.lean](../../lean/Erdos249257/CampbellShiftSynchronization.lean#L294-L299) — lines `294–299`; excerpt `sha256:a33a451732d6d625372bccee6302e08dfdb1ec94ea88b2bb9013d5eff55197d4`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9543-L9549) — lines `9543–9549`; excerpt `sha256:a764b921cc13bcb1cc2ca1ce687e7493ad39d0ad55326278645b6b44ec94cfdc`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9343-L9349) — lines `9343–9349`; excerpt `sha256:a764b921cc13bcb1cc2ca1ce687e7493ad39d0ad55326278645b6b44ec94cfdc`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2253](../../paper/archive/erdos249-257-main-paper.tex#L2253-L2254)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1387](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1387-L1387), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1187](../../paper/reasoning-parts/erdos257/a257_front.tex#L1187-L1187)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1253-L1257) — lines `1253–1257`; excerpt `sha256:40aecd254891fc812f0e8980ec61fe681a524880f510bb6cfc26f94b02d1b732`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4020-L4024) — lines `4020–4024`; excerpt `sha256:40aecd254891fc812f0e8980ec61fe681a524880f510bb6cfc26f94b02d1b732`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3981-L3985) — lines `3981–3985`; excerpt `sha256:40aecd254891fc812f0e8980ec61fe681a524880f510bb6cfc26f94b02d1b732`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:643](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L643-L643)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2595](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2595-L2595), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3156](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3156-L3156), [cite at paper/reasoning-parts/erdos243/core.tex:2556](../../paper/reasoning-parts/erdos243/core.tex#L2556-L2556), [cite at paper/reasoning-parts/erdos243/core.tex:3117](../../paper/reasoning-parts/erdos243/core.tex#L3117-L3117)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10042-L10047) — lines `10042–10047`; excerpt `sha256:32599e7a2120d5129deed6138e89e7ebef17cd091f20f82776fde8449312e5ca`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9850-L9855) — lines `9850–9855`; excerpt `sha256:32599e7a2120d5129deed6138e89e7ebef17cd091f20f82776fde8449312e5ca`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8033](../../paper/249/erdos249-totient-reasoning-surface.tex#L8033-L8033), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7841](../../paper/reasoning-parts/erdos249/a249_front.tex#L7841-L7841)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L857-L861) — lines `857–861`; excerpt `sha256:809f864ff438892c5e39d707a4ca21b142f8134a6475d204916011234a842169`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2989-L2993) — lines `2989–2993`; excerpt `sha256:56545f01462da2d6bd59af54b4c105a4e78489461a9719ab3c6db971299941ef`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2954-L2958) — lines `2954–2958`; excerpt `sha256:56545f01462da2d6bd59af54b4c105a4e78489461a9719ab3c6db971299941ef`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L739-L739) — lines `739–739`; excerpt `sha256:7a549791ed341c1373f0b0c9b40e13b147f3aa3b9484ded64b1ef2f2a94aefa9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L739-L739) — lines `739–739`; excerpt `sha256:7a549791ed341c1373f0b0c9b40e13b147f3aa3b9484ded64b1ef2f2a94aefa9`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:621](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L621-L621)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:774](../../paper/68/erdos68-factorial-reasoning-surface.tex#L774-L774), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2175](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2175-L2175), [cite at paper/reasoning-parts/erdos68/core.tex:739](../../paper/reasoning-parts/erdos68/core.tex#L739-L739), [cite at paper/reasoning-parts/erdos68/core.tex:2140](../../paper/reasoning-parts/erdos68/core.tex#L2140-L2140)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L535-L535) — lines `535–535`; excerpt `sha256:2b4bc5fe17fd8e238debc2df722a5d5ae84b5416fb38720f4a94b13b2f06e216`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9081-L9081) — lines `9081–9081`; excerpt `sha256:ec7c5a5f4b94d4c2488e3f5a57b5af9b264fc4f248b588252be6eb05d0e88fe2`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8881-L8881) — lines `8881–8881`; excerpt `sha256:ec7c5a5f4b94d4c2488e3f5a57b5af9b264fc4f248b588252be6eb05d0e88fe2`

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

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2314-L2320) — lines `2314–2320`; excerpt `sha256:47977a6056cdfc3896fa8809315451f7388750fbf3c2c4dc8cecc22c8db23ce3`
- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L1354-L1354) — lines `1354–1354`; excerpt `sha256:96ba3449869250ee797a74c61af26bb684a11fdafa259cc3adebbfc6c0c854c7`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1354](../../paper/synthesis/optimal-sparse-perturbations.tex#L1354-L1354)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L950-L953) — lines `950–953`; excerpt `sha256:a2ea0b0d9fe464fd26b77c94c6b482f3c945b98a5fd53c85d7624d1728340989`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5339-L5342) — lines `5339–5342`; excerpt `sha256:a2ea0b0d9fe464fd26b77c94c6b482f3c945b98a5fd53c85d7624d1728340989`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5295-L5298) — lines `5295–5298`; excerpt `sha256:a2ea0b0d9fe464fd26b77c94c6b482f3c945b98a5fd53c85d7624d1728340989`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:828](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L828-L828)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4970](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4970-L4970), [cite at paper/reasoning-parts/erdos1041/core.tex:4926](../../paper/reasoning-parts/erdos1041/core.tex#L4926-L4926)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3065-L3069) — lines `3065–3069`; excerpt `sha256:9840d0a92d94f920800cfb600e645cca774371293151ecea13c66a6cce76d3c8`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3030-L3034) — lines `3030–3034`; excerpt `sha256:9840d0a92d94f920800cfb600e645cca774371293151ecea13c66a6cce76d3c8`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1742](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1742-L1742), [cite at paper/reasoning-parts/erdos68/core.tex:1707](../../paper/reasoning-parts/erdos68/core.tex#L1707-L1707)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1037-L1041) — lines `1037–1041`; excerpt `sha256:985c11e75c32024f7b85ea003ea9eddbd077703fea826834a3b574b6cc2d115c`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4832-L4836) — lines `4832–4836`; excerpt `sha256:985c11e75c32024f7b85ea003ea9eddbd077703fea826834a3b574b6cc2d115c`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4801-L4805) — lines `4801–4805`; excerpt `sha256:985c11e75c32024f7b85ea003ea9eddbd077703fea826834a3b574b6cc2d115c`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:698](../../paper/1049/erdos-1049-rational-base-lambert.tex#L698-L698)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:266](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L266-L266), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:479](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L479-L479), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4733](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4733-L4733), [cite at paper/reasoning-parts/erdos1049/core.tex:235](../../paper/reasoning-parts/erdos1049/core.tex#L235-L235), [cite at paper/reasoning-parts/erdos1049/core.tex:448](../../paper/reasoning-parts/erdos1049/core.tex#L448-L448), [cite at paper/reasoning-parts/erdos1049/core.tex:4702](../../paper/reasoning-parts/erdos1049/core.tex#L4702-L4702)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L877-L881) — lines `877–881`; excerpt `sha256:d0240691fa5956d3f42d0e151a25cfaa8d0a16e7b1cc510ba6b9ef168ed084dc`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3041-L3045) — lines `3041–3045`; excerpt `sha256:d0240691fa5956d3f42d0e151a25cfaa8d0a16e7b1cc510ba6b9ef168ed084dc`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3006-L3010) — lines `3006–3010`; excerpt `sha256:d0240691fa5956d3f42d0e151a25cfaa8d0a16e7b1cc510ba6b9ef168ed084dc`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:605](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L605-L605)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1685](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1685-L1685), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1714](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1714-L1714), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2178](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2178-L2178), [cite at paper/reasoning-parts/erdos68/core.tex:1650](../../paper/reasoning-parts/erdos68/core.tex#L1650-L1650), [cite at paper/reasoning-parts/erdos68/core.tex:1679](../../paper/reasoning-parts/erdos68/core.tex#L1679-L1679), [cite at paper/reasoning-parts/erdos68/core.tex:2143](../../paper/reasoning-parts/erdos68/core.tex#L2143-L2143)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L871-L875) — lines `871–875`; excerpt `sha256:372ad8d3f82ff0212ee04c7dd5a7269a56a5c9a52cae45f7d05245ccae260a87`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L5270-L5279) — lines `5270–5279`; excerpt `sha256:72a88e5a23c5730b248edc8d8bc104d1818c8c71ea25dbdd60a7c6074bb79d61`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L5226-L5235) — lines `5226–5235`; excerpt `sha256:72a88e5a23c5730b248edc8d8bc104d1818c8c71ea25dbdd60a7c6074bb79d61`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4228-L4228) — lines `4228–4228`; excerpt `sha256:636651adc41018ae6f90faa70e4010583deaa28671fcc1c916acccd02f62d5c8`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4228-L4228) — lines `4228–4228`; excerpt `sha256:636651adc41018ae6f90faa70e4010583deaa28671fcc1c916acccd02f62d5c8`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:774](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L774-L774)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4269](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4269-L4269), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4272](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4272-L4272), [cite at paper/reasoning-parts/erdos1041/core.tex:4225](../../paper/reasoning-parts/erdos1041/core.tex#L4225-L4225), [cite at paper/reasoning-parts/erdos1041/core.tex:4228](../../paper/reasoning-parts/erdos1041/core.tex#L4228-L4228)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2903-L2905) — lines `2903–2905`; excerpt `sha256:82eaf36e749d94b9bc85e72cb6decbd8b7ce392b18e1edb0f50d7c491ba8f4cf`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2862-L2864) — lines `2862–2864`; excerpt `sha256:82eaf36e749d94b9bc85e72cb6decbd8b7ce392b18e1edb0f50d7c491ba8f4cf`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L330-L330) — lines `330–330`; excerpt `sha256:160a2b014966aaf70cba2fb38dd6be86a729335f10185109e6e77f49fbcedee2`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1914-L1914) — lines `1914–1914`; excerpt `sha256:ad49b5aa94a8d9963ee6dcb001d2d84dc32e0776315128832b860e41fd3a9cf0`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L608-L610) — lines `608–610`; excerpt `sha256:82eaf36e749d94b9bc85e72cb6decbd8b7ce392b18e1edb0f50d7c491ba8f4cf`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:316](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L316-L316)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:371](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L371-L371), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1956](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1956-L1956), [cite at paper/reasoning-parts/erdos251/core.tex:330](../../paper/reasoning-parts/erdos251/core.tex#L330-L330), [cite at paper/reasoning-parts/erdos251/core.tex:1915](../../paper/reasoning-parts/erdos251/core.tex#L1915-L1915)

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

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5395-L5400) — lines `5395–5400`; excerpt `sha256:4caf7a23e043524edc0b28f6c56ff51ffc65fbd8e9bcea766fda7d8bd0b07263`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:923](../../paper/archive/erdos249-257-main-paper.tex#L923-L923), [cite at paper/archive/erdos249-257-main-paper.tex:4674](../../paper/archive/erdos249-257-main-paper.tex#L4674-L4674), [cite at paper/archive/erdos249-257-main-paper.tex:4709](../../paper/archive/erdos249-257-main-paper.tex#L4709-L4709)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1063-L1068) — lines `1063–1068`; excerpt `sha256:76708e9e1ba9cb5b881eb2f319d5a6bf94dc5132c846fc6c1ebd51aef0fb72d4`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4853-L4858) — lines `4853–4858`; excerpt `sha256:6e2271ffb0543bc3fdc177f643ec7c22e54002e1c42ef7828bffd0cf406d75df`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4822-L4827) — lines `4822–4827`; excerpt `sha256:6e2271ffb0543bc3fdc177f643ec7c22e54002e1c42ef7828bffd0cf406d75df`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:54](../../paper/1049/erdos-1049-rational-base-lambert.tex#L54-L54)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1728](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1728-L1728), [cite at paper/reasoning-parts/erdos1049/core.tex:1697](../../paper/reasoning-parts/erdos1049/core.tex#L1697-L1697)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1477-L1483) — lines `1477–1483`; excerpt `sha256:6c20454741356816e2d6d22e0fde01df4c611d7435ed3814f610e86ef368a80d`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9568-L9574) — lines `9568–9574`; excerpt `sha256:6c20454741356816e2d6d22e0fde01df4c611d7435ed3814f610e86ef368a80d`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9368-L9374) — lines `9368–9374`; excerpt `sha256:6c20454741356816e2d6d22e0fde01df4c611d7435ed3814f610e86ef368a80d`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:837](../../paper/257/erdos-257-mersenne-support-subseries.tex#L837-L837)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9408](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9408-L9408), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9208](../../paper/reasoning-parts/erdos257/a257_front.tex#L9208-L9208)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4862-L4867) — lines `4862–4867`; excerpt `sha256:bd1db09a836b7bae7294afc1da1a7ae1ba135a083600d289e0dd8b45d24c10e4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4831-L4836) — lines `4831–4836`; excerpt `sha256:bd1db09a836b7bae7294afc1da1a7ae1ba135a083600d289e0dd8b45d24c10e4`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1433](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1433-L1433), [cite at paper/reasoning-parts/erdos1049/core.tex:1402](../../paper/reasoning-parts/erdos1049/core.tex#L1402-L1402)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L602-L604) — lines `602–604`; excerpt `sha256:2efe0e466de39d202e8f4b37c4f1254922fdfb071f848b688d6e85dd4f4cfff4`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2895-L2897) — lines `2895–2897`; excerpt `sha256:509f2c022f6bb16fcc6561688a6ee2a68568c8655480a3a52794977fbfd3eeec`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2854-L2856) — lines `2854–2856`; excerpt `sha256:509f2c022f6bb16fcc6561688a6ee2a68568c8655480a3a52794977fbfd3eeec`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:64](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L64-L64)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:283](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L283-L283), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:471](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L471-L471), [cite at paper/reasoning-parts/erdos251/core.tex:242](../../paper/reasoning-parts/erdos251/core.tex#L242-L242), [cite at paper/reasoning-parts/erdos251/core.tex:430](../../paper/reasoning-parts/erdos251/core.tex#L430-L430)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:883](../../paper/synthesis/optimal-sparse-perturbations.tex#L883-L883), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1018](../../paper/synthesis/optimal-sparse-perturbations.tex#L1018-L1018), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1858](../../paper/synthesis/optimal-sparse-perturbations.tex#L1858-L1858), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1975](../../paper/synthesis/optimal-sparse-perturbations.tex#L1975-L1975)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L3053-L3057) — lines `3053–3057`; excerpt `sha256:913a7268d821938b55f3e6c38752a0db175dd6dca90b4edd9be62c706db57416`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L3018-L3022) — lines `3018–3022`; excerpt `sha256:913a7268d821938b55f3e6c38752a0db175dd6dca90b4edd9be62c706db57416`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1731](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1731-L1731), [cite at paper/reasoning-parts/erdos68/core.tex:1696](../../paper/reasoning-parts/erdos68/core.tex#L1696-L1696)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4269-L4272) — lines `4269–4272`; excerpt `sha256:c0c58cb7c064ff51cdf457f20ba15d04a78eb43f30bbf3764f9162de257e6a00`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L1049-L1052) — lines `1049–1052`; excerpt `sha256:c0c58cb7c064ff51cdf457f20ba15d04a78eb43f30bbf3764f9162de257e6a00`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L4218-L4221) — lines `4218–4221`; excerpt `sha256:c0c58cb7c064ff51cdf457f20ba15d04a78eb43f30bbf3764f9162de257e6a00`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L94-L94) — lines `94–94`; excerpt `sha256:072346b11faedd93181d1f5ba983b7885b1d5fd9b4292dcfa07310184ac025ab`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L94-L94) — lines `94–94`; excerpt `sha256:072346b11faedd93181d1f5ba983b7885b1d5fd9b4292dcfa07310184ac025ab`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:424](../../paper/269/erdos-269-three-prime-running-lcm.tex#L424-L424)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:145](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L145-L145), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:411](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L411-L411), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1214](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1214-L1214), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:3706](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3706-L3706), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:4200](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L4200-L4200), [cite at paper/reasoning-parts/erdos269/core.tex:94](../../paper/reasoning-parts/erdos269/core.tex#L94-L94), [cite at paper/reasoning-parts/erdos269/core.tex:360](../../paper/reasoning-parts/erdos269/core.tex#L360-L360), [cite at paper/reasoning-parts/erdos269/core.tex:1163](../../paper/reasoning-parts/erdos269/core.tex#L1163-L1163), [cite at paper/reasoning-parts/erdos269/core.tex:3655](../../paper/reasoning-parts/erdos269/core.tex#L3655-L3655), [cite at paper/reasoning-parts/erdos269/core.tex:4149](../../paper/reasoning-parts/erdos269/core.tex#L4149-L4149)
- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1297](../../paper/synthesis/optimal-sparse-perturbations.tex#L1297-L1297)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L10130-L10135) — lines `10130–10135`; excerpt `sha256:5ab6928799e39a4d3e26716ecba39c7c67a800837b04a83ce236837f3eae312d`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L7415-L7415) — lines `7415–7415`; excerpt `sha256:6137621520080ad6f0ea38d5b86775d92fec7d19b870807a765fdfd728e9362c`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9938-L9943) — lines `9938–9943`; excerpt `sha256:5ab6928799e39a4d3e26716ecba39c7c67a800837b04a83ce236837f3eae312d`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7223-L7223) — lines `7223–7223`; excerpt `sha256:6137621520080ad6f0ea38d5b86775d92fec7d19b870807a765fdfd728e9362c`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7415](../../paper/249/erdos249-totient-reasoning-surface.tex#L7415-L7415), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7223](../../paper/reasoning-parts/erdos249/a249_front.tex#L7223-L7223)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4975-L4979) — lines `4975–4979`; excerpt `sha256:284f2b11997d11abbeb3afe292b15bc5217f0f0f9edf5787e81581abdf458efa`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2444-L2444) — lines `2444–2444`; excerpt `sha256:e45056ad57ac969b6825cff487af5bde054739cf76036caa64219404edfb82fe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4944-L4948) — lines `4944–4948`; excerpt `sha256:284f2b11997d11abbeb3afe292b15bc5217f0f0f9edf5787e81581abdf458efa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2413-L2413) — lines `2413–2413`; excerpt `sha256:e45056ad57ac969b6825cff487af5bde054739cf76036caa64219404edfb82fe`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2444](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2444-L2444), [cite at paper/reasoning-parts/erdos1049/core.tex:2413](../../paper/reasoning-parts/erdos1049/core.tex#L2413-L2413)

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

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2115-L2119) — lines `2115–2119`; excerpt `sha256:5404323f44e0bf7745e5f12de10c65654b41f753d8706832e970ae20416d06be`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1805](../../paper/synthesis/optimal-sparse-perturbations.tex#L1805-L1805), [cite at paper/synthesis/optimal-sparse-perturbations.tex:1832](../../paper/synthesis/optimal-sparse-perturbations.tex#L1832-L1832)

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

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2123-L2127) — lines `2123–2127`; excerpt `sha256:3d65436d31201d414ea230e03345193de1bd649376c50acdc800ef0e44b497c7`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1814](../../paper/synthesis/optimal-sparse-perturbations.tex#L1814-L1814)

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

- [paper/synthesis/optimal-sparse-perturbations.tex](../../paper/synthesis/optimal-sparse-perturbations.tex#L2119-L2123) — lines `2119–2123`; excerpt `sha256:dd7f0d46e967844319c928981d430ccea291c9ca3135f81eb0cc7cfe494ff39b`

Paper citation usages:

- `optimal-sparse-perturbations`: [cite at paper/synthesis/optimal-sparse-perturbations.tex:1807](../../paper/synthesis/optimal-sparse-perturbations.tex#L1807-L1807)

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

- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4998-L5005) — lines `4998–5005`; excerpt `sha256:737d5477a37bdfbe338d30af01c736674dfc46101542dd73448f0906325c87ee`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L5029-L5036) — lines `5029–5036`; excerpt `sha256:737d5477a37bdfbe338d30af01c736674dfc46101542dd73448f0906325c87ee`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:291](../../paper/1049/erdos-1049-rational-base-lambert.tex#L291-L291)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1976](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1976-L1976), [cite at paper/reasoning-parts/erdos1049/core.tex:1945](../../paper/reasoning-parts/erdos1049/core.tex#L1945-L1945)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4858-L4862) — lines `4858–4862`; excerpt `sha256:4e24fef998f109ce93696a8d9d04b5a1a6af4b7a9e8b88bd4ccee7a4154cfd88`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2430-L2430) — lines `2430–2430`; excerpt `sha256:7a145aa9594fa020d57e86e4eea374a60a878af8c1b11118e150c4a10410fe93`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4827-L4831) — lines `4827–4831`; excerpt `sha256:4e24fef998f109ce93696a8d9d04b5a1a6af4b7a9e8b88bd4ccee7a4154cfd88`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2399-L2399) — lines `2399–2399`; excerpt `sha256:7a145aa9594fa020d57e86e4eea374a60a878af8c1b11118e150c4a10410fe93`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2430](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2430-L2430), [cite at paper/reasoning-parts/erdos1049/core.tex:2399](../../paper/reasoning-parts/erdos1049/core.tex#L2399-L2399)

## Coverage requiring review

These gaps are shown explicitly so the catalogue cannot be mistaken for complete historical knowledge.

- Registered papers scanned: `22`; TeX source files scanned after local includes: `91`.
- Citation keys without a local bibliography definition: `0`
- Bibliography entries without a curated source link: `94`
- Lean lexical candidates awaiting review: `793`
- Unresolved local TeX includes: `0`

Machine-readable inventories, hashes, unresolved keys, and lexical candidates: [source-attribution-index.json](source-attribution-index.json).
