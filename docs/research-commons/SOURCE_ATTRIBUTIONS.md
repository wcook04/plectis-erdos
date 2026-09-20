<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Source attributions

_Generated from the authored source registry; do not hand-edit._

This index shows which public sources informed which papers, problems, Lean-facing records, and implemented changes. Source credit does not establish proof, novelty, endorsement, peer review, or complete historical coverage.

Private correspondence appears only under a neutral anonymous identity until public naming is confirmed. Its email, mailbox location, message text, and private evidence remain outside this repository.

## Coverage and anonymous implementation credits

The registry contains `291` curated sources across `23` registered papers and `1448` Lean library files.

Source review states: `bibliography_only`: `89`; `existing_source_closure`: `31`; `external_claim_unverified`: `1`; `implemented_advice`: `3`; `source_verified`: `167`.

Bibliography coverage records attribution already present in the corpus. A `bibliography_only` record still needs direct source-passage verification; a completed lexical review does not certify a source-to-theorem correspondence.

Implemented advice whose identity is awaiting confirmation:

- [Formalization classification and cheap inspection advice](#source-correspondence-001) — Implemented advice to classify each selected result, expose exact statements, proof provenance, novelty status, sorry count, axiom budget, and boundaries in formalization.yaml, and to provide a cheap Comparator inspection route with an altered-statement rejection fixture. The current public surface has evolved beyond the original interface count; the durable implementation is the manifest-plus-Comparator pattern and its explicit scope ceiling.
- [Theorem-first packaging and literature-comparison advice](#source-correspondence-002) — Implemented advice to lead with the exact finite-level rank and basis, give the CRT/Dirichlet-style independence mechanism, compare the result precisely with Allouche–Shallit, Coons, Martin, and adjacent k-kernel literature, and link a minimal Lean entry. The paper states the exact rank k^e+1 and basis, records that Coons already proved non-k-regularity and Martin supplies a broader external affine-independence antecedent while the public Lean proof establishes all-base independence separately, and keeps the unbounded #249 irrationality endpoint open. No proof verification, novelty judgment, or progress-on-parent-problem judgment is attributed to the correspondent.
- [Prior-art comparison advice](#source-correspondence-003) — Implemented a received pointer by comparing the cited q-Apéry construction with the #1049 rational-base programme. The public source closure verifies that the paper targets the same Lambert value, identifies the q-WZ operator and the integer-base denominator-clearing boundary, and credits both published authors in the ordinary literature row. The local Lean module separately proves that Van Assche’s different moving diagonal has a nonzero n=0 residual for the cited operator. This correspondence row credits only the private prior-art pointer; it does not claim the correspondent checked the comparison, calculations, Lean, or #1049 mathematics.

- Unmatched citation keys: `0`
- Bibliography entries awaiting curated links: `41`
- Lean candidates awaiting review: `293` (`3` direct URL/DOI/arXiv rows; `1169` surname/key rows; categories may overlap).

## Browse by problem

- **Erdős #1041**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates), [Formalization classification and cheap inspection advice](#source-correspondence-001), [Degree-seven total-variation counterexample for polynomial lemniscates](#source-erdos1041-ani-degree-seven-candidate-counterexample), [Independent check of candidate degree-seven counterexample](#source-erdos1041-morluto-independent-check), [Quartic case of Erdős #1041](#source-erdos1041-pendyala-quartic), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [A Markov-type inequality for arbitrary plane continua](#source-eremenko-2007-markov-type-inequality-plane-continua), [An extremal problem for polynomials](#source-eremenko-lempert-1994-extremal-problem-for-polynomials), [Comb functions](#source-eremenko-yuditskii-2012-comb-functions), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [The maximal length of the Erdős–Herzog–Piranian lemniscate in high…](#source-source-0e12f93aeac487), [Lemniscates and inequalities for the logarithmic capacities of cont…](#source-source-2a86f52125aec0), [Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zu…](#source-source-2ec6bf87654604), [Bad Polynomials for Newton's Method](#source-source-318ee5e7cf6d74), [The area of polynomial images and preimages](#source-source-40bc4064b92788), [Three refinements for the lemniscate-path programme](#source-source-45037c29c04bed), [Length functions of lemniscates](#source-source-57fe330e419648), [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff), [Critical points and values of complex polynomials](#source-source-7ac8693558c1a2), [On the length of lemniscates](#source-source-7f1f2a3fd9238c), [A bound for Smale's mean value conjecture for complex polynomials](#source-source-818467bc1cb170), [Shortest paths in polynomial lemniscate sublevel sets and a problem…](#source-source-8710374c3e8c9f), [The arc length of the lemniscate |p(z)|=1](#source-source-89b9a294db76bb), [Computing the Newtonian Graph](#source-source-92b0dfb67f5009), [A Degree-Four Lemniscate Path Theorem](#source-source-951f70d8dfc418), [Number of Components of Polynomial Lemniscates: A Problem of Erdős,…](#source-source-97b4e6a82335a7), [Two-dimensional shapes and lemniscates](#source-source-9e37cc2fe7db3e), [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec), [Inequalities for critical values of polynomials](#source-source-b10b965e63a00d), [Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichun…](#source-source-b4b0f2811b1d2d), [Some inequalities for polynomials and rational functions associated…](#source-source-dcbe400c96be59), [Four-point distortion theorem for complex polynomials](#source-source-f0af8e6f36727f), [A Short Path Joining Two Zeros Inside a Polynomial Lemniscate](#source-source-f300911fb03a5c)
- **Erdős #1049**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Prior-art comparison advice](#source-correspondence-003), [Retrieval of Chowla 1947 original scan](#source-erdos1049-bloom-chowla-scan-retrieval), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #1049](#source-formal-conjectures-adapter-problem-1049), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [A problem about Mahler functions](#source-source-0a6b8c93371570), [Stieltjes moment sequences of polynomials](#source-source-0f46dee5024c66), [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [À propos de la série ∑\_{n≥1} x^n/(q^n−1)](#source-source-169c3d67838965), [On a permutation group related to ζ(2)](#source-source-176d35cb60b651), [On the non-quadraticity of values of the q-exponential function and…](#source-source-22ef36d016ca81), [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62), [On powers of Stieltjes moment sequences, II](#source-source-2a10c7287879c3), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [A determinant identity for moments of orthogonal polynomials that i…](#source-source-3479bad7869d7c), [Common Factors in Fraction-Free Matrix Decompositions](#source-source-39e4fc546549fd), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [Lattice paths and branched continued fractions: An infinite sequenc…](#source-source-490b1875016ea4), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Calculation of Gauss Quadrature Rules](#source-source-53a2a9c4a9e7c2), [NIST Digital Library of Mathematical Functions, Eq. 17.2.37](#source-source-5857f9959e7529), [On an incomplete argument of Erdős on the irrationality of Lambert…](#source-source-5911448b65fdf9), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [On the irrationality of ∑ 1/(q^n+r)](#source-source-62f9190aeb7d34), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [Arithmetical functions and irrationality of Lambert series](#source-source-6cfe654e650970), [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b), [Smith normal form in combinatorics](#source-source-91756d895a28a8), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Zero Coefficients of Rational Power Series and Rational Lambert Series](#source-source-aa2d5c249362f1), [On the irrationality of generalized q-logarithm](#source-source-ae9859af28fdcd), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [Continued-fraction characterization of Stieltjes moment sequences w…](#source-source-c61a0cf3f328ce), [Irrationality proof of certain Lambert series using little q-Jacobi…](#source-source-ca19e504149107), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94), [FormalConjectures.ErdosProblems.1049](#source-source-d7a43109c64c0c), [Log-convex and Stieltjes moment sequences](#source-source-e535117ac620e6), [Arithmetical investigations of a certain infinite product](#source-source-e553241a97e580), [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f), [Remarks on irrationality of q-harmonic series](#source-source-f1c687cb5e9ae4), [A determinantal approach to irrationality](#source-source-f67bf9959aa230), [Rational approximations to a q-analogue of π and some other q-series](#source-source-f9fd9214c9ef11), [Multivariate Rogers-Szego polynomials and flags in finite vector sp…](#source-source-vinroot-2010-multivariate-rogers-szego)
- **Erdős #243**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Koizumi pseudo-greedy equivalence and computation pointer](#source-erdos243-kovac-koizumi-pointer), [Rational-tail deterministic pair recurrence and open-boundary reduc…](#source-erdos243-tao-tail-pair-recurrence), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Irrationality exponents of certain fast converging series of ration…](#source-source-0f03e2dab0b8c2), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [FormalConjectures.ErdosProblems.243](#source-source-1713b9ad6350bd), [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641), [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62), [Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partia…](#source-source-2a3af2a360bb15), [A theorem on irrationality of infinite series and applications](#source-source-318b37ba5af2eb), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [On the irrationality of polynomial Cantor series](#source-source-77ddbf43e364f7), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Irrationality of the reciprocal sum of doubly exponential sequences](#source-source-86d1745e2d139b), [Chebotarëv and his density theorem](#source-source-abedb02f9939e5), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [{Digital Library of Mathematical Functions}, {Section} 5.11(iii): R…](#source-source-b95bf142df7fb5), [Irrationality Criteria for Series by Erdős and Straus](#source-source-c6e97d89c9fa5f), [On the rationality of Cantor and Ahmes series](#source-source-cbaba7aeeb0f71), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f), [Erdős #243: working report](#source-source-ee991edd431d57)
- **Erdős #249**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Theorem-first packaging and literature-comparison advice](#source-correspondence-002), [Möbius-transform identity for the binary totient constant](#source-erdos249-fan-mobius-transform), [Irrationality of the n=2^m sparse totient subseries](#source-erdos249-rafik-sparse-power-two-subseries), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #249](#source-formal-conjectures-adapter-problem-249), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891), [Erdős–Gál lacunary-series law of the iterated logarithm (two-part s…](#source-proposed-direct-7f278004ad452a), [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c), [Note on normal numbers](#source-proposed-direct-f7f90747134dba), [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da), [On asymptotic distributions of arithmetical functions](#source-source-0e9b7210b29d99), [On the set of partial sums of an infinite series](#source-source-0ecb074e507b86), [Answer to An infinite sum based on the mod-parity of Euler's totien…](#source-source-0f61ad0796acdf), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Simultaneous inequalities among values of the Euler phi-function](#source-source-11b46a0435368f), [A survey of gcd-sum functions](#source-source-22ce74d28ddb49), [Regular sequences and the joint spectral radius](#source-source-296ff41148fff7), [On a curious property of vulgar fractions](#source-source-2aa4970cfda278), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [On the law of the iterated logarithm. I](#source-source-39690ee8e07b0c), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [A dynamical proof of the van der Corput inequality](#source-source-3d300ccd5e4cbb), [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [The ring of k -regular sequences](#source-source-5752bb5009e4de), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Integer sequences and periodic points](#source-source-5cac1ad51acb12), [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [Modular functions and transcendence questions](#source-source-6346eeeac5036d), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [How to prove that a sequence is not automatic](#source-source-6b460d123159d9), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [Comment and formula added to OEIS A256936 (revisions 28 and 31)](#source-source-71037224a1dd7c), [(Non)automaticity of number theoretic functions](#source-source-741da55b02c5a9), [On the complexity of algebraic numbers I. Expansions in integer bases](#source-source-7c8ba4ea6eea79), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [The Lambert series factorization theorem](#source-source-8935df46fb4693), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [Comment on Erdős Problem #249](#source-source-99c2f3cb190b95), [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81), [Multiplicative functions and k-automatic sequences](#source-source-a0d109b4492fba), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [Transcendence of generating functions whose coefficients are multip…](#source-source-b791f5b49e0da6), [Smooth numbers: computational number theory and beyond](#source-source-bc5d16b84e62c7), [The Fourier transform of functions of the greatest common divisor](#source-source-c786f202d47318), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [On the binary digits of the Erdős--Borwein constant](#source-source-eca9e699590922), [Uber die asymptotische Verteilung reeller Zahlen mod 1](#source-source-eeff3fa685af8a), [Sparse Polynomial-Weighted Expansions](#source-source-f4ad17717c8fd4)
- **Erdős #251**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Schlage-Puchta Theorem 2 literature pointer](#source-erdos251-alfaiz-schlage-puchta-pointer), [Counterexample to Erdős variable-denominator expectation](#source-erdos251-kovac-variable-denominator-counterexample), [Conditional #251 proof under Kuperberg Conjecture 1.3 and Lean form…](#source-erdos251-land-conditional-proof-lean), [Prime-gap summation-by-parts equivalence and conditional route](#source-erdos251-tao-prime-gap-equivalence), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #251](#source-formal-conjectures-adapter-problem-251), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Multiplicative Number Theory I: Classical Theory](#source-source-0aca0e5e4e03c0), [On the Erdős problem #251](#source-source-0ec7ca07508557), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Beweis eines Satzes von Tschebyschef](#source-source-20c650f8cf3744), [Erdős Problems discussion thread #251](#source-source-21738452dcb95c), [On the largest prime factors of n and n+1](#source-source-27575f46a101c1), [Multigeometric sequences and Cantorvals](#source-source-2b0038d2c239f5), [Sur certaines séries à valeur irrationnelle](#source-source-2ee394177d0f38), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [Sums of singular series along arithmetic progressions and with smoo…](#source-source-450aed97015b8f), [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Continued Fractions](#source-source-5ee5f85bd606ee), [Subsum sets: intervals, Cantor sets, and Cantorvals](#source-source-63a234b13e4427), [Small gaps between primes](#source-source-6564b203677735), [On Kakeya Conditions for Achievement Sets](#source-source-6d8837bbc174ce), [Achievement sets -- current results and open problems](#source-source-77333436a9e579), [Achievable Cantorvals almost without reversed Kakeya conditions](#source-source-779915b8355ac1), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Sums of singular series with large sets and the tail of the distrib…](#source-source-811205223e0788), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3), [Variants of the Selberg sieve, and bounded intervals containing man…](#source-source-91aa380a16dba9), [Local gap statistics, telescoping, and normality](#source-source-9a38b2d8b0dada), [Ford circles, continued fractions, and best approximation of the se…](#source-source-9b23918ce33c38), [FormalConjectures.ErdosProblems.251](#source-source-b202a3f125817d), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [More on Kakeya Conditions for Achievement Sets](#source-source-b46f8a083b4271), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001), [Bounded gaps between primes](#source-source-c32d672658410d), [The Poisson Tail Conjecture for primes in short intervals](#source-source-c9b987093aaf4e), [On a new condition implying that an achievement set is a Cantorval…](#source-source-ce27d27dd5ec77), [Long gaps between primes](#source-source-d3995db1508bc9), [The irrationality of some number theoretical series](#source-source-d471eacdba0f87), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [Partitions with prescribed sum of reciprocals: asymptotic bounds](#source-source-dbbc7de069eeee), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f), [A conditional proof of the irrationality of ∑\_{n≥1} p\_n 2^{−n} unde…](#source-source-f42f9e04743a4c), [Generalized bases for the real numbers](#source-source-fb4194cadb150b)
- **Erdős #257**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Earlier variants, interval-filling negative variant, and fat-Cantor…](#source-erdos257-kovac-context-bundle), [Older Erdős and Borwein attribution for even/odd supports](#source-erdos257-kovac-older-special-case-attribution), [Period-two Lambert theorem applied to even and odd supports](#source-erdos257-tang-tachiya-period-two), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #257](#source-formal-conjectures-adapter-problem-257), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Diophantine Problems for q-Zeta Values](#source-proposed-direct-0ef4f73f93ceed), [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [Divisor-bounded multiplicative functions in short intervals](#source-proposed-direct-6c67db53ef5f8c), [The critical-window profile for d\_k in short intervals](#source-proposed-direct-6f90767d1d01dd), [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da), [On the set of partial sums of an infinite series](#source-source-0ecb074e507b86), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [On a curious property of vulgar fractions](#source-source-2aa4970cfda278), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [Some problems and results on the irrationality of the sum of infini…](#source-source-43a734be32736f), [FormalConjectures.ErdosProblems.257](#source-source-4bb571f8383293), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [The ring of k -regular sequences](#source-source-5752bb5009e4de), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [Modular functions and transcendence questions](#source-source-6346eeeac5036d), [Subsum sets: intervals, Cantor sets, and Cantorvals](#source-source-63a234b13e4427), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Über beliebige Teilsummen absolut konvergenter Reihen](#source-source-691e9cc3c46273), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [(Non)automaticity of number theoretic functions](#source-source-741da55b02c5a9), [Achievement sets -- current results and open problems](#source-source-77333436a9e579), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3), [The Lambert series factorization theorem](#source-source-8935df46fb4693), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [Irrationality of Lambert series associated with a periodic sequence](#source-source-9ce84321e202f1), [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [On the binary digits of the Erdős--Borwein constant](#source-source-eca9e699590922), [The logarithmic endpoint fails under arithmetic sampling](#source-source-endpoint2026-logarithmic-repair), [Sparse Polynomial-Weighted Expansions](#source-source-f4ad17717c8fd4), [Linear independence of certain Lambert series](#source-source-f6ee6890db85d9)
- **Erdős #269**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Infinite-prime-set irrationality proof and correction chain](#source-erdos269-fan-infinite-p-proof-repair), [Two-prime Hecke–Mahler factorisation and transcendence disclosure](#source-erdos269-fan-two-prime-disclosure), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [The Prime Number Theorem](#source-source-06457731c60720), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [On the irrationality of Cantor and Ahmes series](#source-source-1a7535a5e17a8c), [Comment on Erdős Problem #269](#source-source-21cdeefea4c8ec), [Letter to the Editor](#source-source-22aba734190d65), [Transcendence of Hecke–Mahler Series](#source-source-29bdada58b414a), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Sur le développement en fraction continue d'un nombre choisi au hasard](#source-source-5270112e32002d), [FormalConjectures.ErdosProblems.269](#source-source-573a79feb36d47), [Continued Fractions](#source-source-5ee5f85bd606ee), [On the set of points of convergence of a lacunary trigonometric ser…](#source-source-62ee65065db497), [Strongly complete sets and a conjecture of Erdős](#source-source-71fb76f6e1363b), [On the irrationality of polynomial Cantor series](#source-source-77ddbf43e364f7), [On the number of positive integers ≤ x and free of prime factors \> y](#source-source-78565c625f0ea3), [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](#source-source-7a9657920d576b), [On the complexity of algebraic numbers I. Expansions in integer bases](#source-source-7c8ba4ea6eea79), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [On the arithmetic properties of complex values of Hecke-Mahler seri…](#source-source-9c2776b87b1155), [On integers generated by a finite number of fixed primes](#source-source-ab6d6d6b890f57), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [Transcendence and continued fraction expansion of values of Hecke--…](#source-source-b9d7160919621f), [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380), [Irrationality Criteria for Series by Erdős and Straus](#source-source-c6e97d89c9fa5f), [A new proof of Nishioka's theorem in Mahler's method](#source-source-e7f2f796dbcdb6), [Mahler's method in several variables and finite automata](#source-source-eaeb7980382323), [Arithmetic properties of certain functions in several variables III](#source-source-fcf73a15ff9c7c)
- **Erdős #68**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #68](#source-formal-conjectures-adapter-problem-68), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [On the sequence $n!$ mod $p$](#source-source-02fc1f0e6f0418), [Lower bounds for some value sets over finite fields: incidence geom…](#source-source-04603f785c9e7f), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674), [An improved point-line incidence bound over arbitrary fields](#source-source-29cbac966b8b76), [On equal products of consecutive integers](#source-source-3068a3586a5e8b), [Character sums and congruences with n!](#source-source-34b520c561ee3c), [Factorial residues modulo a prime: beyond the square-root bound](#source-source-365c2b5cf46ebe), [On the greatest and least prime factors of n!+1](#source-source-3fb9e4907eec24), [Some problems and results on the irrationality of the sum of infini…](#source-source-43a734be32736f), [On the irrationality of certain 2-adic zeta values](#source-source-5122572a1e7312), [On the largest prime divisor of n!+1](#source-source-57adfd0cdcd8c2), [Prime divisors of shifted factorials](#source-source-5f85fb0bd75b8b), [A geometric proof that e is irrational and a new measure of its irr…](#source-source-6a5bf83735fdef), [Distribution of factorials modulo $p$](#source-source-724fef812699b7), [The product of consecutive integers is never a power](#source-source-7d923cace5602a), [Über die einfachen Zahlensysteme](#source-source-8ac37c92429a46), [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [On the irrationality of certain p-adic zeta values](#source-source-b3b7518e07e159), [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5), [On Equal Products of Consecutive Integers](#source-source-b6d577df139d85), [On the irrationality of factorial series](#source-source-c835bc94aad831), [On the greatest and least prime factors of n!+1 , II](#source-source-d1710db60eae06), [Representations of Real Numbers by Infinite Series](#source-source-e13ecb7c94852a), [On the largest prime factor of n!+2^n−1](#source-source-e66e0693f05f0a), [Rational numbers with odd greedy expansion of fixed length](#source-source-ef6233b59b95cb), [Additive congruences with factorials modulo a prime](#source-source-f1a42898642b5f), [NIST Digital Library of Mathematical Functions, §1.12(ii) Convergents](#source-source-f213b302ada43a), [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](#source-source-fb64da05c3acc7)

<details>
<summary>Browse alphabetically by author or public identity</summary>


- **A mathematician (name withheld pending confirmation)**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Theorem-first packaging and literature-comparison advice](#source-correspondence-002), [Prior-art comparison advice](#source-correspondence-003)
- **A. Anandkumar**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **A. Baanen**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **A. C. W. Finkelstein**: [An analysis of the requirements traceability problem](#source-source-e1665a6398558f)
- **A. D. Brucker**: [Isabelle/DOF: Design and Implementation](#source-source-51efe25c48a86d)
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
- **Alain Togbé**: [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380)
- **Alan D. Sokal**: [Lattice paths and branched continued fractions: An infinite sequenc…](#source-source-490b1875016ea4), [Continued-fraction characterization of Stieltjes moment sequences w…](#source-source-c61a0cf3f328ce)
- **Alessandro Languasco**: [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380)
- **Alex Zhindon-Romero**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Alexander Fryntov**: [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec)
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
- **B. Wolff**: [Isabelle/DOF: Design and Implementation](#source-source-51efe25c48a86d)
- **B. Yanahama**: [Lean Atlas: An Integrated Proof Environment for Scalable Human--AI…](#source-source-ae32306341559a)
- **Banks, William D.**: [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5)
- **Bao-Xuan Zhu**: [Lattice paths and branched continued fractions: An infinite sequenc…](#source-source-490b1875016ea4), [Log-convex and Stieltjes moment sequences](#source-source-e535117ac620e6)
- **Barrodale, I.**: [On Equal Products of Consecutive Integers](#source-source-b6d577df139d85)
- **Bartoszewicz, Artur**: [Multigeometric sequences and Cantorvals](#source-source-2b0038d2c239f5)
- **Bin Dong**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Boris Adamczewski**: [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c), [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082), [A new proof of Nishioka's theorem in Mahler's method](#source-source-e7f2f796dbcdb6), [Mahler's method in several variables and finite automata](#source-source-eaeb7980382323)
- **Brian Etz**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Bryan Dai**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
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
- **D. Pratt**: [Symposium: Trust via Auditable Records for Communities of AI Scient…](#source-source-f9a9d10dc9c525)
- **D. Schmersau**: [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0)
- **D. Smertnig**: [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63)
- **D. Testa**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **D. Zeilberger**: [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b)
- **Daniel Duverney**: [Irrationality exponents of certain fast converging series of ration…](#source-source-0f03e2dab0b8c2), [Arithmetical functions and irrationality of Lambert series](#source-source-6cfe654e650970)
- **Daniel Jarka**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Daniel Rosendo**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **David J. Jeffrey**: [Common Factors in Fraction-Free Matrix Decompositions](#source-source-39e4fc546549fd)
- **David Tischler**: [Critical points and values of complex polynomials](#source-source-7ac8693558c1a2)
- **Dawsen Hwang**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Demis Hassabis**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Dongruo An**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **E. Crane**: [The area of polynomial images and preimages](#source-source-40bc4064b92788)
- **E. G. Straus**: [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f)
- **Earl T. Barr**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Edward Crane**: [A bound for Smale's mean value conjecture for complex polynomials](#source-source-818467bc1cb170)
- **Edward van de Meent**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Emad Shihab**: [Synergizing LLMs and Knowledge Graphs: A Novel Approach to Software…](#source-arxiv-2412-03815)
- **Erdős, Paul**: [The product of consecutive integers is never a power](#source-source-7d923cace5602a)
- **Eric Leonen**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Erick Wong**: [Answer to An infinite sum based on the mod-parity of Euler's totien…](#source-source-0f61ad0796acdf)
- **Evan Wang**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Evan Zheran Liu**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Evgenia Karunus**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **F. G. Sayward**: [Hints on test data selection](#source-source-c309c1132b63e3)
- **F. Herzog**: [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff)
- **F. Luca**: [Character sums and congruences with n!](#source-source-34b520c561ee3c), [Prime divisors of shifted factorials](#source-source-5f85fb0bd75b8b), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44)
- **F. W. J. Olver et al. (eds.)**: [NIST Digital Library of Mathematical Functions, Eq. 17.2.37](#source-source-5857f9959e7529)
- **Fanjin Zhang**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Federico Pasqualotto**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Federico Pellarin**: [On the arithmetic properties of complex values of Hecke-Mahler seri…](#source-source-9c2776b87b1155)
- **Fedor Nazarov**: [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec)
- **Filipczak, Ma{\\l}gorzata**: [Multigeometric sequences and Cantorvals](#source-source-2b0038d2c239f5)
- **Florian Luca**: [Transcendence of Hecke–Mahler Series](#source-source-29bdada58b414a), [On Transcendence of Numbers Related to Sturmian and Arnoux-Rauzy Words](#source-source-7a9657920d576b), [Irrationality of Lambert series associated with a periodic sequence](#source-source-9ce84321e202f1), [Sequences of integers generated by two fixed primes](#source-source-bbb68df5b83380), [On the largest prime factor of n!+2^n−1](#source-source-e66e0693f05f0a), [Linear independence of certain Lambert series](#source-source-f6ee6890db85d9), [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](#source-source-fb64da05c3acc7)
- **Floris van Doorn**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **G. Cantor**: [Über die einfachen Zahlensysteme](#source-source-8ac37c92429a46)
- **G. Everest**: [Integer sequences and periodic points](#source-source-5cac1ad51acb12)
- **G. Piranian**: [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff)
- **G. Pólya**: [Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zu…](#source-source-2ec6bf87654604)
- **G. Rhin**: [On a permutation group related to ζ(2)](#source-source-176d35cb60b651)
- **Garrett Bingham**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Gene H. Golub**: [Calculation of Gauss Quadrature Rules](#source-source-53a2a9c4a9e7c2)
- **Giovanni Inchiostro**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **GitHub**: [Preventing pwn requests](#source-source-9ef9271dbecbce)
- **Glyn Harman**: [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001)
- **Golnaz Ghiasi**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Google DeepMind**: [formal-conjectures](#source-source-5edeb2408c36bd)
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
- **Henry Yuen**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Hu, Xiyu**: [Lower bounds for some value sets over finite fields: incidence geom…](#source-source-04603f785c9e7f)
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
- **I. Takahara**: [Toward Auditable AI Scientists: A Hypothesis Evolution Protocol for…](#source-source-4c664304e00cd3)
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
- **M. Harman**: [An analysis and survey of the development of mutation testing](#source-source-3a21eca35f05cf)
- **M. Kripner**: [OpenProver: Agentic and Interactive Theorem Proving with Lean 4](#source-source-d31e3bc51f2784)
- **M. Laurent**: [Transcendence and continued fraction expansion of values of Hecke--…](#source-source-b9d7160919621f)
- **M. Merca**: [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [The Lambert series factorization theorem](#source-source-8935df46fb4693)
- **M. R. Ballard**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **M. Rothgang**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **M. Stern**: [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81)
- **M. Straka**: [OpenProver: Agentic and Interactive Theorem Proving with Lean 4](#source-source-d31e3bc51f2784)
- **M. Z. Garaev**: [Character sums and congruences with n!](#source-source-34b520c561ee3c)
- **Macleod, R. A.**: [On Equal Products of Consecutive Integers](#source-source-b6d577df139d85)
- **Maksym Radziwiłł**: [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404)
- **Marchwicki, Jacek**: [On Kakeya Conditions for Achievement Sets](#source-source-6d8837bbc174ce)
- **Maria Drencheva**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Mark Harman**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Martin Höst**: [Guidelines for Conducting and Reporting Case Study Research in Soft…](#source-source-25efc27ed2130d)
- **Martin Vechev**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **María Inés de Frutos-Fernández**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Mathias Pétréolle**: [Lattice paths and branched continued fractions: An infinite sequenc…](#source-source-490b1875016ea4)
- **Melinda Yuan**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Michael Coons**: [Transcendence of generating functions whose coefficients are multip…](#source-source-b791f5b49e0da6)
- **Michael Drmota**: [(Logarithmic) densities for automatic sequences along primes and sq…](#source-source-4afc43674f7082)
- **Michael Rothgang**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Milen Shumanov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Miroslav Marinov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Miska, Piotr**: [On Kakeya Conditions for Achievement Sets](#source-source-6d8837bbc174ce), [More on Kakeya Conditions for Achievement Sets](#source-source-b46f8a083b4271)
- **Mislav Balunovic**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Moubariz Z. Garaev**: [Additive congruences with factorials modulo a prime](#source-source-f1a42898642b5f), [Distribution of harmonic sums and Bernoulli polynomials modulo a prime](#source-source-fb64da05c3acc7)
- **Munsch, Marc**: [Distribution of factorials modulo $p$](#source-source-724fef812699b7)
- **Muzammil Shahbaz**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **N. Edeko**: [A dynamical proof of the van der Corput inequality](#source-source-3d300ccd5e4cbb)
- **N. Garg**: [EconCSLib: AI-Assisted Lean Formalization for Economics & Computati…](#source-source-b300504b513ffb)
- **N. Peng**: [The Network Structure of Mathlib](#source-source-81b67bfd835ac9)
- **NISO**: [CRediT: Contributor Roles Taxonomy](#source-source-d517c8a2d6f84d)
- **National Academies of Sciences, Engineering, and Medicine**: [Reproducibility and Replicability in Science](#source-source-011f43e5a781d7)
- **National Aeronautics and Space Administration**: [Software Assurance and Software Safety Standard](#source-source-278e74bfddddf0)
- **National Information Standards Organization.**: [Reproducibility Badging and Definitions](#source-source-f2a047037bae55)
- **National Institute of Standards**: [National Institute of Standards and Technology](#source-source-e6716218a1ac07)
- **National Institute of Standards and Technology**: [Secure Hash Standard](#source-source-f6e839bcb8a60f)
- **Nguyen Xuan Tho**: [On equal products of consecutive integers](#source-source-3068a3586a5e8b)
- **Nigamaa Nayakanti**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Nils Bruin**: [Transcendence of generating functions whose coefficients are multip…](#source-source-b791f5b49e0da6)
- **Nowakowski, Piotr**: [On a new condition implying that an achievement set is a Cantorval…](#source-source-ce27d27dd5ec77)
- **O. C. Z. Gotel**: [An analysis of the requirements traceability problem](#source-source-e1665a6398558f)
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
- **Pietro Monticone**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Plectis working note**: [The logarithmic endpoint fails under arithmetic sampling](#source-source-endpoint2026-logarithmic-repair)
- **Polymath Project**: [General polymath rules](#source-source-af9e99293e9dd0)
- **Prasanna Balaprakash**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Priyamvad Srivastav**: [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891)
- **Prus-Wi\\'sniowski, Franciszek**: [Achievement sets -- current results and open problems](#source-source-77333436a9e579), [Achievable Cantorvals almost without reversed Kakeya conditions](#source-source-779915b8355ac1), [More on Kakeya Conditions for Achievement Sets](#source-source-b46f8a083b4271)
- **Ptak, Jolanta**: [Achievable Cantorvals almost without reversed Kakeya conditions](#source-source-779915b8355ac1), [More on Kakeya Conditions for Achievement Sets](#source-source-b46f8a083b4271)
- **Q. Tang**: [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641)
- **Quanyu Tang**: [Period-two Lambert theorem applied to even and odd supports](#source-erdos257-tang-tachiya-period-two)
- **Quoc V. Le**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **R. A. DeMillo**: [Hints on test data selection](#source-source-c309c1132b63e3)
- **R. Balasubramanian**: [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891)
- **R. C. Baker**: [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001)
- **R. C. Vaughan**: [The Prime Number Theorem](#source-source-06457731c60720), [Multiplicative Number Theory I: Classical Theory](#source-source-0aca0e5e4e03c0)
- **R. Chalamala**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **R. Crandall**: [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da)
- **R. J. Lipton**: [Hints on test data selection](#source-source-c309c1132b63e3)
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
- **RomanLeLan**: [Retrieval of Chowla 1947 original scan](#source-erdos1049-bloom-chowla-scan-retrieval)
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
- **Sebastian Ullrich**: [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3)
- **Selfridge, John L.**: [The product of consecutive integers is never a power](#source-source-7d923cace5602a)
- **Semchankau, Aliaksei**: [On the sequence $n!$ mod $p$](#source-source-02fc1f0e6f0418)
- **Sergei Gukov**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Shengtong Zhang**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **Shin Yoo**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Shparlinski, Igor E.**: [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5)
- **Shuze Chen**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Simon Kurgan**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Sophie Szeto**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Soroosh Yazdani**: [Multiplicative functions and k-automatic sequences](#source-source-a0d109b4492fba)
- **Steve Fan**: [Möbius-transform identity for the binary totient constant](#source-erdos249-fan-mobius-transform), [Infinite-prime-set irrationality proof and correction chain](#source-erdos269-fan-infinite-p-proof-repair), [Two-prime Hecke–Mahler factorisation and transcendence disclosure](#source-erdos269-fan-two-prime-disclosure), [Strongly complete sets and a conjecture of Erdős](#source-source-71fb76f6e1363b)
- **Stevens, Sophie**: [An improved point-line incidence bound over arbitrary fields](#source-source-29cbac966b8b76)
- **Stichtenoth, Henning**: [On the Value Set of $n!$ Modulo a Prime](#source-source-b3decc410aa4b5)
- **Sumit Giri**: [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891)
- **Sunny Hu**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Szabolcs Marka**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Szymonik, Emilia**: [Multigeometric sequences and Cantorvals](#source-source-2b0038d2c239f5)
- **Sébastien Gouëzel**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **T. Amdeberhan**: [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b)
- **T. M. Apostol**: [Introduction to Analytic Number Theory](#source-source-99385343e032a3)
- **T. Matala-aho**: [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f)
- **T. Mizoguchi**: [Toward Auditable AI Scientists: A Hypothesis Evolution Protocol for…](#source-source-4c664304e00cd3)
- **T. Tao**: [The maximal length of the Erdős–Herzog–Piranian lemniscate in high…](#source-source-0e12f93aeac487), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Mathematics in the age of AI](#source-source-75e79d15dfab15), [Long gaps between primes](#source-source-d3995db1508bc9)
- **T. Ward**: [Integer sequences and periodic points](#source-source-5cac1ad51acb12)
- **T. Zhu**: [LeanArchitect: Automating Blueprint Generation for Humans and AI](#source-source-80c9ae60b7f7be)
- **Takeshi Kurosawa**: [Irrationality exponents of certain fast converging series of ration…](#source-source-0f03e2dab0b8c2)
- **Technology**: [National Institute of Standards and Technology](#source-source-e6716218a1ac07)
- **Terence Tao**: [Rational-tail deterministic pair recurrence and open-boundary reduc…](#source-erdos243-tao-tail-pair-recurrence), [Prime-gap summation-by-parts equivalence and conditional route](#source-erdos251-tao-prime-gap-equivalence), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [Erdős Problems discussion thread #251](#source-source-21738452dcb95c), [AI contributions to Erdős problems](#source-source-e99ce64694b554)
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
- **Unknown**: [NIST Digital Library of Mathematical Functions, §1.12(ii) Convergents](#source-source-f213b302ada43a)
- **V. Kovač**: [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3)
- **V. Kuperberg**: [Sums of singular series with large sets and the tail of the distrib…](#source-source-811205223e0788)
- **V. N. Dubinin**: [Lemniscates and inequalities for the logarithmic capacities of cont…](#source-source-2a86f52125aec0), [Some inequalities for polynomials and rational functions associated…](#source-source-dcbe400c96be59)
- **V. S. Pendyala**: [Shortest paths in polynomial lemniscate sublevel sets and a problem…](#source-source-8710374c3e8c9f), [A Degree-Four Lemniscate Path Theorem](#source-source-951f70d8dfc418)
- **Vasilevskii, Aliaksei**: [On the sequence $n!$ mod $p$](#source-source-02fc1f0e6f0418)
- **Vasily Ilin**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Venkata Pendyala**: [Quartic case of Erdős #1041](#source-erdos1041-pendyala-quartic)
- **Vjekoslav Kovač**: [Koizumi pseudo-greedy equivalence and computation pointer](#source-erdos243-kovac-koizumi-pointer), [Counterexample to Erdős variable-denominator expectation](#source-erdos251-kovac-variable-denominator-counterexample), [Earlier variants, interval-filling negative variant, and fat-Cantor…](#source-erdos257-kovac-context-bundle), [Older Erdős and Borwein attribution for even/odd supports](#source-erdos257-kovac-older-special-case-attribution), [On the irrationality of certain super-polynomially decaying series](#source-source-41df26fdff66cb), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **Vladimir G. Tkachev**: [Length functions of lemniscates](#source-source-57fe330e419648)
- **Vladimir N. Dubinin**: [Inequalities for critical values of polynomials](#source-source-b10b965e63a00d), [Four-point distortion theorem for complex polynomials](#source-source-f0af8e6f36727f)
- **W. Hayman**: [On the length of lemniscates](#source-source-7f1f2a3fd9238c)
- **W. Koepf**: [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0)
- **W. Li**: [Irrationality Criteria for Series by Erdős and Straus](#source-source-c6e97d89c9fa5f)
- **W. R. Alford**: [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31)
- **W. Schramm**: [The Fourier transform of functions of the greatest common divisor](#source-source-c786f202d47318)
- **W. Van Assche**: [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94)
- **W. Zudilin**: [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [On the non-quadraticity of values of the q-exponential function and…](#source-source-22ef36d016ca81), [On the irrationality of generalized q-logarithm](#source-source-ae9859af28fdcd), [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f), [Remarks on irrationality of q-harmonic series](#source-source-f1c687cb5e9ae4), [A determinantal approach to irrationality](#source-source-f67bf9959aa230), [Rational approximations to a q-analogue of π and some other q-series](#source-source-f9fd9214c9ef11)
- **W. van Doorn**: [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3)
- **Wadim Zudilin**: [Diophantine Problems for q-Zeta Values](#source-proposed-direct-0ef4f73f93ceed)
- **Wei-Yuan Li**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Wenjie Ma**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Will Cook (coverage audit author)**: [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary)
- **Woong Shin**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **X. Li**: [The Network Structure of Mathlib](#source-source-81b67bfd835ac9)
- **Xiaomeng Yang**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Xiaoyang Lu**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Xiyu Hu**: [Factorial residues modulo a prime: beyond the square-root bound](#source-source-365c2b5cf46ebe)
- **Xujie Si**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Y. Bugeaud**: [On the complexity of algebraic numbers I. Expansions in integer bases](#source-source-7c8ba4ea6eea79), [Transcendence and continued fraction expansion of values of Hecke--…](#source-source-b9d7160919621f)
- **Y. Jia**: [An analysis and survey of the development of mutation testing](#source-source-3a21eca35f05cf)
- **Y. Li**: [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641)
- **Y. Puri**: [Integer sequences and periodic points](#source-source-5cac1ad51acb12)
- **Y. Tachiya**: [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44)
- **Y. Zhang**: [Bounded gaps between primes](#source-source-c32d672658410d)
- **YaGuang Li**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yann Bugeaud**: [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c)
- **Yi Tay**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yi Wang**: [Log-convex and Stieltjes moment sequences](#source-source-e535117ac620e6)
- **Yohei Tachiya**: [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9), [Irrationality of Lambert series associated with a periodic sequence](#source-source-9ce84321e202f1), [Linear independence of certain Lambert series](#source-source-f6ee6890db85d9)
- **Youngbeom Jin**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Youyuan Zhang**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Yu-Chen Sun**: [The critical-window profile for d\_k in short intervals](#source-proposed-direct-6f90767d1d01dd)
- **Yu-Sheng Shih**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Yu. V. Nesterenko**: [Modular functions and transcendence questions](#source-source-6346eeeac5036d)
- **Yuan Liu**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yuri Chervonyi**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yuta Suzuki**: [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9)
- **Yutong Wang**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Z. Nitecki**: [Subsum sets: intervals, Cantor sets, and Cantorvals](#source-source-63a234b13e4427)
- **Zaiwen Wen**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **Zeming Sun**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Zeraoulia Rafik**: [Irrationality of the n=2^m sparse totient subseries](#source-erdos249-rafik-sparse-power-two-subseries)
- **Zhaoyu Li**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Zichen Lai**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **Zijun Yao**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Zsuzsa Marka**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
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

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:1169](../../paper/systems/open-source-mathematics-strategy.tex#L1169-L1169)
- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:1000](../../docs/papers/mirror/plectis-public-system.tex#L1000-L1000)

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

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:483](../../paper/systems/cold-clone-to-proof-receipt.tex#L483-L483)

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

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:367](../../paper/systems/cold-clone-to-proof-receipt.tex#L367-L367)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1809-L1815) — lines `1809–1815`; excerpt `sha256:bfae70e92b17ff0eb46d5a89787ab01a60a09ee1c2fa3385ddf8b2ff8854f038`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4691-L4697) — lines `4691–4697`; excerpt `sha256:26d60d27d7d495f7259334fef196a51735ac5030652cb8728846fed7b1146393`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4649-L4655) — lines `4649–4655`; excerpt `sha256:26d60d27d7d495f7259334fef196a51735ac5030652cb8728846fed7b1146393`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1061](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1061-L1061)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3724](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3724-L3724), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3727](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3727-L3727), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3794](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3794-L3794), [cite at paper/reasoning-parts/erdos1041/core.tex:3682](../../paper/reasoning-parts/erdos1041/core.tex#L3682-L3682), [cite at paper/reasoning-parts/erdos1041/core.tex:3685](../../paper/reasoning-parts/erdos1041/core.tex#L3685-L3685), [cite at paper/reasoning-parts/erdos1041/core.tex:3752](../../paper/reasoning-parts/erdos1041/core.tex#L3752-L3752)

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

- [formalization.yaml](../../formalization.yaml#L1-L60) — lines `1–60`; excerpt `sha256:aa13f45cec4aebd5960b2dae8794a0642d9a2045491f8f5bbfca50237c116785`
- [verification/comparator.json](../../verification/comparator.json#L1-L38) — lines `1–38`; excerpt `sha256:59da13809c33a93943095066b40909da907617aa28592c6201635ba1b55d5e81`
- [verification/comparator-negative-mismatch.json](../../verification/comparator-negative-mismatch.json#L1-L13) — lines `1–13`; excerpt `sha256:43aca5f4da7f5f42baf826e53324c045e4fa11acd20ffd1743609e20b5084157`
- [docs/EXTERNAL\_VERIFICATION.md](../../docs/EXTERNAL_VERIFICATION.md#L4-L14) — lines `4–14`; excerpt `sha256:b56beae8041d4268c9de0997498bfbf2653c61cb6ec86eb372d9447ed1018ab9`

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L17-L17) — lines `17–17`; excerpt `sha256:37939b0c59ae11c8e4bb844bd7553dbed82895e4d9fc5c757c897c1aa28f8854`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L61-L61) — lines `61–61`; excerpt `sha256:b6ce0fb599e9bf02898ae89ea89e3bf47a7a31efcaab7ffbe2a9e2aaaae8ab8c`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L60-L60) — lines `60–60`; excerpt `sha256:c8b8a219e2d05b9d599b8a34430f56e76d7a92ecc1a80f73411c4e6c05a43b18`
- [lean/Erdos249257/TotientMahlerDefect.lean](../../lean/Erdos249257/TotientMahlerDefect.lean#L935-L1145) — lines `935–1145`; excerpt `sha256:e4bbeef9407526e58653fc7ed307d51530c41af7bd6d225f36388486dc845a6e`
- [formalization.yaml](../../formalization.yaml#L159-L216) — lines `159–216`; excerpt `sha256:b323e9a098414f61b29469d542453a446713a6650efbe384accb4d657f9a1e7e`
- [docs/EXTERNAL\_VERIFICATION.md](../../docs/EXTERNAL_VERIFICATION.md#L522-L532) — lines `522–532`; excerpt `sha256:cb49ade0a57a20d0355d24a8ebc443b2be0b82e0f3c2bdd61f361abe2913a17b`

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
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L854-L854) — lines `854–854`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L369-L373) — lines `369–373`; excerpt `sha256:c9f8d191bbf7d39a3e75436d9d7036604d3f396d1223d6f8d505668cafc4971e`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L1-L100) — lines `1–100`; excerpt `sha256:2869c3db2da5857a4c9fc56be272d52f5a7b1242f3633bd8ed0b01f0da016724`

<a id="source-erdos1041-ani-degree-seven-candidate-counterexample"></a>

### [Degree-seven total-variation counterexample for polynomial lemniscates](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-8861)

- Source id: `erdos1041\_ani\_degree\_seven\_candidate\_counterexample`
- Author or public identity: ani (forum handle)
- Kind: `website\_contribution`
- Problems: #1041
- Relationship and boundary: Ani publicly posted the explicit degree-seven construction and linked manuscript. This repository credits that construction to ani and formalises one explicit instance in Lean: all seven roots lie in the open unit disc and every continuous root-to-root path inside the strict unit lemniscate has total variation greater than two. The checked theorem refutes the universal total-variation formulation. It does not formalise the manuscript's full small-parameter family or adjudicate correspondence with the historical curve-length question.
- Source verification: `source\_verified` — The public source identity, ani attribution and correspondence to the linked local Lean declarations are verified. Lean's kernel checks the local explicit-instance and universal-negation theorems. This does not independently validate the manuscript's full family, establish novelty or priority, or settle the historical curve-length correspondence.
- Local mapping: `exact\_authored\_attribution` — The public forum post owns finder credit; the linked local Lean declarations own the repository's checked total-variation refutation.

Exact source locations:

- [Comment posted 7 Sep 2026 by ani; exact HTML element permalink #post-8861](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-8861)
- [Public Overleaf project title \`1041counterexample\`; main.tex viewed 2026-09-12; no \\author command between title/date and document body](https://www.overleaf.com/read/ctmqrqwthkcn#bf8155)
- [Theorem 1.1 and equations (1.1)–(1.2): one-parameter monic degree-7 family; all seven simple zeros have modulus rho=1-s^16\<1; every joining path has length \>2+(alpha/2)s^2](https://www.overleaf.com/read/ctmqrqwthkcn#bf8155)

Public implementation or evidence coordinates:

- [lean/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean](../../lean/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean#L3-L13) — lines `3–13`; excerpt `sha256:0dc7be32db4ccb96eb5a7cc2b22e956f6422aea7ec5706b6217b0a15925b86eb`
- [lean/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean](../../lean/ErdosProblems/Erdos1041/Counterexample/CatalogueAdapter.lean#L23-L40) — lines `23–40`; excerpt `sha256:de7c9f67adba5db7a57c763684b751678c107891d725c6a4a3296b34acb2b7c2`

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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L76-L80) — lines `76–80`; excerpt `sha256:c2864518e4865dd44a4a7f0e412686c80f1580a48114e8077d016e2b7ddcb64b`
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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L262-L266) — lines `262–266`; excerpt `sha256:eaf3b2d51c02f396311adf2ef91d0f021cca117e79f8f4b020ac851aa8ba0289`
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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L270-L274) — lines `270–274`; excerpt `sha256:0f62f937441a579688654793f759c8d3a907ac15bb22aa83897d45df1462216a`
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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L277-L277) — lines `277–277`; excerpt `sha256:564fef3b1c83b587c34b3db58f1f89d199d9b9f7fccafdea2fbbe0766f05f34a`
- [lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean](../../lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L138-L172) — lines `138–172`; excerpt `sha256:df88134179386f6161b138662a0cf1e7faf8a0ff67d5a839a7ac4608d03ad1c2`
- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L392-L423) — lines `392–423`; excerpt `sha256:912d421ce3a607706d9b45fcb033ab97d4d81f834be36a029c3407aca9e05ae8`

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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L146-L150) — lines `146–150`; excerpt `sha256:badb6c16b351f142047e83c1c8631e63319c82edabf1973f16a616deead6f4d6`
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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L314-L330) — lines `314–330`; excerpt `sha256:f4d1278504a386c4d49236ab4efd039ef5ddd233f5bae878c29728b527bd5417`

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
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1163-L1167) — lines `1163–1167`; excerpt `sha256:b901a58ca5f4fa10b5877f77546cf4c15ae0e086b4ea3be59376b1a5cbe7b336`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2848-L2852) — lines `2848–2852`; excerpt `sha256:fd3671803715497848f50b7e406b351a3c0b3100358db5c0e7912563aefc2384`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1181-L1184) — lines `1181–1184`; excerpt `sha256:51cf1a9022003db39cbb367941bf95bd307e11c77addb1858093fbf1d5875d99`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4030-L4033) — lines `4030–4033`; excerpt `sha256:b01d4201961354aa2fcf031776776c91eb7db17740171a6695c31c1427a4a4a2`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L797-L799) — lines `797–799`; excerpt `sha256:835dc22e46b6d6929b2d85594412500fac03a0e9cf711221604213fe4335f356`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3011-L3013) — lines `3011–3013`; excerpt `sha256:835dc22e46b6d6929b2d85594412500fac03a0e9cf711221604213fe4335f356`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2961-L2964) — lines `2961–2964`; excerpt `sha256:31915c67293505124e4e64b2dab2c9812e8c2ca3dee769b5b34383d617c64b51`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L805-L808) — lines `805–808`; excerpt `sha256:29dac9d4258d940e744c9f183d2563013f54887e62491308cf386e555621ff55`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1750-L1752) — lines `1750–1752`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4601-L4603) — lines `4601–4603`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1325-L1330) — lines `1325–1330`; excerpt `sha256:ca4961b07db9ad87fb029632eea765fe437a48a66378723f1fc3195a99aa0f8b`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4538-L4543) — lines `4538–4543`; excerpt `sha256:ca4961b07db9ad87fb029632eea765fe437a48a66378723f1fc3195a99aa0f8b`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1577-L1582) — lines `1577–1582`; excerpt `sha256:bb8050123710e542e010c55df517209f1e56e938a1655ebb63df13ec2e2c8c44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4559-L4561) — lines `4559–4561`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L84-L84) — lines `84–84`; excerpt `sha256:bf59465f69868d365972af0f59f5d9fd80c35bc621145e7b6df25267c41820ec`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4513-L4518) — lines `4513–4518`; excerpt `sha256:ca4961b07db9ad87fb029632eea765fe437a48a66378723f1fc3195a99aa0f8b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:960ed480813e248da8738aef7c8742c60974d9b5a146370ce1d2d63fda38f21a`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:960ed480813e248da8738aef7c8742c60974d9b5a146370ce1d2d63fda38f21a`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3998-L4001) — lines `3998–4001`; excerpt `sha256:b01d4201961354aa2fcf031776776c91eb7db17740171a6695c31c1427a4a4a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L45-L45) — lines `45–45`; excerpt `sha256:291771799f1e1c8a9a0b43391570fd9b02e3836c3944d9938c7a8118de5e6afb`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L43-L43) — lines `43–43`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L45-L45) — lines `45–45`; excerpt `sha256:291771799f1e1c8a9a0b43391570fd9b02e3836c3944d9938c7a8118de5e6afb`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2971-L2973) — lines `2971–2973`; excerpt `sha256:835dc22e46b6d6929b2d85594412500fac03a0e9cf711221604213fe4335f356`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L49-L49) — lines `49–49`; excerpt `sha256:df504a3275aa10412a2ec020ef3edd1f2a4cf2003dc39d3fe07e9a34ec158ce6`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L49-L49) — lines `49–49`; excerpt `sha256:df504a3275aa10412a2ec020ef3edd1f2a4cf2003dc39d3fe07e9a34ec158ce6`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L49-L49) — lines `49–49`; excerpt `sha256:df504a3275aa10412a2ec020ef3edd1f2a4cf2003dc39d3fe07e9a34ec158ce6`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2916-L2919) — lines `2916–2919`; excerpt `sha256:31915c67293505124e4e64b2dab2c9812e8c2ca3dee769b5b34383d617c64b51`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:44fd9c14c25e5775404be7ccea03d3057255373bee9505c5739d20d124ad3866`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:44fd9c14c25e5775404be7ccea03d3057255373bee9505c5739d20d124ad3866`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:44fd9c14c25e5775404be7ccea03d3057255373bee9505c5739d20d124ad3866`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2814-L2818) — lines `2814–2818`; excerpt `sha256:fd3671803715497848f50b7e406b351a3c0b3100358db5c0e7912563aefc2384`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L63-L63) — lines `63–63`; excerpt `sha256:90bc75ae3dd71b563564da4ea76ddc7b5ebe6e5e3ec19448222b9bd4e799a484`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4538-L4543) — lines `4538–4543`; excerpt `sha256:ca4961b07db9ad87fb029632eea765fe437a48a66378723f1fc3195a99aa0f8b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4513-L4518) — lines `4513–4518`; excerpt `sha256:ca4961b07db9ad87fb029632eea765fe437a48a66378723f1fc3195a99aa0f8b`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:138](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L138-L138)
- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1151](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1151-L1151)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:145](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L145-L145)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:655](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L655-L655)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:636](../../paper/269/erdos-269-three-prime-running-lcm.tex#L636-L636)
- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:131](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L131-L131)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:126](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L126-L126), [cite at paper/reasoning-parts/erdos1041/core.tex:84](../../paper/reasoning-parts/erdos1041/core.tex#L84-L84)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:79](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L79-L79), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4306](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4306-L4306), [cite at paper/reasoning-parts/erdos1049/core.tex:54](../../paper/reasoning-parts/erdos1049/core.tex#L54-L54), [cite at paper/reasoning-parts/erdos1049/core.tex:4281](../../paper/reasoning-parts/erdos1049/core.tex#L4281-L4281)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:77](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L77-L77), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:766](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L766-L766), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3735](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3735-L3735), [cite at paper/reasoning-parts/erdos243/core.tex:45](../../paper/reasoning-parts/erdos243/core.tex#L45-L45), [cite at paper/reasoning-parts/erdos243/core.tex:734](../../paper/reasoning-parts/erdos243/core.tex#L734-L734), [cite at paper/reasoning-parts/erdos243/core.tex:3703](../../paper/reasoning-parts/erdos243/core.tex#L3703-L3703)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:197](../../paper/archive/erdos249-257-main-paper.tex#L197-L197), [cite at paper/archive/erdos249-257-main-paper.tex:4524](../../paper/archive/erdos249-257-main-paper.tex#L4524-L4524)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:89](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L89-L89), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2109](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2109-L2109), [cite at paper/reasoning-parts/erdos251/core.tex:49](../../paper/reasoning-parts/erdos251/core.tex#L49-L49), [cite at paper/reasoning-parts/erdos251/core.tex:2069](../../paper/reasoning-parts/erdos251/core.tex#L2069-L2069)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:74](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L74-L74), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2481](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2481-L2481), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2498](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2498-L2498), [cite at paper/reasoning-parts/erdos269/core.tex:29](../../paper/reasoning-parts/erdos269/core.tex#L29-L29), [cite at paper/reasoning-parts/erdos269/core.tex:2436](../../paper/reasoning-parts/erdos269/core.tex#L2436-L2436), [cite at paper/reasoning-parts/erdos269/core.tex:2453](../../paper/reasoning-parts/erdos269/core.tex#L2453-L2453)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:97](../../paper/68/erdos68-factorial-reasoning-surface.tex#L97-L97), [cite at paper/reasoning-parts/erdos68/core.tex:63](../../paper/reasoning-parts/erdos68/core.tex#L63-L63)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:516](../../paper/systems/open-source-mathematics-strategy.tex#L516-L516), [cite at paper/systems/open-source-mathematics-strategy.tex:714](../../paper/systems/open-source-mathematics-strategy.tex#L714-L714)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1803-L1809) — lines `1803–1809`; excerpt `sha256:9b66ac2741824a4fb126ce6c85cdddc7806daa4534b4f393e06ebf1a210dbd9c`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4685-L4691) — lines `4685–4691`; excerpt `sha256:23a731c181be1a3d3f4f814b84774f68a8a5b6bcebb7b8717ac21e9917899da5`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4643-L4649) — lines `4643–4649`; excerpt `sha256:23a731c181be1a3d3f4f814b84774f68a8a5b6bcebb7b8717ac21e9917899da5`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1229](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1229-L1229)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1873](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1873-L1873), [cite at paper/reasoning-parts/erdos1041/core.tex:1831](../../paper/reasoning-parts/erdos1041/core.tex#L1831-L1831)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1798-L1803) — lines `1798–1803`; excerpt `sha256:a3161ac11344fd8199bdbbb63800da9443a64e2a1d3fdd2007366848b954d26f`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4680-L4685) — lines `4680–4685`; excerpt `sha256:2ca5100ac1e4e768257b05ac88a40e2a04ae625930bbba2c8e7c147703d176a6`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4638-L4643) — lines `4638–4643`; excerpt `sha256:2ca5100ac1e4e768257b05ac88a40e2a04ae625930bbba2c8e7c147703d176a6`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1228](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1228-L1228)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1871](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1871-L1871), [cite at paper/reasoning-parts/erdos1041/core.tex:1829](../../paper/reasoning-parts/erdos1041/core.tex#L1829-L1829)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1794-L1798) — lines `1794–1798`; excerpt `sha256:97ed6ed938a762a7aa078c24d5e27afbbef833b6e4baddc2c4ebde5eff3f4607`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4676-L4680) — lines `4676–4680`; excerpt `sha256:42b99f9986d17fa7c89618f299bdc5940ef3f67b0a8129937e2dcd5521a15379`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4634-L4638) — lines `4634–4638`; excerpt `sha256:42b99f9986d17fa7c89618f299bdc5940ef3f67b0a8129937e2dcd5521a15379`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1220](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1220-L1220), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1222](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1222-L1222)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1856](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1856-L1856), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1864](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1864-L1864), [cite at paper/reasoning-parts/erdos1041/core.tex:1814](../../paper/reasoning-parts/erdos1041/core.tex#L1814-L1814), [cite at paper/reasoning-parts/erdos1041/core.tex:1822](../../paper/reasoning-parts/erdos1041/core.tex#L1822-L1822)

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

- [research/adapters/FormalConjecturesAdapter.lean](../../research/adapters/FormalConjecturesAdapter.lean#L94-L107) — lines `94–107`; excerpt `sha256:6103702256378b99f284f4867d0c51dd9dd0c5c5e808b1d22f64210a0dbd2253`

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

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L272-L290) — lines `272–290`; excerpt `sha256:12a5b1f7563cefb7d10a26be861ae84e01bcba9b150a9655b9c3e2aabd93108b`

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

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L364-L428) — lines `364–428`; excerpt `sha256:4db989ccba90a32a255fe9bd93b65967fa391e1cf1c9974d07cfa64d5d0e92c8`

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

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L344-L362) — lines `344–362`; excerpt `sha256:7ff63cde13f349a5f42b41b5bbc6f9160c468a7a7ae2a92d8cd54b5d8afc85d6`

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

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L473-L506) — lines `473–506`; excerpt `sha256:5bd0c8f1316751bbcc0c8dd95f60449cc49b395f5984c254b1db288a24fda020`

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

- [research/adapters/FormalConjecturesAdapter.lean](../../research/adapters/FormalConjecturesAdapter.lean#L9-L41) — lines `9–41`; excerpt `sha256:a09ac08e4260951af6627cc74ccc029207e6497eb1840a65bda22888010525ed`
- [lakefile.toml](../../lakefile.toml#L56-L68) — lines `56–68`; excerpt `sha256:831b7c7270f57c8606e4effd1314f87cfd4b9ad0eee57b89a546b5457b16aa78`

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

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L794-L794) — lines `794–794`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1105-L1105) — lines `1105–1105`; excerpt `sha256:603c399e18eec54e4b76bcb455d51b93adf56ce7a26e699ca50aa8527aaa25fa`

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

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1038-L1038) — lines `1038–1038`; excerpt `sha256:bd3042b8bb213124b09edd0ae290bc793d67b690b4f3eaa43e75f1389ed209f9`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L136-L136) — lines `136–136`; excerpt `sha256:fa9c5470b10974096a81d5f934190f18c1303bfbab8ccee75a7290efabe75eab`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1396-L1400) — lines `1396–1400`; excerpt `sha256:1d98da1cc9acba9dff63b689605b7402eee23c5f2cea8e887c7c18989b40d0d1`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L503-L503) — lines `503–503`; excerpt `sha256:1ed1ce69c8bf73f3362ff5a2aca04fe7d02e4cc4dbe0784bc0f09ca0a22ad778`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9723-L9732) — lines `9723–9732`; excerpt `sha256:29419ac25750a3ca44cb2c1c49ac4bd44f6206b9eff9cc840572a0d12a962f43`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9539-L9548) — lines `9539–9548`; excerpt `sha256:29419ac25750a3ca44cb2c1c49ac4bd44f6206b9eff9cc840572a0d12a962f43`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:350](../../paper/257/erdos-257-mersenne-support-subseries.tex#L350-L350)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:687](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L687-L687), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:503](../../paper/reasoning-parts/erdos257/a257_front.tex#L503-L503)

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

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7954-L7954) — lines `7954–7954`; excerpt `sha256:bad452dab3a80d026ba2b9d6aca2caf78d90b3a49add7f6d1955eef4c220342f`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9463-L9469) — lines `9463–9469`; excerpt `sha256:f37eea22c3c2e50c9106c29e8480d8c2ab20d0f3f59a7faec27317f14c9ea473`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9293-L9299) — lines `9293–9299`; excerpt `sha256:f37eea22c3c2e50c9106c29e8480d8c2ab20d0f3f59a7faec27317f14c9ea473`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9469-L9475) — lines `9469–9475`; excerpt `sha256:e35aaa04403be003a4b96499d83a53616643be3a1bc6ec591562551be6db9bf5`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9299-L9305) — lines `9299–9305`; excerpt `sha256:e35aaa04403be003a4b96499d83a53616643be3a1bc6ec591562551be6db9bf5`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9475-L9482) — lines `9475–9482`; excerpt `sha256:4ca7b4c0db1de3a40807dc6214421cb78ee688d52511a96a2204550ee24c19a4`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9305-L9312) — lines `9305–9312`; excerpt `sha256:4ca7b4c0db1de3a40807dc6214421cb78ee688d52511a96a2204550ee24c19a4`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9770-L9775) — lines `9770–9775`; excerpt `sha256:0b4989fd169ff765ea3d5b38ef8e6aea0f4cd59a60283d86861edd55ca023917`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9586-L9591) — lines `9586–9591`; excerpt `sha256:0b4989fd169ff765ea3d5b38ef8e6aea0f4cd59a60283d86861edd55ca023917`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8124](../../paper/249/erdos249-totient-reasoning-surface.tex#L8124-L8124), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8127](../../paper/249/erdos249-totient-reasoning-surface.tex#L8127-L8127), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8129](../../paper/249/erdos249-totient-reasoning-surface.tex#L8129-L8129), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7954](../../paper/reasoning-parts/erdos249/a249_front.tex#L7954-L7954), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7957](../../paper/reasoning-parts/erdos249/a249_front.tex#L7957-L7957), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7959](../../paper/reasoning-parts/erdos249/a249_front.tex#L7959-L7959)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:8218](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L8218-L8218), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:8034](../../paper/reasoning-parts/erdos257/a257_front.tex#L8034-L8034)

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

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L82-L82) — lines `82–82`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1095-L1101) — lines `1095–1101`; excerpt `sha256:a8cf6f2cdc8cb0b26a0a37cb8141e5828d7e67bf0a8de5e636412840e1a2f1b7`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9437-L9443) — lines `9437–9443`; excerpt `sha256:1e409fb0093faa23ebcc4e5651da0b5eac48a708ad25c90724afa7a140769712`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9267-L9273) — lines `9267–9273`; excerpt `sha256:1e409fb0093faa23ebcc4e5651da0b5eac48a708ad25c90724afa7a140769712`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:737](../../paper/249/erdos-249-binary-totient-series.tex#L737-L737), [cite at paper/249/erdos-249-binary-totient-series.tex:739](../../paper/249/erdos-249-binary-totient-series.tex#L739-L739)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9301](../../paper/249/erdos249-totient-reasoning-surface.tex#L9301-L9301), [cite at paper/249/erdos249-totient-reasoning-surface.tex:9303](../../paper/249/erdos249-totient-reasoning-surface.tex#L9303-L9303), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9131](../../paper/reasoning-parts/erdos249/a249_front.tex#L9131-L9131), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9133](../../paper/reasoning-parts/erdos249/a249_front.tex#L9133-L9133)

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

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8034-L8034) — lines `8034–8034`; excerpt `sha256:d50e57ea55fd331cc5fcd2f60b7cbbe4f74bdfad5ed5d507e3e2607f34a7aae6`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9775-L9779) — lines `9775–9779`; excerpt `sha256:c5c4489e4688d8773d399bf748456a2ae9b05460c54f6faafd532fa836da5957`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9591-L9595) — lines `9591–9595`; excerpt `sha256:c5c4489e4688d8773d399bf748456a2ae9b05460c54f6faafd532fa836da5957`

Paper citation usages:

- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:8220](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L8220-L8220), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:8036](../../paper/reasoning-parts/erdos257/a257_front.tex#L8036-L8036)

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

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8034-L8034) — lines `8034–8034`; excerpt `sha256:d50e57ea55fd331cc5fcd2f60b7cbbe4f74bdfad5ed5d507e3e2607f34a7aae6`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9779-L9783) — lines `9779–9783`; excerpt `sha256:6d0851d07c69f2ae700a812b4b5fc31762d09234debac02cca0ca4ff63212261`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9595-L9599) — lines `9595–9599`; excerpt `sha256:6d0851d07c69f2ae700a812b4b5fc31762d09234debac02cca0ca4ff63212261`

Paper citation usages:

- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:8222](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L8222-L8222), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:8038](../../paper/reasoning-parts/erdos257/a257_front.tex#L8038-L8038)

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

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L7712-L7712) — lines `7712–7712`; excerpt `sha256:df8b5a08361a8b2709dbfbc190e9e72f41b2ef5c5874a6274b6c15c70054b621`

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

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L8135-L8135) — lines `8135–8135`; excerpt `sha256:be78c26f277d33338d36a1396ef173f2016a8d8cd7654b87697206f4f4ceb081`

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1323-L1329) — lines `1323–1329`; excerpt `sha256:f06c40636e471872b987aaee6322971311baed24c1120af1f18cddd808e50e98`

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2948-L2952) — lines `2948–2952`; excerpt `sha256:bddcb7495409ba674f37573e14998a223896847e01c9d7d112a430f0cca41d03`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2914-L2918) — lines `2914–2918`; excerpt `sha256:bddcb7495409ba674f37573e14998a223896847e01c9d7d112a430f0cca41d03`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1634](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1634-L1634), [cite at paper/reasoning-parts/erdos68/core.tex:1600](../../paper/reasoning-parts/erdos68/core.tex#L1600-L1600)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2936-L2940) — lines `2936–2940`; excerpt `sha256:a14aa06f222d10c851dd2bfa10beea5352390803145dcffcbdd0759d84e41498`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2902-L2906) — lines `2902–2906`; excerpt `sha256:a14aa06f222d10c851dd2bfa10beea5352390803145dcffcbdd0759d84e41498`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1644](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1644-L1644), [cite at paper/reasoning-parts/erdos68/core.tex:1610](../../paper/reasoning-parts/erdos68/core.tex#L1610-L1610)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2973-L2976) — lines `2973–2976`; excerpt `sha256:0db3df8cac9eaa008e4ba1fc69bf370097ffa91fb0e512033da28a1cab6e2dbc`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2928-L2931) — lines `2928–2931`; excerpt `sha256:0db3df8cac9eaa008e4ba1fc69bf370097ffa91fb0e512033da28a1cab6e2dbc`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L145-L145) — lines `145–145`; excerpt `sha256:1c00ff08c0bb546e88524087a8ce119b5c6657047f90ea161ba3a81fc71d61e6`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:190](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L190-L190), [cite at paper/reasoning-parts/erdos269/core.tex:145](../../paper/reasoning-parts/erdos269/core.tex#L145-L145)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L691-L696) — lines `691–696`; excerpt `sha256:361c5b2fa1f2778906e262b1d0e58a126d4e7d28ea4d10e58c4b3607ef4706e2`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:493](../../paper/systems/cold-clone-to-proof-receipt.tex#L493-L493)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4477-L4486) — lines `4477–4486`; excerpt `sha256:559ea13819baf75b04cc9d7303f6c7c0c031c962cc19c07bc95ad20eac0a8832`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4452-L4461) — lines `4452–4461`; excerpt `sha256:559ea13819baf75b04cc9d7303f6c7c0c031c962cc19c07bc95ad20eac0a8832`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L3957-L3957) — lines `3957–3957`; excerpt `sha256:255e468ab972fcdcc21a815a58d107099746c2882b841d319f2239751a44e4fe`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3982](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3982-L3982), [cite at paper/reasoning-parts/erdos1049/core.tex:3957](../../paper/reasoning-parts/erdos1049/core.tex#L3957-L3957)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L791-L793) — lines `791–793`; excerpt `sha256:3d71bbddc99148fa6f400d6073bc710036ddebbb185cbdacfb3337763934d3fc`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2614-L2614) — lines `2614–2614`; excerpt `sha256:19cfb014840fa377aa38df9849019ad015dd70327f7bf8e708af471ac52e8466`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2574-L2574) — lines `2574–2574`; excerpt `sha256:19cfb014840fa377aa38df9849019ad015dd70327f7bf8e708af471ac52e8466`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3001-L3003) — lines `3001–3003`; excerpt `sha256:b7e63e9f291863fbd6b9fd3c4dc4951de337b3fe54505a8871c92d96d21d90a9`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2961-L2963) — lines `2961–2963`; excerpt `sha256:b7e63e9f291863fbd6b9fd3c4dc4951de337b3fe54505a8871c92d96d21d90a9`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:294](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L294-L294)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:779](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L779-L779), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1493](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1493-L1493), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1553](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1553-L1553), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2614](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2614-L2614), [cite at paper/reasoning-parts/erdos251/core.tex:739](../../paper/reasoning-parts/erdos251/core.tex#L739-L739), [cite at paper/reasoning-parts/erdos251/core.tex:1453](../../paper/reasoning-parts/erdos251/core.tex#L1453-L1453), [cite at paper/reasoning-parts/erdos251/core.tex:1513](../../paper/reasoning-parts/erdos251/core.tex#L1513-L1513), [cite at paper/reasoning-parts/erdos251/core.tex:2574](../../paper/reasoning-parts/erdos251/core.tex#L2574-L2574)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1576-L1579) — lines `1576–1579`; excerpt `sha256:55fac0c52a656a727b0b1d2a37c977ee88cc196b466008fa9cddb3198fd500fe`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1623-L1628) — lines `1623–1628`; excerpt `sha256:6ab1870a7b04b9f3cc30d59640dcc05a0b6fcd49f9ea44245ecb129aba0f4c4e`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:979](../../paper/systems/claim-faithful-publication-systems-paper.tex#L979-L979), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1312](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1312-L1312)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:704](../../paper/systems/open-source-mathematics-strategy.tex#L704-L704), [cite at paper/systems/open-source-mathematics-strategy.tex:941](../../paper/systems/open-source-mathematics-strategy.tex#L941-L941)

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
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L794-L794) — lines `794–794`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4672-L4676) — lines `4672–4676`; excerpt `sha256:7968722d9338768846f85bc2ef2063b55804e78527ad41a2e77023c434d04535`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4630-L4634) — lines `4630–4634`; excerpt `sha256:7968722d9338768846f85bc2ef2063b55804e78527ad41a2e77023c434d04535`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1220-L1220) — lines `1220–1220`; excerpt `sha256:adaee106fc9f14bfa32c5f6ab3ba20afe848ed080f83389485ba7fbd8b3be932`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1262](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1262-L1262), [cite at paper/reasoning-parts/erdos1041/core.tex:1220](../../paper/reasoning-parts/erdos1041/core.tex#L1220-L1220)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9453-L9457) — lines `9453–9457`; excerpt `sha256:2ffe3c91d993950605f8bf070b0a5a11ffc1f8ef39055137701039e8577a8e67`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9283-L9287) — lines `9283–9287`; excerpt `sha256:2ffe3c91d993950605f8bf070b0a5a11ffc1f8ef39055137701039e8577a8e67`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7984](../../paper/249/erdos249-totient-reasoning-surface.tex#L7984-L7984), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7814](../../paper/reasoning-parts/erdos249/a249_front.tex#L7814-L7814)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L801-L803) — lines `801–803`; excerpt `sha256:3ae9fa667b08eb5987a7e973b889bd3c52e080f8d91bd6fba3f1e66a8cc2f1b7`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3015-L3017) — lines `3015–3017`; excerpt `sha256:1565fef6512ed60adfcce853ce390a078eea05be1ecd50bcf8d12b0b2b596645`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2975-L2977) — lines `2975–2977`; excerpt `sha256:1565fef6512ed60adfcce853ce390a078eea05be1ecd50bcf8d12b0b2b596645`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L461-L461) — lines `461–461`; excerpt `sha256:ab4242568354b2c2c641f08bb7574ea4d9e86b6baaddd73d201a5e9169a983d3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L461-L461) — lines `461–461`; excerpt `sha256:ab4242568354b2c2c641f08bb7574ea4d9e86b6baaddd73d201a5e9169a983d3`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:323](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L323-L323)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:501](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L501-L501), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:514](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L514-L514), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1861](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1861-L1861), [cite at paper/reasoning-parts/erdos251/core.tex:461](../../paper/reasoning-parts/erdos251/core.tex#L461-L461), [cite at paper/reasoning-parts/erdos251/core.tex:474](../../paper/reasoning-parts/erdos251/core.tex#L474-L474), [cite at paper/reasoning-parts/erdos251/core.tex:1821](../../paper/reasoning-parts/erdos251/core.tex#L1821-L1821)

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
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1034-L1034) — lines `1034–1034`; excerpt `sha256:2f13d854d17862e3e84cfe8260e36f3e508b7165189455204d23c133aeac237e`

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1194-L1200) — lines `1194–1200`; excerpt `sha256:c6ad3b74ba433b2451bb8a22ac558445aec5cb56ecfef0b9118236d8dbc841ac`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4048-L4054) — lines `4048–4054`; excerpt `sha256:c6ad3b74ba433b2451bb8a22ac558445aec5cb56ecfef0b9118236d8dbc841ac`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4016-L4022) — lines `4016–4022`; excerpt `sha256:c6ad3b74ba433b2451bb8a22ac558445aec5cb56ecfef0b9118236d8dbc841ac`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:669](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L669-L669)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:826](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L826-L826), [cite at paper/reasoning-parts/erdos243/core.tex:794](../../paper/reasoning-parts/erdos243/core.tex#L794-L794)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2888-L2892) — lines `2888–2892`; excerpt `sha256:de382823fb7376836cf48c1a4705162b30877bceecea105e5ba9fd991dc8dcc9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2854-L2858) — lines `2854–2858`; excerpt `sha256:de382823fb7376836cf48c1a4705162b30877bceecea105e5ba9fd991dc8dcc9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1907-L1907) — lines `1907–1907`; excerpt `sha256:c6c8cf9b68fb541c95c305abe93492fb959422799957e770844d1c594c99ab29`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1907-L1907) — lines `1907–1907`; excerpt `sha256:c6c8cf9b68fb541c95c305abe93492fb959422799957e770844d1c594c99ab29`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1907-L1907) — lines `1907–1907`; excerpt `sha256:c6c8cf9b68fb541c95c305abe93492fb959422799957e770844d1c594c99ab29`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1941](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1941-L1941), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2328](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2328-L2328), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2340](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2340-L2340), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2342](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2342-L2342), [cite at paper/reasoning-parts/erdos68/core.tex:1907](../../paper/reasoning-parts/erdos68/core.tex#L1907-L1907), [cite at paper/reasoning-parts/erdos68/core.tex:2294](../../paper/reasoning-parts/erdos68/core.tex#L2294-L2294), [cite at paper/reasoning-parts/erdos68/core.tex:2306](../../paper/reasoning-parts/erdos68/core.tex#L2306-L2306), [cite at paper/reasoning-parts/erdos68/core.tex:2308](../../paper/reasoning-parts/erdos68/core.tex#L2308-L2308)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4594-L4597) — lines `4594–4597`; excerpt `sha256:e321a18827767ed58cdd1dd982eeeb9a39803cd37871901a8449163cbd346499`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4569-L4572) — lines `4569–4572`; excerpt `sha256:e321a18827767ed58cdd1dd982eeeb9a39803cd37871901a8449163cbd346499`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2246](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2246-L2246), [cite at paper/reasoning-parts/erdos1049/core.tex:2221](../../paper/reasoning-parts/erdos1049/core.tex#L2221-L2221)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1082-L1086) — lines `1082–1086`; excerpt `sha256:6a55d9dd03c7696ffe1aa2c5a2737a8f049a95714e471bb30b7e43314e7506a9`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9378-L9382) — lines `9378–9382`; excerpt `sha256:a550ec768381cedd7a6eeb6b4523783c7294044d1c637ec4e2264bb7d9a4439e`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9208-L9212) — lines `9208–9212`; excerpt `sha256:a550ec768381cedd7a6eeb6b4523783c7294044d1c637ec4e2264bb7d9a4439e`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:365](../../paper/249/erdos-249-binary-totient-series.tex#L365-L365)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9290](../../paper/249/erdos249-totient-reasoning-surface.tex#L9290-L9290), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9120](../../paper/reasoning-parts/erdos249/a249_front.tex#L9120-L9120)

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
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1155) — lines `1151–1155`; excerpt `sha256:8d04873393ce01957978e7bf822e3411f2a23947e1a44f04f81a2db2f17c6332`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3989-L3993) — lines `3989–3993`; excerpt `sha256:8d04873393ce01957978e7bf822e3411f2a23947e1a44f04f81a2db2f17c6332`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1092-L1095) — lines `1092–1095`; excerpt `sha256:e79adb56b67cd11616132762fbeadb6b20811b0217440e25c49e7a4f695da264`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L769-L771) — lines `769–771`; excerpt `sha256:44c67147da17a5a42fe794398401c5f1d3beb10fb6f1b30933e004aa1a164fd5`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2971-L2973) — lines `2971–2973`; excerpt `sha256:44c67147da17a5a42fe794398401c5f1d3beb10fb6f1b30933e004aa1a164fd5`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2952-L2955) — lines `2952–2955`; excerpt `sha256:8466f5a9dd4ced1a4f291d5d67e847f3b2fca1cf34f259ca712ff23fe61bbc42`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L796-L799) — lines `796–799`; excerpt `sha256:8466f5a9dd4ced1a4f291d5d67e847f3b2fca1cf34f259ca712ff23fe61bbc42`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1551-L1554) — lines `1551–1554`; excerpt `sha256:851267bb83e0426f3dc46e58eca0ec223ffefbf930eeba52eeeccf56d165f807`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3957-L3961) — lines `3957–3961`; excerpt `sha256:8d04873393ce01957978e7bf822e3411f2a23947e1a44f04f81a2db2f17c6332`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L43-L43) — lines `43–43`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2931-L2933) — lines `2931–2933`; excerpt `sha256:44c67147da17a5a42fe794398401c5f1d3beb10fb6f1b30933e004aa1a164fd5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L48-L48) — lines `48–48`; excerpt `sha256:7f9971210ce1d8295bfd2da08dd2dae6cde77e72e05cc25210e713a613768912`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2907-L2910) — lines `2907–2910`; excerpt `sha256:8466f5a9dd4ced1a4f291d5d67e847f3b2fca1cf34f259ca712ff23fe61bbc42`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:44fd9c14c25e5775404be7ccea03d3057255373bee9505c5739d20d124ad3866`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9390-L9394) — lines `9390–9394`; excerpt `sha256:727de5144fdf771c479a2e03e7b875cffecf9400543450974b25f25aced90f03`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9220-L9224) — lines `9220–9224`; excerpt `sha256:727de5144fdf771c479a2e03e7b875cffecf9400543450974b25f25aced90f03`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:993](../../paper/systems/claim-faithful-publication-systems-paper.tex#L993-L993)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:143](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L143-L143)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:835](../../paper/249/erdos-249-binary-totient-series.tex#L835-L835)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:321](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L321-L321)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:57](../../paper/269/erdos-269-three-prime-running-lcm.tex#L57-L57)
- `erdos-synthesis-subsums-across-bases`: [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:58](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L58-L58), [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:67](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L67-L67)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:75](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L75-L75), [cite at paper/reasoning-parts/erdos243/core.tex:43](../../paper/reasoning-parts/erdos243/core.tex#L43-L43)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:193](../../paper/archive/erdos249-257-main-paper.tex#L193-L193), [cite at paper/archive/erdos249-257-main-paper.tex:194](../../paper/archive/erdos249-257-main-paper.tex#L194-L194)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:252](../../paper/249/erdos249-totient-reasoning-surface.tex#L252-L252), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:82](../../paper/reasoning-parts/erdos249/a249_front.tex#L82-L82)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:88](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L88-L88), [cite at paper/reasoning-parts/erdos251/core.tex:48](../../paper/reasoning-parts/erdos251/core.tex#L48-L48)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:74](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L74-L74), [cite at paper/reasoning-parts/erdos269/core.tex:29](../../paper/reasoning-parts/erdos269/core.tex#L29-L29)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1078-L1082) — lines `1078–1082`; excerpt `sha256:5c07b90db96e384410ed6cbfa6f0a0260dd341520e919d4e5654581d25bb3b5c`
- [lean/Erdos249257/AllBaseTotientKernel.lean](../../lean/Erdos249257/AllBaseTotientKernel.lean#L4-L61) — lines `4–61`; excerpt `sha256:a7583f78b57fbb25305024044671d8303e0dfd61da003f0de23f3c82ca558fb4`
- [lean/Erdos249257/AllBaseTotientKernel.lean](../../lean/Erdos249257/AllBaseTotientKernel.lean#L642-L644) — lines `642–644`; excerpt `sha256:f2847f43a004d01715e61f5510732df2e0014e197cb1796803035180a98f88f6`
- [lean/Erdos249257/TotientKernelConditional.lean](../../lean/Erdos249257/TotientKernelConditional.lean#L5-L18) — lines `5–18`; excerpt `sha256:bb1cbd9adcabf879040179a1dda4145da0903770eb95510584365a88131340ba`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L89-L89) — lines `89–89`; excerpt `sha256:0b9c9251af21e6eeb9177cb4f168d77d98fe8e2be6e6f70f8029efd8b0ef9375`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9374-L9378) — lines `9374–9378`; excerpt `sha256:c97e654465265fb62b6de801d7921a842ace01171d8790c26144b859fefa809c`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9204-L9208) — lines `9204–9208`; excerpt `sha256:c97e654465265fb62b6de801d7921a842ace01171d8790c26144b859fefa809c`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:63](../../paper/249/erdos-249-binary-totient-series.tex#L63-L63), [cite at paper/249/erdos-249-binary-totient-series.tex:270](../../paper/249/erdos-249-binary-totient-series.tex#L270-L270), [cite at paper/249/erdos-249-binary-totient-series.tex:763](../../paper/249/erdos-249-binary-totient-series.tex#L763-L763)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:259](../../paper/249/erdos249-totient-reasoning-surface.tex#L259-L259), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7070](../../paper/249/erdos249-totient-reasoning-surface.tex#L7070-L7070), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7168](../../paper/249/erdos249-totient-reasoning-surface.tex#L7168-L7168), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:89](../../paper/reasoning-parts/erdos249/a249_front.tex#L89-L89), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6900](../../paper/reasoning-parts/erdos249/a249_front.tex#L6900-L6900), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6998](../../paper/reasoning-parts/erdos249/a249_front.tex#L6998-L6998)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1298-L1304) — lines `1298–1304`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4429-L4435) — lines `4429–4435`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4404-L4410) — lines `4404–4410`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57) — lines `57–57`; excerpt `sha256:c78e7588221f1a95c20afd98fb89102739372faca040684d00847149dcbc61b4`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L794-L794) — lines `794–794`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1105-L1105) — lines `1105–1105`; excerpt `sha256:603c399e18eec54e4b76bcb455d51b93adf56ce7a26e699ca50aa8527aaa25fa`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L8-L36) — lines `8–36`; excerpt `sha256:580a0329d38f93ac21807ae3e4b5576bc7cc0a60f32dc890b169224bff93a983`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L121-L143) — lines `121–143`; excerpt `sha256:9cbb2521fc20ab9b5f2b1ef19d400d7a4706ab42e437b60f3d445f245666ebab`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L312-L317) — lines `312–317`; excerpt `sha256:9d8f3b2b1f69665003c2e2e1011aa3ab2153e1279df369928b397383f2c62c70`
- [lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean](../../lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L8-L15) — lines `8–15`; excerpt `sha256:944f0e0e804396ce17b086bb0755d7c33ca82e608e624be2a2542fcd18124e82`
- [lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean](../../lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L72-L79) — lines `72–79`; excerpt `sha256:519814e5b5744e92c8a9dc9ac2c0c0fd009c2f4c5e71df7e3e2af9a3034f730a`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9758-L9764) — lines `9758–9764`; excerpt `sha256:b26157f8e2462fe6a9cb317178ca1aa00c80c57d6b9c2a7ae528d32e670113ad`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9574-L9580) — lines `9574–9580`; excerpt `sha256:b26157f8e2462fe6a9cb317178ca1aa00c80c57d6b9c2a7ae528d32e670113ad`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:70](../../paper/1049/erdos-1049-rational-base-lambert.tex#L70-L70), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:118](../../paper/1049/erdos-1049-rational-base-lambert.tex#L118-L118), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:120](../../paper/1049/erdos-1049-rational-base-lambert.tex#L120-L120), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:170](../../paper/1049/erdos-1049-rational-base-lambert.tex#L170-L170), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:201](../../paper/1049/erdos-1049-rational-base-lambert.tex#L201-L201), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:216](../../paper/1049/erdos-1049-rational-base-lambert.tex#L216-L216), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:227](../../paper/1049/erdos-1049-rational-base-lambert.tex#L227-L227), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:230](../../paper/1049/erdos-1049-rational-base-lambert.tex#L230-L230), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:301](../../paper/1049/erdos-1049-rational-base-lambert.tex#L301-L301), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:411](../../paper/1049/erdos-1049-rational-base-lambert.tex#L411-L411), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:485](../../paper/1049/erdos-1049-rational-base-lambert.tex#L485-L485), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:504](../../paper/1049/erdos-1049-rational-base-lambert.tex#L504-L504)
- `erdos-synthesis-subsums-across-bases`: [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:144](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L144-L144)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:82](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L82-L82), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:157](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L157-L157), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:187](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L187-L187), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:198](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L198-L198), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:232](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L232-L232), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:254](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L254-L254), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:279](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L279-L279), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:293](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L293-L293), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:296](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L296-L296), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:329](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L329-L329), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:468](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L468-L468), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:502](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L502-L503), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:791](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L791-L791), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:792](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L792-L792), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:797](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L797-L797), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:843](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L843-L843), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:856](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L856-L856), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1148](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1148-L1148), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1157](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1157-L1157), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1286](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1286-L1286), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2606](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2606-L2606), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2778](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2778-L2778), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3068](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3068-L3068), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4245](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4245-L4245), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4287](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4287-L4287), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4476](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4476-L4476), [cite at paper/reasoning-parts/erdos1049/core.tex:57](../../paper/reasoning-parts/erdos1049/core.tex#L57-L57), [cite at paper/reasoning-parts/erdos1049/core.tex:132](../../paper/reasoning-parts/erdos1049/core.tex#L132-L132), [cite at paper/reasoning-parts/erdos1049/core.tex:162](../../paper/reasoning-parts/erdos1049/core.tex#L162-L162), [cite at paper/reasoning-parts/erdos1049/core.tex:173](../../paper/reasoning-parts/erdos1049/core.tex#L173-L173), [cite at paper/reasoning-parts/erdos1049/core.tex:207](../../paper/reasoning-parts/erdos1049/core.tex#L207-L207), [cite at paper/reasoning-parts/erdos1049/core.tex:229](../../paper/reasoning-parts/erdos1049/core.tex#L229-L229), [cite at paper/reasoning-parts/erdos1049/core.tex:254](../../paper/reasoning-parts/erdos1049/core.tex#L254-L254), [cite at paper/reasoning-parts/erdos1049/core.tex:268](../../paper/reasoning-parts/erdos1049/core.tex#L268-L268), [cite at paper/reasoning-parts/erdos1049/core.tex:271](../../paper/reasoning-parts/erdos1049/core.tex#L271-L271), [cite at paper/reasoning-parts/erdos1049/core.tex:304](../../paper/reasoning-parts/erdos1049/core.tex#L304-L304), [cite at paper/reasoning-parts/erdos1049/core.tex:443](../../paper/reasoning-parts/erdos1049/core.tex#L443-L443), [cite at paper/reasoning-parts/erdos1049/core.tex:477](../../paper/reasoning-parts/erdos1049/core.tex#L477-L478), [cite at paper/reasoning-parts/erdos1049/core.tex:766](../../paper/reasoning-parts/erdos1049/core.tex#L766-L766), [cite at paper/reasoning-parts/erdos1049/core.tex:767](../../paper/reasoning-parts/erdos1049/core.tex#L767-L767), [cite at paper/reasoning-parts/erdos1049/core.tex:772](../../paper/reasoning-parts/erdos1049/core.tex#L772-L772), [cite at paper/reasoning-parts/erdos1049/core.tex:818](../../paper/reasoning-parts/erdos1049/core.tex#L818-L818), [cite at paper/reasoning-parts/erdos1049/core.tex:831](../../paper/reasoning-parts/erdos1049/core.tex#L831-L831), [cite at paper/reasoning-parts/erdos1049/core.tex:1123](../../paper/reasoning-parts/erdos1049/core.tex#L1123-L1123), [cite at paper/reasoning-parts/erdos1049/core.tex:1132](../../paper/reasoning-parts/erdos1049/core.tex#L1132-L1132), [cite at paper/reasoning-parts/erdos1049/core.tex:1261](../../paper/reasoning-parts/erdos1049/core.tex#L1261-L1261), [cite at paper/reasoning-parts/erdos1049/core.tex:2581](../../paper/reasoning-parts/erdos1049/core.tex#L2581-L2581), [cite at paper/reasoning-parts/erdos1049/core.tex:2753](../../paper/reasoning-parts/erdos1049/core.tex#L2753-L2753), [cite at paper/reasoning-parts/erdos1049/core.tex:3043](../../paper/reasoning-parts/erdos1049/core.tex#L3043-L3043), [cite at paper/reasoning-parts/erdos1049/core.tex:4220](../../paper/reasoning-parts/erdos1049/core.tex#L4220-L4220), [cite at paper/reasoning-parts/erdos1049/core.tex:4262](../../paper/reasoning-parts/erdos1049/core.tex#L4262-L4262), [cite at paper/reasoning-parts/erdos1049/core.tex:4451](../../paper/reasoning-parts/erdos1049/core.tex#L4451-L4451)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1289](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1289-L1289), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7517](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7517-L7517), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1105](../../paper/reasoning-parts/erdos257/a257_front.tex#L1105-L1105), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7333](../../paper/reasoning-parts/erdos257/a257_front.tex#L7333-L7333)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4463-L4470) — lines `4463–4470`; excerpt `sha256:2e85c59828644ad3c8fb345c8b459c4f9c86946c02a53b466028be600adf3dcf`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4438-L4445) — lines `4438–4445`; excerpt `sha256:2e85c59828644ad3c8fb345c8b459c4f9c86946c02a53b466028be600adf3dcf`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L813-L813) — lines `813–813`; excerpt `sha256:fbce7f2db65bdd8d9f109301fb1bc86d09291626cd9714baf8b44fb0defea1c4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L813-L813) — lines `813–813`; excerpt `sha256:fbce7f2db65bdd8d9f109301fb1bc86d09291626cd9714baf8b44fb0defea1c4`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:838](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L838-L838), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4282](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4282-L4282), [cite at paper/reasoning-parts/erdos1049/core.tex:813](../../paper/reasoning-parts/erdos1049/core.tex#L813-L813), [cite at paper/reasoning-parts/erdos1049/core.tex:4257](../../paper/reasoning-parts/erdos1049/core.tex#L4257-L4257)

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

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4033-L4038) — lines `4033–4038`; excerpt `sha256:1aefcf6f7f768fe29af3e6054e3b0cd92df53c67a5b2082873142c699135431c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4001-L4006) — lines `4001–4006`; excerpt `sha256:1aefcf6f7f768fe29af3e6054e3b0cd92df53c67a5b2082873142c699135431c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L901-L901) — lines `901–901`; excerpt `sha256:adfa536049be0e74065800037ce0ba5a0d022d83f1cf5dfdd9d4c0dda34e205f`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L933-L933) — lines `933–933`; excerpt `sha256:adfa536049be0e74065800037ce0ba5a0d022d83f1cf5dfdd9d4c0dda34e205f`

Paper citation usages:

- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:933](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L933-L933), [cite at paper/reasoning-parts/erdos243/core.tex:901](../../paper/reasoning-parts/erdos243/core.tex#L901-L901)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4486-L4491) — lines `4486–4491`; excerpt `sha256:b75b67635c18f80de0c876644a0d855886ffebd57e78291c56d2b76c6f5fe91f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4461-L4466) — lines `4461–4466`; excerpt `sha256:b75b67635c18f80de0c876644a0d855886ffebd57e78291c56d2b76c6f5fe91f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2748-L2748) — lines `2748–2748`; excerpt `sha256:7d171ed1577013457353cdde13d778d34a71fbed4c861b7ce3d975c634196d90`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2748-L2748) — lines `2748–2748`; excerpt `sha256:7d171ed1577013457353cdde13d778d34a71fbed4c861b7ce3d975c634196d90`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2773](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2773-L2773), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4250](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4250-L4250), [cite at paper/reasoning-parts/erdos1049/core.tex:2748](../../paper/reasoning-parts/erdos1049/core.tex#L2748-L2748), [cite at paper/reasoning-parts/erdos1049/core.tex:4225](../../paper/reasoning-parts/erdos1049/core.tex#L4225-L4225)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L820-L823) — lines `820–823`; excerpt `sha256:102b617cbf408f358626ce785399d55baf63d64228a12995ce76a5747cad8bfb`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2991-L2994) — lines `2991–2994`; excerpt `sha256:d7d4cedfe807acd8fbf6994b4c4ea185099dead717184730b0485ff8e4adf7fe`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2946-L2949) — lines `2946–2949`; excerpt `sha256:d7d4cedfe807acd8fbf6994b4c4ea185099dead717184730b0485ff8e4adf7fe`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:420](../../paper/269/erdos-269-three-prime-running-lcm.tex#L420-L420)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1259](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1259-L1259), [cite at paper/reasoning-parts/erdos269/core.tex:1214](../../paper/reasoning-parts/erdos269/core.tex#L1214-L1214)

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

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4020-L4024) — lines `4020–4024`; excerpt `sha256:d1521927de67d3175dadffc4db2ca2b2786b8297ec43e4eec74b73a350d2d98c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3988-L3992) — lines `3988–3992`; excerpt `sha256:d1521927de67d3175dadffc4db2ca2b2786b8297ec43e4eec74b73a350d2d98c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2847-L2847) — lines `2847–2847`; excerpt `sha256:7031adbd8ee1ddab8aa252c4d2184fcfd608e6225a7ebbe27418145af8fd95d2`

Paper citation usages:

- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2879](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2879-L2879), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2883](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2883-L2883), [cite at paper/reasoning-parts/erdos243/core.tex:2847](../../paper/reasoning-parts/erdos243/core.tex#L2847-L2847), [cite at paper/reasoning-parts/erdos243/core.tex:2851](../../paper/reasoning-parts/erdos243/core.tex#L2851-L2851)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2977-L2979) — lines `2977–2979`; excerpt `sha256:e12f144375e5514cf3ca5b5c578990d0af610fa16c55c2bbfa94d6d3dc603533`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2937-L2939) — lines `2937–2939`; excerpt `sha256:e12f144375e5514cf3ca5b5c578990d0af610fa16c55c2bbfa94d6d3dc603533`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L819-L821) — lines `819–821`; excerpt `sha256:9f99ab4abb9eff1473257f6e3d761345f3ec4a6ed070161011aa5016e99df64b`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:246](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L246-L246)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2119](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2119-L2119), [cite at paper/reasoning-parts/erdos251/core.tex:2079](../../paper/reasoning-parts/erdos251/core.tex#L2079-L2079)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3013-L3015) — lines `3013–3015`; excerpt `sha256:fa3bcf168a1340d8601007b6c72c53c3522ccbfd26f78776332e6c0f9092861f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2973-L2975) — lines `2973–2975`; excerpt `sha256:fa3bcf168a1340d8601007b6c72c53c3522ccbfd26f78776332e6c0f9092861f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L394-L394) — lines `394–394`; excerpt `sha256:d51067079b4e215c7e248a94840bfb0a809d0fbd2b2272202e48db377def60ae`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L394-L394) — lines `394–394`; excerpt `sha256:d51067079b4e215c7e248a94840bfb0a809d0fbd2b2272202e48db377def60ae`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2004-L2004) — lines `2004–2004`; excerpt `sha256:12505b93fd9fe42cc2789467c5e348722fb0f6684320328f30690cdcc31c269c`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L799-L801) — lines `799–801`; excerpt `sha256:fa3bcf168a1340d8601007b6c72c53c3522ccbfd26f78776332e6c0f9092861f`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:383](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L383-L383)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:434](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L434-L434), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2045](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2045-L2045), [cite at paper/reasoning-parts/erdos251/core.tex:394](../../paper/reasoning-parts/erdos251/core.tex#L394-L394), [cite at paper/reasoning-parts/erdos251/core.tex:2005](../../paper/reasoning-parts/erdos251/core.tex#L2005-L2005)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2985-L2988) — lines `2985–2988`; excerpt `sha256:cf8585af0cb481ca30a6e5ac45913052ead0e0e5ceae275a06d522f0825578f7`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L814-L817) — lines `814–817`; excerpt `sha256:cf8585af0cb481ca30a6e5ac45913052ead0e0e5ceae275a06d522f0825578f7`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2940-L2943) — lines `2940–2943`; excerpt `sha256:cf8585af0cb481ca30a6e5ac45913052ead0e0e5ceae275a06d522f0825578f7`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L32-L32) — lines `32–32`; excerpt `sha256:6d7110fd8cd028c94015637429a3ddb6e5abe8a714e8b6268356d67749dfff26`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L32-L32) — lines `32–32`; excerpt `sha256:6d7110fd8cd028c94015637429a3ddb6e5abe8a714e8b6268356d67749dfff26`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L32-L32) — lines `32–32`; excerpt `sha256:6d7110fd8cd028c94015637429a3ddb6e5abe8a714e8b6268356d67749dfff26`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L32-L32) — lines `32–32`; excerpt `sha256:6d7110fd8cd028c94015637429a3ddb6e5abe8a714e8b6268356d67749dfff26`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:66](../../paper/269/erdos-269-three-prime-running-lcm.tex#L66-L66), [cite at paper/269/erdos-269-three-prime-running-lcm.tex:230](../../paper/269/erdos-269-three-prime-running-lcm.tex#L230-L230)
- `erdos-synthesis-reading-together-record`: [cite at paper/synthesis/erdos-synthesis-reading-together-record.tex:133](../../paper/synthesis/erdos-synthesis-reading-together-record.tex#L133-L133)
- `erdos-synthesis-subsums-across-bases`: [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:371](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L371-L371)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:77](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L77-L77), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:101](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L101-L101), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:643](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L643-L643), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2477](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2477-L2477), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2515](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2515-L2515), [cite at paper/reasoning-parts/erdos269/core.tex:32](../../paper/reasoning-parts/erdos269/core.tex#L32-L32), [cite at paper/reasoning-parts/erdos269/core.tex:56](../../paper/reasoning-parts/erdos269/core.tex#L56-L56), [cite at paper/reasoning-parts/erdos269/core.tex:598](../../paper/reasoning-parts/erdos269/core.tex#L598-L598), [cite at paper/reasoning-parts/erdos269/core.tex:2432](../../paper/reasoning-parts/erdos269/core.tex#L2432-L2432), [cite at paper/reasoning-parts/erdos269/core.tex:2470](../../paper/reasoning-parts/erdos269/core.tex#L2470-L2470)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2958-L2961) — lines `2958–2961`; excerpt `sha256:c96fc6ec675af873515b2c54bc711717a8fc43e0ef49d8237f9f330492b2bfa1`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L802-L805) — lines `802–805`; excerpt `sha256:c96fc6ec675af873515b2c54bc711717a8fc43e0ef49d8237f9f330492b2bfa1`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2913-L2916) — lines `2913–2916`; excerpt `sha256:c96fc6ec675af873515b2c54bc711717a8fc43e0ef49d8237f9f330492b2bfa1`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2458-L2458) — lines `2458–2458`; excerpt `sha256:384fe3be0235ab7e75b830dd668fd755331e43ab39ec59e14a0456d8ec1aee5e`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:296](../../paper/269/erdos-269-three-prime-running-lcm.tex#L296-L296)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2503](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2503-L2503), [cite at paper/reasoning-parts/erdos269/core.tex:2458](../../paper/reasoning-parts/erdos269/core.tex#L2458-L2458)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9414-L9419) — lines `9414–9419`; excerpt `sha256:6b26831b0198ae83ddcc51944fe34abc4a33f500ca85d17497481409ce3268b5`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9244-L9249) — lines `9244–9249`; excerpt `sha256:6b26831b0198ae83ddcc51944fe34abc4a33f500ca85d17497481409ce3268b5`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1640](../../paper/249/erdos249-totient-reasoning-surface.tex#L1640-L1641), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1470](../../paper/reasoning-parts/erdos249/a249_front.tex#L1470-L1471)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4456-L4463) — lines `4456–4463`; excerpt `sha256:037d8d669c712adb2ce488ddaad6988ca8a9e433e3271c97496d29be910f9ded`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4431-L4438) — lines `4431–4438`; excerpt `sha256:037d8d669c712adb2ce488ddaad6988ca8a9e433e3271c97496d29be910f9ded`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1360-L1367) — lines `1360–1367`; excerpt `sha256:f964675e399704b559c29b51eea44fc7fd16035cbb7bfee0f3491e3f1433945c`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:763](../../paper/1049/erdos-1049-rational-base-lambert.tex#L763-L763)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1459](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1459-L1459), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1461](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1461-L1461), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2506](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2506-L2506), [cite at paper/reasoning-parts/erdos1049/core.tex:1434](../../paper/reasoning-parts/erdos1049/core.tex#L1434-L1434), [cite at paper/reasoning-parts/erdos1049/core.tex:1436](../../paper/reasoning-parts/erdos1049/core.tex#L1436-L1436), [cite at paper/reasoning-parts/erdos1049/core.tex:2481](../../paper/reasoning-parts/erdos1049/core.tex#L2481-L2481)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1317-L1323) — lines `1317–1323`; excerpt `sha256:4ece33472f9eb3ee10b399b4e65ea39cee778bd9cd7f3f8e4f59aca5de46732f`

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L771-L773) — lines `771–773`; excerpt `sha256:b4c77ac8d585a2bd2069a38e1c79a60b2fad942e48f3b3f28ef5324369021f67`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2973-L2975) — lines `2973–2975`; excerpt `sha256:b4c77ac8d585a2bd2069a38e1c79a60b2fad942e48f3b3f28ef5324369021f67`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2933-L2935) — lines `2933–2935`; excerpt `sha256:b4c77ac8d585a2bd2069a38e1c79a60b2fad942e48f3b3f28ef5324369021f67`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L481-L481) — lines `481–481`; excerpt `sha256:8512bbc97e99faf26e79d6c8b92de42e4aee99cb8e1f47bc6fcd1006598c138f`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:324](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L324-L324)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:521](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L521-L521), [cite at paper/reasoning-parts/erdos251/core.tex:481](../../paper/reasoning-parts/erdos251/core.tex#L481-L481)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1372-L1376) — lines `1372–1376`; excerpt `sha256:e451a824e41d073b225ae1abab1c62ca244baecf39aa9ed66d457b7b7eae3586`

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4503-L4507) — lines `4503–4507`; excerpt `sha256:009f0d973b996ec8f00395a65152d98054ea2ab49f230fdc01672a16b260f5cc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4478-L4482) — lines `4478–4482`; excerpt `sha256:009f0d973b996ec8f00395a65152d98054ea2ab49f230fdc01672a16b260f5cc`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4207](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4207-L4207), [cite at paper/reasoning-parts/erdos1049/core.tex:4182](../../paper/reasoning-parts/erdos1049/core.tex#L4182-L4182)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1071-L1078) — lines `1071–1078`; excerpt `sha256:35232d77de2ddf4ba567da9e409016c66c0f5cf9a2043005e44829a8e3810ecb`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L781-L781) — lines `781–781`; excerpt `sha256:ba2623fd0d16d511439ef0687c6297f7daa8de19a37077c607d2130b31b303ec`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L814-L814) — lines `814–814`; excerpt `sha256:0142ca2770f5fed6e6ed78dbeece75dce215597f563a5c5ad5d387565ab27aa0`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L6981-L6981) — lines `6981–6981`; excerpt `sha256:56fdec6410c26f8914c14fa0ed7570a72d4d32a7732a20d469535683c1238267`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9368-L9374) — lines `9368–9374`; excerpt `sha256:de208be728552e87a1ec173f99d8429dd11fd4df8ecf144d7252710e5141acaa`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9198-L9204) — lines `9198–9204`; excerpt `sha256:de208be728552e87a1ec173f99d8429dd11fd4df8ecf144d7252710e5141acaa`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:781](../../paper/249/erdos-249-binary-totient-series.tex#L781-L781), [cite at paper/249/erdos-249-binary-totient-series.tex:816](../../paper/249/erdos-249-binary-totient-series.tex#L816-L816)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7151](../../paper/249/erdos249-totient-reasoning-surface.tex#L7151-L7151), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6981](../../paper/reasoning-parts/erdos249/a249_front.tex#L6981-L6981)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L832-L835) — lines `832–835`; excerpt `sha256:c38b879eb5217d10f2aed8b52d4612ade541384e4d3e5da0fc7060cf204a573b`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3012-L3015) — lines `3012–3015`; excerpt `sha256:c38b879eb5217d10f2aed8b52d4612ade541384e4d3e5da0fc7060cf204a573b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2967-L2970) — lines `2967–2970`; excerpt `sha256:c38b879eb5217d10f2aed8b52d4612ade541384e4d3e5da0fc7060cf204a573b`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:689](../../paper/269/erdos-269-three-prime-running-lcm.tex#L689-L689)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1981](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1981-L1981), [cite at paper/reasoning-parts/erdos269/core.tex:1936](../../paper/reasoning-parts/erdos269/core.tex#L1936-L1936)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2952-L2956) — lines `2952–2956`; excerpt `sha256:3aaa23b0ee5980d4b7a569cd8945d5e49ec49e7301ec40d1a5ab10ee81d75a3f`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2918-L2922) — lines `2918–2922`; excerpt `sha256:3aaa23b0ee5980d4b7a569cd8945d5e49ec49e7301ec40d1a5ab10ee81d75a3f`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1651](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1651-L1651), [cite at paper/reasoning-parts/erdos68/core.tex:1617](../../paper/reasoning-parts/erdos68/core.tex#L1617-L1617)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1372-L1376) — lines `1372–1376`; excerpt `sha256:67bdfa0d9c73d3ef9074f492e01b18101ff6ce673d7d7e006e7add28eefa7c93`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4585-L4589) — lines `4585–4589`; excerpt `sha256:67bdfa0d9c73d3ef9074f492e01b18101ff6ce673d7d7e006e7add28eefa7c93`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4560-L4564) — lines `4560–4564`; excerpt `sha256:67bdfa0d9c73d3ef9074f492e01b18101ff6ce673d7d7e006e7add28eefa7c93`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1177](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1177-L1177)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2167](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2167-L2167), [cite at paper/reasoning-parts/erdos1049/core.tex:2142](../../paper/reasoning-parts/erdos1049/core.tex#L2142-L2142)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1160-L1165) — lines `1160–1165`; excerpt `sha256:0b698c4756fa8f99456ed34f52b4cf9be3600160caf3f3dec408e04cc0d7d111`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4005-L4010) — lines `4005–4010`; excerpt `sha256:0b698c4756fa8f99456ed34f52b4cf9be3600160caf3f3dec408e04cc0d7d111`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3973-L3978) — lines `3973–3978`; excerpt `sha256:0b698c4756fa8f99456ed34f52b4cf9be3600160caf3f3dec408e04cc0d7d111`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:253](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L253-L253), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:411](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L411-L411), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:490](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L490-L490)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1426](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1426-L1426), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1829](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1829-L1829), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2935](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2935-L2935), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3238](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3238-L3238), [cite at paper/reasoning-parts/erdos243/core.tex:1394](../../paper/reasoning-parts/erdos243/core.tex#L1394-L1394), [cite at paper/reasoning-parts/erdos243/core.tex:1797](../../paper/reasoning-parts/erdos243/core.tex#L1797-L1797), [cite at paper/reasoning-parts/erdos243/core.tex:2903](../../paper/reasoning-parts/erdos243/core.tex#L2903-L2903), [cite at paper/reasoning-parts/erdos243/core.tex:3206](../../paper/reasoning-parts/erdos243/core.tex#L3206-L3206)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4631-L4637) — lines `4631–4637`; excerpt `sha256:2bbaf57338864a16529f3ab7d08eeeff8fb2358b4fafc7034087e3c4761985ee`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4589-L4595) — lines `4589–4595`; excerpt `sha256:2bbaf57338864a16529f3ab7d08eeeff8fb2358b4fafc7034087e3c4761985ee`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1850-L1855) — lines `1850–1855`; excerpt `sha256:72718134788b958a62bff3e97274b643933433c7df05bbba88477d8e130e3199`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1535](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1535-L1535)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3817](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3817-L3817), [cite at paper/reasoning-parts/erdos1041/core.tex:3775](../../paper/reasoning-parts/erdos1041/core.tex#L3775-L3775)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L815-L817) — lines `815–817`; excerpt `sha256:43bd9def386ccbb639374046fe11783990aedddb477c5470004d7a6155628547`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3031-L3033) — lines `3031–3033`; excerpt `sha256:3ba50a821565d47f20a7cf904fc3290b1f3c5126a28229eafe3917129456236e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2991-L2993) — lines `2991–2993`; excerpt `sha256:3ba50a821565d47f20a7cf904fc3290b1f3c5126a28229eafe3917129456236e`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:745](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L745-L745)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:586](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L586-L586), [cite at paper/reasoning-parts/erdos251/core.tex:546](../../paper/reasoning-parts/erdos251/core.tex#L546-L546)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1820-L1826) — lines `1820–1826`; excerpt `sha256:550b981b3e8c869d0df50cfb0dea1be1b90d0f2ad814088a1f8a1a3ac9ffade8`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4589-L4595) — lines `4589–4595`; excerpt `sha256:81544feb2d8e4a8dc89d7c14926bbdc17f7c170e2812d2e600bc764613620048`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4547-L4553) — lines `4547–4553`; excerpt `sha256:81544feb2d8e4a8dc89d7c14926bbdc17f7c170e2812d2e600bc764613620048`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L282-L282) — lines `282–282`; excerpt `sha256:e9af8055987c041e602fc36e4a30d002d7968c9be42fc2308fabbfc5f03eda0d`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L282-L282) — lines `282–282`; excerpt `sha256:e9af8055987c041e602fc36e4a30d002d7968c9be42fc2308fabbfc5f03eda0d`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1666-L1666) — lines `1666–1666`; excerpt `sha256:513d9455ccd8f11d7bcdd4c503ae02528701d9a1e8bef30b6c9cb257b35a2b5f`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:749](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L749-L749)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:728](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L728-L728), [cite at paper/reasoning-parts/erdos1041/core.tex:686](../../paper/reasoning-parts/erdos1041/core.tex#L686-L686)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L767-L769) — lines `767–769`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2969-L2971) — lines `2969–2971`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2929-L2931) — lines `2929–2931`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L47-L47) — lines `47–47`; excerpt `sha256:c16779e8ef1829576503b1d911e55d11c0d4f12db6c7168a113049c1f0cefdce`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L47-L47) — lines `47–47`; excerpt `sha256:c16779e8ef1829576503b1d911e55d11c0d4f12db6c7168a113049c1f0cefdce`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L47-L47) — lines `47–47`; excerpt `sha256:c16779e8ef1829576503b1d911e55d11c0d4f12db6c7168a113049c1f0cefdce`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:321](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L321-L321)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:87](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L87-L87), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:487](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L487-L487), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:504](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L504-L504), [cite at paper/reasoning-parts/erdos251/core.tex:47](../../paper/reasoning-parts/erdos251/core.tex#L47-L47), [cite at paper/reasoning-parts/erdos251/core.tex:447](../../paper/reasoning-parts/erdos251/core.tex#L447-L447), [cite at paper/reasoning-parts/erdos251/core.tex:464](../../paper/reasoning-parts/erdos251/core.tex#L464-L464)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2960-L2964) — lines `2960–2964`; excerpt `sha256:0237824e9b1bc6846e06ebc8479034b15e0574bcf800f0b614d1d0a682ca52bb`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2926-L2930) — lines `2926–2930`; excerpt `sha256:0237824e9b1bc6846e06ebc8479034b15e0574bcf800f0b614d1d0a682ca52bb`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1759](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1759-L1759), [cite at paper/reasoning-parts/erdos68/core.tex:1725](../../paper/reasoning-parts/erdos68/core.tex#L1725-L1725)

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
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1389-L1396) — lines `1389–1396`; excerpt `sha256:0ef99b680f15dcdcdc4890932040fe1bad3f3ee018e801c7204dea8bae0d1b51`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L886-L886) — lines `886–886`; excerpt `sha256:e8f0eb9c08b32d040eb9d382b55721fcbada06cfa90efaa2936a851eae07396b`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L794-L794) — lines `794–794`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8529-L8529) — lines `8529–8529`; excerpt `sha256:53ca69e59ff43d0292ca42e7954e5800d1314c64e4be23c03c224c016e357b49`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8696-L8696) — lines `8696–8696`; excerpt `sha256:1197efd3480c3d18971ff7587e64c3696907146bd64660e41bda3a5ac9fbd8f2`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9090-L9090) — lines `9090–9090`; excerpt `sha256:b02d5126a31d6f516b011882cd7b77604eb511797cbc09d89912554f44c242e9`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L136-L136) — lines `136–136`; excerpt `sha256:fa9c5470b10974096a81d5f934190f18c1303bfbab8ccee75a7290efabe75eab`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L136-L136) — lines `136–136`; excerpt `sha256:fa9c5470b10974096a81d5f934190f18c1303bfbab8ccee75a7290efabe75eab`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L136-L136) — lines `136–136`; excerpt `sha256:fa9c5470b10974096a81d5f934190f18c1303bfbab8ccee75a7290efabe75eab`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L503-L503) — lines `503–503`; excerpt `sha256:1ed1ce69c8bf73f3362ff5a2aca04fe7d02e4cc4dbe0784bc0f09ca0a22ad778`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4518-L4525) — lines `4518–4525`; excerpt `sha256:d84745edafcc3ae3ed868569f0e1e327404f0c2a6ff86a0c327422d4a6ddbebd`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4493-L4500) — lines `4493–4500`; excerpt `sha256:d84745edafcc3ae3ed868569f0e1e327404f0c2a6ff86a0c327422d4a6ddbebd`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9732-L9747) — lines `9732–9747`; excerpt `sha256:639844231444857a119025ab8e330a05e28514cf1dc9e9c65fdc92da1d687928`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9548-L9563) — lines `9548–9563`; excerpt `sha256:639844231444857a119025ab8e330a05e28514cf1dc9e9c65fdc92da1d687928`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1341-L1348) — lines `1341–1348`; excerpt `sha256:1efaad4cfc934457449068fdeec1040f4a4c014a88951973ae9338a1d554132d`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1165](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1165-L1165)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:136](../../paper/257/erdos-257-mersenne-support-subseries.tex#L136-L136), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:348](../../paper/257/erdos-257-mersenne-support-subseries.tex#L348-L348), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:767](../../paper/257/erdos-257-mersenne-support-subseries.tex#L767-L767)
- `erdos-synthesis-reading-together-record`: [cite at paper/synthesis/erdos-synthesis-reading-together-record.tex:231](../../paper/synthesis/erdos-synthesis-reading-together-record.tex#L231-L232)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4234](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4234-L4234), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4235](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4235-L4235), [cite at paper/reasoning-parts/erdos1049/core.tex:4209](../../paper/reasoning-parts/erdos1049/core.tex#L4209-L4209), [cite at paper/reasoning-parts/erdos1049/core.tex:4210](../../paper/reasoning-parts/erdos1049/core.tex#L4210-L4210)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:749](../../paper/archive/erdos249-257-main-paper.tex#L749-L749)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1291](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1291-L1291), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3266](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3266-L3266), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1107](../../paper/reasoning-parts/erdos257/a257_front.tex#L1107-L1107), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:3082](../../paper/reasoning-parts/erdos257/a257_front.tex#L3082-L3082)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1142-L1147) — lines `1142–1147`; excerpt `sha256:ee897c806cc6764f8001bdbab28ecd44a7ae784f93c8b76cdca0c229578e334b`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3980-L3985) — lines `3980–3985`; excerpt `sha256:ee897c806cc6764f8001bdbab28ecd44a7ae784f93c8b76cdca0c229578e334b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3948-L3953) — lines `3948–3953`; excerpt `sha256:ee897c806cc6764f8001bdbab28ecd44a7ae784f93c8b76cdca0c229578e334b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L1579-L1579) — lines `1579–1579`; excerpt `sha256:2df19ae3d0b16a50ae460b309f4d509936436c1b79c214baa753b21bb87891dd`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:400](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L400-L400), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:418](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L418-L418), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:682](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L682-L682)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:840](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L840-L841), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1611](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1611-L1611), [cite at paper/reasoning-parts/erdos243/core.tex:808](../../paper/reasoning-parts/erdos243/core.tex#L808-L809), [cite at paper/reasoning-parts/erdos243/core.tex:1579](../../paper/reasoning-parts/erdos243/core.tex#L1579-L1579)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4614-L4619) — lines `4614–4619`; excerpt `sha256:620501b65c595f397bcb8546b8f32f2dc7376a436f617b51b629ce031def07e1`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4572-L4577) — lines `4572–4577`; excerpt `sha256:620501b65c595f397bcb8546b8f32f2dc7376a436f617b51b629ce031def07e1`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L3544-L3544) — lines `3544–3544`; excerpt `sha256:018d096210a7ffec3eb82decf527d824cd58c2bd4eb4f692250cc5c4b2b8caa9`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3586](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3586-L3586), [cite at paper/reasoning-parts/erdos1041/core.tex:3544](../../paper/reasoning-parts/erdos1041/core.tex#L3544-L3544)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4565-L4570) — lines `4565–4570`; excerpt `sha256:58eae42e166b8f8a536b9cfe4c4577e41e70667815b654f00bc6a6c1c848d0dc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4540-L4545) — lines `4540–4545`; excerpt `sha256:58eae42e166b8f8a536b9cfe4c4577e41e70667815b654f00bc6a6c1c848d0dc`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2372](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2372-L2372), [cite at paper/reasoning-parts/erdos1049/core.tex:2347](../../paper/reasoning-parts/erdos1049/core.tex#L2347-L2347)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2868-L2872) — lines `2868–2872`; excerpt `sha256:0758379961a43fb0431ee76d95c75e47c003353f90b6a707964f44a842f3ea87`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2834-L2838) — lines `2834–2838`; excerpt `sha256:0758379961a43fb0431ee76d95c75e47c003353f90b6a707964f44a842f3ea87`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L326-L326) — lines `326–326`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L326-L326) — lines `326–326`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L326-L326) — lines `326–326`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L326-L326) — lines `326–326`; excerpt `sha256:1a52c485d1fdebe90cd0c446b9b2a978037b65c10e172426cb4f473a12f1a0bd`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1223-L1227) — lines `1223–1227`; excerpt `sha256:25aaa19e96eb7b41573f74f4702b9cbc37b54a817dc5039af5bd04f243600052`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1040](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1040-L1040)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:360](../../paper/68/erdos68-factorial-reasoning-surface.tex#L360-L360), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1711](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1711-L1711), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2108](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2108-L2108), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2408](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2408-L2408), [cite at paper/reasoning-parts/erdos68/core.tex:326](../../paper/reasoning-parts/erdos68/core.tex#L326-L326), [cite at paper/reasoning-parts/erdos68/core.tex:1677](../../paper/reasoning-parts/erdos68/core.tex#L1677-L1677), [cite at paper/reasoning-parts/erdos68/core.tex:2074](../../paper/reasoning-parts/erdos68/core.tex#L2074-L2074), [cite at paper/reasoning-parts/erdos68/core.tex:2374](../../paper/reasoning-parts/erdos68/core.tex#L2374-L2374)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2928-L2932) — lines `2928–2932`; excerpt `sha256:c81f5719e7e0059427c6fe7295699d3523c4215f7fe430b755be834cb594cfe9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2894-L2898) — lines `2894–2898`; excerpt `sha256:c81f5719e7e0059427c6fe7295699d3523c4215f7fe430b755be834cb594cfe9`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1636](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1636-L1636), [cite at paper/reasoning-parts/erdos68/core.tex:1602](../../paper/reasoning-parts/erdos68/core.tex#L1602-L1602)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1567-L1570) — lines `1567–1570`; excerpt `sha256:25fcd00d820b828b68dba750d3e3e88ad0a38d380b364ccab859a097d3101298`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1608-L1613) — lines `1608–1613`; excerpt `sha256:c89d595871311eec76167add03b720a82202963564fd46493036b4e96b08de98`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:894](../../paper/systems/claim-faithful-publication-systems-paper.tex#L894-L894), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1320](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1320-L1320)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:821](../../paper/systems/open-source-mathematics-strategy.tex#L821-L821), [cite at paper/systems/open-source-mathematics-strategy.tex:863](../../paper/systems/open-source-mathematics-strategy.tex#L863-L863), [cite at paper/systems/open-source-mathematics-strategy.tex:951](../../paper/systems/open-source-mathematics-strategy.tex#L951-L951)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9490-L9494) — lines `9490–9494`; excerpt `sha256:e8efab4ceb7a738eebd6f794631df1b61792fb0a00d2d6d557380dd4e37f9c41`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9320-L9324) — lines `9320–9324`; excerpt `sha256:e8efab4ceb7a738eebd6f794631df1b61792fb0a00d2d6d557380dd4e37f9c41`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7882](../../paper/249/erdos249-totient-reasoning-surface.tex#L7882-L7882), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7712](../../paper/reasoning-parts/erdos249/a249_front.tex#L7712-L7712)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4605-L4611) — lines `4605–4611`; excerpt `sha256:bd367f3dba72019c86ec01aacbc2dc2ba3af36d5b42d189d2c16647299c55964`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4580-L4586) — lines `4580–4586`; excerpt `sha256:bd367f3dba72019c86ec01aacbc2dc2ba3af36d5b42d189d2c16647299c55964`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2499](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2499-L2499), [cite at paper/reasoning-parts/erdos1049/core.tex:2474](../../paper/reasoning-parts/erdos1049/core.tex#L2474-L2474)

<a id="source-source-3a21eca35f05cf"></a>

### An analysis and survey of the development of mutation testing

- Source id: `source-3a21eca35f05cf`
- Author or public identity: Y. Jia, M. Harman
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1596-L1599) — lines `1596–1599`; excerpt `sha256:efbc6debda6e31a0cdfdb49d071c431b6d93c01f84a033351248ad1b2f3f7734`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1429](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1429-L1429)

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
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1330-L1336) — lines `1330–1336`; excerpt `sha256:f7f8625de08bee4472f7198ac41b6132a598c68fb4f2c5d046fbf4555082ef4d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L3970-L3970) — lines `3970–3970`; excerpt `sha256:9c2a91a02fdf0d919533a27cf6d9347afee25f7427ccbde7d620a561bd32d9e8`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3995-L3995) — lines `3995–3995`; excerpt `sha256:9c2a91a02fdf0d919533a27cf6d9347afee25f7427ccbde7d620a561bd32d9e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4518-L4524) — lines `4518–4524`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4543-L4549) — lines `4543–4549`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1112-L1116) — lines `1112–1116`; excerpt `sha256:a596a5a3ab90688c2d2e40605ef4e488e6632133e5a12a5f09f3821c37ac1dbd`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9505-L9509) — lines `9505–9509`; excerpt `sha256:a596a5a3ab90688c2d2e40605ef4e488e6632133e5a12a5f09f3821c37ac1dbd`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9335-L9339) — lines `9335–9339`; excerpt `sha256:a596a5a3ab90688c2d2e40605ef4e488e6632133e5a12a5f09f3821c37ac1dbd`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4543-L4549) — lines `4543–4549`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4518-L4524) — lines `4518–4524`; excerpt `sha256:44a0e3e721340d6f0b081dd1ebb6cd8cae7f421a3666d648a9c42a21cc2d2f00`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1185](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1185-L1185)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:800](../../paper/249/erdos-249-binary-totient-series.tex#L800-L800)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3923](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3923-L3923), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4485](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4485-L4485), [cite at paper/reasoning-parts/erdos1049/core.tex:3898](../../paper/reasoning-parts/erdos1049/core.tex#L3898-L3898), [cite at paper/reasoning-parts/erdos1049/core.tex:4460](../../paper/reasoning-parts/erdos1049/core.tex#L4460-L4460)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3192](../../paper/archive/erdos249-257-main-paper.tex#L3192-L3192)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9318](../../paper/249/erdos249-totient-reasoning-surface.tex#L9318-L9318), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9148](../../paper/reasoning-parts/erdos249/a249_front.tex#L9148-L9148)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9457-L9463) — lines `9457–9463`; excerpt `sha256:5ea3e979eefb577068ea145beb2c4d5913b323a0f5a413f315280b716ec5eb58`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9287-L9293) — lines `9287–9293`; excerpt `sha256:5ea3e979eefb577068ea145beb2c4d5913b323a0f5a413f315280b716ec5eb58`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7772](../../paper/249/erdos249-totient-reasoning-surface.tex#L7772-L7772), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7602](../../paper/reasoning-parts/erdos249/a249_front.tex#L7602-L7602)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1207-L1211) — lines `1207–1211`; excerpt `sha256:01afe33226c434943312f632a5b1272516885eec61dfda3c99448c38f71ab1f1`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2912-L2916) — lines `2912–2916`; excerpt `sha256:01afe33226c434943312f632a5b1272516885eec61dfda3c99448c38f71ab1f1`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2878-L2882) — lines `2878–2882`; excerpt `sha256:01afe33226c434943312f632a5b1272516885eec61dfda3c99448c38f71ab1f1`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1025](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1025-L1025)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:281](../../paper/68/erdos68-factorial-reasoning-surface.tex#L281-L281), [cite at paper/reasoning-parts/erdos68/core.tex:247](../../paper/reasoning-parts/erdos68/core.tex#L247-L247)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4595-L4601) — lines `4595–4601`; excerpt `sha256:428989f59406f939d2c86c6f7824295f410f97de0a786684b7faeddbd01f4a71`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4553-L4559) — lines `4553–4559`; excerpt `sha256:428989f59406f939d2c86c6f7824295f410f97de0a786684b7faeddbd01f4a71`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1776-L1782) — lines `1776–1782`; excerpt `sha256:cd02a3f4bd4ab2831d4e82f0258f2e99b98627ee1ba71dc7fcd33aaae61f7342`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:354](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L354-L354), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:750](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L750-L750), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1663](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1663-L1663)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:324](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L324-L324), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:728](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L728-L728), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:837](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L837-L837), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:997](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L997-L997), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1070](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1070-L1070), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1234](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1234-L1234), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1234](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1234-L1234), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1571](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1571-L1571), [cite at paper/reasoning-parts/erdos1041/core.tex:282](../../paper/reasoning-parts/erdos1041/core.tex#L282-L282), [cite at paper/reasoning-parts/erdos1041/core.tex:686](../../paper/reasoning-parts/erdos1041/core.tex#L686-L686), [cite at paper/reasoning-parts/erdos1041/core.tex:795](../../paper/reasoning-parts/erdos1041/core.tex#L795-L795), [cite at paper/reasoning-parts/erdos1041/core.tex:955](../../paper/reasoning-parts/erdos1041/core.tex#L955-L955), [cite at paper/reasoning-parts/erdos1041/core.tex:1028](../../paper/reasoning-parts/erdos1041/core.tex#L1028-L1028), [cite at paper/reasoning-parts/erdos1041/core.tex:1192](../../paper/reasoning-parts/erdos1041/core.tex#L1192-L1192), [cite at paper/reasoning-parts/erdos1041/core.tex:1192](../../paper/reasoning-parts/erdos1041/core.tex#L1192-L1192), [cite at paper/reasoning-parts/erdos1041/core.tex:1529](../../paper/reasoning-parts/erdos1041/core.tex#L1529-L1529)

<a id="source-source-41df26fdff66cb"></a>

### [On the irrationality of certain super-polynomially decaying series](https://arxiv.org/abs/2504.18712v1)

- Source id: `source-41df26fdff66cb`
- Author or public identity: Tonći Crmarić, Vjekoslav Kovač
- Kind: `literature`
- Problems: #243, #251
- Relationship and boundary: Full text of the specified source object/passage was read; this is not independent refereeing of the complete article.
- Source verification: `source\_verified` — full\_text
- Local mapping: `not recorded`

Exact source locations:

- [Theorems 1 and 2, arXiv pp. 2–3](https://arxiv.org/abs/2504.18712v1)
- [Construction and measure arguments, §§2–3](https://arxiv.org/abs/2504.18712v1)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1200-L1206) — lines `1200–1206`; excerpt `sha256:94123b672bbe246ca5a1da5c42f627ccc32ae5d9d6727e40019a7798db0120de`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4054-L4060) — lines `4054–4060`; excerpt `sha256:94123b672bbe246ca5a1da5c42f627ccc32ae5d9d6727e40019a7798db0120de`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4022-L4028) — lines `4022–4028`; excerpt `sha256:94123b672bbe246ca5a1da5c42f627ccc32ae5d9d6727e40019a7798db0120de`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L805-L807) — lines `805–807`; excerpt `sha256:828f4da9714361921bc80071c0a1ee81ffb2c4cd7328ba82c26137466ef09a38`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3021-L3023) — lines `3021–3023`; excerpt `sha256:828f4da9714361921bc80071c0a1ee81ffb2c4cd7328ba82c26137466ef09a38`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2981-L2983) — lines `2981–2983`; excerpt `sha256:828f4da9714361921bc80071c0a1ee81ffb2c4cd7328ba82c26137466ef09a38`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:931](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L931-L931)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:203](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L203-L203), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:327](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L327-L327)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:921](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L921-L921), [cite at paper/reasoning-parts/erdos243/core.tex:889](../../paper/reasoning-parts/erdos243/core.tex#L889-L889)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:325](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L325-L325), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:543](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L543-L543), [cite at paper/reasoning-parts/erdos251/core.tex:285](../../paper/reasoning-parts/erdos251/core.tex#L285-L285), [cite at paper/reasoning-parts/erdos251/core.tex:503](../../paper/reasoning-parts/erdos251/core.tex#L503-L503)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1419-L1422) — lines `1419–1422`; excerpt `sha256:8fe2d89da58a1e4e231d39f70b8dc5e5e218e128f6a1964d09e9a63a746e2b0a`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2852-L2856) — lines `2852–2856`; excerpt `sha256:b938d408a670bde68b8522a01fa71ee3a1b30b4fbb78368431f5fb9cded5f0f9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2818-L2822) — lines `2818–2822`; excerpt `sha256:b938d408a670bde68b8522a01fa71ee3a1b30b4fbb78368431f5fb9cded5f0f9`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:779](../../paper/257/erdos-257-mersenne-support-subseries.tex#L779-L779)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1939](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1939-L1939), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2117](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2117-L2117), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2321](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2321-L2321), [cite at paper/reasoning-parts/erdos68/core.tex:1905](../../paper/reasoning-parts/erdos68/core.tex#L1905-L1905), [cite at paper/reasoning-parts/erdos68/core.tex:2083](../../paper/reasoning-parts/erdos68/core.tex#L2083-L2083), [cite at paper/reasoning-parts/erdos68/core.tex:2287](../../paper/reasoning-parts/erdos68/core.tex#L2287-L2287)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1846-L1850) — lines `1846–1850`; excerpt `sha256:39a146bf8942c0ebb786121a43c32dbc5f98a38f4e25cf1cd5d5a0c9459ff405`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4717-L4721) — lines `4717–4721`; excerpt `sha256:c7daa6ecb347084bcfff886434d3ee286e92a61de85db715bfea9f6822a2669b`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4675-L4679) — lines `4675–4679`; excerpt `sha256:c7daa6ecb347084bcfff886434d3ee286e92a61de85db715bfea9f6822a2669b`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:827](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L827-L827), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1405](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1405-L1405), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1593](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1593-L1594)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1030](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1030-L1030), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2703](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2703-L2703), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3322](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3322-L3322), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3449](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3449-L3449), [cite at paper/reasoning-parts/erdos1041/core.tex:988](../../paper/reasoning-parts/erdos1041/core.tex#L988-L988), [cite at paper/reasoning-parts/erdos1041/core.tex:2661](../../paper/reasoning-parts/erdos1041/core.tex#L2661-L2661), [cite at paper/reasoning-parts/erdos1041/core.tex:3280](../../paper/reasoning-parts/erdos1041/core.tex#L3280-L3280), [cite at paper/reasoning-parts/erdos1041/core.tex:3407](../../paper/reasoning-parts/erdos1041/core.tex#L3407-L3407)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3033-L3035) — lines `3033–3035`; excerpt `sha256:c13202ba0e0b2c61e1309389eeaf97212f8f3b05eea87b49c4ad2e8748454dc3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2993-L2995) — lines `2993–2995`; excerpt `sha256:c13202ba0e0b2c61e1309389eeaf97212f8f3b05eea87b49c4ad2e8748454dc3`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:633](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L633-L633), [cite at paper/reasoning-parts/erdos251/core.tex:593](../../paper/reasoning-parts/erdos251/core.tex#L593-L593)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L679-L682) — lines `679–682`; excerpt `sha256:facbf8174f29ec644aa87ad59cf5ec179262bc093a6f37a813598d55c1c8af77`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:472](../../paper/systems/cold-clone-to-proof-receipt.tex#L472-L472)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1340-L1345) — lines `1340–1345`; excerpt `sha256:b72eaf7771719b0f871cf252ff08d155c348754cbbc333e06e0587f20db646de`

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4597-L4605) — lines `4597–4605`; excerpt `sha256:17a9f0c77da491dc851c4a65e945725b1c61e75da287cb94849f3bb840ee6c33`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4572-L4580) — lines `4572–4580`; excerpt `sha256:17a9f0c77da491dc851c4a65e945725b1c61e75da287cb94849f3bb840ee6c33`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2246](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2246-L2246), [cite at paper/reasoning-parts/erdos1049/core.tex:2221](../../paper/reasoning-parts/erdos1049/core.tex#L2221-L2221)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9515-L9522) — lines `9515–9522`; excerpt `sha256:c412b56a71492694abbd8a4bb30d4b12dd25d5050689bc96bb8d162c095f07c6`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9345-L9352) — lines `9345–9352`; excerpt `sha256:c412b56a71492694abbd8a4bb30d4b12dd25d5050689bc96bb8d162c095f07c6`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L807-L809) — lines `807–809`; excerpt `sha256:6e5c026e217aafc0c8b121d5e6586f0139ff79cbf8c2871b89cdc840c4041993`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3023-L3025) — lines `3023–3025`; excerpt `sha256:6e5c026e217aafc0c8b121d5e6586f0139ff79cbf8c2871b89cdc840c4041993`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2983-L2985) — lines `2983–2985`; excerpt `sha256:6e5c026e217aafc0c8b121d5e6586f0139ff79cbf8c2871b89cdc840c4041993`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:759](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L759-L759)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9326](../../paper/249/erdos249-totient-reasoning-surface.tex#L9326-L9326), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9156](../../paper/reasoning-parts/erdos249/a249_front.tex#L9156-L9156)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:620](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L620-L620), [cite at paper/reasoning-parts/erdos251/core.tex:580](../../paper/reasoning-parts/erdos251/core.tex#L580-L580)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1410-L1415) — lines `1410–1415`; excerpt `sha256:25cf3513f78fba977dc2a6cefb4a67e70b7815d304207cbac09e637aaa5db383`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1208](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1208-L1208)

<a id="source-source-4c664304e00cd3"></a>

### [Toward Auditable AI Scientists: A Hypothesis Evolution Protocol for LLM Agents](https://doi.org/10.48550/arXiv.2607.09195)

- Source id: `source-4c664304e00cd3`
- Author or public identity: I. Takahara, T. Mizoguchi
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1621-L1624) — lines `1621–1624`; excerpt `sha256:f8672f9682d847ef8ecd3bf492f33dc58169ae1bc0f90b355f3f23a9dd953bff`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1418](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1418-L1418)

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
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3998-L4005) — lines `3998–4005`; excerpt `sha256:cc6aca2237133e921cd97b74d25252bfe07f4ac85f0f29888f9c09d741fbe072`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L779-L781) — lines `779–781`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2989-L2991) — lines `2989–2991`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1404-L1408) — lines `1404–1408`; excerpt `sha256:da365fb3627d4a62500ab14506a5fa9a7c61368c1f67b75982752d2ba474ccc5`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2976-L2979) — lines `2976–2979`; excerpt `sha256:20b55c219bde90eb922d16a4e4e7195151a7a94f401f50f85e1f72c5e3a46342`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4531-L4538) — lines `4531–4538`; excerpt `sha256:31734bb5dbd8d4b44ac368c926cf6ce72c577a3e05d74dab77682764ee7da3da`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4506-L4513) — lines `4506–4513`; excerpt `sha256:31734bb5dbd8d4b44ac368c926cf6ce72c577a3e05d74dab77682764ee7da3da`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4235-L4235) — lines `4235–4235`; excerpt `sha256:1102bfe9b1f75f0d5960a2f3d22f55f277c362853922162565b2ad5506af83b9`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3966-L3973) — lines `3966–3973`; excerpt `sha256:cc6aca2237133e921cd97b74d25252bfe07f4ac85f0f29888f9c09d741fbe072`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L871-L871) — lines `871–871`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L871-L871) — lines `871–871`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L871-L871) — lines `871–871`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2949-L2951) — lines `2949–2951`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L288-L288) — lines `288–288`; excerpt `sha256:e38cfe37c091ed4d54a9bcc39dbb67a8262dd704b46157bbb80c32da2db1a529`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2931-L2934) — lines `2931–2934`; excerpt `sha256:20b55c219bde90eb922d16a4e4e7195151a7a94f401f50f85e1f72c5e3a46342`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L111-L111) — lines `111–111`; excerpt `sha256:6c25d2b2b7888daf62b5ab292babae6e65eda1f261a7ee1c25d93397f886f920`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L82-L82) — lines `82–82`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1034-L1034) — lines `1034–1034`; excerpt `sha256:2f13d854d17862e3e84cfe8260e36f3e508b7165189455204d23c133aeac237e`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L603-L613) — lines `603–613`; excerpt `sha256:c989aa24e7d0cd4a81a2207dea6e4647a9e1d349d2fb8a86a8fcd45cc9386fd7`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L208-L208) — lines `208–208`; excerpt `sha256:6f8969654fea1cb47d7ba3861a42ba34927ee62b8f04a937e3d1c7026be242d8`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L208-L208) — lines `208–208`; excerpt `sha256:6f8969654fea1cb47d7ba3861a42ba34927ee62b8f04a937e3d1c7026be242d8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L288-L288) — lines `288–288`; excerpt `sha256:e38cfe37c091ed4d54a9bcc39dbb67a8262dd704b46157bbb80c32da2db1a529`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L288-L288) — lines `288–288`; excerpt `sha256:e38cfe37c091ed4d54a9bcc39dbb67a8262dd704b46157bbb80c32da2db1a529`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L288-L288) — lines `288–288`; excerpt `sha256:e38cfe37c091ed4d54a9bcc39dbb67a8262dd704b46157bbb80c32da2db1a529`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L328-L328) — lines `328–328`; excerpt `sha256:e38cfe37c091ed4d54a9bcc39dbb67a8262dd704b46157bbb80c32da2db1a529`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L328-L328) — lines `328–328`; excerpt `sha256:e38cfe37c091ed4d54a9bcc39dbb67a8262dd704b46157bbb80c32da2db1a529`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L328-L328) — lines `328–328`; excerpt `sha256:e38cfe37c091ed4d54a9bcc39dbb67a8262dd704b46157bbb80c32da2db1a529`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9431-L9437) — lines `9431–9437`; excerpt `sha256:aa7e7a743f9042755d99379ed9c411c18d6b86186718b25aa42a57c133a0f41e`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9261-L9267) — lines `9261–9267`; excerpt `sha256:aa7e7a743f9042755d99379ed9c411c18d6b86186718b25aa42a57c133a0f41e`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L779-L781) — lines `779–781`; excerpt `sha256:1386a45340d81984e945f5e55245e8ffbe9117cc649c342ae293feaf6fea972a`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L844-L847) — lines `844–847`; excerpt `sha256:9c3c5db10d94904b54c40a45565db137f38253e6cc98c36fb7f0446f37302911`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:208](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L208-L208), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:328](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L328-L328)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:814](../../paper/257/erdos-257-mersenne-support-subseries.tex#L814-L814)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:698](../../paper/269/erdos-269-three-prime-running-lcm.tex#L698-L698)
- `erdos-synthesis-subsums-across-bases`: [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:94](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L94-L94), [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:120](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L120-L120), [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:210](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L210-L210), [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:223](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L223-L223)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4260](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4260-L4260), [cite at paper/reasoning-parts/erdos1049/core.tex:4235](../../paper/reasoning-parts/erdos1049/core.tex#L4235-L4235)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:903](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L903-L903), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:906](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L906-L906), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:915](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L915-L915), [cite at paper/reasoning-parts/erdos243/core.tex:871](../../paper/reasoning-parts/erdos243/core.tex#L871-L871), [cite at paper/reasoning-parts/erdos243/core.tex:874](../../paper/reasoning-parts/erdos243/core.tex#L874-L874), [cite at paper/reasoning-parts/erdos243/core.tex:883](../../paper/reasoning-parts/erdos243/core.tex#L883-L883)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:835](../../paper/archive/erdos249-257-main-paper.tex#L835-L835), [cite at paper/archive/erdos249-257-main-paper.tex:836](../../paper/archive/erdos249-257-main-paper.tex#L836-L836), [cite at paper/archive/erdos249-257-main-paper.tex:2157](../../paper/archive/erdos249-257-main-paper.tex#L2157-L2157), [cite at paper/archive/erdos249-257-main-paper.tex:4676](../../paper/archive/erdos249-257-main-paper.tex#L4676-L4676), [cite at paper/archive/erdos249-257-main-paper.tex:5067](../../paper/archive/erdos249-257-main-paper.tex#L5067-L5067), [cite at paper/archive/erdos249-257-main-paper.tex:5113](../../paper/archive/erdos249-257-main-paper.tex#L5113-L5113)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9294](../../paper/249/erdos249-totient-reasoning-surface.tex#L9294-L9294), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9124](../../paper/reasoning-parts/erdos249/a249_front.tex#L9124-L9124)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:328](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L328-L328), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:552](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L552-L552), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:665](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L665-L665), [cite at paper/reasoning-parts/erdos251/core.tex:288](../../paper/reasoning-parts/erdos251/core.tex#L288-L288), [cite at paper/reasoning-parts/erdos251/core.tex:512](../../paper/reasoning-parts/erdos251/core.tex#L512-L512), [cite at paper/reasoning-parts/erdos251/core.tex:625](../../paper/reasoning-parts/erdos251/core.tex#L625-L625)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9336](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9336-L9336), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9152](../../paper/reasoning-parts/erdos257/a257_front.tex#L9152-L9152)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:156](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L156-L156), [cite at paper/reasoning-parts/erdos269/core.tex:111](../../paper/reasoning-parts/erdos269/core.tex#L111-L111)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1199-L1203) — lines `1199–1203`; excerpt `sha256:c1feb1fd30f80a42ea7b93c301207ea72abff8a1961dc7646ef336d6bf938b73`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2904-L2908) — lines `2904–2908`; excerpt `sha256:c1feb1fd30f80a42ea7b93c301207ea72abff8a1961dc7646ef336d6bf938b73`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2870-L2874) — lines `2870–2874`; excerpt `sha256:c1feb1fd30f80a42ea7b93c301207ea72abff8a1961dc7646ef336d6bf938b73`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1052](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1052-L1052)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:460](../../paper/68/erdos68-factorial-reasoning-surface.tex#L460-L460), [cite at paper/reasoning-parts/erdos68/core.tex:426](../../paper/reasoning-parts/erdos68/core.tex#L426-L426)

<a id="source-source-51efe25c48a86d"></a>

### Isabelle/DOF: Design and Implementation

- Source id: `source-51efe25c48a86d`
- Author or public identity: A. D. Brucker, B. Wolff
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1588-L1591) — lines `1588–1591`; excerpt `sha256:b538f4cc62eabdb4674393f8df9e52b4043594fc2724cb91a6cd99b1cda26ac5`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1411](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1411-L1411)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3003-L3006) — lines `3003–3006`; excerpt `sha256:53305164d06918956b307b2a2bd9e37d95e4d93aff557246b8ebc65eee173fbd`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2958-L2961) — lines `2958–2961`; excerpt `sha256:53305164d06918956b307b2a2bd9e37d95e4d93aff557246b8ebc65eee173fbd`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1802](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1802-L1802), [cite at paper/reasoning-parts/erdos269/core.tex:1757](../../paper/reasoning-parts/erdos269/core.tex#L1757-L1757)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1381-L1385) — lines `1381–1385`; excerpt `sha256:f1b2f72f71f3c59cf3228251451f17d759ad32698b19f9a76233084f8239a615`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4611-L4615) — lines `4611–4615`; excerpt `sha256:3b958d96041c8d7357ca2a6320bad4a5c5dd5c24e66c13f3fdcb75343dfb1596`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4586-L4590) — lines `4586–4590`; excerpt `sha256:3b958d96041c8d7357ca2a6320bad4a5c5dd5c24e66c13f3fdcb75343dfb1596`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1178](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1178-L1178)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2367](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2367-L2367), [cite at paper/reasoning-parts/erdos1049/core.tex:2342](../../paper/reasoning-parts/erdos1049/core.tex#L2342-L2342)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2964-L2967) — lines `2964–2967`; excerpt `sha256:dad66e1d91ee56df1368adfe2ef9592eef350506274c14cc06dcf5ad03ef77ed`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2919-L2922) — lines `2919–2922`; excerpt `sha256:dad66e1d91ee56df1368adfe2ef9592eef350506274c14cc06dcf5ad03ef77ed`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2478-L2478) — lines `2478–2478`; excerpt `sha256:70156aa149e95bc051830fe62c9e4dead62a9dfae84a47de933e386647c09bdb`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2478-L2478) — lines `2478–2478`; excerpt `sha256:70156aa149e95bc051830fe62c9e4dead62a9dfae84a47de933e386647c09bdb`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2523-L2523) — lines `2523–2523`; excerpt `sha256:70156aa149e95bc051830fe62c9e4dead62a9dfae84a47de933e386647c09bdb`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2523](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2523-L2523), [cite at paper/reasoning-parts/erdos269/core.tex:2478](../../paper/reasoning-parts/erdos269/core.tex#L2478-L2478)

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
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1063-L1067) — lines `1063–1067`; excerpt `sha256:822cceaa2102882ca659544f6f24812353e6082e3f3fd963beaa90ce4be4a49a`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9358-L9363) — lines `9358–9363`; excerpt `sha256:1faa5900afcaadc94dc78596f20f82bc542cdeea10be862bbe3be3e9ca92f21f`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9188-L9193) — lines `9188–9193`; excerpt `sha256:1faa5900afcaadc94dc78596f20f82bc542cdeea10be862bbe3be3e9ca92f21f`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:60](../../paper/249/erdos-249-binary-totient-series.tex#L60-L60), [cite at paper/249/erdos-249-binary-totient-series.tex:774](../../paper/249/erdos-249-binary-totient-series.tex#L774-L774)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3184](../../paper/archive/erdos249-257-main-paper.tex#L3184-L3184)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8405](../../paper/249/erdos249-totient-reasoning-surface.tex#L8405-L8405), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8235](../../paper/reasoning-parts/erdos249/a249_front.tex#L8235-L8235)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1187-L1191) — lines `1187–1191`; excerpt `sha256:00f686cb4c9f7ec34f4862095318a0388b914d486a42bca48ec232dec92aebc4`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2896-L2900) — lines `2896–2900`; excerpt `sha256:e82d9607acf436d2f4aa8d7afad731fa862ecbfa84e051d3b8579701aa30e049`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2862-L2866) — lines `2862–2866`; excerpt `sha256:e82d9607acf436d2f4aa8d7afad731fa862ecbfa84e051d3b8579701aa30e049`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1028-L1028) — lines `1028–1028`; excerpt `sha256:5a48d6023f1855be2f3774034893f39527bd7050de870649fd617f22912ee186`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1028-L1028) — lines `1028–1028`; excerpt `sha256:5a48d6023f1855be2f3774034893f39527bd7050de870649fd617f22912ee186`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L244-L244) — lines `244–244`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L244-L244) — lines `244–244`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L242-L242) — lines `242–242`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L244-L244) — lines `244–244`; excerpt `sha256:833f277049f234d19cee90708049d8bb8d106262d2830e645962cc3683abfb63`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1028](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1028-L1028), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1032](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1032-L1032)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:278](../../paper/68/erdos68-factorial-reasoning-surface.tex#L278-L278), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:372](../../paper/68/erdos68-factorial-reasoning-surface.tex#L372-L372), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2111](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2111-L2111), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2114](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2114-L2114), [cite at paper/reasoning-parts/erdos68/core.tex:244](../../paper/reasoning-parts/erdos68/core.tex#L244-L244), [cite at paper/reasoning-parts/erdos68/core.tex:338](../../paper/reasoning-parts/erdos68/core.tex#L338-L338), [cite at paper/reasoning-parts/erdos68/core.tex:2077](../../paper/reasoning-parts/erdos68/core.tex#L2077-L2077), [cite at paper/reasoning-parts/erdos68/core.tex:2080](../../paper/reasoning-parts/erdos68/core.tex#L2080-L2080)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1838-L1843) — lines `1838–1843`; excerpt `sha256:9976334d2d074f47b0f36053eafc88c2da992e02c4c4c2eb6956f0ecc319a48b`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4709-L4714) — lines `4709–4714`; excerpt `sha256:9976334d2d074f47b0f36053eafc88c2da992e02c4c4c2eb6956f0ecc319a48b`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4667-L4672) — lines `4667–4672`; excerpt `sha256:9976334d2d074f47b0f36053eafc88c2da992e02c4c4c2eb6956f0ecc319a48b`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1675](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1675-L1675)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1142](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1142-L1142), [cite at paper/reasoning-parts/erdos1041/core.tex:1100](../../paper/reasoning-parts/erdos1041/core.tex#L1100-L1100)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4549-L4553) — lines `4549–4553`; excerpt `sha256:1f93dd63fdcecc1c50a9e4192bb21b88580fe393bef2b1a4a2bd32200489b8f2`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4524-L4528) — lines `4524–4528`; excerpt `sha256:1f93dd63fdcecc1c50a9e4192bb21b88580fe393bef2b1a4a2bd32200489b8f2`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1692](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1692-L1692), [cite at paper/reasoning-parts/erdos1049/core.tex:1667](../../paper/reasoning-parts/erdos1049/core.tex#L1667-L1667)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4507-L4512) — lines `4507–4512`; excerpt `sha256:8145c4e8df8a670bb4c71753052c607b975795318f4a6fdaaed256f6644f773f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4482-L4487) — lines `4482–4487`; excerpt `sha256:8145c4e8df8a670bb4c71753052c607b975795318f4a6fdaaed256f6644f773f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4198-L4198) — lines `4198–4198`; excerpt `sha256:4cba849220b6d89a05527440677a635fe05b976de1d3d125b3c7d9e3b37a61fe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4198-L4198) — lines `4198–4198`; excerpt `sha256:4cba849220b6d89a05527440677a635fe05b976de1d3d125b3c7d9e3b37a61fe`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1336-L1341) — lines `1336–1341`; excerpt `sha256:8d3a5a9309dacce42b935afcf56eac11bf777dafe926a5de5f7e5dbb71726aca`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1163](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1163-L1163)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4223](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4223-L4223), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4226](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4226-L4226), [cite at paper/reasoning-parts/erdos1049/core.tex:4198](../../paper/reasoning-parts/erdos1049/core.tex#L4198-L4198), [cite at paper/reasoning-parts/erdos1049/core.tex:4201](../../paper/reasoning-parts/erdos1049/core.tex#L4201-L4201)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1329-L1335) — lines `1329–1335`; excerpt `sha256:0b4c870e91ea3111d69ea85b7c94783a709618f7b2b3124f463426effcfb8ffc`

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
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1408-L1410) — lines `1408–1410`; excerpt `sha256:12e925bb796b6215db708d25b5d1ab1c5640c351e7f3683e2c91ae968206b259`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4397-L4401) — lines `4397–4401`; excerpt `sha256:cf446c3cbb0c405bcc80ec2c25d599a8a83cd781fed2f9312d32338c1383374d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4372-L4376) — lines `4372–4376`; excerpt `sha256:cf446c3cbb0c405bcc80ec2c25d599a8a83cd781fed2f9312d32338c1383374d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L53-L53) — lines `53–53`; excerpt `sha256:2c27f9ef016823a6835d8c951b5c7a9752e557fa2220d82721e7a4885081d6ca`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L53-L53) — lines `53–53`; excerpt `sha256:2c27f9ef016823a6835d8c951b5c7a9752e557fa2220d82721e7a4885081d6ca`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L53-L53) — lines `53–53`; excerpt `sha256:2c27f9ef016823a6835d8c951b5c7a9752e557fa2220d82721e7a4885081d6ca`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L2028-L2028) — lines `2028–2028`; excerpt `sha256:774210986ed7b0796074293d40767210bab87f09c6be3458577f12648221827d`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L794-L794) — lines `794–794`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
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
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9394-L9398) — lines `9394–9398`; excerpt `sha256:83ff6ef68815bf0b391a143e9e5336b1ff5b127bd0fbcac01ed9f7a399d02225`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9224-L9228) — lines `9224–9228`; excerpt `sha256:83ff6ef68815bf0b391a143e9e5336b1ff5b127bd0fbcac01ed9f7a399d02225`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9694-L9697) — lines `9694–9697`; excerpt `sha256:7a684bfaefd18d542b221d902849314551f3d7d7c0bdd860824a938e6896ecd7`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9510-L9513) — lines `9510–9513`; excerpt `sha256:7a684bfaefd18d542b221d902849314551f3d7d7c0bdd860824a938e6896ecd7`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:760](../../paper/257/erdos-257-mersenne-support-subseries.tex#L760-L760)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:78](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L78-L78), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3087](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3087-L3087), [cite at paper/reasoning-parts/erdos1049/core.tex:53](../../paper/reasoning-parts/erdos1049/core.tex#L53-L53), [cite at paper/reasoning-parts/erdos1049/core.tex:3062](../../paper/reasoning-parts/erdos1049/core.tex#L3062-L3062)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:115](../../paper/archive/erdos249-257-main-paper.tex#L115-L115), [cite at paper/archive/erdos249-257-main-paper.tex:630](../../paper/archive/erdos249-257-main-paper.tex#L630-L630), [cite at paper/archive/erdos249-257-main-paper.tex:633](../../paper/archive/erdos249-257-main-paper.tex#L633-L633)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1560](../../paper/249/erdos249-totient-reasoning-surface.tex#L1560-L1560), [cite at paper/249/erdos249-totient-reasoning-surface.tex:1582](../../paper/249/erdos249-totient-reasoning-surface.tex#L1582-L1582), [cite at paper/249/erdos249-totient-reasoning-surface.tex:5681](../../paper/249/erdos249-totient-reasoning-surface.tex#L5681-L5681), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7796](../../paper/249/erdos249-totient-reasoning-surface.tex#L7796-L7796), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7807](../../paper/249/erdos249-totient-reasoning-surface.tex#L7807-L7807), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1390](../../paper/reasoning-parts/erdos249/a249_front.tex#L1390-L1390), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1412](../../paper/reasoning-parts/erdos249/a249_front.tex#L1412-L1412), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:5511](../../paper/reasoning-parts/erdos249/a249_front.tex#L5511-L5511), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7626](../../paper/reasoning-parts/erdos249/a249_front.tex#L7626-L7626), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7637](../../paper/reasoning-parts/erdos249/a249_front.tex#L7637-L7637)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:978](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L978-L978), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1288](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1288-L1288), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2974](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2974-L2974), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:6990](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L6990-L6990), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:794](../../paper/reasoning-parts/erdos257/a257_front.tex#L794-L794), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1104](../../paper/reasoning-parts/erdos257/a257_front.tex#L1104-L1104), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2790](../../paper/reasoning-parts/erdos257/a257_front.tex#L2790-L2790), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:6806](../../paper/reasoning-parts/erdos257/a257_front.tex#L6806-L6806)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9486-L9490) — lines `9486–9490`; excerpt `sha256:77de149e1b9e4c1cbd9c39690b007e9959c56e7732149a19d644b96ce9c396c8`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9316-L9320) — lines `9316–9320`; excerpt `sha256:77de149e1b9e4c1cbd9c39690b007e9959c56e7732149a19d644b96ce9c396c8`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:4265](../../paper/249/erdos249-totient-reasoning-surface.tex#L4265-L4265), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:4095](../../paper/reasoning-parts/erdos249/a249_front.tex#L4095-L4095)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1587-L1592) — lines `1587–1592`; excerpt `sha256:573f52e0c7b894eeeb44cdeb82b9844001ad1c0155ff50cf96d645b233996e9d`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:519](../../paper/systems/open-source-mathematics-strategy.tex#L519-L519), [cite at paper/systems/open-source-mathematics-strategy.tex:925](../../paper/systems/open-source-mathematics-strategy.tex#L925-L925)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2987-L2989) — lines `2987–2989`; excerpt `sha256:46d4d39e3d51b2837c93b4e701c6caaf1022bcecb3c0b0c8dcc4e198022fc852`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2947-L2949) — lines `2947–2949`; excerpt `sha256:46d4d39e3d51b2837c93b4e701c6caaf1022bcecb3c0b0c8dcc4e198022fc852`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3006-L3009) — lines `3006–3009`; excerpt `sha256:3bb82e6b41bc7ebd606d251e5b57d3c92e82927c527268e1c978c3131c24c529`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2961-L2964) — lines `2961–2964`; excerpt `sha256:3bb82e6b41bc7ebd606d251e5b57d3c92e82927c527268e1c978c3131c24c529`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1299](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1299-L1299), [cite at paper/reasoning-parts/erdos251/core.tex:1259](../../paper/reasoning-parts/erdos251/core.tex#L1259-L1259)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1786](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1786-L1786), [cite at paper/reasoning-parts/erdos269/core.tex:1741](../../paper/reasoning-parts/erdos269/core.tex#L1741-L1741)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1191-L1195) — lines `1191–1195`; excerpt `sha256:7eb810a856d8371d607b27c13d08cdb1e45b57dea452204683e677e9ad4ad61e`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2892-L2896) — lines `2892–2896`; excerpt `sha256:dd044dad6d56b9bf4fbea7b10c5f1541732d45804e9ab24eba3d70dc193802b7`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2858-L2862) — lines `2858–2862`; excerpt `sha256:dd044dad6d56b9bf4fbea7b10c5f1541732d45804e9ab24eba3d70dc193802b7`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1027-L1027) — lines `1027–1027`; excerpt `sha256:55a7beff732036d1316e71ccdb2ac3e30f0efb34f59c68e9268ff53a400e009a`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1027-L1027) — lines `1027–1027`; excerpt `sha256:55a7beff732036d1316e71ccdb2ac3e30f0efb34f59c68e9268ff53a400e009a`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L242-L242) — lines `242–242`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L242-L242) — lines `242–242`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L242-L242) — lines `242–242`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L242-L242) — lines `242–242`; excerpt `sha256:e52805e976c27402da4d5287575f00f9b1b37c362bb1528322e7c65132fd96e3`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1027](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1027-L1027), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1033](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1033-L1033)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:276](../../paper/68/erdos68-factorial-reasoning-surface.tex#L276-L276), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:371](../../paper/68/erdos68-factorial-reasoning-surface.tex#L371-L371), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2111](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2111-L2111), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2113](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2113-L2113), [cite at paper/reasoning-parts/erdos68/core.tex:242](../../paper/reasoning-parts/erdos68/core.tex#L242-L242), [cite at paper/reasoning-parts/erdos68/core.tex:337](../../paper/reasoning-parts/erdos68/core.tex#L337-L337), [cite at paper/reasoning-parts/erdos68/core.tex:2077](../../paper/reasoning-parts/erdos68/core.tex#L2077-L2077), [cite at paper/reasoning-parts/erdos68/core.tex:2079](../../paper/reasoning-parts/erdos68/core.tex#L2079-L2079)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L685-L688) — lines `685–688`; excerpt `sha256:6e5e795918967c2ca83bcb0a103c3da562b3b3aa08b5719dc822b75f46a612b9`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:475](../../paper/systems/cold-clone-to-proof-receipt.tex#L475-L475)

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
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L82-L82) — lines `82–82`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9419-L9426) — lines `9419–9426`; excerpt `sha256:168b06eeef0d655602ef10d79d4d5a2c298c562e5b09b730a812b94d0458d1a2`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9249-L9256) — lines `9249–9256`; excerpt `sha256:168b06eeef0d655602ef10d79d4d5a2c298c562e5b09b730a812b94d0458d1a2`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:500](../../paper/archive/erdos249-257-main-paper.tex#L500-L500), [cite at paper/archive/erdos249-257-main-paper.tex:4086](../../paper/archive/erdos249-257-main-paper.tex#L4086-L4086), [cite at paper/archive/erdos249-257-main-paper.tex:4785](../../paper/archive/erdos249-257-main-paper.tex#L4785-L4785)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1609](../../paper/249/erdos249-totient-reasoning-surface.tex#L1609-L1610), [cite at paper/249/erdos249-totient-reasoning-surface.tex:9297](../../paper/249/erdos249-totient-reasoning-surface.tex#L9297-L9297), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1439](../../paper/reasoning-parts/erdos249/a249_front.tex#L1439-L1440), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9127](../../paper/reasoning-parts/erdos249/a249_front.tex#L9127-L9127)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1752-L1756) — lines `1752–1756`; excerpt `sha256:eacde95a2a008044b34dad3bc740d3a6e33953232b7364e5c222730a382b3f1e`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4603-L4607) — lines `4603–4607`; excerpt `sha256:b88bf461b59f2aca4fbd717fe1f7fae9a31ad41586223d8984be19883d35f1de`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4561-L4565) — lines `4561–4565`; excerpt `sha256:b88bf461b59f2aca4fbd717fe1f7fae9a31ad41586223d8984be19883d35f1de`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L97-L97) — lines `97–97`; excerpt `sha256:7304b5cf4d9525b9c1502b4b9944fd430f498b46003ca30b4cac688362d02663`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L97-L97) — lines `97–97`; excerpt `sha256:7304b5cf4d9525b9c1502b4b9944fd430f498b46003ca30b4cac688362d02663`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L97-L97) — lines `97–97`; excerpt `sha256:7304b5cf4d9525b9c1502b4b9944fd430f498b46003ca30b4cac688362d02663`
- [lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean](../../lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean#L47-L52) — lines `47–52`; excerpt `sha256:33cfc2f7e37e3a2c10db006bdf734166bb372b874a1933fa3324a066b6552b44`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:137](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L137-L137), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1207](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1207-L1207), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1643](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1643-L1643), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1666](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1666-L1666)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:139](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L139-L139), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1280](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1280-L1280), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1835](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1835-L1835), [cite at paper/reasoning-parts/erdos1041/core.tex:97](../../paper/reasoning-parts/erdos1041/core.tex#L97-L97), [cite at paper/reasoning-parts/erdos1041/core.tex:1238](../../paper/reasoning-parts/erdos1041/core.tex#L1238-L1238), [cite at paper/reasoning-parts/erdos1041/core.tex:1793](../../paper/reasoning-parts/erdos1041/core.tex#L1793-L1793)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L823-L826) — lines `823–826`; excerpt `sha256:a90c5dfbfb8e145cf527f538fca7dae79167bd3b9090eb55e85806bc4d0edba4`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2997-L3000) — lines `2997–3000`; excerpt `sha256:a90c5dfbfb8e145cf527f538fca7dae79167bd3b9090eb55e85806bc4d0edba4`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2952-L2955) — lines `2952–2955`; excerpt `sha256:a90c5dfbfb8e145cf527f538fca7dae79167bd3b9090eb55e85806bc4d0edba4`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:680](../../paper/269/erdos-269-three-prime-running-lcm.tex#L680-L680)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:948](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L948-L948), [cite at paper/reasoning-parts/erdos269/core.tex:903](../../paper/reasoning-parts/erdos269/core.tex#L903-L903)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4405-L4409) — lines `4405–4409`; excerpt `sha256:ba25c19782edca439fc59536016a13c5d36a33cd2f359c1c6f2080fb7a229a6d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4380-L4384) — lines `4380–4384`; excerpt `sha256:ba25c19782edca439fc59536016a13c5d36a33cd2f359c1c6f2080fb7a229a6d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4126-L4126) — lines `4126–4126`; excerpt `sha256:c2aaa0c462b306e178c3f673ec026c7a33d2885dc0bdb20b45061a7ba1d2ad52`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4151](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4151-L4151), [cite at paper/reasoning-parts/erdos1049/core.tex:4126](../../paper/reasoning-parts/erdos1049/core.tex#L4126-L4126)

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
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L2395-L2395) — lines `2395–2395`; excerpt `sha256:18bf395f3f7709c9becd4665ef18292d1284189d731e98e4d8ea5e52e0201426`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L2395-L2395) — lines `2395–2395`; excerpt `sha256:18bf395f3f7709c9becd4665ef18292d1284189d731e98e4d8ea5e52e0201426`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L18396-L18404) — lines `18396–18404`; excerpt `sha256:6d631a23b443180906d917bb60d1a6c65c9fd2a705b5a9ed4ed4e026e91ae20d`
- [lean/Erdos249257/MersenneLambertLadder.lean](../../lean/Erdos249257/MersenneLambertLadder.lean#L15-L27) — lines `15–27`; excerpt `sha256:b17ccf4eb86418af3ba24ecd888e62fe5e23ef5fbf22c02f21fad26eef0562d0`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9404-L9409) — lines `9404–9409`; excerpt `sha256:786abf98fbd01e8ff40ec5a22574fff70c8c6565197a70a1b1cf5f71fbf62c38`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9234-L9239) — lines `9234–9239`; excerpt `sha256:786abf98fbd01e8ff40ec5a22574fff70c8c6565197a70a1b1cf5f71fbf62c38`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:529](../../paper/archive/erdos249-257-main-paper.tex#L529-L529), [cite at paper/archive/erdos249-257-main-paper.tex:560](../../paper/archive/erdos249-257-main-paper.tex#L560-L560)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:2565](../../paper/249/erdos249-totient-reasoning-surface.tex#L2565-L2565), [cite at paper/249/erdos249-totient-reasoning-surface.tex:3846](../../paper/249/erdos249-totient-reasoning-surface.tex#L3846-L3846), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:2395](../../paper/reasoning-parts/erdos249/a249_front.tex#L2395-L2395), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:3676](../../paper/reasoning-parts/erdos249/a249_front.tex#L3676-L3676)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1426-L1429) — lines `1426–1429`; excerpt `sha256:defd9a2ce501d09c198612d2849b08f6a067d1b43209958db0a0f1bc2c6a9fee`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9717-L9723) — lines `9717–9723`; excerpt `sha256:155147817b2ab91767d94108d0e5215ebda5501add1a233ca3558274306650ce`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9533-L9539) — lines `9533–9539`; excerpt `sha256:155147817b2ab91767d94108d0e5215ebda5501add1a233ca3558274306650ce`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L823-L825) — lines `823–825`; excerpt `sha256:17a384a1fdc66bdc50bfc789563acfc6b6e42f091c58ab6c6108261e4a3dd127`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3039-L3041) — lines `3039–3041`; excerpt `sha256:17a384a1fdc66bdc50bfc789563acfc6b6e42f091c58ab6c6108261e4a3dd127`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2999-L3001) — lines `2999–3001`; excerpt `sha256:17a384a1fdc66bdc50bfc789563acfc6b6e42f091c58ab6c6108261e4a3dd127`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:750](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L750-L750)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:808](../../paper/257/erdos-257-mersenne-support-subseries.tex#L808-L808)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:599](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L599-L599), [cite at paper/reasoning-parts/erdos251/core.tex:559](../../paper/reasoning-parts/erdos251/core.tex#L559-L559)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1218](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1218-L1218), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2289](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2289-L2289), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:5738](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L5738-L5738), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9665](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9665-L9665), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1034](../../paper/reasoning-parts/erdos257/a257_front.tex#L1034-L1034), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2105](../../paper/reasoning-parts/erdos257/a257_front.tex#L2105-L2105), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:5554](../../paper/reasoning-parts/erdos257/a257_front.tex#L5554-L5554), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9481](../../paper/reasoning-parts/erdos257/a257_front.tex#L9481-L9481)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L789-L791) — lines `789–791`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2999-L3001) — lines `2999–3001`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2959-L2961) — lines `2959–2961`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1989-L1989) — lines `1989–1989`; excerpt `sha256:1c353b92a6150c3c1fd31caf9ea67c600326deef9ecc2bd683a7fda752871261`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1990-L1990) — lines `1990–1990`; excerpt `sha256:b6e73fa3c5843b9322f980cfbc458e10518d0b0d75da433be27f464b8b1db2c8`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L21-L21) — lines `21–21`; excerpt `sha256:07dad1a6dbaa03c54631370154c906de91a50cd710b3b9c6e143f85e14b3c973`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L789-L791) — lines `789–791`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2999-L3001) — lines `2999–3001`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2959-L2961) — lines `2959–2961`; excerpt `sha256:e0cdf66cd89fa67f2f9a3d3c6f323475758efe2e39f2801613ca5fd24480d6c8`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:616](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L616-L616)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2030](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2030-L2030), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2032](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2032-L2032), [cite at paper/reasoning-parts/erdos251/core.tex:1990](../../paper/reasoning-parts/erdos251/core.tex#L1990-L1990), [cite at paper/reasoning-parts/erdos251/core.tex:1992](../../paper/reasoning-parts/erdos251/core.tex#L1992-L1992)

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
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1400-L1404) — lines `1400–1404`; excerpt `sha256:b8aeba1b74c5004a308c7a77d0dacb7f303d2e1210da60dac512f3834b9dfb1d`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L886-L886) — lines `886–886`; excerpt `sha256:e8f0eb9c08b32d040eb9d382b55721fcbada06cfa90efaa2936a851eae07396b`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1844-L1844) — lines `1844–1844`; excerpt `sha256:65cd5e4e29d1cdc61e86b1fdfd3aa0da4bc9945beae2af9f53b372cd68363f58`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8333-L8333) — lines `8333–8333`; excerpt `sha256:15ac24d3bb2a60a3a8644dbaa74f8f7584e82afe96beea17331f198e477b3da8`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L8702-L8702) — lines `8702–8702`; excerpt `sha256:7ddfabbfa80938c48b779f2b3418205424c4f3e925ef9cc11a07e77b0ce99902`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9141-L9146) — lines `9141–9146`; excerpt `sha256:c427aea096590bf4f8315ac8e13c2e92925eb10e1f02993b79815bfea6191556`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9651-L9656) — lines `9651–9656`; excerpt `sha256:01736f364c6af6f08a7498583610f9761ec3023900cdc6b3a5a25a416cccbf9e`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9747-L9758) — lines `9747–9758`; excerpt `sha256:3171372fd423eb3435f8b30446d71ac1de6f8b8a34d05c55191952194f66d6dd`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9563-L9574) — lines `9563–9574`; excerpt `sha256:3171372fd423eb3435f8b30446d71ac1de6f8b8a34d05c55191952194f66d6dd`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:653](../../paper/257/erdos-257-mersenne-support-subseries.tex#L653-L653)
- `erdos-synthesis-reading-together-record`: [cite at paper/synthesis/erdos-synthesis-reading-together-record.tex:132](../../paper/synthesis/erdos-synthesis-reading-together-record.tex#L132-L132)
- `erdos-synthesis-subsums-across-bases`: [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:378](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L378-L378)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:767](../../paper/archive/erdos249-257-main-paper.tex#L767-L768)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2110](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2110-L2110), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1926](../../paper/reasoning-parts/erdos257/a257_front.tex#L1926-L1926)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1454-L1460) — lines `1454–1460`; excerpt `sha256:a35f89f65cc066e7a94a5e3ea78d6f9d637ec56da4cfcc79fb014da7ccc0cd72`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9802-L9808) — lines `9802–9808`; excerpt `sha256:e9c60c753e365223406c899dee816ed5743af3cc67081cc3002ceb4f8cf6b1da`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9618-L9624) — lines `9618–9624`; excerpt `sha256:e9c60c753e365223406c899dee816ed5743af3cc67081cc3002ceb4f8cf6b1da`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:807](../../paper/257/erdos-257-mersenne-support-subseries.tex#L807-L807)
- `erdos-synthesis-reading-together-record`: [cite at paper/synthesis/erdos-synthesis-reading-together-record.tex:213](../../paper/synthesis/erdos-synthesis-reading-together-record.tex#L213-L213)
- `erdos-synthesis-subsums-across-bases`: [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:92](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L92-L92), [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:118](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L118-L118)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9664](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9664-L9664), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9480](../../paper/reasoning-parts/erdos257/a257_front.tex#L9480-L9480)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1215-L1219) — lines `1215–1219`; excerpt `sha256:fc6fd8468b61e2df565a66c6f80ada42f10c2a199342733fd32a56b58a37f741`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2924-L2928) — lines `2924–2928`; excerpt `sha256:e676e6cb0116aea00ea8f9c6ab98b451db00b3a8f7711be43649ec04855f1014`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2890-L2894) — lines `2890–2894`; excerpt `sha256:e676e6cb0116aea00ea8f9c6ab98b451db00b3a8f7711be43649ec04855f1014`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1076](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1076-L1076)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1539](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1539-L1539), [cite at paper/reasoning-parts/erdos68/core.tex:1505](../../paper/reasoning-parts/erdos68/core.tex#L1505-L1505)

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
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4512-L4518) — lines `4512–4518`; excerpt `sha256:7edeec595003b28ac91040a61c50d3a57a5872bbc9871d704d9ba32a048e1a23`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4487-L4493) — lines `4487–4493`; excerpt `sha256:7edeec595003b28ac91040a61c50d3a57a5872bbc9871d704d9ba32a048e1a23`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4206-L4206) — lines `4206–4206`; excerpt `sha256:21196a6cc9019dd41d30945a6a3d9e8e466447c7c1830ee9e83704db25a0ef1f`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L11735-L11740) — lines `11735–11740`; excerpt `sha256:563923daea706e56c4f2e7175d13053380af2dc3a24ac50d9212c2b0b6d7634e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L12806-L12811) — lines `12806–12811`; excerpt `sha256:448131d83b624b6ce5520dce8ac090fcec58010089d33f41e6a4644fb0ca8a01`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L12962-L12969) — lines `12962–12969`; excerpt `sha256:85e296ca403f80f61aacb885a69266e7645176834ee36a40fbd6e9652cf62bce`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L13680-L13685) — lines `13680–13685`; excerpt `sha256:0de2a3ac66ecee1b3a0e617d573bb7de8678b3975f019984a2d7a83aa43ffbf9`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L14196-L14200) — lines `14196–14200`; excerpt `sha256:12fe3f3b9cef7b6405e234a689ac1e837abfeb24254cb43a2d6815961f8e0b30`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1429-L1435) — lines `1429–1435`; excerpt `sha256:e2ea1dec26aa5bc12b24ae324b5eec9758dfe18eef2464f06f2c610f65164b7d`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9706-L9717) — lines `9706–9717`; excerpt `sha256:dc3b6825148962fe6dcac631ca31bbed24b0c5d155adf89e2b13951655dda752`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9522-L9533) — lines `9522–9533`; excerpt `sha256:dc3b6825148962fe6dcac631ca31bbed24b0c5d155adf89e2b13951655dda752`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1206](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1206-L1206)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4231](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4231-L4231), [cite at paper/reasoning-parts/erdos1049/core.tex:4206](../../paper/reasoning-parts/erdos1049/core.tex#L4206-L4206)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:718](../../paper/archive/erdos249-257-main-paper.tex#L718-L718), [cite at paper/archive/erdos249-257-main-paper.tex:720](../../paper/archive/erdos249-257-main-paper.tex#L720-L720), [cite at paper/archive/erdos249-257-main-paper.tex:724](../../paper/archive/erdos249-257-main-paper.tex#L724-L724), [cite at paper/archive/erdos249-257-main-paper.tex:726](../../paper/archive/erdos249-257-main-paper.tex#L726-L726), [cite at paper/archive/erdos249-257-main-paper.tex:729](../../paper/archive/erdos249-257-main-paper.tex#L729-L729), [cite at paper/archive/erdos249-257-main-paper.tex:3853](../../paper/archive/erdos249-257-main-paper.tex#L3853-L3854), [cite at paper/archive/erdos249-257-main-paper.tex:3859](../../paper/archive/erdos249-257-main-paper.tex#L3859-L3859)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:982](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L982-L982), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:985](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L985-L985), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1093](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1093-L1093), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2227](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2227-L2227), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:2258](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L2258-L2258), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3081](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3081-L3081), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3116](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3116-L3116), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3123](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3123-L3123), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:3254](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L3254-L3254), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7110](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7110-L7110), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:7267](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L7267-L7267), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9655](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9655-L9655), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:798](../../paper/reasoning-parts/erdos257/a257_front.tex#L798-L798), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:801](../../paper/reasoning-parts/erdos257/a257_front.tex#L801-L801), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:909](../../paper/reasoning-parts/erdos257/a257_front.tex#L909-L909), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2043](../../paper/reasoning-parts/erdos257/a257_front.tex#L2043-L2043), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2074](../../paper/reasoning-parts/erdos257/a257_front.tex#L2074-L2074), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2897](../../paper/reasoning-parts/erdos257/a257_front.tex#L2897-L2897), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2932](../../paper/reasoning-parts/erdos257/a257_front.tex#L2932-L2932), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:2939](../../paper/reasoning-parts/erdos257/a257_front.tex#L2939-L2939), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:3070](../../paper/reasoning-parts/erdos257/a257_front.tex#L3070-L3070), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:6926](../../paper/reasoning-parts/erdos257/a257_front.tex#L6926-L6926), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:7083](../../paper/reasoning-parts/erdos257/a257_front.tex#L7083-L7083), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9471](../../paper/reasoning-parts/erdos257/a257_front.tex#L9471-L9471)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1582-L1585) — lines `1582–1585`; excerpt `sha256:294f4940c49e7e83f5c9a316dacd84e70465f990c00cbcf92273c2caaf0a7a4b`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1374](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1374-L1374)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1106-L1112) — lines `1106–1112`; excerpt `sha256:baac1f8ff06d86954ea6fb3d6ea4be3f7ba3e7cc9c207ea61e4e3d1c42db53d0`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9499-L9505) — lines `9499–9505`; excerpt `sha256:baac1f8ff06d86954ea6fb3d6ea4be3f7ba3e7cc9c207ea61e4e3d1c42db53d0`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9329-L9335) — lines `9329–9335`; excerpt `sha256:baac1f8ff06d86954ea6fb3d6ea4be3f7ba3e7cc9c207ea61e4e3d1c42db53d0`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:359](../../paper/249/erdos-249-binary-totient-series.tex#L359-L359), [cite at paper/249/erdos-249-binary-totient-series.tex:756](../../paper/249/erdos-249-binary-totient-series.tex#L756-L757)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:267](../../paper/249/erdos249-totient-reasoning-surface.tex#L267-L268), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:97](../../paper/reasoning-parts/erdos249/a249_front.tex#L97-L98)

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
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9398-L9404) — lines `9398–9404`; excerpt `sha256:d225e8a6b24e1aa1895e5b08441a48c78042c267387c9e1c0073591e2991cb37`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9228-L9234) — lines `9228–9234`; excerpt `sha256:d225e8a6b24e1aa1895e5b08441a48c78042c267387c9e1c0073591e2991cb37`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1354-L1360) — lines `1354–1360`; excerpt `sha256:4ce4046469794790aba2dd446aea947f73b80cbd8f7aa313de40dda280a3a9ef`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4559-L4565) — lines `4559–4565`; excerpt `sha256:761e023172196c4decffac4dc93b4787a57fef7d96f3e61f22d47bdbb1885dc5`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4534-L4540) — lines `4534–4540`; excerpt `sha256:761e023172196c4decffac4dc93b4787a57fef7d96f3e61f22d47bdbb1885dc5`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:600](../../paper/1049/erdos-1049-rational-base-lambert.tex#L600-L600)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1217](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1217-L1217), [cite at paper/reasoning-parts/erdos1049/core.tex:1192](../../paper/reasoning-parts/erdos1049/core.tex#L1192-L1192)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3970](../../paper/archive/erdos249-257-main-paper.tex#L3970-L3971)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1625](../../paper/249/erdos249-totient-reasoning-surface.tex#L1625-L1625), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1455](../../paper/reasoning-parts/erdos249/a249_front.tex#L1455-L1455)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4580-L4585) — lines `4580–4585`; excerpt `sha256:62cef4449bffe123aa3b82aa7eaf0a6af4fcb0d0c65605d5e1dbe7aee94f0a73`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4555-L4560) — lines `4555–4560`; excerpt `sha256:62cef4449bffe123aa3b82aa7eaf0a6af4fcb0d0c65605d5e1dbe7aee94f0a73`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4237](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4237-L4237), [cite at paper/reasoning-parts/erdos1049/core.tex:4212](../../paper/reasoning-parts/erdos1049/core.tex#L4212-L4212)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3043-L3045) — lines `3043–3045`; excerpt `sha256:4b2c462e9156fcefa9deab67573f0793906c11306432364ce53464dbb6c19538`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3003-L3005) — lines `3003–3005`; excerpt `sha256:4b2c462e9156fcefa9deab67573f0793906c11306432364ce53464dbb6c19538`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:605](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L605-L605), [cite at paper/reasoning-parts/erdos251/core.tex:565](../../paper/reasoning-parts/erdos251/core.tex#L565-L565)

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

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1599-L1601) — lines `1599–1601`; excerpt `sha256:e22b714a411702e74c05c8664cdaefcf8f5c4dcb370228e523cf673d46d64846`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1127](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1127-L1127)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1086-L1089) — lines `1086–1089`; excerpt `sha256:56a8f02f756379e8b9f86571b2146e088317bf4d41df88c247647efa76da475f`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9382-L9386) — lines `9382–9386`; excerpt `sha256:bb9e02a0cb308737040e1d9af54ab2a42d227d1dbf584528d1d8763f1f2fe1e1`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9212-L9216) — lines `9212–9216`; excerpt `sha256:bb9e02a0cb308737040e1d9af54ab2a42d227d1dbf584528d1d8763f1f2fe1e1`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:613](../../paper/249/erdos-249-binary-totient-series.tex#L613-L613)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1458](../../paper/249/erdos249-totient-reasoning-surface.tex#L1458-L1458), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1288](../../paper/reasoning-parts/erdos249/a249_front.tex#L1288-L1288)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3000-L3003) — lines `3000–3003`; excerpt `sha256:4fd45772ff7add1f64a2a0aceb707abf3ec134b84b8189985e359c4a31876a7b`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L826-L829) — lines `826–829`; excerpt `sha256:89365f17cd5c9375bfee104214e4355cd14808bfdc25bae5d0d57d71698246ad`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2955-L2958) — lines `2955–2958`; excerpt `sha256:4fd45772ff7add1f64a2a0aceb707abf3ec134b84b8189985e359c4a31876a7b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L905-L905) — lines `905–905`; excerpt `sha256:b87bb3e4a7af82e9910a8693bb635b75f50fdfb4e5b86a06543454c0545aca25`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L681-L681) — lines `681–681`; excerpt `sha256:38bc71f698002b6838a9f3a313c1ae74f93d90a94f65db0715526a6b8d4b3506`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:681](../../paper/269/erdos-269-three-prime-running-lcm.tex#L681-L681)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:950](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L950-L950), [cite at paper/reasoning-parts/erdos269/core.tex:905](../../paper/reasoning-parts/erdos269/core.tex#L905-L905)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2944-L2948) — lines `2944–2948`; excerpt `sha256:a48ddc588b042ca4c1ef063504be6dd2e3c0c0d8f6ce9a6a0b3fe1989375c081`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2910-L2914) — lines `2910–2914`; excerpt `sha256:a48ddc588b042ca4c1ef063504be6dd2e3c0c0d8f6ce9a6a0b3fe1989375c081`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1631](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1631-L1631), [cite at paper/reasoning-parts/erdos68/core.tex:1597](../../paper/reasoning-parts/erdos68/core.tex#L1597-L1597)

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
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1067-L1071) — lines `1067–1071`; excerpt `sha256:3a615d5188e3c811f81c9421c1fae9cae57aa51eaecc361017b08887fd690350`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L60-L60) — lines `60–60`; excerpt `sha256:c8b8a219e2d05b9d599b8a34430f56e76d7a92ecc1a80f73411c4e6c05a43b18`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L61-L61) — lines `61–61`; excerpt `sha256:b6ce0fb599e9bf02898ae89ea89e3bf47a7a31efcaab7ffbe2a9e2aaaae8ab8c`
- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L156-L156) — lines `156–156`; excerpt `sha256:3260d5a1253a2750f8cda31532306f204142e47cb4ce3964043dff2fdb598f14`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L276-L276) — lines `276–276`; excerpt `sha256:48a3dc935a9efd4f525b4196ade8751cfd054cab2285d0b3acf1c074f18578f9`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L85-L85) — lines `85–85`; excerpt `sha256:cb49a811183c00893bef1ffc247d63d3efebe505db66c5ea17d14f12b750a7bf`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L85-L85) — lines `85–85`; excerpt `sha256:cb49a811183c00893bef1ffc247d63d3efebe505db66c5ea17d14f12b750a7bf`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L276-L276) — lines `276–276`; excerpt `sha256:48a3dc935a9efd4f525b4196ade8751cfd054cab2285d0b3acf1c074f18578f9`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9363-L9368) — lines `9363–9368`; excerpt `sha256:5cedcebcfca20ab63e92ba4441d035c85b0a632e564a43408ffe6b79fe30ae48`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9193-L9198) — lines `9193–9198`; excerpt `sha256:5cedcebcfca20ab63e92ba4441d035c85b0a632e564a43408ffe6b79fe30ae48`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:61](../../paper/249/erdos-249-binary-totient-series.tex#L61-L61), [cite at paper/249/erdos-249-binary-totient-series.tex:777](../../paper/249/erdos-249-binary-totient-series.tex#L777-L777), [cite at paper/249/erdos-249-binary-totient-series.tex:782](../../paper/249/erdos-249-binary-totient-series.tex#L782-L782)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3187](../../paper/archive/erdos249-257-main-paper.tex#L3187-L3187)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:255](../../paper/249/erdos249-totient-reasoning-surface.tex#L255-L255), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7067](../../paper/249/erdos249-totient-reasoning-surface.tex#L7067-L7067), [cite at paper/249/erdos249-totient-reasoning-surface.tex:8410](../../paper/249/erdos249-totient-reasoning-surface.tex#L8410-L8410), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:85](../../paper/reasoning-parts/erdos249/a249_front.tex#L85-L85), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:6897](../../paper/reasoning-parts/erdos249/a249_front.tex#L6897-L6897), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8240](../../paper/reasoning-parts/erdos249/a249_front.tex#L8240-L8240)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1601-L1603) — lines `1601–1603`; excerpt `sha256:3512dbed9859b7bdff32e6c30c9caf824a9e8638de1e2632e6009f8d0618fc41`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1548-L1552) — lines `1548–1552`; excerpt `sha256:0e32e51882f8449928d597050d67e151bf67b120c65ffffdeb1ad3182cbfbb6a`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:940](../../paper/systems/claim-faithful-publication-systems-paper.tex#L940-L940)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:397](../../paper/systems/open-source-mathematics-strategy.tex#L397-L397), [cite at paper/systems/open-source-mathematics-strategy.tex:1023](../../paper/systems/open-source-mathematics-strategy.tex#L1023-L1023)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L811-L813) — lines `811–813`; excerpt `sha256:61ad353ab13c9df0f317f4f72d599dc10397c01254ccf1035a02cf84853d8304`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3027-L3029) — lines `3027–3029`; excerpt `sha256:61ad353ab13c9df0f317f4f72d599dc10397c01254ccf1035a02cf84853d8304`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2987-L2989) — lines `2987–2989`; excerpt `sha256:61ad353ab13c9df0f317f4f72d599dc10397c01254ccf1035a02cf84853d8304`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9808-L9814) — lines `9808–9814`; excerpt `sha256:e118982ef9fb8a4e691c79683424d1b891a905dfc8672b0a0f1e9237f5fb3d99`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9624-L9630) — lines `9624–9630`; excerpt `sha256:e118982ef9fb8a4e691c79683424d1b891a905dfc8672b0a0f1e9237f5fb3d99`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:749](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L749-L749)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:596](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L596-L596), [cite at paper/reasoning-parts/erdos251/core.tex:556](../../paper/reasoning-parts/erdos251/core.tex#L556-L556)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9666](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9666-L9666), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9482](../../paper/reasoning-parts/erdos257/a257_front.tex#L9482-L9482)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L813-L815) — lines `813–815`; excerpt `sha256:a876ac96db99087a07bfa49f869f9990f286e49a52310ceab8423d7980641577`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3029-L3031) — lines `3029–3031`; excerpt `sha256:a876ac96db99087a07bfa49f869f9990f286e49a52310ceab8423d7980641577`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2989-L2991) — lines `2989–2991`; excerpt `sha256:a876ac96db99087a07bfa49f869f9990f286e49a52310ceab8423d7980641577`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:747](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L747-L747)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:588](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L588-L588), [cite at paper/reasoning-parts/erdos251/core.tex:548](../../paper/reasoning-parts/erdos251/core.tex#L548-L548)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1188-L1194) — lines `1188–1194`; excerpt `sha256:fdc72e5f8bd263e4a323f5c9a3cde8b9b721106fee45e5666a814b1163e3a605`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4042-L4048) — lines `4042–4048`; excerpt `sha256:fdc72e5f8bd263e4a323f5c9a3cde8b9b721106fee45e5666a814b1163e3a605`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4010-L4016) — lines `4010–4016`; excerpt `sha256:fdc72e5f8bd263e4a323f5c9a3cde8b9b721106fee45e5666a814b1163e3a605`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L829-L832) — lines `829–832`; excerpt `sha256:45604844b23b875721c499f1d941719928dcc2b6bb269b97c8564702e5d3051b`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3009-L3012) — lines `3009–3012`; excerpt `sha256:45604844b23b875721c499f1d941719928dcc2b6bb269b97c8564702e5d3051b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2964-L2967) — lines `2964–2967`; excerpt `sha256:45604844b23b875721c499f1d941719928dcc2b6bb269b97c8564702e5d3051b`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:928](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L928-L928)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:683](../../paper/269/erdos-269-three-prime-running-lcm.tex#L683-L683)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:736](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L736-L736), [cite at paper/reasoning-parts/erdos243/core.tex:704](../../paper/reasoning-parts/erdos243/core.tex#L704-L704)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1302](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1302-L1302), [cite at paper/reasoning-parts/erdos269/core.tex:1257](../../paper/reasoning-parts/erdos269/core.tex#L1257-L1257)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2970-L2973) — lines `2970–2973`; excerpt `sha256:5eafead45851c5d9d3dbc7e8333b2811c3bfb396c82d092e088a35955fc4a00e`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2925-L2928) — lines `2925–2928`; excerpt `sha256:5eafead45851c5d9d3dbc7e8333b2811c3bfb396c82d092e088a35955fc4a00e`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L104-L104) — lines `104–104`; excerpt `sha256:01a5fae67b68650964abbf3f3663d797e06703153d42450737b8fb3730e2229f`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:149](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L149-L149), [cite at paper/reasoning-parts/erdos269/core.tex:104](../../paper/reasoning-parts/erdos269/core.tex#L104-L104)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4415-L4421) — lines `4415–4421`; excerpt `sha256:d5178dbf9e857836e9898ea177d620546af9d24a1826f669a5c173ec6dea9c58`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4390-L4396) — lines `4390–4396`; excerpt `sha256:d5178dbf9e857836e9898ea177d620546af9d24a1826f669a5c173ec6dea9c58`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4140-L4140) — lines `4140–4140`; excerpt `sha256:e85a60b5f00cd26f892425661c3e141ada248c650f76fa1bbab1b0d4d117a642`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L88-L95) — lines `88–95`; excerpt `sha256:2223d196ea50c7aa4910ff7135c17302d35865756bc58597c18dfb8b05e931ac`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4165](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4165-L4165), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4186](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4186-L4186), [cite at paper/reasoning-parts/erdos1049/core.tex:4140](../../paper/reasoning-parts/erdos1049/core.tex#L4140-L4140), [cite at paper/reasoning-parts/erdos1049/core.tex:4161](../../paper/reasoning-parts/erdos1049/core.tex#L4161-L4161)

<a id="source-source-79afab8abaf9d5"></a>

### [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the Erdős Problems](https://arxiv.org/abs/2601.22401)

- Source id: `source-79afab8abaf9d5`
- Author or public identity: Tony Feng, Trieu Trinh, Garrett Bingham, Jiwon Kang, Shengtong Zhang, Sang-hyun Kim, Kevin Barreto, Carl Schildkraut, Junehyuk Jung, Jaehyeon Seo, Carlo Pagano, Yuri Chervonyi, Dawsen Hwang, Kaiying Hou, Sergei Gukov, Cheng-Chiang Tsai, Hyunwoo Choi, Youngbeom Jin, Wei-Yuan Li, Hao-An Wu, Ruey-An Shiu, Yu-Sheng Shih, Quoc V. Le, Thang Luong
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by both public systems papers as prior published evidence (v3, 5 February 2026) that kernel-correct solutions of misread statements are vacuous (63 technically correct, 13 meaningfully correct of 200 graded; the Erdős-75 appendix), that literature identification and intent dominate review effort, for the AI-verifier-then-expert attention funnel, the four-way outcome taxonomy, the subconscious-plagiarism risk, and the rule that humans author mathematics papers. None of this repository's eight problems appears in its results.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1570-L1573) — lines `1570–1573`; excerpt `sha256:0c2bee4d10e2ab1fbc297d9e55ba8944905aa1466a55359f48e11b90d3526883`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1613-L1618) — lines `1613–1618`; excerpt `sha256:35c50b80ea4e9bece2ad431b8db8fe260367c76ed945564205813263b357e81f`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:125](../../paper/systems/claim-faithful-publication-systems-paper.tex#L125-L125), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:977](../../paper/systems/claim-faithful-publication-systems-paper.tex#L977-L977), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1347](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1347-L1347)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:667](../../paper/systems/open-source-mathematics-strategy.tex#L667-L667), [cite at paper/systems/open-source-mathematics-strategy.tex:747](../../paper/systems/open-source-mathematics-strategy.tex#L747-L747), [cite at paper/systems/open-source-mathematics-strategy.tex:778](../../paper/systems/open-source-mathematics-strategy.tex#L778-L778), [cite at paper/systems/open-source-mathematics-strategy.tex:985](../../paper/systems/open-source-mathematics-strategy.tex#L985-L985)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L835-L838) — lines `835–838`; excerpt `sha256:b9e2249bc4d01297697400d9029b3c8e7883b75d69de50546f4bde27319bc74f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3015-L3018) — lines `3015–3018`; excerpt `sha256:b9e2249bc4d01297697400d9029b3c8e7883b75d69de50546f4bde27319bc74f`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2970-L2973) — lines `2970–2973`; excerpt `sha256:b9e2249bc4d01297697400d9029b3c8e7883b75d69de50546f4bde27319bc74f`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:691](../../paper/269/erdos-269-three-prime-running-lcm.tex#L691-L691)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2042](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2042-L2042), [cite at paper/reasoning-parts/erdos269/core.tex:1997](../../paper/reasoning-parts/erdos269/core.tex#L1997-L1997)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1335-L1340) — lines `1335–1340`; excerpt `sha256:8c9e993b368de8fbbc0268799b73c63a9a57820cb67067d572137c49613f2ef8`

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1843-L1846) — lines `1843–1846`; excerpt `sha256:6aaf6da69e5a056c56565ce65b93dc9624cd8a22480a7b32eacbb405f875508a`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4714-L4717) — lines `4714–4717`; excerpt `sha256:6aaf6da69e5a056c56565ce65b93dc9624cd8a22480a7b32eacbb405f875508a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4672-L4675) — lines `4672–4675`; excerpt `sha256:6aaf6da69e5a056c56565ce65b93dc9624cd8a22480a7b32eacbb405f875508a`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1403](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1403-L1403)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2698](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2698-L2698), [cite at paper/reasoning-parts/erdos1041/core.tex:2656](../../paper/reasoning-parts/erdos1041/core.tex#L2656-L2656)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9482-L9486) — lines `9482–9486`; excerpt `sha256:48c8f377367df5c421434058ed0f1e7474c781ee36061cf7ab0d39eda785c36d`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9312-L9316) — lines `9312–9316`; excerpt `sha256:48c8f377367df5c421434058ed0f1e7474c781ee36061cf7ab0d39eda785c36d`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L850-L854) — lines `850–854`; excerpt `sha256:2d8e8e60c166ca01ea9461e45af9157b2f035c8a50a7d38749db5dbf50c5e728`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3024-L3028) — lines `3024–3028`; excerpt `sha256:ef78f91a2a53616a917a9b8d574a5da55953d5024938b45990e8decb1515b07b`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2979-L2983) — lines `2979–2983`; excerpt `sha256:ef78f91a2a53616a917a9b8d574a5da55953d5024938b45990e8decb1515b07b`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:692](../../paper/269/erdos-269-three-prime-running-lcm.tex#L692-L692)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:8305](../../paper/249/erdos249-totient-reasoning-surface.tex#L8305-L8305), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:8135](../../paper/reasoning-parts/erdos249/a249_front.tex#L8135-L8135)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2164](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2164-L2164), [cite at paper/reasoning-parts/erdos269/core.tex:2119](../../paper/reasoning-parts/erdos269/core.tex#L2119-L2119)

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

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1618-L1621) — lines `1618–1621`; excerpt `sha256:1b5d7bac4be42590e61a579f1d80ea2cb6adb8f6f2ce9ca2ed0c61289d5fa104`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1305](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1305-L1305)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2964-L2968) — lines `2964–2968`; excerpt `sha256:ea1e57fc8df0e5e2dc90fc296ae5b3eb8139cdc0ae9ec706f448b795a1933541`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2930-L2934) — lines `2930–2934`; excerpt `sha256:ea1e57fc8df0e5e2dc90fc296ae5b3eb8139cdc0ae9ec706f448b795a1933541`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1754](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1754-L1754), [cite at paper/reasoning-parts/erdos68/core.tex:1720](../../paper/reasoning-parts/erdos68/core.tex#L1720-L1720)

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
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1415-L1419) — lines `1415–1419`; excerpt `sha256:4ea0575269b0cc301d69524665b7d6cb05120bcbba9460851e9fa2718c3cafec`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L144-L144) — lines `144–144`; excerpt `sha256:c7a81b8d86ce7c996d630dcf84722c50dcd66186b2043ffbb325b11eedbbf227`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L10768-L10777) — lines `10768–10777`; excerpt `sha256:162189e1cf0c892075ed7cffb8ef885d1d9da766b3f16a7a6ae07d5c83afc90e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9741-L9741) — lines `9741–9741`; excerpt `sha256:cdc7c634e30bd34ca3a9b807193c3645b42bcbe20c8c45508b70001c4eae795d`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L99-L99) — lines `99–99`; excerpt `sha256:677da0e70221819bf9c739687410bd2ad1617b0c49b0d665915d40e40c4ee20c`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L328-L328) — lines `328–328`; excerpt `sha256:c7a81b8d86ce7c996d630dcf84722c50dcd66186b2043ffbb325b11eedbbf227`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L99-L99) — lines `99–99`; excerpt `sha256:677da0e70221819bf9c739687410bd2ad1617b0c49b0d665915d40e40c4ee20c`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L151-L151) — lines `151–151`; excerpt `sha256:e3872dd726142058db24d451b073eb106f0d6e35aea52bb385f849574ba5ce02`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L817-L820) — lines `817–820`; excerpt `sha256:38cd73fc723cb87858bf5ad1ff85bc3a6aed38bc336429f816ee84816442c7d9`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2988-L2991) — lines `2988–2991`; excerpt `sha256:38cd73fc723cb87858bf5ad1ff85bc3a6aed38bc336429f816ee84816442c7d9`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2943-L2946) — lines `2943–2946`; excerpt `sha256:38cd73fc723cb87858bf5ad1ff85bc3a6aed38bc336429f816ee84816442c7d9`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2981-L2983) — lines `2981–2983`; excerpt `sha256:f27417f97884dcd2e5140620cdfa45a7fbcbc3cec44992f67d8feb50d91f535c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2941-L2943) — lines `2941–2943`; excerpt `sha256:f27417f97884dcd2e5140620cdfa45a7fbcbc3cec44992f67d8feb50d91f535c`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9697-L9706) — lines `9697–9706`; excerpt `sha256:23b75d9385f4d7c31ec74d72a39ca533b7b4c020d60c4718af8894c4ba6f4ed4`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9513-L9522) — lines `9513–9522`; excerpt `sha256:23b75d9385f4d7c31ec74d72a39ca533b7b4c020d60c4718af8894c4ba6f4ed4`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1184-L1188) — lines `1184–1188`; excerpt `sha256:7534aa59bb234c308a55714341b32d4a03d5c73d5381c36bf619a6d8cdc5e0c4`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4038-L4042) — lines `4038–4042`; excerpt `sha256:7534aa59bb234c308a55714341b32d4a03d5c73d5381c36bf619a6d8cdc5e0c4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4006-L4010) — lines `4006–4010`; excerpt `sha256:7534aa59bb234c308a55714341b32d4a03d5c73d5381c36bf619a6d8cdc5e0c4`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:925](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L925-L925)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:99](../../paper/257/erdos-257-mersenne-support-subseries.tex#L99-L99), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:100](../../paper/257/erdos-257-mersenne-support-subseries.tex#L100-L100), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:105](../../paper/257/erdos-257-mersenne-support-subseries.tex#L105-L105)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:419](../../paper/269/erdos-269-three-prime-running-lcm.tex#L419-L419)
- `erdos-synthesis-subsums-across-bases`: [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:139](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L139-L139)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:731](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L731-L731), [cite at paper/reasoning-parts/erdos243/core.tex:699](../../paper/reasoning-parts/erdos243/core.tex#L699-L699)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:705](../../paper/archive/erdos249-257-main-paper.tex#L705-L705)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1886](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1886-L1886), [cite at paper/reasoning-parts/erdos251/core.tex:1846](../../paper/reasoning-parts/erdos251/core.tex#L1846-L1846)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:980](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L980-L980), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:796](../../paper/reasoning-parts/erdos257/a257_front.tex#L796-L796)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1254](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1254-L1254), [cite at paper/reasoning-parts/erdos269/core.tex:1209](../../paper/reasoning-parts/erdos269/core.tex#L1209-L1209)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4661-L4666) — lines `4661–4666`; excerpt `sha256:fbbf29db45c62cfa84769c87ea4dfb6dcbc312a557a3335deb161872d3ae4d44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4619-L4624) — lines `4619–4624`; excerpt `sha256:fbbf29db45c62cfa84769c87ea4dfb6dcbc312a557a3335deb161872d3ae4d44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1218-L1218) — lines `1218–1218`; excerpt `sha256:9b744f2b7f5621dd470311a82aeee2e8b051a79200911c2b6b0f3b283301c6d6`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1789-L1794) — lines `1789–1794`; excerpt `sha256:03547751579bddb06550186cbd4cd5363e790e059ff80b147b313232f2329016`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1226](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1226-L1226), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1654](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1654-L1655)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1260](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1260-L1260), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1868](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1868-L1868), [cite at paper/reasoning-parts/erdos1041/core.tex:1218](../../paper/reasoning-parts/erdos1041/core.tex#L1218-L1218), [cite at paper/reasoning-parts/erdos1041/core.tex:1826](../../paper/reasoning-parts/erdos1041/core.tex#L1826-L1826)

<a id="source-source-80c9ae60b7f7be"></a>

### [LeanArchitect: Automating Blueprint Generation for Humans and AI](https://doi.org/10.4230/LIPIcs.ITP.2026.25)

- Source id: `source-80c9ae60b7f7be`
- Author or public identity: T. Zhu, P. Monticone, S. Welleck, J. Avigad
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1557-L1561) — lines `1557–1561`; excerpt `sha256:db2532f557964ac96576952c8607d916e5278b3c6d7a29bd13295a77ff345e28`
- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L660-L665) — lines `660–665`; excerpt `sha256:1f3f3c8f59b09e017af2d71374c7c46368d97929557de076c9b6d0b5f80c83bf`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1395](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1395-L1395)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:453](../../paper/systems/cold-clone-to-proof-receipt.tex#L453-L453)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L781-L783) — lines `781–783`; excerpt `sha256:5cfb10540069185577d738da52c429d1b74a4f8ce94c54018d941550c730eeaf`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2991-L2993) — lines `2991–2993`; excerpt `sha256:5cfb10540069185577d738da52c429d1b74a4f8ce94c54018d941550c730eeaf`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2951-L2953) — lines `2951–2953`; excerpt `sha256:5cfb10540069185577d738da52c429d1b74a4f8ce94c54018d941550c730eeaf`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:341](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L341-L341)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:453](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L453-L453), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:631](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L631-L631), [cite at paper/reasoning-parts/erdos251/core.tex:413](../../paper/reasoning-parts/erdos251/core.tex#L413-L413), [cite at paper/reasoning-parts/erdos251/core.tex:591](../../paper/reasoning-parts/erdos251/core.tex#L591-L591)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1830-L1835) — lines `1830–1835`; excerpt `sha256:dd81dda92210816aa997d12725fdd2b3d2f7a70097cbd438d5ef8102c0c13e44`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4701-L4706) — lines `4701–4706`; excerpt `sha256:dd81dda92210816aa997d12725fdd2b3d2f7a70097cbd438d5ef8102c0c13e44`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4659-L4664) — lines `4659–4664`; excerpt `sha256:dd81dda92210816aa997d12725fdd2b3d2f7a70097cbd438d5ef8102c0c13e44`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1668](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1668-L1669)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4396](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4396-L4396), [cite at paper/reasoning-parts/erdos1041/core.tex:4354](../../paper/reasoning-parts/erdos1041/core.tex#L4354-L4354)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L682-L685) — lines `682–685`; excerpt `sha256:ebb7c8c62fa7ff44ee571f137c47de8e5508a51405cbdd51807c60b2bad5a1f3`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:472](../../paper/systems/cold-clone-to-proof-receipt.tex#L472-L472)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L688-L691) — lines `688–691`; excerpt `sha256:8662990def0156ee9fa798ccb6915b9367683e2590ac54e5debcf5a71f027cb9`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:475](../../paper/systems/cold-clone-to-proof-receipt.tex#L475-L475)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1175-L1181) — lines `1175–1181`; excerpt `sha256:eb7d5ec7e254bbf424e424d7b70e149f642ec316eed5ca8d2357045a54b32cc6`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4024-L4030) — lines `4024–4030`; excerpt `sha256:eb7d5ec7e254bbf424e424d7b70e149f642ec316eed5ca8d2357045a54b32cc6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3992-L3998) — lines `3992–3998`; excerpt `sha256:eb7d5ec7e254bbf424e424d7b70e149f642ec316eed5ca8d2357045a54b32cc6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L176-L176) — lines `176–176`; excerpt `sha256:8994330960bdf9e6d8836c94468834265a2e79cdf99b7892977ebbb3dc21c6a2`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:93](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L93-L93), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:320](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L320-L320), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:348](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L348-L348), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:350](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L350-L350), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:377](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L377-L377), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:403](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L403-L403), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:408](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L408-L408), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:417](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L417-L417), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:747](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L747-L747), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:1082](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1082-L1083)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:208](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L208-L208), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:749](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L749-L749), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:769](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L769-L769), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:851](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L851-L851), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:857](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L857-L857), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:868](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L868-L868), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:881](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L881-L881), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:882](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L882-L882), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:884](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L884-L884), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:890](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L890-L890), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:985](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L985-L985), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2365](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2365-L2365), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2374](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2374-L2374), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2401](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2401-L2401), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2449](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2449-L2449), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2509](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2509-L2509), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2832](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2832-L2832), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2836](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2836-L2836), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3156](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3156-L3156), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3160](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3160-L3160), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3173](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3173-L3173), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3252](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3252-L3252), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3253](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3253-L3253), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3560](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3560-L3560), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3563](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3563-L3563), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3569](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3569-L3569), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3849](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3849-L3850), [cite at paper/reasoning-parts/erdos243/core.tex:176](../../paper/reasoning-parts/erdos243/core.tex#L176-L176), [cite at paper/reasoning-parts/erdos243/core.tex:717](../../paper/reasoning-parts/erdos243/core.tex#L717-L717), [cite at paper/reasoning-parts/erdos243/core.tex:737](../../paper/reasoning-parts/erdos243/core.tex#L737-L737), [cite at paper/reasoning-parts/erdos243/core.tex:819](../../paper/reasoning-parts/erdos243/core.tex#L819-L819), [cite at paper/reasoning-parts/erdos243/core.tex:825](../../paper/reasoning-parts/erdos243/core.tex#L825-L825), [cite at paper/reasoning-parts/erdos243/core.tex:836](../../paper/reasoning-parts/erdos243/core.tex#L836-L836), [cite at paper/reasoning-parts/erdos243/core.tex:849](../../paper/reasoning-parts/erdos243/core.tex#L849-L849), [cite at paper/reasoning-parts/erdos243/core.tex:850](../../paper/reasoning-parts/erdos243/core.tex#L850-L850), [cite at paper/reasoning-parts/erdos243/core.tex:852](../../paper/reasoning-parts/erdos243/core.tex#L852-L852), [cite at paper/reasoning-parts/erdos243/core.tex:858](../../paper/reasoning-parts/erdos243/core.tex#L858-L858), [cite at paper/reasoning-parts/erdos243/core.tex:953](../../paper/reasoning-parts/erdos243/core.tex#L953-L953), [cite at paper/reasoning-parts/erdos243/core.tex:2333](../../paper/reasoning-parts/erdos243/core.tex#L2333-L2333), [cite at paper/reasoning-parts/erdos243/core.tex:2342](../../paper/reasoning-parts/erdos243/core.tex#L2342-L2342), [cite at paper/reasoning-parts/erdos243/core.tex:2369](../../paper/reasoning-parts/erdos243/core.tex#L2369-L2369), [cite at paper/reasoning-parts/erdos243/core.tex:2417](../../paper/reasoning-parts/erdos243/core.tex#L2417-L2417), [cite at paper/reasoning-parts/erdos243/core.tex:2477](../../paper/reasoning-parts/erdos243/core.tex#L2477-L2477), [cite at paper/reasoning-parts/erdos243/core.tex:2800](../../paper/reasoning-parts/erdos243/core.tex#L2800-L2800), [cite at paper/reasoning-parts/erdos243/core.tex:2804](../../paper/reasoning-parts/erdos243/core.tex#L2804-L2804), [cite at paper/reasoning-parts/erdos243/core.tex:3124](../../paper/reasoning-parts/erdos243/core.tex#L3124-L3124), [cite at paper/reasoning-parts/erdos243/core.tex:3128](../../paper/reasoning-parts/erdos243/core.tex#L3128-L3128), [cite at paper/reasoning-parts/erdos243/core.tex:3141](../../paper/reasoning-parts/erdos243/core.tex#L3141-L3141), [cite at paper/reasoning-parts/erdos243/core.tex:3220](../../paper/reasoning-parts/erdos243/core.tex#L3220-L3220), [cite at paper/reasoning-parts/erdos243/core.tex:3221](../../paper/reasoning-parts/erdos243/core.tex#L3221-L3221), [cite at paper/reasoning-parts/erdos243/core.tex:3528](../../paper/reasoning-parts/erdos243/core.tex#L3528-L3528), [cite at paper/reasoning-parts/erdos243/core.tex:3531](../../paper/reasoning-parts/erdos243/core.tex#L3531-L3531), [cite at paper/reasoning-parts/erdos243/core.tex:3537](../../paper/reasoning-parts/erdos243/core.tex#L3537-L3537), [cite at paper/reasoning-parts/erdos243/core.tex:3817](../../paper/reasoning-parts/erdos243/core.tex#L3817-L3818)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1765-L1771) — lines `1765–1771`; excerpt `sha256:82d28a8215cfaad9830f9c69ac73ab8a39b6b8fde4ba10c62ec7be6337dc3ff0`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1646](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1646-L1646)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L793-L795) — lines `793–795`; excerpt `sha256:9418f72235db07cc6cd7f1772c2ce7a82d075de7ad72f5c574173c93b1d28da6`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3007-L3009) — lines `3007–3009`; excerpt `sha256:9418f72235db07cc6cd7f1772c2ce7a82d075de7ad72f5c574173c93b1d28da6`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2967-L2969) — lines `2967–2969`; excerpt `sha256:9418f72235db07cc6cd7f1772c2ce7a82d075de7ad72f5c574173c93b1d28da6`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L331-L331) — lines `331–331`; excerpt `sha256:e0112aa09775833b2b5805a2f000870346fe5ac721f16d8ee046c6d88b7f539e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L237-L237) — lines `237–237`; excerpt `sha256:4bb5c965a6c97930918d73aac6a90230480aa0e07852ddc5f444a141e20b74eb`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L237-L237) — lines `237–237`; excerpt `sha256:4bb5c965a6c97930918d73aac6a90230480aa0e07852ddc5f444a141e20b74eb`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L277-L277) — lines `277–277`; excerpt `sha256:4bb5c965a6c97930918d73aac6a90230480aa0e07852ddc5f444a141e20b74eb`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L277-L277) — lines `277–277`; excerpt `sha256:4bb5c965a6c97930918d73aac6a90230480aa0e07852ddc5f444a141e20b74eb`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1464-L1470) — lines `1464–1470`; excerpt `sha256:08841993ec7ee7aa859d0a63801cb36c9d22ae35f6f155707172b3fa7712308a`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9825-L9834) — lines `9825–9834`; excerpt `sha256:d09ac96b0131bd7dfc76f01dbf0e7d50ec3b4558035379307812584b13065d36`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9641-L9650) — lines `9641–9650`; excerpt `sha256:d09ac96b0131bd7dfc76f01dbf0e7d50ec3b4558035379307812584b13065d36`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:331](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L331-L331)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:783](../../paper/257/erdos-257-mersenne-support-subseries.tex#L783-L783)
- `erdos-synthesis-reading-together-record`: [cite at paper/synthesis/erdos-synthesis-reading-together-record.tex:130](../../paper/synthesis/erdos-synthesis-reading-together-record.tex#L130-L130), [cite at paper/synthesis/erdos-synthesis-reading-together-record.tex:216](../../paper/synthesis/erdos-synthesis-reading-together-record.tex#L216-L216)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:277](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L277-L277), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:556](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L556-L556), [cite at paper/reasoning-parts/erdos251/core.tex:237](../../paper/reasoning-parts/erdos251/core.tex#L237-L237), [cite at paper/reasoning-parts/erdos251/core.tex:516](../../paper/reasoning-parts/erdos251/core.tex#L516-L516)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9343](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9343-L9343), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9159](../../paper/reasoning-parts/erdos257/a257_front.tex#L9159-L9159)

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
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L82-L82) — lines `82–82`; excerpt `sha256:4ea29869cd265779e2b382b777deba5458a168a43c91355b5717552704efda65`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9426-L9431) — lines `9426–9431`; excerpt `sha256:68764d4d7a89374c4c04bae75c94f6c2e0e288f6e20da9c4a285948259753998`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9256-L9261) — lines `9256–9261`; excerpt `sha256:68764d4d7a89374c4c04bae75c94f6c2e0e288f6e20da9c4a285948259753998`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:497](../../paper/archive/erdos249-257-main-paper.tex#L497-L497), [cite at paper/archive/erdos249-257-main-paper.tex:498](../../paper/archive/erdos249-257-main-paper.tex#L498-L498), [cite at paper/archive/erdos249-257-main-paper.tex:4085](../../paper/archive/erdos249-257-main-paper.tex#L4085-L4085), [cite at paper/archive/erdos249-257-main-paper.tex:4784](../../paper/archive/erdos249-257-main-paper.tex#L4784-L4784)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9296](../../paper/249/erdos249-totient-reasoning-surface.tex#L9296-L9296), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9126](../../paper/reasoning-parts/erdos249/a249_front.tex#L9126-L9126)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4656-L4661) — lines `4656–4661`; excerpt `sha256:2eb3162258360253b5cf7a590c5d7eefeabfb1b4633350ee641a14035d11359c`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4614-L4619) — lines `4614–4619`; excerpt `sha256:2eb3162258360253b5cf7a590c5d7eefeabfb1b4633350ee641a14035d11359c`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1217-L1217) — lines `1217–1217`; excerpt `sha256:5b6b0635f8d7bc8209166c68611d1605127309d1ef4997e63819762365a6909a`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1259](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1259-L1259), [cite at paper/reasoning-parts/erdos1041/core.tex:1217](../../paper/reasoning-parts/erdos1041/core.tex#L1217-L1217)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1167-L1171) — lines `1167–1171`; excerpt `sha256:495e90612bc48250f516ad11282d20ee19e249325363e3dd38cfe59a6de6a6c5`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2860-L2864) — lines `2860–2864`; excerpt `sha256:495e90612bc48250f516ad11282d20ee19e249325363e3dd38cfe59a6de6a6c5`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2826-L2830) — lines `2826–2830`; excerpt `sha256:495e90612bc48250f516ad11282d20ee19e249325363e3dd38cfe59a6de6a6c5`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L570-L570) — lines `570–570`; excerpt `sha256:05ae035c98ef1be04452fd7e72676d785c26a101271763e5bf6acf84902d1963`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L570-L570) — lines `570–570`; excerpt `sha256:05ae035c98ef1be04452fd7e72676d785c26a101271763e5bf6acf84902d1963`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:740](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L740-L740)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:604](../../paper/68/erdos68-factorial-reasoning-surface.tex#L604-L604), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2097](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2097-L2097), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2218](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2218-L2218), [cite at paper/reasoning-parts/erdos68/core.tex:570](../../paper/reasoning-parts/erdos68/core.tex#L570-L570), [cite at paper/reasoning-parts/erdos68/core.tex:2063](../../paper/reasoning-parts/erdos68/core.tex#L2063-L2063), [cite at paper/reasoning-parts/erdos68/core.tex:2184](../../paper/reasoning-parts/erdos68/core.tex#L2184-L2184)

<a id="source-source-91756d895a28a8"></a>

### [Smith normal form in combinatorics](https://doi.org/10.1016/j.jcta.2016.06.013)

- Source id: `source-91756d895a28a8`
- Author or public identity: R. P. Stanley
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Description of Smith invariants through gcds of minors (Theorems 2.3–2.4), used for the rank-two lattice index formulas.
- Source verification: `source\_verified` — The cited passages (Thms. 2.3--2.4, p. 3) were checked against the arXiv v1 copy on 15 September 2026. This checks each locator and the stated use; it does not certify the source's proofs or imply further local use.
- Local mapping: `exact\_bibliographic\_use` — Exact local paper citation and bibliography key located.

Exact source locations:

- [Thms. 2.3--2.4, p. 3](https://doi.org/10.1016/j.jcta.2016.06.013)
- [Full text consulted at Theorems 2.3--2.4, p. 3, on Smith invariants and determinantal divisors.](https://doi.org/10.1016/j.jcta.2016.06.013)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1315-L1320) — lines `1315–1320`; excerpt `sha256:3e8d9bba274ba0d1fa7883a36808baad3612c511dcd54421d1fb5d61d279fd1e`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4575-L4580) — lines `4575–4580`; excerpt `sha256:f56843a81f14f05368c09617997aad73fc6b35003af9f80f751f87b4ad29611f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4550-L4555) — lines `4550–4555`; excerpt `sha256:f56843a81f14f05368c09617997aad73fc6b35003af9f80f751f87b4ad29611f`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1012](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1012-L1012)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3802](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3802-L3802), [cite at paper/reasoning-parts/erdos1049/core.tex:3777](../../paper/reasoning-parts/erdos1049/core.tex#L3777-L3777)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L821-L823) — lines `821–823`; excerpt `sha256:b91b61385dc89f0e6767647854a990d52e4590e0b3e52ac921e4d46e37c4a36b`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3037-L3039) — lines `3037–3039`; excerpt `sha256:b91b61385dc89f0e6767647854a990d52e4590e0b3e52ac921e4d46e37c4a36b`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2997-L2999) — lines `2997–2999`; excerpt `sha256:b91b61385dc89f0e6767647854a990d52e4590e0b3e52ac921e4d46e37c4a36b`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:616](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L616-L616), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:619](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L619-L619)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2034](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2034-L2034), [cite at paper/reasoning-parts/erdos251/core.tex:1994](../../paper/reasoning-parts/erdos251/core.tex#L1994-L1994)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1771-L1776) — lines `1771–1776`; excerpt `sha256:ed2e1d97e25042a1c3cc333a2f890caed82f4b663b8b32c55aee9808f3380583`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4619-L4624) — lines `4619–4624`; excerpt `sha256:bfa2ad242e4a6f037e19e479a20a53b503839419b0cda9e5daa5e3cb598fe13a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4577-L4582) — lines `4577–4582`; excerpt `sha256:bfa2ad242e4a6f037e19e479a20a53b503839419b0cda9e5daa5e3cb598fe13a`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:869](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L869-L869), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:924](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L924-L924), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:926](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L926-L926), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1545](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1545-L1545), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1661](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1661-L1661)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3587](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3587-L3587), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3589](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3589-L3589), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3600](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3600-L3600), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3651](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3651-L3651), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3683](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3683-L3683), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3812](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3812-L3812), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4261](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4261-L4261), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4265](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4265-L4265), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4269](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4269-L4269), [cite at paper/reasoning-parts/erdos1041/core.tex:3545](../../paper/reasoning-parts/erdos1041/core.tex#L3545-L3545), [cite at paper/reasoning-parts/erdos1041/core.tex:3547](../../paper/reasoning-parts/erdos1041/core.tex#L3547-L3547), [cite at paper/reasoning-parts/erdos1041/core.tex:3558](../../paper/reasoning-parts/erdos1041/core.tex#L3558-L3558), [cite at paper/reasoning-parts/erdos1041/core.tex:3609](../../paper/reasoning-parts/erdos1041/core.tex#L3609-L3609), [cite at paper/reasoning-parts/erdos1041/core.tex:3641](../../paper/reasoning-parts/erdos1041/core.tex#L3641-L3641), [cite at paper/reasoning-parts/erdos1041/core.tex:3770](../../paper/reasoning-parts/erdos1041/core.tex#L3770-L3770), [cite at paper/reasoning-parts/erdos1041/core.tex:4219](../../paper/reasoning-parts/erdos1041/core.tex#L4219-L4219), [cite at paper/reasoning-parts/erdos1041/core.tex:4223](../../paper/reasoning-parts/erdos1041/core.tex#L4223-L4223), [cite at paper/reasoning-parts/erdos1041/core.tex:4227](../../paper/reasoning-parts/erdos1041/core.tex#L4227-L4227)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1554-L1557) — lines `1554–1557`; excerpt `sha256:7309da2fcaace6abbd9af2aeeb912021812d164e3d40997aa7c1cb4e98c478c8`
- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L656-L660) — lines `656–660`; excerpt `sha256:bb8a82a2eaf9299171683c436633a3cdfe8688aba06e1bc995a951bd364c907e`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1395](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1395-L1395)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:450](../../paper/systems/cold-clone-to-proof-receipt.tex#L450-L450)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1760-L1765) — lines `1760–1765`; excerpt `sha256:de6f7f3e7ce0991e2f6ce37362689f9baf718419396e29df27966f24fa9d4a1f`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4646-L4651) — lines `4646–4651`; excerpt `sha256:47c15ddd8236ce68dd0ecbf6270bce0d6213cbaaf1750e780da87c87894d6230`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4604-L4609) — lines `4604–4609`; excerpt `sha256:47c15ddd8236ce68dd0ecbf6270bce0d6213cbaaf1750e780da87c87894d6230`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L120-L120) — lines `120–120`; excerpt `sha256:1ec851451ff3afc8a03f2ce9627c388291130e0150709a0d1912251780bb979f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L120-L120) — lines `120–120`; excerpt `sha256:1ec851451ff3afc8a03f2ce9627c388291130e0150709a0d1912251780bb979f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L120-L120) — lines `120–120`; excerpt `sha256:1ec851451ff3afc8a03f2ce9627c388291130e0150709a0d1912251780bb979f`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:139](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L139-L139), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:784](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L784-L784), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1644](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1644-L1644)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:162](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L162-L162), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1363](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1363-L1363), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2584](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2584-L2584), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2585](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2585-L2585), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2663](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2663-L2663), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2665](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2665-L2665), [cite at paper/reasoning-parts/erdos1041/core.tex:120](../../paper/reasoning-parts/erdos1041/core.tex#L120-L120), [cite at paper/reasoning-parts/erdos1041/core.tex:1321](../../paper/reasoning-parts/erdos1041/core.tex#L1321-L1321), [cite at paper/reasoning-parts/erdos1041/core.tex:2542](../../paper/reasoning-parts/erdos1041/core.tex#L2542-L2542), [cite at paper/reasoning-parts/erdos1041/core.tex:2543](../../paper/reasoning-parts/erdos1041/core.tex#L2543-L2543), [cite at paper/reasoning-parts/erdos1041/core.tex:2621](../../paper/reasoning-parts/erdos1041/core.tex#L2621-L2621), [cite at paper/reasoning-parts/erdos1041/core.tex:2623](../../paper/reasoning-parts/erdos1041/core.tex#L2623-L2623)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1552-L1557) — lines `1552–1557`; excerpt `sha256:b08b660d84c300da10b0cff0235eddaac275ba376ce6b7d77fbee66ccfb561fd`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:525](../../paper/systems/open-source-mathematics-strategy.tex#L525-L525), [cite at paper/systems/open-source-mathematics-strategy.tex:849](../../paper/systems/open-source-mathematics-strategy.tex#L849-L849), [cite at paper/systems/open-source-mathematics-strategy.tex:907](../../paper/systems/open-source-mathematics-strategy.tex#L907-L907)

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
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4409-L4415) — lines `4409–4415`; excerpt `sha256:62e9f12c9446297c621f7f486af4e1739cd6b6e5b979419191df4d31b8bb4cdc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4384-L4390) — lines `4384–4390`; excerpt `sha256:62e9f12c9446297c621f7f486af4e1739cd6b6e5b979419191df4d31b8bb4cdc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4157-L4157) — lines `4157–4157`; excerpt `sha256:5fd985589a096c7284944042b00248690d1d7fceed1258356a6e91864e8e051c`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4182](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4182-L4182), [cite at paper/reasoning-parts/erdos1049/core.tex:4157](../../paper/reasoning-parts/erdos1049/core.tex#L4157-L4157)
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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1592-L1598) — lines `1592–1598`; excerpt `sha256:50025897e9875f1e8eb278c5a5c91ea2be1d03b9c7afc2bedf2dcec1c82f6162`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:522](../../paper/systems/open-source-mathematics-strategy.tex#L522-L522), [cite at paper/systems/open-source-mathematics-strategy.tex:710](../../paper/systems/open-source-mathematics-strategy.tex#L710-L710)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4607-L4614) — lines `4607–4614`; excerpt `sha256:ac93a1f2c5c87957117830efd99688e57dc988e65987811c68128cdf2f71aa9f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4565-L4572) — lines `4565–4572`; excerpt `sha256:ac93a1f2c5c87957117830efd99688e57dc988e65987811c68128cdf2f71aa9f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L3675-L3675) — lines `3675–3675`; excerpt `sha256:789975730662255be1953f14644da72f9bee1ce16a61867e38c8b7ddd266fcb5`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3717](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3717-L3717), [cite at paper/reasoning-parts/erdos1041/core.tex:3675](../../paper/reasoning-parts/erdos1041/core.tex#L3675-L3675)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L665-L668) — lines `665–668`; excerpt `sha256:6a2d98ee6e3166e49ad37af7f7fe86c949a4155e4ba493a60d73e7ff90e2c8e9`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1572-L1577) — lines `1572–1577`; excerpt `sha256:a4a2cd5ff74bcf8ec7bc773aba6629192b6c1e90033142603ec6d7509d3e306e`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:458](../../paper/systems/cold-clone-to-proof-receipt.tex#L458-L458)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:922](../../paper/systems/open-source-mathematics-strategy.tex#L922-L922)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2967-L2970) — lines `2967–2970`; excerpt `sha256:24eacdd006d27f46e0ea49feb1a0b92cc03b5cd554204a5ff82c31aef527f7d2`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2922-L2925) — lines `2922–2925`; excerpt `sha256:24eacdd006d27f46e0ea49feb1a0b92cc03b5cd554204a5ff82c31aef527f7d2`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L145-L145) — lines `145–145`; excerpt `sha256:1c00ff08c0bb546e88524087a8ce119b5c6657047f90ea161ba3a81fc71d61e6`
- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5325-L5328) — lines `5325–5328`; excerpt `sha256:d83b8379aa5d3a8d993822c9518436371502939df5b9c449f945ffb60730454b`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:495](../../paper/archive/erdos249-257-main-paper.tex#L495-L495), [cite at paper/archive/erdos249-257-main-paper.tex:4084](../../paper/archive/erdos249-257-main-paper.tex#L4084-L4084), [cite at paper/archive/erdos249-257-main-paper.tex:4678](../../paper/archive/erdos249-257-main-paper.tex#L4678-L4678), [cite at paper/archive/erdos249-257-main-paper.tex:4782](../../paper/archive/erdos249-257-main-paper.tex#L4782-L4782)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:190](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L190-L190), [cite at paper/reasoning-parts/erdos269/core.tex:145](../../paper/reasoning-parts/erdos269/core.tex#L145-L145)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1089-L1092) — lines `1089–1092`; excerpt `sha256:2fd518712f78c5863c24df2988af2303d5d5610ce069a736fcb6f69c30c4d37b`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9386-L9390) — lines `9386–9390`; excerpt `sha256:6f68ca842cab80e0e80859b0448d856556a74a77fbf2793f408455173289681c`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9216-L9220) — lines `9216–9220`; excerpt `sha256:6f68ca842cab80e0e80859b0448d856556a74a77fbf2793f408455173289681c`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:615](../../paper/249/erdos-249-binary-totient-series.tex#L615-L615)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:1459](../../paper/249/erdos249-totient-reasoning-surface.tex#L1459-L1459), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:1289](../../paper/reasoning-parts/erdos249/a249_front.tex#L1289-L1289)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L673-L679) — lines `673–679`; excerpt `sha256:915b21de98fc6d842625837028364b4383eeb5ccd9db3a58c6484bb7d7791545`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1608-L1612) — lines `1608–1612`; excerpt `sha256:7052c9564e3a50f71416b68353c32c939efbb5b719a371014e847871a2e0b349`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1300](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1300-L1300)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:377](../../paper/systems/cold-clone-to-proof-receipt.tex#L377-L377), [cite at paper/systems/cold-clone-to-proof-receipt.tex:464](../../paper/systems/cold-clone-to-proof-receipt.tex#L464-L464)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L343-L343) — lines `343–343`; excerpt `sha256:de42989aca8e9f9df81b70cf216ea13bde1ed2a0f52324ffcb596652690e9c1e`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L803-L805) — lines `803–805`; excerpt `sha256:a68775eea867950e9742ad93dd4089e04252a31cf488340177ac456e7b57c84f`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L446-L446) — lines `446–446`; excerpt `sha256:44c17b2b122a67bbb353a05e6a8b3a57d8a7784d280452abe114db8702131123`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3019-L3021) — lines `3019–3021`; excerpt `sha256:a68775eea867950e9742ad93dd4089e04252a31cf488340177ac456e7b57c84f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L406-L406) — lines `406–406`; excerpt `sha256:44c17b2b122a67bbb353a05e6a8b3a57d8a7784d280452abe114db8702131123`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2979-L2981) — lines `2979–2981`; excerpt `sha256:a68775eea867950e9742ad93dd4089e04252a31cf488340177ac456e7b57c84f`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:343](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L343-L343)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:446](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L446-L446), [cite at paper/reasoning-parts/erdos251/core.tex:406](../../paper/reasoning-parts/erdos251/core.tex#L406-L406)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3005-L3007) — lines `3005–3007`; excerpt `sha256:2bdb1af734a1c86a2ea7603f390d84d3309c1d1abf8a8f4eb21930714a5a0c9d`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2965-L2967) — lines `2965–2967`; excerpt `sha256:2bdb1af734a1c86a2ea7603f390d84d3309c1d1abf8a8f4eb21930714a5a0c9d`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1300](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1300-L1300), [cite at paper/reasoning-parts/erdos251/core.tex:1260](../../paper/reasoning-parts/erdos251/core.tex#L1260-L1260)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3028-L3033) — lines `3028–3033`; excerpt `sha256:4d3c475c2dd44a15da10bb68d05eedaa5bb7ef373c98a81bf0994e003e8022e6`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2983-L2988) — lines `2983–2988`; excerpt `sha256:4d3c475c2dd44a15da10bb68d05eedaa5bb7ef373c98a81bf0994e003e8022e6`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2266](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2266-L2266), [cite at paper/reasoning-parts/erdos269/core.tex:2221](../../paper/reasoning-parts/erdos269/core.tex#L2221-L2221)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1435-L1441) — lines `1435–1441`; excerpt `sha256:3f90c9c82f80686f1efe4c911cd5f754201a1464c150d626d59690b5e96927f9`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9783-L9789) — lines `9783–9789`; excerpt `sha256:3f90c9c82f80686f1efe4c911cd5f754201a1464c150d626d59690b5e96927f9`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9599-L9605) — lines `9599–9605`; excerpt `sha256:3f90c9c82f80686f1efe4c911cd5f754201a1464c150d626d59690b5e96927f9`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1205](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1205-L1205)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1092](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1092-L1092), [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9655](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9655-L9655), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:908](../../paper/reasoning-parts/erdos257/a257_front.tex#L908-L908), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9471](../../paper/reasoning-parts/erdos257/a257_front.tex#L9471-L9471)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1782-L1789) — lines `1782–1789`; excerpt `sha256:0b086dc6c508b56a163e9e87eadee8f83406883c0bb951c90f8c3195b296ef03`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4624-L4631) — lines `4624–4631`; excerpt `sha256:ff50af06cc617795c60c2ca89ddaec781a6c4593028140edc22775c58cb3e3a9`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4582-L4589) — lines `4582–4589`; excerpt `sha256:ff50af06cc617795c60c2ca89ddaec781a6c4593028140edc22775c58cb3e3a9`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:721](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L721-L721), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1665](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1665-L1665)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:329](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L329-L329), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1173](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1173-L1173), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1285](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1285-L1285), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1428](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1428-L1428), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3346](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3346-L3346), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3718](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3718-L3718), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3813](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3813-L3813), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3862](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3862-L3862), [cite at paper/reasoning-parts/erdos1041/core.tex:287](../../paper/reasoning-parts/erdos1041/core.tex#L287-L287), [cite at paper/reasoning-parts/erdos1041/core.tex:1131](../../paper/reasoning-parts/erdos1041/core.tex#L1131-L1131), [cite at paper/reasoning-parts/erdos1041/core.tex:1243](../../paper/reasoning-parts/erdos1041/core.tex#L1243-L1243), [cite at paper/reasoning-parts/erdos1041/core.tex:1386](../../paper/reasoning-parts/erdos1041/core.tex#L1386-L1386), [cite at paper/reasoning-parts/erdos1041/core.tex:3304](../../paper/reasoning-parts/erdos1041/core.tex#L3304-L3304), [cite at paper/reasoning-parts/erdos1041/core.tex:3676](../../paper/reasoning-parts/erdos1041/core.tex#L3676-L3676), [cite at paper/reasoning-parts/erdos1041/core.tex:3771](../../paper/reasoning-parts/erdos1041/core.tex#L3771-L3771), [cite at paper/reasoning-parts/erdos1041/core.tex:3820](../../paper/reasoning-parts/erdos1041/core.tex#L3820-L3820)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1643-L1648) — lines `1643–1648`; excerpt `sha256:a2823f7bc0eabe07dcb16e2476c88ca0a6ae7777617c24762b0674c83ce2e1da`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:869](../../paper/systems/open-source-mathematics-strategy.tex#L869-L869)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1573-L1576) — lines `1573–1576`; excerpt `sha256:e775b66977668941a659b8429f65fc028df3b7a6b4da133136e26469b36e69a1`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1618-L1623) — lines `1618–1623`; excerpt `sha256:17dfc81b2347996ae518d9ae35b9f4cbbe428802c4df971c821bb500a90d87de`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:977](../../paper/systems/claim-faithful-publication-systems-paper.tex#L977-L977), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1308](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1308-L1308), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1355](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1355-L1355)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:622](../../paper/systems/open-source-mathematics-strategy.tex#L622-L622), [cite at paper/systems/open-source-mathematics-strategy.tex:678](../../paper/systems/open-source-mathematics-strategy.tex#L678-L678), [cite at paper/systems/open-source-mathematics-strategy.tex:756](../../paper/systems/open-source-mathematics-strategy.tex#L756-L756), [cite at paper/systems/open-source-mathematics-strategy.tex:884](../../paper/systems/open-source-mathematics-strategy.tex#L884-L884), [cite at paper/systems/open-source-mathematics-strategy.tex:997](../../paper/systems/open-source-mathematics-strategy.tex#L997-L997)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1101-L1106) — lines `1101–1106`; excerpt `sha256:1afac1390d37599a1aabc74b5e4f00b9c13fe3b5510b23747164aafc5cabb79f`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9494-L9499) — lines `9494–9499`; excerpt `sha256:1afac1390d37599a1aabc74b5e4f00b9c13fe3b5510b23747164aafc5cabb79f`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9324-L9329) — lines `9324–9329`; excerpt `sha256:1afac1390d37599a1aabc74b5e4f00b9c13fe3b5510b23747164aafc5cabb79f`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:358](../../paper/249/erdos-249-binary-totient-series.tex#L358-L358), [cite at paper/249/erdos-249-binary-totient-series.tex:755](../../paper/249/erdos-249-binary-totient-series.tex#L755-L755)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:264](../../paper/249/erdos249-totient-reasoning-surface.tex#L264-L264), [cite at paper/249/erdos249-totient-reasoning-surface.tex:266](../../paper/249/erdos249-totient-reasoning-surface.tex#L266-L266), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:94](../../paper/reasoning-parts/erdos249/a249_front.tex#L94-L94), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:96](../../paper/reasoning-parts/erdos249/a249_front.tex#L96-L96)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1579-L1582) — lines `1579–1582`; excerpt `sha256:8ab339d3f03d368563034e43b8b108cfb876801aaf50ed2c3f951f5bb490d37e`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1628-L1633) — lines `1628–1633`; excerpt `sha256:d7199ff140a739a7be732b44e20113885c623918791626d0f99bd6c7e2a83cc2`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1312](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1312-L1312)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:704](../../paper/systems/open-source-mathematics-strategy.tex#L704-L704), [cite at paper/systems/open-source-mathematics-strategy.tex:943](../../paper/systems/open-source-mathematics-strategy.tex#L943-L943)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4666-L4672) — lines `4666–4672`; excerpt `sha256:bcdad75ad0ef6a705b6fe89763d0da02f0663ec648798c57bec9c5455264dc47`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4624-L4630) — lines `4624–4630`; excerpt `sha256:bcdad75ad0ef6a705b6fe89763d0da02f0663ec648798c57bec9c5455264dc47`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1215-L1215) — lines `1215–1215`; excerpt `sha256:8f0116d285182c3169d8171b8d13c4c752a018a50c51df8dfd0a78fe648e1fe0`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1257](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1257-L1257), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1261](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1261-L1261), [cite at paper/reasoning-parts/erdos1041/core.tex:1215](../../paper/reasoning-parts/erdos1041/core.tex#L1215-L1215), [cite at paper/reasoning-parts/erdos1041/core.tex:1219](../../paper/reasoning-parts/erdos1041/core.tex#L1219-L1219)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2876-L2880) — lines `2876–2880`; excerpt `sha256:3a26f5bc4eb9c2426ec95588f15ecf2d22cd99dd0ae4aa88e40f0d69fe5e8750`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2842-L2846) — lines `2842–2846`; excerpt `sha256:3a26f5bc4eb9c2426ec95588f15ecf2d22cd99dd0ae4aa88e40f0d69fe5e8750`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L574-L574) — lines `574–574`; excerpt `sha256:5139a5f6ebb95c3e704baeace6907b8ca37b7f8ea44fd4d7e73ced8285e38c76`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L574-L574) — lines `574–574`; excerpt `sha256:5139a5f6ebb95c3e704baeace6907b8ca37b7f8ea44fd4d7e73ced8285e38c76`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1175-L1179) — lines `1175–1179`; excerpt `sha256:e8cae7318c8c143094d52d1da99fd4dda7271236e256e02a746de55f05d72d67`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1064](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1064-L1064)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:608](../../paper/68/erdos68-factorial-reasoning-surface.tex#L608-L608), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2099](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2099-L2099), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2269](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2269-L2269), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2276](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2276-L2276), [cite at paper/reasoning-parts/erdos68/core.tex:574](../../paper/reasoning-parts/erdos68/core.tex#L574-L574), [cite at paper/reasoning-parts/erdos68/core.tex:2065](../../paper/reasoning-parts/erdos68/core.tex#L2065-L2065), [cite at paper/reasoning-parts/erdos68/core.tex:2235](../../paper/reasoning-parts/erdos68/core.tex#L2235-L2235), [cite at paper/reasoning-parts/erdos68/core.tex:2242](../../paper/reasoning-parts/erdos68/core.tex#L2242-L2242)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4525-L4531) — lines `4525–4531`; excerpt `sha256:547a282df5e35d2d260581efbb9d6958a6a3bf47c2d9a4d9b39949fd65e27f76`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4500-L4506) — lines `4500–4506`; excerpt `sha256:547a282df5e35d2d260581efbb9d6958a6a3bf47c2d9a4d9b39949fd65e27f76`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L3961-L3961) — lines `3961–3961`; excerpt `sha256:54e3d1ef752ffcb54e8ee1bfe7534ff85b97adcfec7a02daa218a664d09cd7f7`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L3961-L3961) — lines `3961–3961`; excerpt `sha256:54e3d1ef752ffcb54e8ee1bfe7534ff85b97adcfec7a02daa218a664d09cd7f7`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L3961-L3961) — lines `3961–3961`; excerpt `sha256:54e3d1ef752ffcb54e8ee1bfe7534ff85b97adcfec7a02daa218a664d09cd7f7`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3986](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3986-L3986), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4134](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4134-L4134), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4139](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4139-L4139), [cite at paper/reasoning-parts/erdos1049/core.tex:3961](../../paper/reasoning-parts/erdos1049/core.tex#L3961-L3961), [cite at paper/reasoning-parts/erdos1049/core.tex:4109](../../paper/reasoning-parts/erdos1049/core.tex#L4109-L4109), [cite at paper/reasoning-parts/erdos1049/core.tex:4114](../../paper/reasoning-parts/erdos1049/core.tex#L4114-L4114)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L838-L841) — lines `838–841`; excerpt `sha256:56c3313573f1c66b97e759caddfa08857ff02beecce742ca74aa60516751dfb8`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3018-L3021) — lines `3018–3021`; excerpt `sha256:56c3313573f1c66b97e759caddfa08857ff02beecce742ca74aa60516751dfb8`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2973-L2976) — lines `2973–2976`; excerpt `sha256:56c3313573f1c66b97e759caddfa08857ff02beecce742ca74aa60516751dfb8`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:697](../../paper/269/erdos-269-three-prime-running-lcm.tex#L697-L697)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:151](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L151-L151), [cite at paper/reasoning-parts/erdos269/core.tex:106](../../paper/reasoning-parts/erdos269/core.tex#L106-L106)

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

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4014-L4020) — lines `4014–4020`; excerpt `sha256:114c6c590cc9d93a8ef21180697160ce21e5fd0ef2e6801cfa8c3bd3dc16e78c`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3982-L3988) — lines `3982–3988`; excerpt `sha256:114c6c590cc9d93a8ef21180697160ce21e5fd0ef2e6801cfa8c3bd3dc16e78c`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1169-L1175) — lines `1169–1175`; excerpt `sha256:4a2a8e4fc977c8352311e72ae7979c821e66a3545b5d72c4ade3b36bc5e51666`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:728](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L728-L728)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:348](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L348-L348), [cite at paper/reasoning-parts/erdos243/core.tex:316](../../paper/reasoning-parts/erdos243/core.tex#L316-L316)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1561-L1564) — lines `1561–1564`; excerpt `sha256:2399864b4721f4d5705dac2a1f050ccf6c91d2631e715007d632aebad0c35d25`
- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L696-L700) — lines `696–700`; excerpt `sha256:3a090cc943cde6fe32e768b3fec5c8f9941b86fe85cffb0b1e502eff8703ea31`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1603-L1608) — lines `1603–1608`; excerpt `sha256:cbc96d2ca058731561fda44e70b5d2f239fbaf14f1de0bb2732381fdead4b7fe`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1403](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1403-L1403)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:498](../../paper/systems/cold-clone-to-proof-receipt.tex#L498-L498)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:932](../../paper/systems/open-source-mathematics-strategy.tex#L932-L932)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1615-L1618) — lines `1615–1618`; excerpt `sha256:06270751176ee840e9cf84912d799856c76acd07dbc3c72f014dda02fc1854e3`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1598-L1603) — lines `1598–1603`; excerpt `sha256:ba3b7d334c4533a7eb892544f07793a641502451252ef40f9dd35e8d49823e68`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1304](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1304-L1304)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:930](../../paper/systems/open-source-mathematics-strategy.tex#L930-L930)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1304-L1315) — lines `1304–1315`; excerpt `sha256:ded7a6e73c64eb888bff8d92fdf9045c0912b78b36a09aaf5d4f28ab76caf53f`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4435-L4446) — lines `4435–4446`; excerpt `sha256:28607cac7b070bebdf820b61863c3daadc81c336a532ef5ffb850e0444467fbe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4410-L4421) — lines `4410–4421`; excerpt `sha256:28607cac7b070bebdf820b61863c3daadc81c336a532ef5ffb850e0444467fbe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L816-L816) — lines `816–816`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L816-L816) — lines `816–816`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L816-L816) — lines `816–816`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L816-L816) — lines `816–816`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L816-L816) — lines `816–816`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L816-L816) — lines `816–816`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L3-L12) — lines `3–12`; excerpt `sha256:2c6a0d27c905ea48c1f25e9aa96f3007e323409c7b093d69e63e5d6389c5dd78`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L294-L341) — lines `294–341`; excerpt `sha256:079ff692126bd3e4d34f548fea370a492cd0c13ef7f93ce3fb3dd3ad6697e51f`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L1373-L1380) — lines `1373–1380`; excerpt `sha256:00ffa8698a1534c856de8c5358848f0e1631280815d61cd62dccca5b31c96703`
- [lean/ErdosProblems/Erdos1049/AdelicHeightBridge.lean](../../lean/ErdosProblems/Erdos1049/AdelicHeightBridge.lean#L177-L184) — lines `177–184`; excerpt `sha256:48cded238c23f3b69267c7634831949873ba61edbfc1d81d7be4e4f53a9dfa1f`
- [lean/ErdosProblems/Erdos1049/AllRow/Producer.lean](../../lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L139-L144) — lines `139–144`; excerpt `sha256:d91ba4591cce7012da8fb4b68e2c502744e2a86cbff69f02ac661f05bbbc77f0`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L675-L679) — lines `675–679`; excerpt `sha256:f4bd612442f7360245d4b631cbdc499c687fc3d6d13818a39db22dc67e091077`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:485](../../paper/1049/erdos-1049-rational-base-lambert.tex#L485-L485), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:502](../../paper/1049/erdos-1049-rational-base-lambert.tex#L502-L502), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:614](../../paper/1049/erdos-1049-rational-base-lambert.tex#L614-L614), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:631](../../paper/1049/erdos-1049-rational-base-lambert.tex#L631-L631), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1172](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1172-L1172)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:841](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L841-L841), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1459](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1459-L1459), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1462](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1462-L1462), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1479](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1479-L1479), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1490](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1490-L1490), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1514](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1514-L1514), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1810](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1810-L1810), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2130](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2130-L2130), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4271](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4271-L4271), [cite at paper/reasoning-parts/erdos1049/core.tex:816](../../paper/reasoning-parts/erdos1049/core.tex#L816-L816), [cite at paper/reasoning-parts/erdos1049/core.tex:1434](../../paper/reasoning-parts/erdos1049/core.tex#L1434-L1434), [cite at paper/reasoning-parts/erdos1049/core.tex:1437](../../paper/reasoning-parts/erdos1049/core.tex#L1437-L1437), [cite at paper/reasoning-parts/erdos1049/core.tex:1454](../../paper/reasoning-parts/erdos1049/core.tex#L1454-L1454), [cite at paper/reasoning-parts/erdos1049/core.tex:1465](../../paper/reasoning-parts/erdos1049/core.tex#L1465-L1465), [cite at paper/reasoning-parts/erdos1049/core.tex:1489](../../paper/reasoning-parts/erdos1049/core.tex#L1489-L1489), [cite at paper/reasoning-parts/erdos1049/core.tex:1785](../../paper/reasoning-parts/erdos1049/core.tex#L1785-L1785), [cite at paper/reasoning-parts/erdos1049/core.tex:2105](../../paper/reasoning-parts/erdos1049/core.tex#L2105-L2105), [cite at paper/reasoning-parts/erdos1049/core.tex:4246](../../paper/reasoning-parts/erdos1049/core.tex#L4246-L4246)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1562-L1567) — lines `1562–1567`; excerpt `sha256:6f2b691dbea0a4758a07048f06dca1acfc4049444971d8bdfab57f8bf75e6a02`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:523](../../paper/systems/open-source-mathematics-strategy.tex#L523-L523), [cite at paper/systems/open-source-mathematics-strategy.tex:915](../../paper/systems/open-source-mathematics-strategy.tex#L915-L915)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1138-L1142) — lines `1138–1142`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3976-L3980) — lines `3976–3980`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3944-L3948) — lines `3944–3948`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L751-L751) — lines `751–751`; excerpt `sha256:ed7a349b06c0fa968d6eac74252e7f637f42e8018159ddf7e209ad4a3fae8037`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L751-L751) — lines `751–751`; excerpt `sha256:ed7a349b06c0fa968d6eac74252e7f637f42e8018159ddf7e209ad4a3fae8037`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2880-L2884) — lines `2880–2884`; excerpt `sha256:82a9d3633d44a7f0d1eb428949e60377edee33c29aa6e38e5941bceb6b962b77`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2846-L2850) — lines `2846–2850`; excerpt `sha256:82a9d3633d44a7f0d1eb428949e60377edee33c29aa6e38e5941bceb6b962b77`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1903-L1903) — lines `1903–1903`; excerpt `sha256:29422f1117ddf0cfe478b48719a3b1d57db703b18e788e0dd9e85d0344241384`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1903-L1903) — lines `1903–1903`; excerpt `sha256:29422f1117ddf0cfe478b48719a3b1d57db703b18e788e0dd9e85d0344241384`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1903-L1903) — lines `1903–1903`; excerpt `sha256:29422f1117ddf0cfe478b48719a3b1d57db703b18e788e0dd9e85d0344241384`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:661](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L661-L661)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:783](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L783-L783), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1686](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1686-L1686), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3703](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3703-L3703), [cite at paper/reasoning-parts/erdos243/core.tex:751](../../paper/reasoning-parts/erdos243/core.tex#L751-L751), [cite at paper/reasoning-parts/erdos243/core.tex:1654](../../paper/reasoning-parts/erdos243/core.tex#L1654-L1654), [cite at paper/reasoning-parts/erdos243/core.tex:3671](../../paper/reasoning-parts/erdos243/core.tex#L3671-L3671)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1937](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1937-L1937), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2309](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2309-L2309), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2312](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2312-L2312), [cite at paper/reasoning-parts/erdos68/core.tex:1903](../../paper/reasoning-parts/erdos68/core.tex#L1903-L1903), [cite at paper/reasoning-parts/erdos68/core.tex:2275](../../paper/reasoning-parts/erdos68/core.tex#L2275-L2275), [cite at paper/reasoning-parts/erdos68/core.tex:2278](../../paper/reasoning-parts/erdos68/core.tex#L2278-L2278)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1826-L1830) — lines `1826–1830`; excerpt `sha256:e71562d62b7120e70fe7b834f65baa80911382d9eec508f8396928584ab1dacf`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4697-L4701) — lines `4697–4701`; excerpt `sha256:e71562d62b7120e70fe7b834f65baa80911382d9eec508f8396928584ab1dacf`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4655-L4659) — lines `4655–4659`; excerpt `sha256:e71562d62b7120e70fe7b834f65baa80911382d9eec508f8396928584ab1dacf`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1333](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1333-L1333), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1399](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1399-L1399), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1533](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1533-L1533)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2681](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2681-L2681), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:3816](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L3816-L3816), [cite at paper/reasoning-parts/erdos1041/core.tex:2639](../../paper/reasoning-parts/erdos1041/core.tex#L2639-L2639), [cite at paper/reasoning-parts/erdos1041/core.tex:3774](../../paper/reasoning-parts/erdos1041/core.tex#L3774-L3774)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3017-L3019) — lines `3017–3019`; excerpt `sha256:8724712f34a0b9289550c3ab049d6a1ee5927433c0a4731b5a6cab0280040067`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2977-L2979) — lines `2977–2979`; excerpt `sha256:8724712f34a0b9289550c3ab049d6a1ee5927433c0a4731b5a6cab0280040067`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L602-L602) — lines `602–602`; excerpt `sha256:c384e283f82a7af357601d537bf3fea0643aec17edef2b2d3fe55664a758a772`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L767-L769) — lines `767–769`; excerpt `sha256:dedbedb4b5e1a08ab2446808a684bf784d81c2ed1909441478d6080382ea7852`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L642-L642) — lines `642–642`; excerpt `sha256:c384e283f82a7af357601d537bf3fea0643aec17edef2b2d3fe55664a758a772`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:642](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L642-L642), [cite at paper/reasoning-parts/erdos251/core.tex:602](../../paper/reasoning-parts/erdos251/core.tex#L602-L602)

<a id="source-source-b300504b513ffb"></a>

### [EconCSLib: AI-Assisted Lean Formalization for Economics & Computation Research](https://doi.org/10.48550/arXiv.2606.13306)

- Source id: `source-b300504b513ffb`
- Author or public identity: N. Garg
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1564-L1567) — lines `1564–1567`; excerpt `sha256:54abdd25410da1b47e3fb5b3fac6ade4ff7dd291f4b481a9e515560c74f3ab42`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1404](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1404-L1404)

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
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1159-L1163) — lines `1159–1163`; excerpt `sha256:b630a0f0ca592293699970eda53a16eea623a9f1d81f881c6dc903179a78eeec`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2844-L2848) — lines `2844–2848`; excerpt `sha256:b630a0f0ca592293699970eda53a16eea623a9f1d81f881c6dc903179a78eeec`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1155-L1160) — lines `1155–1160`; excerpt `sha256:78f98ff5782c3f26518953792349ad37efb90e1c262886d330c17b9bd9667677`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3993-L3998) — lines `3993–3998`; excerpt `sha256:eaf6cb9470a050bc0ac5978773ab824fd5e2486d1c128ad600ecc049ec5e1863`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L773-L775) — lines `773–775`; excerpt `sha256:d48a3b5fc1a3db1218dc2cebafed7ac30142d5ecb2e63f7fecff1e2a5c569695`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2975-L2977) — lines `2975–2977`; excerpt `sha256:33443e1df07646c816cedeb1eb59f9662fa5abee19c5b12c98dc3dbea83c505f`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2955-L2958) — lines `2955–2958`; excerpt `sha256:a170cdfc562020c04faf65c58a81863df6e925b08eae36eba6e3fe186dbf1eb0`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L799-L802) — lines `799–802`; excerpt `sha256:a170cdfc562020c04faf65c58a81863df6e925b08eae36eba6e3fe186dbf1eb0`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1286-L1290) — lines `1286–1290`; excerpt `sha256:46dc589925f18c98a38b701dc32978cf7bf47298f8b19fc97e2d6eb3b37ddaf2`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4401-L4405) — lines `4401–4405`; excerpt `sha256:5dc4499ba85b2a90c1b7eeae654d404e424be3f9aa288c8eaf30e698ab7cf0e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4376-L4380) — lines `4376–4380`; excerpt `sha256:5dc4499ba85b2a90c1b7eeae654d404e424be3f9aa288c8eaf30e698ab7cf0e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L45-L45) — lines `45–45`; excerpt `sha256:daac0a1d16bf29ee1a7aed78143060b303b0c73e76e968b083ac1748e249105f`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3961-L3966) — lines `3961–3966`; excerpt `sha256:eaf6cb9470a050bc0ac5978773ab824fd5e2486d1c128ad600ecc049ec5e1863`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L43-L43) — lines `43–43`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L43-L43) — lines `43–43`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2935-L2937) — lines `2935–2937`; excerpt `sha256:33443e1df07646c816cedeb1eb59f9662fa5abee19c5b12c98dc3dbea83c505f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L48-L48) — lines `48–48`; excerpt `sha256:7f9971210ce1d8295bfd2da08dd2dae6cde77e72e05cc25210e713a613768912`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L48-L48) — lines `48–48`; excerpt `sha256:7f9971210ce1d8295bfd2da08dd2dae6cde77e72e05cc25210e713a613768912`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2910-L2913) — lines `2910–2913`; excerpt `sha256:a170cdfc562020c04faf65c58a81863df6e925b08eae36eba6e3fe186dbf1eb0`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:44fd9c14c25e5775404be7ccea03d3057255373bee9505c5739d20d124ad3866`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:44fd9c14c25e5775404be7ccea03d3057255373bee9505c5739d20d124ad3866`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L29-L29) — lines `29–29`; excerpt `sha256:44fd9c14c25e5775404be7ccea03d3057255373bee9505c5739d20d124ad3866`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2810-L2814) — lines `2810–2814`; excerpt `sha256:b630a0f0ca592293699970eda53a16eea623a9f1d81f881c6dc903179a78eeec`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L58-L58) — lines `58–58`; excerpt `sha256:8b98e4914a5c561507a8e98d3359f73caa242a5011b9b09998c78cfb7e4ce514`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:67](../../paper/1049/erdos-1049-rational-base-lambert.tex#L67-L67)
- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:144](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L144-L144)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:322](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L322-L322)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:57](../../paper/269/erdos-269-three-prime-running-lcm.tex#L57-L57)
- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:131](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L131-L131)
- `erdos-synthesis-subsums-across-bases`: [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:58](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L58-L58)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:70](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L70-L70), [cite at paper/reasoning-parts/erdos1049/core.tex:45](../../paper/reasoning-parts/erdos1049/core.tex#L45-L45)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:75](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L75-L75), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:766](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L766-L766), [cite at paper/reasoning-parts/erdos243/core.tex:43](../../paper/reasoning-parts/erdos243/core.tex#L43-L43), [cite at paper/reasoning-parts/erdos243/core.tex:734](../../paper/reasoning-parts/erdos243/core.tex#L734-L734)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:193](../../paper/archive/erdos249-257-main-paper.tex#L193-L193), [cite at paper/archive/erdos249-257-main-paper.tex:195](../../paper/archive/erdos249-257-main-paper.tex#L195-L195)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:88](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L88-L88), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:497](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L497-L497), [cite at paper/reasoning-parts/erdos251/core.tex:48](../../paper/reasoning-parts/erdos251/core.tex#L48-L48), [cite at paper/reasoning-parts/erdos251/core.tex:457](../../paper/reasoning-parts/erdos251/core.tex#L457-L457)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:74](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L74-L74), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2497](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2497-L2497), [cite at paper/reasoning-parts/erdos269/core.tex:29](../../paper/reasoning-parts/erdos269/core.tex#L29-L29), [cite at paper/reasoning-parts/erdos269/core.tex:2452](../../paper/reasoning-parts/erdos269/core.tex#L2452-L2452)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:92](../../paper/68/erdos68-factorial-reasoning-surface.tex#L92-L92), [cite at paper/reasoning-parts/erdos68/core.tex:58](../../paper/reasoning-parts/erdos68/core.tex#L58-L58)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1195-L1199) — lines `1195–1199`; excerpt `sha256:eb4b28f73e685f8395aaa64be8cef4676a9807d8e5c53e9480cb7c0132a381f6`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2900-L2904) — lines `2900–2904`; excerpt `sha256:eb4b28f73e685f8395aaa64be8cef4676a9807d8e5c53e9480cb7c0132a381f6`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2866-L2870) — lines `2866–2870`; excerpt `sha256:eb4b28f73e685f8395aaa64be8cef4676a9807d8e5c53e9480cb7c0132a381f6`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1048-L1048) — lines `1048–1048`; excerpt `sha256:fd1185408488f8cb948bfd34f2b8d50d7e05fe3fa95d2f2c017261121f5b1c11`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1048-L1048) — lines `1048–1048`; excerpt `sha256:fd1185408488f8cb948bfd34f2b8d50d7e05fe3fa95d2f2c017261121f5b1c11`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1048-L1048) — lines `1048–1048`; excerpt `sha256:fd1185408488f8cb948bfd34f2b8d50d7e05fe3fa95d2f2c017261121f5b1c11`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1048-L1048) — lines `1048–1048`; excerpt `sha256:fd1185408488f8cb948bfd34f2b8d50d7e05fe3fa95d2f2c017261121f5b1c11`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L422-L422) — lines `422–422`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L422-L422) — lines `422–422`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L422-L422) — lines `422–422`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1048](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1048-L1048), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1049](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1049-L1049), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1050](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1050-L1050), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1051](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1051-L1051)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:456](../../paper/68/erdos68-factorial-reasoning-surface.tex#L456-L456), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:457](../../paper/68/erdos68-factorial-reasoning-surface.tex#L457-L457), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:459](../../paper/68/erdos68-factorial-reasoning-surface.tex#L459-L459), [cite at paper/reasoning-parts/erdos68/core.tex:422](../../paper/reasoning-parts/erdos68/core.tex#L422-L422), [cite at paper/reasoning-parts/erdos68/core.tex:423](../../paper/reasoning-parts/erdos68/core.tex#L423-L423), [cite at paper/reasoning-parts/erdos68/core.tex:425](../../paper/reasoning-parts/erdos68/core.tex#L425-L425)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2940-L2944) — lines `2940–2944`; excerpt `sha256:3505a37c28e494a2a50e4fe25e04a275f47dea02e877ed8c2299dbfd058f927a`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2906-L2910) — lines `2906–2910`; excerpt `sha256:3505a37c28e494a2a50e4fe25e04a275f47dea02e877ed8c2299dbfd058f927a`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1629](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1629-L1629), [cite at paper/reasoning-parts/erdos68/core.tex:1595](../../paper/reasoning-parts/erdos68/core.tex#L1595-L1595)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L825-L827) — lines `825–827`; excerpt `sha256:8f10822b69cd8cf883503ebca2d3926c448249cf09f66999038ab3b2c5b3aaf7`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3041-L3043) — lines `3041–3043`; excerpt `sha256:4d23f3968fb1ccd53933b23fc840988fd48072550d470fc5a28559b929df023f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3001-L3003) — lines `3001–3003`; excerpt `sha256:4d23f3968fb1ccd53933b23fc840988fd48072550d470fc5a28559b929df023f`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:752](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L752-L752)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:606](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L606-L606), [cite at paper/reasoning-parts/erdos251/core.tex:566](../../paper/reasoning-parts/erdos251/core.tex#L566-L566)

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

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4721-L4725) — lines `4721–4725`; excerpt `sha256:99939ef8c0a5cb1b8c7690f76fd5e569b585f9d6d4c28a5194e30f4c7f6c42d0`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4679-L4683) — lines `4679–4683`; excerpt `sha256:99939ef8c0a5cb1b8c7690f76fd5e569b585f9d6d4c28a5194e30f4c7f6c42d0`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2700](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2700-L2700), [cite at paper/reasoning-parts/erdos1041/core.tex:2658](../../paper/reasoning-parts/erdos1041/core.tex#L2658-L2658)

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
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L785-L787) — lines `785–787`; excerpt `sha256:ad96b93897cb722f9a63aa344b11a333231b11971c032d6bf1a0781e0d6ded9f`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2995-L2997) — lines `2995–2997`; excerpt `sha256:ad96b93897cb722f9a63aa344b11a333231b11971c032d6bf1a0781e0d6ded9f`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1547-L1551) — lines `1547–1551`; excerpt `sha256:1bbd690c4787d1f1d80dd1f1ce42127d2dbec30c78a37ad55889e085911ed906`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1582-L1587) — lines `1582–1587`; excerpt `sha256:10b82bb930fe79ac10a4ea88fdca0fe6cef302ef6284568b8ea7a1bd56f969d0`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2955-L2957) — lines `2955–2957`; excerpt `sha256:ad96b93897cb722f9a63aa344b11a333231b11971c032d6bf1a0781e0d6ded9f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L97-L97) — lines `97–97`; excerpt `sha256:8e56484cbb8a2a51938d6d95f9eb16930424134d3eb232b2a1c1323f9489b0f2`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:644](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L644-L644)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3773](../../paper/archive/erdos249-257-main-paper.tex#L3773-L3773)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2078](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2078-L2078), [cite at paper/reasoning-parts/erdos251/core.tex:2038](../../paper/reasoning-parts/erdos251/core.tex#L2038-L2038)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:517](../../paper/systems/open-source-mathematics-strategy.tex#L517-L517)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2956-L2960) — lines `2956–2960`; excerpt `sha256:e3b1d19fa4854f7153d25ef24896c1b7f697c819f9574977485c2759ead98276`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2922-L2926) — lines `2922–2926`; excerpt `sha256:e3b1d19fa4854f7153d25ef24896c1b7f697c819f9574977485c2759ead98276`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1758](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1758-L1758), [cite at paper/reasoning-parts/erdos68/core.tex:1724](../../paper/reasoning-parts/erdos68/core.tex#L1724-L1724)

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L1116-L1122) — lines `1116–1122`; excerpt `sha256:6cb7dcabcbc0e388ffa8e2348251a577293e5169688f4aaaffac1b8ae868d1ea`
- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9509-L9515) — lines `9509–9515`; excerpt `sha256:e10593522712515931ddcbaa7131d36a55628516394338e405b737d442819636`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9339-L9345) — lines `9339–9345`; excerpt `sha256:e10593522712515931ddcbaa7131d36a55628516394338e405b737d442819636`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:802](../../paper/249/erdos-249-binary-totient-series.tex#L802-L802)
- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:9320](../../paper/249/erdos249-totient-reasoning-surface.tex#L9320-L9320), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:9150](../../paper/reasoning-parts/erdos249/a249_front.tex#L9150-L9150)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1211-L1214) — lines `1211–1214`; excerpt `sha256:10c3199fda8e6b96e9871391653c60d86629257f2027c73dec8028c99d52a01a`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4065-L4068) — lines `4065–4068`; excerpt `sha256:68ea153c3563a568a2f8dd959b99f6641b703032a1460306b051df5a3a19d4f9`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4033-L4036) — lines `4033–4036`; excerpt `sha256:68ea153c3563a568a2f8dd959b99f6641b703032a1460306b051df5a3a19d4f9`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:745](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L745-L745)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:579](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L579-L579), [cite at paper/reasoning-parts/erdos243/core.tex:547](../../paper/reasoning-parts/erdos243/core.tex#L547-L547)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2979-L2982) — lines `2979–2982`; excerpt `sha256:3566f4017e8d66bd416398ee1ff4829b468fbfc27cdd460a22f7d3c1443a3892`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L808-L811) — lines `808–811`; excerpt `sha256:3566f4017e8d66bd416398ee1ff4829b468fbfc27cdd460a22f7d3c1443a3892`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2934-L2937) — lines `2934–2937`; excerpt `sha256:3566f4017e8d66bd416398ee1ff4829b468fbfc27cdd460a22f7d3c1443a3892`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L50-L50) — lines `50–50`; excerpt `sha256:67efcd7001b521421bc4441b99ab1ad46a9420077b9e914f2e44d2915ba715cf`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L50-L50) — lines `50–50`; excerpt `sha256:67efcd7001b521421bc4441b99ab1ad46a9420077b9e914f2e44d2915ba715cf`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:279](../../paper/269/erdos-269-three-prime-running-lcm.tex#L279-L279)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:95](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L95-L95), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:398](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L398-L398), [cite at paper/reasoning-parts/erdos269/core.tex:50](../../paper/reasoning-parts/erdos269/core.tex#L50-L50), [cite at paper/reasoning-parts/erdos269/core.tex:353](../../paper/reasoning-parts/erdos269/core.tex#L353-L353)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1383-L1389) — lines `1383–1389`; excerpt `sha256:848005fb515337995c8dbc8192771103fe3414debe3bde5da05f345ee7b14055`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:1271](../../docs/papers/mirror/plectis-public-system.tex#L1271-L1271)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L841-L844) — lines `841–844`; excerpt `sha256:4882a3b299d75653e0733b29ff553b0c30bef3f7e4584c239baa2dc69d719f05`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3021-L3024) — lines `3021–3024`; excerpt `sha256:d2de58d8a1aef218af5e1cbe7a8d2d2e6c1b7fa33cca90bcee80d5265ac4b37f`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2976-L2979) — lines `2976–2979`; excerpt `sha256:d2de58d8a1aef218af5e1cbe7a8d2d2e6c1b7fa33cca90bcee80d5265ac4b37f`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:697](../../paper/269/erdos-269-three-prime-running-lcm.tex#L697-L697)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:152](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L152-L152), [cite at paper/reasoning-parts/erdos269/core.tex:107](../../paper/reasoning-parts/erdos269/core.tex#L107-L107)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9443-L9448) — lines `9443–9448`; excerpt `sha256:3b4314143d0179f0e80db37bd37b8d4c9238a3d5a98cff4c888fcdf15fd2d416`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9273-L9278) — lines `9273–9278`; excerpt `sha256:3b4314143d0179f0e80db37bd37b8d4c9238a3d5a98cff4c888fcdf15fd2d416`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7972](../../paper/249/erdos249-totient-reasoning-surface.tex#L7972-L7972), [cite at paper/249/erdos249-totient-reasoning-surface.tex:7973](../../paper/249/erdos249-totient-reasoning-surface.tex#L7973-L7973), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7802](../../paper/reasoning-parts/erdos249/a249_front.tex#L7802-L7802), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7803](../../paper/reasoning-parts/erdos249/a249_front.tex#L7803-L7803)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1345-L1351) — lines `1345–1351`; excerpt `sha256:18a8d4297efae6feb71647744dd95041e21981acc49c27a0e1687c67df212362`

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1603-L1606) — lines `1603–1606`; excerpt `sha256:00533dbf0653285d403f4d880ae6c06199d42aedaead4cf8e51773d95b99c3ce`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1567-L1572) — lines `1567–1572`; excerpt `sha256:a61b861ef9dfbc8c5a24e60e162f7b7fa072c019024917cf1a7847ac064e8432`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:692](../../paper/systems/claim-faithful-publication-systems-paper.tex#L692-L692)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:922](../../paper/systems/open-source-mathematics-strategy.tex#L922-L922), [cite at paper/systems/open-source-mathematics-strategy.tex:1323](../../paper/systems/open-source-mathematics-strategy.tex#L1323-L1323)

<a id="source-source-c309c1132b63e3"></a>

### Hints on test data selection

- Source id: `source-c309c1132b63e3`
- Author or public identity: R. A. DeMillo, R. J. Lipton, F. G. Sayward
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1594-L1596) — lines `1594–1596`; excerpt `sha256:2a24ff23359ad7b3c311119906da81233df24832b89222f2be5f86235548b475`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1429](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1429-L1429)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L795-L797) — lines `795–797`; excerpt `sha256:5bb26410e95839b64ea4bf5f23b0e11414c0841dab9afdc4a31c006cc4754751`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3009-L3011) — lines `3009–3011`; excerpt `sha256:5bb26410e95839b64ea4bf5f23b0e11414c0841dab9afdc4a31c006cc4754751`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2969-L2971) — lines `2969–2971`; excerpt `sha256:5bb26410e95839b64ea4bf5f23b0e11414c0841dab9afdc4a31c006cc4754751`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L21-L21) — lines `21–21`; excerpt `sha256:07dad1a6dbaa03c54631370154c906de91a50cd710b3b9c6e143f85e14b3c973`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:615](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L615-L615)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2027](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2027-L2027), [cite at paper/reasoning-parts/erdos251/core.tex:1987](../../paper/reasoning-parts/erdos251/core.tex#L1987-L1987)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1376-L1381) — lines `1376–1381`; excerpt `sha256:8b16aa8ce3f46b281fb40b2e16b106525ac072214009c4f43d3751d3148a85ef`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4589-L4594) — lines `4589–4594`; excerpt `sha256:e0b4d65450b872a2ec9473172bcabec68557987449286f48db42d3c226f70988`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4564-L4569) — lines `4564–4569`; excerpt `sha256:e0b4d65450b872a2ec9473172bcabec68557987449286f48db42d3c226f70988`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1178](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1178-L1178)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2314](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2314-L2314), [cite at paper/reasoning-parts/erdos1049/core.tex:2289](../../paper/reasoning-parts/erdos1049/core.tex#L2289-L2289)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2994-L2997) — lines `2994–2997`; excerpt `sha256:fc54218ee2caf5338f8576a083a77ebf02ded7474aabe6fadbda0c33f1624c08`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2949-L2952) — lines `2949–2952`; excerpt `sha256:fc54218ee2caf5338f8576a083a77ebf02ded7474aabe6fadbda0c33f1624c08`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1206-L1211) — lines `1206–1211`; excerpt `sha256:24a478d3e71a9e5ce6ab2dcf8084cf9ba533270acd0b15cdfd19710d0c338733`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4060-L4065) — lines `4060–4065`; excerpt `sha256:24a478d3e71a9e5ce6ab2dcf8084cf9ba533270acd0b15cdfd19710d0c338733`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L4028-L4033) — lines `4028–4033`; excerpt `sha256:24a478d3e71a9e5ce6ab2dcf8084cf9ba533270acd0b15cdfd19710d0c338733`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L847-L850) — lines `847–850`; excerpt `sha256:997988654d9ef70ccc079da055de714cc3514f6ed4822ee4b84eab7c073da669`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:919](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L919-L919)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:685](../../paper/269/erdos-269-three-prime-running-lcm.tex#L685-L685)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:943](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L943-L943), [cite at paper/reasoning-parts/erdos243/core.tex:911](../../paper/reasoning-parts/erdos243/core.tex#L911-L911)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1261](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1261-L1261), [cite at paper/reasoning-parts/erdos269/core.tex:1216](../../paper/reasoning-parts/erdos269/core.tex#L1216-L1216)

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1422-L1426) — lines `1422–1426`; excerpt `sha256:156df176c039566fa6a406e54730ac45e0fabbf03ff99eaeb3b08442cc0945c5`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:782](../../paper/257/erdos-257-mersenne-support-subseries.tex#L782-L782)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9409-L9414) — lines `9409–9414`; excerpt `sha256:cda83ebde02e28a432b8ceb19002a8a337d3c75febb082deef2e12df21f76d3e`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9239-L9244) — lines `9239–9244`; excerpt `sha256:cda83ebde02e28a432b8ceb19002a8a337d3c75febb082deef2e12df21f76d3e`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:2455](../../paper/249/erdos249-totient-reasoning-surface.tex#L2455-L2455), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:2285](../../paper/reasoning-parts/erdos249/a249_front.tex#L2285-L2285)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2884-L2888) — lines `2884–2888`; excerpt `sha256:1c1ed4ef4c6101db50bde9f966d63761d20c722b5a1a19916cb663d42ee249fd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2850-L2854) — lines `2850–2854`; excerpt `sha256:1c1ed4ef4c6101db50bde9f966d63761d20c722b5a1a19916cb663d42ee249fd`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2332-L2332) — lines `2332–2332`; excerpt `sha256:eaef0eb562b2565c4e6cca9b9e2071d569a2d058ca3df8fe1a95c3b9fbbe116f`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1179-L1183) — lines `1179–1183`; excerpt `sha256:3875de59e714310957e9a10579cc224e98e345c01f4ca934900cb9d1bd7e5c4a`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1071](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1071-L1071), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1080](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1080-L1080), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1082](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1082-L1082)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:500](../../paper/68/erdos68-factorial-reasoning-surface.tex#L500-L501), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2103](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2103-L2104), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2366](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2366-L2366), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2369](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2369-L2369), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2377](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2377-L2377), [cite at paper/reasoning-parts/erdos68/core.tex:466](../../paper/reasoning-parts/erdos68/core.tex#L466-L467), [cite at paper/reasoning-parts/erdos68/core.tex:2069](../../paper/reasoning-parts/erdos68/core.tex#L2069-L2070), [cite at paper/reasoning-parts/erdos68/core.tex:2332](../../paper/reasoning-parts/erdos68/core.tex#L2332-L2332), [cite at paper/reasoning-parts/erdos68/core.tex:2335](../../paper/reasoning-parts/erdos68/core.tex#L2335-L2335), [cite at paper/reasoning-parts/erdos68/core.tex:2343](../../paper/reasoning-parts/erdos68/core.tex#L2343-L2343)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3035-L3037) — lines `3035–3037`; excerpt `sha256:e6fc69e63673756998024749e72cb913b9a0094933c34fd8e81d93f0eeca483e`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2995-L2997) — lines `2995–2997`; excerpt `sha256:e6fc69e63673756998024749e72cb913b9a0094933c34fd8e81d93f0eeca483e`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:635](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L635-L635), [cite at paper/reasoning-parts/erdos251/core.tex:595](../../paper/reasoning-parts/erdos251/core.tex#L595-L595)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4497-L4503) — lines `4497–4503`; excerpt `sha256:b6b59c3f516fe753628de797f741e46ad1554bcd562427e309cfd40f794a23f8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4472-L4478) — lines `4472–4478`; excerpt `sha256:b6b59c3f516fe753628de797f741e46ad1554bcd562427e309cfd40f794a23f8`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4204](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4204-L4204), [cite at paper/reasoning-parts/erdos1049/core.tex:4179](../../paper/reasoning-parts/erdos1049/core.tex#L4179-L4179)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1147-L1151) — lines `1147–1151`; excerpt `sha256:8a847cb8c6d7ed0d59130cbc1d2e6cc75ca5363d7b766e4b4549f87e237f59d6`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3985-L3989) — lines `3985–3989`; excerpt `sha256:8a847cb8c6d7ed0d59130cbc1d2e6cc75ca5363d7b766e4b4549f87e237f59d6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3953-L3957) — lines `3953–3957`; excerpt `sha256:8a847cb8c6d7ed0d59130cbc1d2e6cc75ca5363d7b766e4b4549f87e237f59d6`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:643](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L643-L643), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:682](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L682-L682)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:772](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L772-L772), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1612](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1612-L1612), [cite at paper/reasoning-parts/erdos243/core.tex:740](../../paper/reasoning-parts/erdos243/core.tex#L740-L740), [cite at paper/reasoning-parts/erdos243/core.tex:1580](../../paper/reasoning-parts/erdos243/core.tex#L1580-L1580)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1557-L1562) — lines `1557–1562`; excerpt `sha256:3b1c1f707242e20b5d386d4825b37ac2214783f7d5eabb0ada5326605f0fc4cd`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:525](../../paper/systems/open-source-mathematics-strategy.tex#L525-L525), [cite at paper/systems/open-source-mathematics-strategy.tex:852](../../paper/systems/open-source-mathematics-strategy.tex#L852-L852), [cite at paper/systems/open-source-mathematics-strategy.tex:907](../../paper/systems/open-source-mathematics-strategy.tex#L907-L907)

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

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1627-L1630) — lines `1627–1630`; excerpt `sha256:41dc4edf06af566e300a6354dd5626e47fca1f6af7f86309ecb4f6d76d1affa0`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1422](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1422-L1422)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4491-L4497) — lines `4491–4497`; excerpt `sha256:caca3710f524135671e299fa1162e5d77947646ae83681362b020268b6f0aac0`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4466-L4472) — lines `4466–4472`; excerpt `sha256:caca3710f524135671e299fa1162e5d77947646ae83681362b020268b6f0aac0`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L829-L829) — lines `829–829`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L829-L829) — lines `829–829`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L829-L829) — lines `829–829`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L829-L829) — lines `829–829`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L4-L13) — lines `4–13`; excerpt `sha256:9e02e269f490c0d8ee088d184d3cf2b53af45d9b0144a4623c9110e7230e7af9`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L19-L32) — lines `19–32`; excerpt `sha256:ed4a3e5b020b06b3f16f2771e4c9518cf5e0c23e46e275e30a93b5b498f5db23`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L58-L62) — lines `58–62`; excerpt `sha256:6fab9c0293d1ca17fe26b54f24d0f7366711b09b71d8f6e869df1315fb5c2dbc`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1447-L1454) — lines `1447–1454`; excerpt `sha256:c67b14d05ad70fe87ae10882e6666f671b4fb879b6ad3b2ac2f9cd21da8d1764`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9795-L9802) — lines `9795–9802`; excerpt `sha256:c67b14d05ad70fe87ae10882e6666f671b4fb879b6ad3b2ac2f9cd21da8d1764`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9611-L9618) — lines `9611–9618`; excerpt `sha256:c67b14d05ad70fe87ae10882e6666f671b4fb879b6ad3b2ac2f9cd21da8d1764`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1348-L1354) — lines `1348–1354`; excerpt `sha256:72d40703f422b4e9c77e9b7f7d1db51028590dcfa3b80e0dfd26187887ef7b98`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1167](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1167-L1167)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:715](../../paper/257/erdos-257-mersenne-support-subseries.tex#L715-L715)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:854](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L854-L854), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2145](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2145-L2145), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4155](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4155-L4155), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4159](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4159-L4159), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4181](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4181-L4181), [cite at paper/reasoning-parts/erdos1049/core.tex:829](../../paper/reasoning-parts/erdos1049/core.tex#L829-L829), [cite at paper/reasoning-parts/erdos1049/core.tex:2120](../../paper/reasoning-parts/erdos1049/core.tex#L2120-L2120), [cite at paper/reasoning-parts/erdos1049/core.tex:4130](../../paper/reasoning-parts/erdos1049/core.tex#L4130-L4130), [cite at paper/reasoning-parts/erdos1049/core.tex:4134](../../paper/reasoning-parts/erdos1049/core.tex#L4134-L4134), [cite at paper/reasoning-parts/erdos1049/core.tex:4156](../../paper/reasoning-parts/erdos1049/core.tex#L4156-L4156)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9660](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9660-L9660), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9476](../../paper/reasoning-parts/erdos257/a257_front.tex#L9476-L9476)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L827-L829) — lines `827–829`; excerpt `sha256:6287f2e5f5563289d4064e0d820c7d7f4d40b15e0efeaa8af2f7bf000182a58a`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3045-L3047) — lines `3045–3047`; excerpt `sha256:6287f2e5f5563289d4064e0d820c7d7f4d40b15e0efeaa8af2f7bf000182a58a`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L3005-L3007) — lines `3005–3007`; excerpt `sha256:6287f2e5f5563289d4064e0d820c7d7f4d40b15e0efeaa8af2f7bf000182a58a`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:753](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L753-L753)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:610](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L610-L610), [cite at paper/reasoning-parts/erdos251/core.tex:570](../../paper/reasoning-parts/erdos251/core.tex#L570-L570)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1357-L1362) — lines `1357–1362`; excerpt `sha256:82ba5ed7e06a2f42df45b4196b5caba7c6b634aab7fa76273b92a7cc6bf3768e`

Paper citation usages:

- `plectis-public-system`: [cite at docs/papers/mirror/plectis-public-system.tex:437](../../docs/papers/mirror/plectis-public-system.tex#L437-L437)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2872-L2876) — lines `2872–2876`; excerpt `sha256:3460ef54d7c16f79f21ea0acd344175689e099e53fd07f95423bbc149ab01fcc`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2838-L2842) — lines `2838–2842`; excerpt `sha256:3460ef54d7c16f79f21ea0acd344175689e099e53fd07f95423bbc149ab01fcc`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L212-L212) — lines `212–212`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L212-L212) — lines `212–212`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L212-L212) — lines `212–212`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [lean/ErdosProblems/Erdos68/PrimeZeroBranch.lean](../../lean/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3134-L3139) — lines `3134–3139`; excerpt `sha256:c866f4949ed4ad3259541be1ab078fcd2c3b951e2dcb35d831286f21d4ff0dae`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1219-L1223) — lines `1219–1223`; excerpt `sha256:3347ae470eba67fe218dfc8f10a1ac6bcff33e960f9653c66d0f9c00f480a123`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1039](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1039-L1039)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:246](../../paper/68/erdos68-factorial-reasoning-surface.tex#L246-L246), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1699](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1699-L1699), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1746](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1746-L1746), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1750](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1750-L1750), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2095](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2095-L2095), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2657](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2657-L2657), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2658](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2658-L2658), [cite at paper/reasoning-parts/erdos68/core.tex:212](../../paper/reasoning-parts/erdos68/core.tex#L212-L212), [cite at paper/reasoning-parts/erdos68/core.tex:1665](../../paper/reasoning-parts/erdos68/core.tex#L1665-L1665), [cite at paper/reasoning-parts/erdos68/core.tex:1712](../../paper/reasoning-parts/erdos68/core.tex#L1712-L1712), [cite at paper/reasoning-parts/erdos68/core.tex:1716](../../paper/reasoning-parts/erdos68/core.tex#L1716-L1716), [cite at paper/reasoning-parts/erdos68/core.tex:2061](../../paper/reasoning-parts/erdos68/core.tex#L2061-L2061), [cite at paper/reasoning-parts/erdos68/core.tex:2623](../../paper/reasoning-parts/erdos68/core.tex#L2623-L2623), [cite at paper/reasoning-parts/erdos68/core.tex:2624](../../paper/reasoning-parts/erdos68/core.tex#L2624-L2624)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1612-L1615) — lines `1612–1615`; excerpt `sha256:45e399824f7a91b588e0da7501989c4218fad45a476eee19f1cf5ed374601f3d`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1302](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1302-L1302)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L775-L777) — lines `775–777`; excerpt `sha256:7d4b3edd3f0259421dd8a74baf144d917da4ddfbfce902474872b62fbe04ff8c`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2983-L2985) — lines `2983–2985`; excerpt `sha256:7d4b3edd3f0259421dd8a74baf144d917da4ddfbfce902474872b62fbe04ff8c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2943-L2945) — lines `2943–2945`; excerpt `sha256:7d4b3edd3f0259421dd8a74baf144d917da4ddfbfce902474872b62fbe04ff8c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1043-L1043) — lines `1043–1043`; excerpt `sha256:4825da1c1a4563510f00f6082213673382fbe87eeb61a99a395507739f85527f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1997-L1997) — lines `1997–1997`; excerpt `sha256:eaaaa84d309b1a0c1d56fc36e531a59a4fa33af5709a256b9b48f214908ca467`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L22-L22) — lines `22–22`; excerpt `sha256:6fe10d86cfbff9e425bdd6578dd696a5a4e58cae9a09bb6b9e1d399e6bd9e791`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:617](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L617-L617)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1084](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1084-L1084), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2038](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2038-L2038), [cite at paper/reasoning-parts/erdos251/core.tex:1044](../../paper/reasoning-parts/erdos251/core.tex#L1044-L1044), [cite at paper/reasoning-parts/erdos251/core.tex:1998](../../paper/reasoning-parts/erdos251/core.tex#L1998-L1998)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3003-L3005) — lines `3003–3005`; excerpt `sha256:1a14b5dab89311efa51f08c6a1083aa9a70ec67efa331a3a3b2b5c065768d4e5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2963-L2965) — lines `2963–2965`; excerpt `sha256:1a14b5dab89311efa51f08c6a1083aa9a70ec67efa331a3a3b2b5c065768d4e5`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L450-L450) — lines `450–450`; excerpt `sha256:c71e8959bba5436eb967fd7bb1a08ff389eb3f6452e2a10a0c68641751c8d576`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L450-L450) — lines `450–450`; excerpt `sha256:c71e8959bba5436eb967fd7bb1a08ff389eb3f6452e2a10a0c68641751c8d576`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L450-L450) — lines `450–450`; excerpt `sha256:c71e8959bba5436eb967fd7bb1a08ff389eb3f6452e2a10a0c68641751c8d576`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1340-L1340) — lines `1340–1340`; excerpt `sha256:abb5af99443a232f9d79b1ad750430239c19325c52435300810f77e8e4e99931`
- [lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean](../../lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L7-L23) — lines `7–23`; excerpt `sha256:321f1f193ba6cea89edee0e703684bdf6234e2bc38d8b5dc53a6395d1b42cf33`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L817-L819) — lines `817–819`; excerpt `sha256:a3a48dc0af2ce0549ba6c3e9eea30a30f6e3554c01f26cebd6566dc236f816dc`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:283](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L283-L283), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:489](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L489-L489), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:757](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L757-L757)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:490](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L490-L490), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:529](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L529-L529), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:535](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L535-L535), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1381](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1381-L1382), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1498](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1498-L1498), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1546](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1546-L1546), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1609](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1609-L1609), [cite at paper/reasoning-parts/erdos251/core.tex:450](../../paper/reasoning-parts/erdos251/core.tex#L450-L450), [cite at paper/reasoning-parts/erdos251/core.tex:489](../../paper/reasoning-parts/erdos251/core.tex#L489-L489), [cite at paper/reasoning-parts/erdos251/core.tex:495](../../paper/reasoning-parts/erdos251/core.tex#L495-L495), [cite at paper/reasoning-parts/erdos251/core.tex:1341](../../paper/reasoning-parts/erdos251/core.tex#L1341-L1342), [cite at paper/reasoning-parts/erdos251/core.tex:1458](../../paper/reasoning-parts/erdos251/core.tex#L1458-L1458), [cite at paper/reasoning-parts/erdos251/core.tex:1506](../../paper/reasoning-parts/erdos251/core.tex#L1506-L1506), [cite at paper/reasoning-parts/erdos251/core.tex:1569](../../paper/reasoning-parts/erdos251/core.tex#L1569-L1569)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1638-L1643) — lines `1638–1643`; excerpt `sha256:0e1fe3e7471b6a0f3864ce0578266000a9fbb85f892248701cd17ba615c3e182`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:769](../../paper/systems/open-source-mathematics-strategy.tex#L769-L769)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4553-L4559) — lines `4553–4559`; excerpt `sha256:fd04dc6525552320cb5e54a12e8e0739172ac9163ecf01bedfd7dcf7a6485be2`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4528-L4534) — lines `4528–4534`; excerpt `sha256:fd04dc6525552320cb5e54a12e8e0739172ac9163ecf01bedfd7dcf7a6485be2`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4293-L4293) — lines `4293–4293`; excerpt `sha256:a687d79281dfe79c9bc043998a9b0da79a7a7066f72571d9b7a84107de6bf44d`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4318-L4318) — lines `4318–4318`; excerpt `sha256:a687d79281dfe79c9bc043998a9b0da79a7a7066f72571d9b7a84107de6bf44d`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4318](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4318-L4318), [cite at paper/reasoning-parts/erdos1049/core.tex:4293](../../paper/reasoning-parts/erdos1049/core.tex#L4293-L4293)

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
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L787-L789) — lines `787–789`; excerpt `sha256:d72e98994bd66ed7b43de80a46537b74234c2d45f82d4b6ff1a1a24103ce7117`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2997-L2999) — lines `2997–2999`; excerpt `sha256:d72e98994bd66ed7b43de80a46537b74234c2d45f82d4b6ff1a1a24103ce7117`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2957-L2959) — lines `2957–2959`; excerpt `sha256:d72e98994bd66ed7b43de80a46537b74234c2d45f82d4b6ff1a1a24103ce7117`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2038-L2038) — lines `2038–2038`; excerpt `sha256:6c9614868ad6ac591604ecab3aefeeaeb3a729ddb735225be25d197b9e9d3c0f`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:644](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L644-L644)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3775](../../paper/archive/erdos249-257-main-paper.tex#L3775-L3775)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2078](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2078-L2078), [cite at paper/reasoning-parts/erdos251/core.tex:2038](../../paper/reasoning-parts/erdos251/core.tex#L2038-L2038)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L809-L811) — lines `809–811`; excerpt `sha256:0ff84f114bce1e696b9859dc6944ea26811f851d98955e2f5cf233d48165ac05`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L3025-L3027) — lines `3025–3027`; excerpt `sha256:0ff84f114bce1e696b9859dc6944ea26811f851d98955e2f5cf233d48165ac05`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2985-L2987) — lines `2985–2987`; excerpt `sha256:0ff84f114bce1e696b9859dc6944ea26811f851d98955e2f5cf233d48165ac05`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:334](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L334-L334)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:573](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L573-L573), [cite at paper/reasoning-parts/erdos251/core.tex:533](../../paper/reasoning-parts/erdos251/core.tex#L533-L533)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1815-L1820) — lines `1815–1820`; excerpt `sha256:ada915f17a1ed537b753f4f88aa73ca8631254a748c99e5c556dd0dcde0016c1`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4651-L4656) — lines `4651–4656`; excerpt `sha256:8c9bd3c3345cf07ffa6815f7ec1a90485fe63e2b80e1724053327490204d780a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4609-L4614) — lines `4609–4614`; excerpt `sha256:8c9bd3c3345cf07ffa6815f7ec1a90485fe63e2b80e1724053327490204d780a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1653-L1653) — lines `1653–1653`; excerpt `sha256:bf660f22b7c2b5ad1586f91c21fc4e625ed74e4ec29b524be165def32d7d016d`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:755](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L755-L755)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1695](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1695-L1695), [cite at paper/reasoning-parts/erdos1041/core.tex:1653](../../paper/reasoning-parts/erdos1041/core.tex#L1653-L1653)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1171-L1175) — lines `1171–1175`; excerpt `sha256:f959bb68cc06d5c8fc21e17f7becd84211e2f55bf7f57c01f14dae8f0a569649`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2864-L2868) — lines `2864–2868`; excerpt `sha256:259feb71f707ecd3c171a22910b7c8c7271afda92cdb5fc376bb96e7b1e3a4c4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2830-L2834) — lines `2830–2834`; excerpt `sha256:259feb71f707ecd3c171a22910b7c8c7271afda92cdb5fc376bb96e7b1e3a4c4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L571-L571) — lines `571–571`; excerpt `sha256:ad8298ac69c418e00f4fc3862912b0d4b44decd465a1ec66f04646c9f5d5ecfb`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L571-L571) — lines `571–571`; excerpt `sha256:ad8298ac69c418e00f4fc3862912b0d4b44decd465a1ec66f04646c9f5d5ecfb`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1062](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1062-L1062)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:605](../../paper/68/erdos68-factorial-reasoning-surface.tex#L605-L605), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2100](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2100-L2100), [cite at paper/reasoning-parts/erdos68/core.tex:571](../../paper/reasoning-parts/erdos68/core.tex#L571-L571), [cite at paper/reasoning-parts/erdos68/core.tex:2066](../../paper/reasoning-parts/erdos68/core.tex#L2066-L2066)

<a id="source-source-e1665a6398558f"></a>

### An analysis of the requirements traceability problem

- Source id: `source-e1665a6398558f`
- Author or public identity: O. C. Z. Gotel, A. C. W. Finkelstein
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1591-L1594) — lines `1591–1594`; excerpt `sha256:f17c0c478335e800131efac3fc47767edf7e649bd313b804266e2bbf30b81ba9`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1412](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1412-L1412)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1606-L1608) — lines `1606–1608`; excerpt `sha256:fabee45be57e7e01287e24c55801ede6426f9262dc1801b956db71edb40c2a6e`
- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L668-L673) — lines `668–673`; excerpt `sha256:e1fb69819625ee4c623683e8876546bfaeba103a154bb24b05f891cf455291a5`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1300](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1300-L1300)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:375](../../paper/systems/cold-clone-to-proof-receipt.tex#L375-L375), [cite at paper/systems/cold-clone-to-proof-receipt.tex:464](../../paper/systems/cold-clone-to-proof-receipt.tex#L464-L464)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1134-L1138) — lines `1134–1138`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3972-L3976) — lines `3972–3976`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2979-L2981) — lines `2979–2981`; excerpt `sha256:7cd258f662728fc8a7ab550dde219bad542c55e2520f19416bf3439de413de29`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3940-L3944) — lines `3940–3944`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L726-L726) — lines `726–726`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L726-L726) — lines `726–726`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L726-L726) — lines `726–726`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2939-L2941) — lines `2939–2941`; excerpt `sha256:7cd258f662728fc8a7ab550dde219bad542c55e2520f19416bf3439de413de29`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L617-L617) — lines `617–617`; excerpt `sha256:eaa1d49db16032d9a995bc268a5e64df15540715982aacd7d504bd007c69cab4`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L30-L32) — lines `30–32`; excerpt `sha256:1139eed2569eedcc245358cbde7bff884c8a36c06c78b0a38246a82257dae3ec`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:640](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L640-L640)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:758](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L758-L758), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2363](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2363-L2364), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2513](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2513-L2513), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3698](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3698-L3698), [cite at paper/reasoning-parts/erdos243/core.tex:726](../../paper/reasoning-parts/erdos243/core.tex#L726-L726), [cite at paper/reasoning-parts/erdos243/core.tex:2331](../../paper/reasoning-parts/erdos243/core.tex#L2331-L2332), [cite at paper/reasoning-parts/erdos243/core.tex:2481](../../paper/reasoning-parts/erdos243/core.tex#L2481-L2481), [cite at paper/reasoning-parts/erdos243/core.tex:3666](../../paper/reasoning-parts/erdos243/core.tex#L3666-L3666)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:657](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L657-L657), [cite at paper/reasoning-parts/erdos251/core.tex:617](../../paper/reasoning-parts/erdos251/core.tex#L617-L617)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1367-L1372) — lines `1367–1372`; excerpt `sha256:878e039506eed9cbdca4b85b0b81b72924aa12144ce61f35980e357fdec8b62e`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4570-L4575) — lines `4570–4575`; excerpt `sha256:f203205a4c16098f6ea390c2eb9ffeedc8e3c1bc649018114be1c761d0cbad7b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4545-L4550) — lines `4545–4550`; excerpt `sha256:f203205a4c16098f6ea390c2eb9ffeedc8e3c1bc649018114be1c761d0cbad7b`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:1175](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1175-L1175)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2225](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2225-L2225), [cite at paper/reasoning-parts/erdos1049/core.tex:2200](../../paper/reasoning-parts/erdos1049/core.tex#L2200-L2200)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1290-L1294) — lines `1290–1294`; excerpt `sha256:e84ccbfd298ca45cdf1dc99cde6fa6c5c320db56fdd37d12d9716a81ae36f325`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4421-L4425) — lines `4421–4425`; excerpt `sha256:e84ccbfd298ca45cdf1dc99cde6fa6c5c320db56fdd37d12d9716a81ae36f325`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4396-L4400) — lines `4396–4400`; excerpt `sha256:e84ccbfd298ca45cdf1dc99cde6fa6c5c320db56fdd37d12d9716a81ae36f325`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L70-L70) — lines `70–70`; excerpt `sha256:9fa749e0b8dc4d20acd3250d16b73a48291c68f53546bf53aec7ec71fceec6b8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L70-L70) — lines `70–70`; excerpt `sha256:9fa749e0b8dc4d20acd3250d16b73a48291c68f53546bf53aec7ec71fceec6b8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L70-L70) — lines `70–70`; excerpt `sha256:9fa749e0b8dc4d20acd3250d16b73a48291c68f53546bf53aec7ec71fceec6b8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L70-L70) — lines `70–70`; excerpt `sha256:9fa749e0b8dc4d20acd3250d16b73a48291c68f53546bf53aec7ec71fceec6b8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L70-L70) — lines `70–70`; excerpt `sha256:9fa749e0b8dc4d20acd3250d16b73a48291c68f53546bf53aec7ec71fceec6b8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L70-L70) — lines `70–70`; excerpt `sha256:9fa749e0b8dc4d20acd3250d16b73a48291c68f53546bf53aec7ec71fceec6b8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L70-L70) — lines `70–70`; excerpt `sha256:9fa749e0b8dc4d20acd3250d16b73a48291c68f53546bf53aec7ec71fceec6b8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L70-L70) — lines `70–70`; excerpt `sha256:9fa749e0b8dc4d20acd3250d16b73a48291c68f53546bf53aec7ec71fceec6b8`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:490](../../paper/1049/erdos-1049-rational-base-lambert.tex#L490-L490)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:95](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L95-L95), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:595](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L595-L595), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:823](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L823-L823), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:851](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L851-L851), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1140](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1140-L1140), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3335](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3335-L3335), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4264](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4264-L4264), [cite at paper/reasoning-parts/erdos1049/core.tex:70](../../paper/reasoning-parts/erdos1049/core.tex#L70-L70), [cite at paper/reasoning-parts/erdos1049/core.tex:570](../../paper/reasoning-parts/erdos1049/core.tex#L570-L570), [cite at paper/reasoning-parts/erdos1049/core.tex:798](../../paper/reasoning-parts/erdos1049/core.tex#L798-L798), [cite at paper/reasoning-parts/erdos1049/core.tex:826](../../paper/reasoning-parts/erdos1049/core.tex#L826-L826), [cite at paper/reasoning-parts/erdos1049/core.tex:1115](../../paper/reasoning-parts/erdos1049/core.tex#L1115-L1115), [cite at paper/reasoning-parts/erdos1049/core.tex:3310](../../paper/reasoning-parts/erdos1049/core.tex#L3310-L3310), [cite at paper/reasoning-parts/erdos1049/core.tex:4239](../../paper/reasoning-parts/erdos1049/core.tex#L4239-L4239)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4470-L4477) — lines `4470–4477`; excerpt `sha256:ca3ad143147a5d2804f66fa9a2b445b365c705a19273a1ae8c77f2c257c09062`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4445-L4452) — lines `4445–4452`; excerpt `sha256:ca3ad143147a5d2804f66fa9a2b445b365c705a19273a1ae8c77f2c257c09062`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4263-L4263) — lines `4263–4263`; excerpt `sha256:a9816f01cbbbed3606bb3c7105e1f1bc81607266eee3e3bc860ed90c8624c684`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:4288](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4288-L4288), [cite at paper/reasoning-parts/erdos1049/core.tex:4263](../../paper/reasoning-parts/erdos1049/core.tex#L4263-L4263)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1211-L1215) — lines `1211–1215`; excerpt `sha256:6d0b157c1bad243c1cdb9d1a9e0b30105bc3e63f1061acabf6c3d01f0b057b0e`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2916-L2920) — lines `2916–2920`; excerpt `sha256:301c9e11ac561f9aaaabc33c46f271f3f0cecc122a99db652c476daecd2fda2a`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2882-L2886) — lines `2882–2886`; excerpt `sha256:301c9e11ac561f9aaaabc33c46f271f3f0cecc122a99db652c476daecd2fda2a`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:1036](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1036-L1036)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:407](../../paper/68/erdos68-factorial-reasoning-surface.tex#L407-L407), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:409](../../paper/68/erdos68-factorial-reasoning-surface.tex#L409-L409), [cite at paper/reasoning-parts/erdos68/core.tex:373](../../paper/reasoning-parts/erdos68/core.tex#L373-L373), [cite at paper/reasoning-parts/erdos68/core.tex:375](../../paper/reasoning-parts/erdos68/core.tex#L375-L375)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1367-L1372) — lines `1367–1372`; excerpt `sha256:8f4293a0a02295b79306f2dd39994ae87fe5e3c104ae2b67eeec226a473b145e`

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3033-L3037) — lines `3033–3037`; excerpt `sha256:66c2a5257f58be1672dd0343ef38da2c5d2f46e01935b51c3b7cec7dcf17b0ea`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2988-L2992) — lines `2988–2992`; excerpt `sha256:66c2a5257f58be1672dd0343ef38da2c5d2f46e01935b51c3b7cec7dcf17b0ea`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2293](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2293-L2293), [cite at paper/reasoning-parts/erdos269/core.tex:2248](../../paper/reasoning-parts/erdos269/core.tex#L2248-L2248)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1585-L1588) — lines `1585–1588`; excerpt `sha256:bd5502f4674131e7e6476f99e36c1253bd5e1fbd3e4ce8174b83c01043baedad`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1633-L1638) — lines `1633–1638`; excerpt `sha256:4fa78969a75193c23aeb06cdd0323df94e0a5887673d1bf5c44d740748d12774`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1387](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1387-L1387)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:1013](../../paper/systems/open-source-mathematics-strategy.tex#L1013-L1013)

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

- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L854-L860) — lines `854–860`; excerpt `sha256:f0b413584f891c1a725c23699a9efae2e7cbaba89e97347422243d21325f0020`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L3037-L3043) — lines `3037–3043`; excerpt `sha256:f0b413584f891c1a725c23699a9efae2e7cbaba89e97347422243d21325f0020`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2992-L2998) — lines `2992–2998`; excerpt `sha256:f0b413584f891c1a725c23699a9efae2e7cbaba89e97347422243d21325f0020`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:693](../../paper/269/erdos-269-three-prime-running-lcm.tex#L693-L693)
- `erdos-synthesis-reading-together-record`: [cite at paper/synthesis/erdos-synthesis-reading-together-record.tex:198](../../paper/synthesis/erdos-synthesis-reading-together-record.tex#L198-L198)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2296](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2296-L2296), [cite at paper/reasoning-parts/erdos269/core.tex:2251](../../paper/reasoning-parts/erdos269/core.tex#L2251-L2251)

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
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L794-L794) — lines `794–794`; excerpt `sha256:a823ade08a65d3c98027889c7115050e03936df38c795fc73ce75bf9d4ff0d07`
- [lean/Erdos249257/CampbellShiftSynchronization.lean](../../lean/Erdos249257/CampbellShiftSynchronization.lean#L4-L22) — lines `4–22`; excerpt `sha256:d517c238bb94dca26752a32c4273074633c39a9b8af3551e069cb7a282081388`
- [lean/Erdos249257/CampbellShiftSynchronization.lean](../../lean/Erdos249257/CampbellShiftSynchronization.lean#L294-L299) — lines `294–299`; excerpt `sha256:a33a451732d6d625372bccee6302e08dfdb1ec94ea88b2bb9013d5eff55197d4`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9764-L9770) — lines `9764–9770`; excerpt `sha256:a764b921cc13bcb1cc2ca1ce687e7493ad39d0ad55326278645b6b44ec94cfdc`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9580-L9586) — lines `9580–9586`; excerpt `sha256:a764b921cc13bcb1cc2ca1ce687e7493ad39d0ad55326278645b6b44ec94cfdc`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2253](../../paper/archive/erdos249-257-main-paper.tex#L2253-L2254)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:1295](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L1295-L1295), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:1111](../../paper/reasoning-parts/erdos257/a257_front.tex#L1111-L1111)

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

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1165-L1169) — lines `1165–1169`; excerpt `sha256:40aecd254891fc812f0e8980ec61fe681a524880f510bb6cfc26f94b02d1b732`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L4010-L4014) — lines `4010–4014`; excerpt `sha256:40aecd254891fc812f0e8980ec61fe681a524880f510bb6cfc26f94b02d1b732`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L3978-L3982) — lines `3978–3982`; excerpt `sha256:40aecd254891fc812f0e8980ec61fe681a524880f510bb6cfc26f94b02d1b732`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:459](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L459-L459)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2642](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2642-L2642), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:3236](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3236-L3236), [cite at paper/reasoning-parts/erdos243/core.tex:2610](../../paper/reasoning-parts/erdos243/core.tex#L2610-L2610), [cite at paper/reasoning-parts/erdos243/core.tex:3204](../../paper/reasoning-parts/erdos243/core.tex#L3204-L3204)

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

- [paper/249/erdos249-totient-reasoning-surface.tex](../../paper/249/erdos249-totient-reasoning-surface.tex#L9448-L9453) — lines `9448–9453`; excerpt `sha256:32599e7a2120d5129deed6138e89e7ebef17cd091f20f82776fde8449312e5ca`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L9278-L9283) — lines `9278–9283`; excerpt `sha256:32599e7a2120d5129deed6138e89e7ebef17cd091f20f82776fde8449312e5ca`

Paper citation usages:

- `erdos249-totient-reasoning-surface`: [cite at paper/249/erdos249-totient-reasoning-surface.tex:7983](../../paper/249/erdos249-totient-reasoning-surface.tex#L7983-L7983), [cite at paper/reasoning-parts/erdos249/a249\_front.tex:7813](../../paper/reasoning-parts/erdos249/a249_front.tex#L7813-L7813)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1183-L1187) — lines `1183–1187`; excerpt `sha256:809f864ff438892c5e39d707a4ca21b142f8134a6475d204916011234a842169`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2856-L2860) — lines `2856–2860`; excerpt `sha256:56545f01462da2d6bd59af54b4c105a4e78489461a9719ab3c6db971299941ef`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2822-L2826) — lines `2822–2826`; excerpt `sha256:56545f01462da2d6bd59af54b4c105a4e78489461a9719ab3c6db971299941ef`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L76-L76) — lines `76–76`; excerpt `sha256:7a549791ed341c1373f0b0c9b40e13b147f3aa3b9484ded64b1ef2f2a94aefa9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L76-L76) — lines `76–76`; excerpt `sha256:7a549791ed341c1373f0b0c9b40e13b147f3aa3b9484ded64b1ef2f2a94aefa9`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:474](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L474-L474)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:110](../../paper/68/erdos68-factorial-reasoning-surface.tex#L110-L110), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2115](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2115-L2115), [cite at paper/reasoning-parts/erdos68/core.tex:76](../../paper/reasoning-parts/erdos68/core.tex#L76-L76), [cite at paper/reasoning-parts/erdos68/core.tex:2081](../../paper/reasoning-parts/erdos68/core.tex#L2081-L2081)

<a id="source-source-endpoint2026-logarithmic-repair"></a>

### The logarithmic endpoint fails under arithmetic sampling

- Source id: `source-endpoint2026-logarithmic-repair`
- Author or public identity: Plectis working note
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Unpublished AI-assisted ordinary proof note dated 17 September 2026. Theorem 1, Corollary 3 and Proposition 4 are the source of the finite-functional arithmetic counterexample, cover-cost separation, and initial-interval bound inserted into the #257 papers. Independent review and fresh Lean verification are outstanding. It is not a published journal article.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1460-L1464) — lines `1460–1464`; excerpt `sha256:a3c2f5b54229a30d640a6c58d8b047148c14ebf7a4e2a33957914102e9d8473a`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9821-L9825) — lines `9821–9825`; excerpt `sha256:a3c2f5b54229a30d640a6c58d8b047148c14ebf7a4e2a33957914102e9d8473a`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9637-L9641) — lines `9637–9641`; excerpt `sha256:a3c2f5b54229a30d640a6c58d8b047148c14ebf7a4e2a33957914102e9d8473a`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:561](../../paper/257/erdos-257-mersenne-support-subseries.tex#L561-L562)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9333](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9333-L9333), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9149](../../paper/reasoning-parts/erdos257/a257_front.tex#L9149-L9149)

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1835-L1838) — lines `1835–1838`; excerpt `sha256:a2ea0b0d9fe464fd26b77c94c6b482f3c945b98a5fd53c85d7624d1728340989`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4706-L4709) — lines `4706–4709`; excerpt `sha256:a2ea0b0d9fe464fd26b77c94c6b482f3c945b98a5fd53c85d7624d1728340989`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4664-L4667) — lines `4664–4667`; excerpt `sha256:a2ea0b0d9fe464fd26b77c94c6b482f3c945b98a5fd53c85d7624d1728340989`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1672](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1672-L1672)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:4399](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4399-L4399), [cite at paper/reasoning-parts/erdos1041/core.tex:4357](../../paper/reasoning-parts/erdos1041/core.tex#L4357-L4357)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2932-L2936) — lines `2932–2936`; excerpt `sha256:9840d0a92d94f920800cfb600e645cca774371293151ecea13c66a6cce76d3c8`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2898-L2902) — lines `2898–2902`; excerpt `sha256:9840d0a92d94f920800cfb600e645cca774371293151ecea13c66a6cce76d3c8`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1636](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1636-L1636), [cite at paper/reasoning-parts/erdos68/core.tex:1602](../../paper/reasoning-parts/erdos68/core.tex#L1602-L1602)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1294-L1298) — lines `1294–1298`; excerpt `sha256:985c11e75c32024f7b85ea003ea9eddbd077703fea826834a3b574b6cc2d115c`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4425-L4429) — lines `4425–4429`; excerpt `sha256:985c11e75c32024f7b85ea003ea9eddbd077703fea826834a3b574b6cc2d115c`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4400-L4404) — lines `4400–4404`; excerpt `sha256:985c11e75c32024f7b85ea003ea9eddbd077703fea826834a3b574b6cc2d115c`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:303](../../paper/1049/erdos-1049-rational-base-lambert.tex#L303-L303)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:257](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L257-L257), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:470](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L470-L470), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:798](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L798-L798), [cite at paper/reasoning-parts/erdos1049/core.tex:232](../../paper/reasoning-parts/erdos1049/core.tex#L232-L232), [cite at paper/reasoning-parts/erdos1049/core.tex:445](../../paper/reasoning-parts/erdos1049/core.tex#L445-L445), [cite at paper/reasoning-parts/erdos1049/core.tex:773](../../paper/reasoning-parts/erdos1049/core.tex#L773-L773)

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

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L1203-L1207) — lines `1203–1207`; excerpt `sha256:d0240691fa5956d3f42d0e151a25cfaa8d0a16e7b1cc510ba6b9ef168ed084dc`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2908-L2912) — lines `2908–2912`; excerpt `sha256:d0240691fa5956d3f42d0e151a25cfaa8d0a16e7b1cc510ba6b9ef168ed084dc`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2874-L2878) — lines `2874–2878`; excerpt `sha256:d0240691fa5956d3f42d0e151a25cfaa8d0a16e7b1cc510ba6b9ef168ed084dc`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:122](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L122-L122)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1572](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1572-L1572), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1606](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1606-L1606), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:2118](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2118-L2118), [cite at paper/reasoning-parts/erdos68/core.tex:1538](../../paper/reasoning-parts/erdos68/core.tex#L1538-L1538), [cite at paper/reasoning-parts/erdos68/core.tex:1572](../../paper/reasoning-parts/erdos68/core.tex#L1572-L1572), [cite at paper/reasoning-parts/erdos68/core.tex:2084](../../paper/reasoning-parts/erdos68/core.tex#L2084-L2084)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1351-L1357) — lines `1351–1357`; excerpt `sha256:afa42db0c4dfb2114be595de4a2efc8acb377b5e1bb8f446e52f2791f475b1eb`

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

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1756-L1760) — lines `1756–1760`; excerpt `sha256:372ad8d3f82ff0212ee04c7dd5a7269a56a5c9a52cae45f7d05245ccae260a87`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L4637-L4646) — lines `4637–4646`; excerpt `sha256:72a88e5a23c5730b248edc8d8bc104d1818c8c71ea25dbdd60a7c6074bb79d61`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L4595-L4604) — lines `4595–4604`; excerpt `sha256:72a88e5a23c5730b248edc8d8bc104d1818c8c71ea25dbdd60a7c6074bb79d61`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L109-L109) — lines `109–109`; excerpt `sha256:07fcf468eb97daf59fb2dc81ba8f582132d97355a60f1a6cf9d66f6fa2bef8bb`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L109-L109) — lines `109–109`; excerpt `sha256:07fcf468eb97daf59fb2dc81ba8f582132d97355a60f1a6cf9d66f6fa2bef8bb`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1651](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1651-L1651)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:151](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L151-L151), [cite at paper/reasoning-parts/erdos1041/core.tex:109](../../paper/reasoning-parts/erdos1041/core.tex#L109-L109)

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

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2993-L2995) — lines `2993–2995`; excerpt `sha256:82eaf36e749d94b9bc85e72cb6decbd8b7ce392b18e1edb0f50d7c491ba8f4cf`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2953-L2955) — lines `2953–2955`; excerpt `sha256:82eaf36e749d94b9bc85e72cb6decbd8b7ce392b18e1edb0f50d7c491ba8f4cf`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L405-L405) — lines `405–405`; excerpt `sha256:05a182c89d3cb5159892f33639988838718fc9f4a035d815850b886355821031`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2006-L2006) — lines `2006–2006`; excerpt `sha256:ad49b5aa94a8d9963ee6dcb001d2d84dc32e0776315128832b860e41fd3a9cf0`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L783-L785) — lines `783–785`; excerpt `sha256:82eaf36e749d94b9bc85e72cb6decbd8b7ce392b18e1edb0f50d7c491ba8f4cf`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:342](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L342-L342)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:445](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L445-L445), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2047](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2047-L2047), [cite at paper/reasoning-parts/erdos251/core.tex:405](../../paper/reasoning-parts/erdos251/core.tex#L405-L405), [cite at paper/reasoning-parts/erdos251/core.tex:2007](../../paper/reasoning-parts/erdos251/core.tex#L2007-L2007)

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

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L1320-L1325) — lines `1320–1325`; excerpt `sha256:76708e9e1ba9cb5b881eb2f319d5a6bf94dc5132c846fc6c1ebd51aef0fb72d4`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4446-L4451) — lines `4446–4451`; excerpt `sha256:41ce33a37be85c639d04c7e0ffada3de52abc55e55f352d0e27837ed17fce6db`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4421-L4426) — lines `4421–4426`; excerpt `sha256:41ce33a37be85c639d04c7e0ffada3de52abc55e55f352d0e27837ed17fce6db`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:675](../../paper/1049/erdos-1049-rational-base-lambert.tex#L675-L675)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1753](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1753-L1753), [cite at paper/reasoning-parts/erdos1049/core.tex:1728](../../paper/reasoning-parts/erdos1049/core.tex#L1728-L1728)

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

- [docs/papers/mirror/plectis-public-system.tex](../../docs/papers/mirror/plectis-public-system.tex#L1362-L1367) — lines `1362–1367`; excerpt `sha256:53b40a353a433ace78f48f685ef15ac1819dc844bcf364ec37ff3b127cdfeaba`

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

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1441-L1447) — lines `1441–1447`; excerpt `sha256:6c20454741356816e2d6d22e0fde01df4c611d7435ed3814f610e86ef368a80d`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9789-L9795) — lines `9789–9795`; excerpt `sha256:6c20454741356816e2d6d22e0fde01df4c611d7435ed3814f610e86ef368a80d`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L9605-L9611) — lines `9605–9611`; excerpt `sha256:6c20454741356816e2d6d22e0fde01df4c611d7435ed3814f610e86ef368a80d`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:138](../../paper/257/erdos-257-mersenne-support-subseries.tex#L138-L138)
- `erdos257-mersenne-reasoning-surface`: [cite at paper/257/erdos257-mersenne-reasoning-surface.tex:9655](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L9655-L9655), [cite at paper/reasoning-parts/erdos257/a257\_front.tex:9471](../../paper/reasoning-parts/erdos257/a257_front.tex#L9471-L9471)

<a id="source-source-f9a9d10dc9c525"></a>

### [Symposium: Trust via Auditable Records for Communities of AI Scientist Agents](https://doi.org/10.48550/arXiv.2608.19511)

- Source id: `source-f9a9d10dc9c525`
- Author or public identity: D. Pratt
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1624-L1627) — lines `1624–1627`; excerpt `sha256:2cb8ef505247970413bcf1ba50b6f4ccd133351e235c7f956ca8b13415b5c6da`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1420](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1420-L1420)

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

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4451-L4456) — lines `4451–4456`; excerpt `sha256:bd1db09a836b7bae7294afc1da1a7ae1ba135a083600d289e0dd8b45d24c10e4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4426-L4431) — lines `4426–4431`; excerpt `sha256:bd1db09a836b7bae7294afc1da1a7ae1ba135a083600d289e0dd8b45d24c10e4`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1458](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1458-L1458), [cite at paper/reasoning-parts/erdos1049/core.tex:1433](../../paper/reasoning-parts/erdos1049/core.tex#L1433-L1433)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L777-L779) — lines `777–779`; excerpt `sha256:2efe0e466de39d202e8f4b37c4f1254922fdfb071f848b688d6e85dd4f4cfff4`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2985-L2987) — lines `2985–2987`; excerpt `sha256:509f2c022f6bb16fcc6561688a6ee2a68568c8655480a3a52794977fbfd3eeec`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L2945-L2947) — lines `2945–2947`; excerpt `sha256:509f2c022f6bb16fcc6561688a6ee2a68568c8655480a3a52794977fbfd3eeec`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:206](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L206-L206), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:328](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L328-L328)
- `erdos-synthesis-reading-together-record`: [cite at paper/synthesis/erdos-synthesis-reading-together-record.tex:130](../../paper/synthesis/erdos-synthesis-reading-together-record.tex#L130-L130), [cite at paper/synthesis/erdos-synthesis-reading-together-record.tex:213](../../paper/synthesis/erdos-synthesis-reading-together-record.tex#L213-L213)
- `erdos-synthesis-subsums-across-bases`: [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:92](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L92-L92), [cite at paper/synthesis/erdos-synthesis-subsums-across-bases.tex:209](../../paper/synthesis/erdos-synthesis-subsums-across-bases.tex#L209-L209)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:327](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L327-L327), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:550](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L550-L550), [cite at paper/reasoning-parts/erdos251/core.tex:287](../../paper/reasoning-parts/erdos251/core.tex#L287-L287), [cite at paper/reasoning-parts/erdos251/core.tex:510](../../paper/reasoning-parts/erdos251/core.tex#L510-L510)

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

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L2920-L2924) — lines `2920–2924`; excerpt `sha256:913a7268d821938b55f3e6c38752a0db175dd6dca90b4edd9be62c706db57416`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L2886-L2890) — lines `2886–2890`; excerpt `sha256:913a7268d821938b55f3e6c38752a0db175dd6dca90b4edd9be62c706db57416`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1625](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1625-L1625), [cite at paper/reasoning-parts/erdos68/core.tex:1591](../../paper/reasoning-parts/erdos68/core.tex#L1591-L1591)

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

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2982-L2985) — lines `2982–2985`; excerpt `sha256:c0c58cb7c064ff51cdf457f20ba15d04a78eb43f30bbf3764f9162de257e6a00`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L811-L814) — lines `811–814`; excerpt `sha256:c0c58cb7c064ff51cdf457f20ba15d04a78eb43f30bbf3764f9162de257e6a00`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L2937-L2940) — lines `2937–2940`; excerpt `sha256:c0c58cb7c064ff51cdf457f20ba15d04a78eb43f30bbf3764f9162de257e6a00`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L49-L49) — lines `49–49`; excerpt `sha256:9e5544a92b411173c439bbe076b4d2eb3986bde7ed29a9977ea41ff793976004`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L49-L49) — lines `49–49`; excerpt `sha256:9e5544a92b411173c439bbe076b4d2eb3986bde7ed29a9977ea41ff793976004`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:284](../../paper/269/erdos-269-three-prime-running-lcm.tex#L284-L284)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:94](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L94-L94), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:400](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L400-L400), [cite at paper/reasoning-parts/erdos269/core.tex:49](../../paper/reasoning-parts/erdos269/core.tex#L49-L49), [cite at paper/reasoning-parts/erdos269/core.tex:355](../../paper/reasoning-parts/erdos269/core.tex#L355-L355)

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

- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L4590-L4597) — lines `4590–4597`; excerpt `sha256:737d5477a37bdfbe338d30af01c736674dfc46101542dd73448f0906325c87ee`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L4615-L4622) — lines `4615–4622`; excerpt `sha256:737d5477a37bdfbe338d30af01c736674dfc46101542dd73448f0906325c87ee`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1950](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1950-L1950), [cite at paper/reasoning-parts/erdos1049/core.tex:1925](../../paper/reasoning-parts/erdos1049/core.tex#L1925-L1925)

## Coverage requiring review

These gaps are shown explicitly so the catalogue cannot be mistaken for complete historical knowledge.

- Registered papers scanned: `23`; TeX source files scanned after local includes: `75`.
- Citation keys without a local bibliography definition: `0`
- Bibliography entries without a curated source link: `41`
- Lean lexical candidates awaiting review: `293`
- Unresolved local TeX includes: `0`

Machine-readable inventories, hashes, unresolved keys, and lexical candidates: [source-attribution-index.json](source-attribution-index.json).
