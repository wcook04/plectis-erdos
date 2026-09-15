<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Source attributions

_Generated from the authored source registry; do not hand-edit._

This index shows which public sources informed which papers, problems, Lean-facing records, and implemented changes. Source credit does not establish proof, novelty, endorsement, peer review, or complete historical coverage.

Private correspondence appears only under a neutral anonymous identity until public naming is confirmed. Its email, mailbox location, message text, and private evidence remain outside this repository.

## Coverage and anonymous implementation credits

The registry contains `197` curated sources across `21` registered papers and `1340` Lean library files.

Source review states: `bibliography_only`: `107`; `existing_source_closure`: `28`; `external_claim_unverified`: `2`; `implemented_advice`: `3`; `source_verified`: `57`.

Bibliography coverage records attribution already present in the corpus. A `bibliography_only` record still needs direct source-passage verification; a completed lexical review does not certify a source-to-theorem correspondence.

Implemented advice whose identity is awaiting confirmation:

- [Formalization classification and cheap inspection advice](#source-correspondence-001) — Implemented advice to classify each selected result, expose exact statements, proof provenance, novelty status, sorry count, axiom budget, and boundaries in formalization.yaml, and to provide a cheap Comparator inspection route with an altered-statement rejection fixture. The current public surface has evolved beyond the original interface count; the durable implementation is the manifest-plus-Comparator pattern and its explicit scope ceiling.
- [Theorem-first packaging and literature-comparison advice](#source-correspondence-002) — Implemented advice to lead with the exact finite-level rank and basis, give the CRT/Dirichlet-style independence mechanism, compare the result precisely with Allouche–Shallit, Coons, Martin, and adjacent k-kernel literature, and link a minimal Lean entry. The paper states the exact rank k^e+1 and basis, records that Coons already proved non-k-regularity and Martin supplies a broader external affine-independence antecedent while the public Lean proof establishes all-base independence separately, and keeps the unbounded #249 irrationality endpoint open. No proof verification, novelty judgment, or progress-on-parent-problem judgment is attributed to the correspondent.
- [Prior-art comparison advice](#source-correspondence-003) — Implemented a received pointer by comparing the cited q-Apéry construction with the #1049 rational-base programme. The public source closure verifies that the paper targets the same Lambert value, identifies the q-WZ operator and the integer-base denominator-clearing boundary, and credits both published authors in the ordinary literature row. The local Lean module separately proves that Van Assche’s different moving diagonal has a nonzero n=0 residual for the cited operator. This correspondence row credits only the private prior-art pointer; it does not claim the correspondent checked the comparison, calculations, Lean, or #1049 mathematics.

- Unmatched citation keys: `0`
- Bibliography entries awaiting curated links: `1`
- Lean candidates awaiting review: `23` (`2` direct URL/DOI/arXiv rows; `915` surname/key rows; categories may overlap).

## Browse by problem

- **Erdős #1041**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates), [Formalization classification and cheap inspection advice](#source-correspondence-001), [A short-path counterexample for polynomial lemniscates (external cl…](#source-erdos1041-ani-degree-seven-candidate-counterexample), [Independent check of candidate degree-seven counterexample](#source-erdos1041-morluto-independent-check), [Quartic case of Erdős #1041](#source-erdos1041-pendyala-quartic), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [A Markov-type inequality for arbitrary plane continua](#source-eremenko-2007-markov-type-inequality-plane-continua), [An extremal problem for polynomials](#source-eremenko-lempert-1994-extremal-problem-for-polynomials), [Comb functions](#source-eremenko-yuditskii-2012-comb-functions), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [The maximal length of the Erdős–Herzog–Piranian lemniscate in high…](#source-source-0e12f93aeac487), [Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zu…](#source-source-2ec6bf87654604), [Bad Polynomials for Newton's Method](#source-source-318ee5e7cf6d74), [The area of polynomial images and preimages](#source-source-40bc4064b92788), [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff), [On the length of lemniscates](#source-source-7f1f2a3fd9238c), [Shortest paths in polynomial lemniscate sublevel sets and a problem…](#source-source-8710374c3e8c9f), [The arc length of the lemniscate |p(z)|=1](#source-source-89b9a294db76bb), [A Degree-Four Lemniscate Path Theorem](#source-source-951f70d8dfc418), [Number of Components of Polynomial Lemniscates: A Problem of Erdős,…](#source-source-97b4e6a82335a7), [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec), [Some inequalities for polynomials and rational functions associated…](#source-source-dcbe400c96be59), [A Short Path Joining Two Zeros Inside a Polynomial Lemniscate](#source-source-f300911fb03a5c)
- **Erdős #1049**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Prior-art comparison advice](#source-correspondence-003), [Retrieval of Chowla 1947 original scan](#source-erdos1049-bloom-chowla-scan-retrieval), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #1049](#source-formal-conjectures-adapter-problem-1049), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [A problem about Mahler functions](#source-source-0a6b8c93371570), [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [À propos de la série ∑\_{n≥1} x^n/(q^n−1)](#source-source-169c3d67838965), [On a permutation group related to ζ(2)](#source-source-176d35cb60b651), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [On an incomplete argument of Erdős on the irrationality of Lambert…](#source-source-5911448b65fdf9), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [On the irrationality of ∑ 1/(q^n+r)](#source-source-62f9190aeb7d34), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Zero Coefficients of Rational Power Series and Rational Lambert Series](#source-source-aa2d5c249362f1), [On the irrationality of generalized q-logarithm](#source-source-ae9859af28fdcd), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94), [FormalConjectures.ErdosProblems.1049](#source-source-d7a43109c64c0c), [Arithmetical investigations of a certain infinite product](#source-source-e553241a97e580), [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f)
- **Erdős #243**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Koizumi pseudo-greedy equivalence and computation pointer](#source-erdos243-kovac-koizumi-pointer), [Rational-tail deterministic pair recurrence and open-boundary reduc…](#source-erdos243-tao-tail-pair-recurrence), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [FormalConjectures.ErdosProblems.243](#source-source-1713b9ad6350bd), [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641), [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62), [Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partia…](#source-source-2a3af2a360bb15), [A theorem on irrationality of infinite series and applications](#source-source-318b37ba5af2eb), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Irrationality of the reciprocal sum of doubly exponential sequences](#source-source-86d1745e2d139b), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f)
- **Erdős #249**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Theorem-first packaging and literature-comparison advice](#source-correspondence-002), [Möbius-transform identity for the binary totient constant](#source-erdos249-fan-mobius-transform), [Irrationality of the n=2^m sparse totient subseries](#source-erdos249-rafik-sparse-power-two-subseries), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #249](#source-formal-conjectures-adapter-problem-249), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891), [Erdős–Gál lacunary-series law of the iterated logarithm (two-part s…](#source-proposed-direct-7f278004ad452a), [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c), [Note on normal numbers](#source-proposed-direct-f7f90747134dba), [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da), [On the set of partial sums of an infinite series](#source-source-0ecb074e507b86), [Answer to An infinite sum based on the mod-parity of Euler's totien…](#source-source-0f61ad0796acdf), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Simultaneous inequalities among values of the Euler phi-function](#source-source-11b46a0435368f), [Regular sequences and the joint spectral radius](#source-source-296ff41148fff7), [On a curious property of vulgar fractions](#source-source-2aa4970cfda278), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [The ring of k -regular sequences](#source-source-5752bb5009e4de), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [Modular functions and transcendence questions](#source-source-6346eeeac5036d), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [(Non)automaticity of number theoretic functions](#source-source-741da55b02c5a9), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [The Lambert series factorization theorem](#source-source-8935df46fb4693), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [Comment on Erdős Problem #249](#source-source-99c2f3cb190b95), [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [On the binary digits of the Erdős--Borwein constant](#source-source-eca9e699590922), [Positive dyadic density for rational weighted binary expansions](#source-source-f4ad17717c8fd4)
- **Erdős #251**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Schlage-Puchta Theorem 2 literature pointer](#source-erdos251-alfaiz-schlage-puchta-pointer), [Counterexample to Erdős variable-denominator expectation](#source-erdos251-kovac-variable-denominator-counterexample), [Conditional #251 proof under Kuperberg Conjecture 1.3 and Lean form…](#source-erdos251-land-conditional-proof-lean), [Prime-gap summation-by-parts equivalence and conditional route](#source-erdos251-tao-prime-gap-equivalence), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #251](#source-formal-conjectures-adapter-problem-251), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Multiplicative Number Theory I: Classical Theory](#source-source-0aca0e5e4e03c0), [On the Erdős problem #251](#source-source-0ec7ca07508557), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Erdős Problems discussion thread #251](#source-source-21738452dcb95c), [On the largest prime factors of n and n+1](#source-source-27575f46a101c1), [Sur certaines séries à valeur irrationnelle](#source-source-2ee394177d0f38), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Continued Fractions](#source-source-5ee5f85bd606ee), [Small gaps between primes](#source-source-6564b203677735), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3), [Local gap statistics, telescoping, and normality](#source-source-9a38b2d8b0dada), [FormalConjectures.ErdosProblems.251](#source-source-b202a3f125817d), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001), [Bounded gaps between primes](#source-source-c32d672658410d), [Long gaps between primes](#source-source-d3995db1508bc9), [The irrationality of some number theoretical series](#source-source-d471eacdba0f87), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f), [A conditional proof of the irrationality of ∑\_{n≥1} p\_n 2^{−n} unde…](#source-source-f42f9e04743a4c)
- **Erdős #257**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Earlier variants, interval-filling negative variant, and fat-Cantor…](#source-erdos257-kovac-context-bundle), [Older Erdős and Borwein attribution for even/odd supports](#source-erdos257-kovac-older-special-case-attribution), [Period-two Lambert theorem applied to even and odd supports](#source-erdos257-tang-tachiya-period-two), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #257](#source-formal-conjectures-adapter-problem-257), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Diophantine Problems for q-Zeta Values](#source-proposed-direct-0ef4f73f93ceed), [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9), [Divisor-bounded multiplicative functions in short intervals](#source-proposed-direct-6c67db53ef5f8c), [The critical-window profile for d\_k in short intervals](#source-proposed-direct-6f90767d1d01dd), [The googol-th bit of the Erdős--Borwein constant](#source-source-0dd4239a1d50da), [On the set of partial sums of an infinite series](#source-source-0ecb074e507b86), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [On a curious property of vulgar fractions](#source-source-2aa4970cfda278), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [The ring of k -regular sequences](#source-source-5752bb5009e4de), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Generating special arithmetic functions by Lambert series factoriza…](#source-source-619de19af78c4c), [Modular functions and transcendence questions](#source-source-6346eeeac5036d), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44), [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [(Non)automaticity of number theoretic functions](#source-source-741da55b02c5a9), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [The Lambert series factorization theorem](#source-source-8935df46fb4693), [On the irrationality of certain series](#source-source-96aef073e2ea33), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [Ueber eine zahlentheoretische Funktion](#source-source-9db8c3859cdc81), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31), [The Lean mathematical library](#source-source-d8b2a7c411bc2d), [On the binary digits of the Erdős--Borwein constant](#source-source-eca9e699590922), [Positive dyadic density for rational weighted binary expansions](#source-source-f4ad17717c8fd4)
- **Erdős #269**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Infinite-prime-set irrationality proof and correction chain](#source-erdos269-fan-infinite-p-proof-repair), [Two-prime Hecke–Mahler factorisation and transcendence disclosure](#source-erdos269-fan-two-prime-disclosure), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [The Prime Number Theorem](#source-source-06457731c60720), [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Comment on Erdős Problem #269](#source-source-21cdeefea4c8ec), [Letter to the Editor](#source-source-22aba734190d65), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [FormalConjectures.ErdosProblems.269](#source-source-573a79feb36d47), [The van der Corput property for sums of two squares](#source-source-5ee4a583f9ca3f), [Strongly complete sets and a conjecture of Erdős](#source-source-71fb76f6e1363b), [On the number of positive integers ≤ x and free of prime factors \> y](#source-source-78565c625f0ea3), [Introduction to Analytic Number Theory](#source-source-99385343e032a3), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [Transcendence and continued fraction expansion of values of Hecke--…](#source-source-b9d7160919621f), [Arithmetic properties of certain functions in several variables III](#source-source-fcf73a15ff9c7c)
- **Erdős #68**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Formal Conjectures compatibility surface for Erdős #68](#source-formal-conjectures-adapter-problem-68), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [mathlib4](#source-mathlib4-pin-5e932f97), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674), [Character sums and congruences with n!](#source-source-34b520c561ee3c), [On the largest prime divisor of n!+1](#source-source-57adfd0cdcd8c2), [Prime divisors of shifted factorials](#source-source-5f85fb0bd75b8b), [Über die einfachen Zahlensysteme](#source-source-8ac37c92429a46), [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [On the irrationality of certain p-adic zeta values](#source-source-b3b7518e07e159), [On the irrationality of factorial series](#source-source-c835bc94aad831), [On the greatest and least prime factors of n!+1 , II](#source-source-d1710db60eae06), [Representations of Real Numbers by Infinite Series](#source-source-e13ecb7c94852a), [Rational numbers with odd greedy expansion of fixed length](#source-source-ef6233b59b95cb)

<details>
<summary>Browse alphabetically by author or public identity</summary>


- **A mathematician (name withheld pending confirmation)**: [Formalization classification and cheap inspection advice](#source-correspondence-001), [Theorem-first packaging and literature-comparison advice](#source-correspondence-002), [Prior-art comparison advice](#source-correspondence-003)
- **A. Anandkumar**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **A. Baanen**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **A. C. W. Finkelstein**: [An analysis of the requirements traceability problem](#source-source-e1665a6398558f)
- **A. D. Brucker**: [Isabelle/DOF: Design and Implementation](#source-source-51efe25c48a86d)
- **A. Eremenko**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates), [A Markov-type inequality for arbitrary plane continua](#source-eremenko-2007-markov-type-inequality-plane-continua), [An extremal problem for polynomials](#source-eremenko-lempert-1994-extremal-problem-for-polynomials), [Comb functions](#source-eremenko-yuditskii-2012-comb-functions), [On the length of lemniscates](#source-source-7f1f2a3fd9238c)
- **A. Granville**: [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31)
- **A. Gu**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **A. Hildebrand**: [On the number of positive integers ≤ x and free of prime factors \> y](#source-source-78565c625f0ea3)
- **A. J. van der Poorten**: [Arithmetic properties of certain functions in several variables III](#source-source-fcf73a15ff9c7c)
- **A. M. Swope**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **A. Sannai**: [Lean Atlas: An Integrated Proof Environment for Scalable Human--AI…](#source-source-ae32306341559a)
- **A. Ya. Khinchin**: [Continued Fractions](#source-source-5ee5f85bd606ee)
- **A. Yokoi**: [Apéry-type approximations and irrationality measures for certain q-…](#source-source-285ee90c8dcd62)
- **Aaroosh Ramadorai**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Alex Zhindon-Romero**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Alexander Fryntov**: [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec)
- **Alexander P. Mangerel**: [Divisor-bounded multiplicative functions in short intervals](#source-proposed-direct-6c67db53ef5f8c)
- **Alfaiz**: [Schlage-Puchta Theorem 2 literature pointer](#source-erdos251-alfaiz-schlage-puchta-pointer)
- **Amal Gueroudji**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Amy Xin**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Andrew Lott**: [The van der Corput property for sums of two squares](#source-source-5ee4a583f9ca3f)
- **Antonio Lobaccaro**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Artemii Remizov**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Arthur H. Copeland**: [Note on normal numbers](#source-proposed-direct-f7f90747134dba)
- **Aruna Das**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Asgar Jamneshan**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Association for Computing Machinery**: [Association for Computing Machinery](#source-source-ce5fddc99aff3f)
- **B. Adamczewski**: [A problem about Mahler functions](#source-source-0a6b8c93371570)
- **B. Gin-ge Chen**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **B. Green**: [Long gaps between primes](#source-source-d3995db1508bc9)
- **B. Miranda**: [Pantograph: A Machine-to-Machine Interaction Interface for Advanced…](#source-source-9a04cbea11fd0b)
- **B. Wolff**: [Isabelle/DOF: Design and Implementation](#source-source-51efe25c48a86d)
- **B. Yanahama**: [Lean Atlas: An Integrated Proof Environment for Scalable Human--AI…](#source-source-ae32306341559a)
- **Bin Dong**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Boris Adamczewski**: [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c)
- **Brian Etz**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Bryan Dai**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **C. Badea**: [A theorem on irrationality of infinite series and applications](#source-source-318b37ba5af2eb)
- **C. Barrett**: [Pantograph: A Machine-to-Machine Interaction Interface for Advanced…](#source-source-9a04cbea11fd0b)
- **C. E. Brown**: [Agent Hunt: Bounty Based Collaborative Autoformalization With LLM A…](#source-source-ae5cc4ddfa6af5)
- **C. J. Bishop**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates)
- **C. Kaliszyk**: [Agent Hunt: Bounty Based Collaborative Autoformalization With LLM A…](#source-source-ae5cc4ddfa6af5)
- **C. L. Stewart**: [On the greatest and least prime factors of n!+1 , II](#source-source-d1710db60eae06)
- **C. Lupu**: [On the irrationality of certain p-adic zeta values](#source-source-b3b7518e07e159)
- **C. Pomerance**: [On the largest prime factors of n and n+1](#source-source-27575f46a101c1), [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31)
- **C. Sun**: [Pantograph: A Machine-to-Machine Interaction Interface for Advanced…](#source-source-9a04cbea11fd0b)
- **C. Viola**: [On a permutation group related to ζ(2)](#source-source-176d35cb60b651)
- **Carl Schildkraut**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Carlo Pagano**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **ChatGPT 5.4 Pro (orchestrated by V. Kovač)**: [On the Erdős problem #251](#source-source-0ec7ca07508557)
- **Cheng-Chiang Tsai**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Chenkai Kuang**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Chenyi Li**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **Christoph Thiele**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Chuqin Geng**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **D. Duverney**: [À propos de la série ∑\_{n≥1} x^n/(q^n−1)](#source-source-169c3d67838965), [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Irrationality of fast converging series of rational numbers](#source-source-b0b779fff5defe)
- **D. P. Anderson**: [BOINC: A Platform for Volunteer Computing](#source-source-967c9acd787096)
- **D. Pratt**: [Symposium: Trust via Auditable Records for Communities of AI Scient…](#source-source-f9a9d10dc9c525)
- **D. Schmersau**: [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0)
- **D. Smertnig**: [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63)
- **D. Testa**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **D. Zeilberger**: [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b)
- **Daniel Jarka**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Daniel Rosendo**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Dawsen Hwang**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Demis Hassabis**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Dongruo An**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **E. Crane**: [The area of polynomial images and preimages](#source-source-40bc4064b92788)
- **E. G. Straus**: [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f)
- **Earl T. Barr**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Edward van de Meent**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Emad Shihab**: [Synergizing LLMs and Knowledge Graphs: A Novel Approach to Software…](#source-arxiv-2412-03815)
- **Eric Leonen**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Erick Wong**: [Answer to An infinite sum based on the mod-parity of Euler's totien…](#source-source-0f61ad0796acdf)
- **Evan Wang**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Evan Zheran Liu**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Evgenia Karunus**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **F. G. Sayward**: [Hints on test data selection](#source-source-c309c1132b63e3)
- **F. Herzog**: [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff)
- **F. Luca**: [Character sums and congruences with n!](#source-source-34b520c561ee3c), [Prime divisors of shifted factorials](#source-source-5f85fb0bd75b8b), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44)
- **Fanjin Zhang**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Federico Pasqualotto**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Fedor Nazarov**: [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](#source-source-a67b8dc01791ec)
- **Floris van Doorn**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **G. Cantor**: [Über die einfachen Zahlensysteme](#source-source-8ac37c92429a46)
- **G. Piranian**: [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff)
- **G. Pólya**: [Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zu…](#source-source-2ec6bf87654604)
- **G. Rhin**: [On a permutation group related to ζ(2)](#source-source-176d35cb60b651)
- **Garrett Bingham**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Giovanni Inchiostro**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **GitHub**: [Preventing pwn requests](#source-source-9ef9271dbecbce)
- **Glyn Harman**: [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001)
- **Golnaz Ghiasi**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Google DeepMind**: [formal-conjectures](#source-source-5edeb2408c36bd)
- **Great Internet Mersenne Prime Search**: [GIMPS](#source-source-cc1c19967d418f)
- **Greg Martin**: [Simultaneous inequalities among values of the Euler phi-function](#source-source-11b46a0435368f)
- **Guoxiong Gao**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **H. L. Montgomery**: [The Prime Number Theorem](#source-source-06457731c60720), [Multiplicative Number Theory I: Classical Theory](#source-source-0aca0e5e4e03c0)
- **H. Wang**: [Positive dyadic density for rational weighted binary expansions](#source-source-f4ad17717c8fd4)
- **Hajime Kaneko**: [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9)
- **Hangrui Bi**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Hanzhao Lin**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Hao-An Wu**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Heng-Tze Cheng**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Henry Yuen**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Hyunwoo Choi**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **I. E. Shparlinski**: [Character sums and congruences with n!](#source-source-34b520c561ee3c), [Prime divisors of shifted factorials](#source-source-5f85fb0bd75b8b)
- **I. O. Bado**: [Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partia…](#source-source-2a3af2a360bb15)
- **I. Rivin**: [Zero Coefficients of Rational Power Series and Rational Lambert Series](#source-source-aa2d5c249362f1)
- **I. Takahara**: [Toward Auditable AI Scientists: A Hypothesis Evolution Protocol for…](#source-source-4c664304e00cd3)
- **Imaan Sidhu**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **István S. Gál**: [Erdős–Gál lacunary-series law of the iterated logarithm (two-part s…](#source-proposed-direct-7f278004ad452a)
- **Ivo Petrov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **J. Asher**: [LeanExplore: A Search Engine for Lean 4 Declarations](#source-source-608828559136f9)
- **J. Avigad**: [LeanArchitect: Automating Blueprint Generation for Humans and AI](#source-source-80c9ae60b7f7be)
- **J. Bell**: [Mahler series with multiplicative coefficient sequences](#source-source-3bc828513b4d63)
- **J. Commelin**: [Growing Mathlib: Maintenance of a Large Scale Mathematical Library](#source-source-07d2ca69e611b7)
- **J. Farey**: [On a curious property of vulgar fractions](#source-source-2aa4970cfda278)
- **J. Galambos**: [Representations of Real Numbers by Infinite Series](#source-source-e13ecb7c94852a)
- **J. H. Loxton**: [Arithmetic properties of certain functions in several variables III](#source-source-fcf73a15ff9c7c)
- **J. Hančl**: [On the irrationality of factorial series](#source-source-c835bc94aad831)
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
- **Jarod Alper**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Jasper Dekoninck**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Jasper Mulder-Sohn**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Jeremiah Alonzo**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Jeremy Tan**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
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
- **Jonas Henkel**: [The Mathematician's Assistant: Integrating AI into Research Practice](#source-source-0d338bb41b8987)
- **Jonathan N. Lee**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Joni Teräväinen**: [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404)
- **Joonkyung Lee**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Joris Roos**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Juanzi Li**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Junehyuk Jung**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Junjie Wang**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Junsu Kim**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **János Pintz**: [The difference between consecutive primes, II](#source-source-baker-harman-pintz-2001)
- **K. Barreto**: [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674)
- **K. Ford**: [Long gaps between primes](#source-source-d3995db1508bc9)
- **K. Lazebnik**: [On the shapes of rational lemniscates](#source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates)
- **K. Postelmans**: [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f)
- **K. Ramachandran**: [Number of Components of Polynomial Lemniscates: A Problem of Erdős,…](#source-source-97b4e6a82335a7)
- **K. Väänänen**: [Arithmetical investigations of a certain infinite product](#source-source-e553241a97e580), [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f)
- **K. Yang**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **Kaisa Matomäki**: [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404)
- **Kaiying Hou**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Kaloyan Tsvetkov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Kevin Barreto**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **Koray Kavukcuoglu**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Kristian Minchev**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Kunal Marwaha**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **L. Aniva**: [Pantograph: A Machine-to-Machine Interaction Interface for Advanced…](#source-source-9a04cbea11fd0b)
- **L. Lai**: [On the largest prime divisor of n!+1](#source-source-57adfd0cdcd8c2), [On the irrationality of certain p-adic zeta values](#source-source-b3b7518e07e159)
- **L. Lempert**: [An extremal problem for polynomials](#source-eremenko-lempert-1994-extremal-problem-for-polynomials)
- **Lars Becker**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Lean Project.**: [Lean Language Reference](#source-source-bae14c21d3e920)
- **Lean community**: [Contributing to mathlib](#source-source-c29036ef9c4da8)
- **Lean contributors**: [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1)
- **Lei Hou**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Leo Diedering**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Leonardo Lobaccaro**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Leonardo de Moura**: [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3)
- **Luca Matone**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
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
- **Maksym Radziwiłł**: [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404)
- **Maria Drencheva**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Mark Harman**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Martin Höst**: [Guidelines for Conducting and Reporting Case Study Research in Soft…](#source-source-25efc27ed2130d)
- **Martin Vechev**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **María Inés de Frutos-Fernández**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Melinda Yuan**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Michael Rothgang**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Milen Shumanov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Miroslav Marinov**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Mislav Balunovic**: [The Open Proof Corpus: A Large-Scale Study of LLM-Generated Mathema…](#source-source-a38774d9a4f1f9)
- **Muzammil Shahbaz**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **N. Garg**: [EconCSLib: AI-Assisted Lean Formalization for Economics & Computati…](#source-source-b300504b513ffb)
- **N. Peng**: [The Network Structure of Mathlib](#source-source-81b67bfd835ac9)
- **NISO**: [CRediT: Contributor Roles Taxonomy](#source-source-d517c8a2d6f84d)
- **National Academies of Sciences, Engineering, and Medicine**: [Reproducibility and Replicability in Science](#source-source-011f43e5a781d7)
- **National Aeronautics and Space Administration**: [Software Assurance and Software Safety Standard](#source-source-278e74bfddddf0)
- **National Information Standards Organization.**: [Reproducibility Badging and Definitions](#source-source-f2a047037bae55)
- **National Institute of Standards**: [National Institute of Standards and Technology](#source-source-e6716218a1ac07)
- **National Institute of Standards and Technology**: [Secure Hash Standard](#source-source-f6e839bcb8a60f)
- **Nigamaa Nayakanti**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **O. C. Z. Gotel**: [An analysis of the requirements traceability problem](#source-source-e1665a6398558f)
- **Object Management Group.**: [Structured Assurance Case Metamodel (SACM)](#source-source-463b7e9f7264b1)
- **P. B. Borwein**: [On the irrationality of ∑ 1/(q^n+r)](#source-source-62f9190aeb7d34), [On the irrationality of certain series](#source-source-96aef073e2ea33)
- **P. Borwein**: [The arc length of the lemniscate |p(z)|=1](#source-source-89b9a294db76bb)
- **P. Bundschuh**: [Arithmetical investigations of a certain infinite product](#source-source-e553241a97e580)
- **P. Erdős**: [Old and New Problems and Results in Combinatorial Number Theory](#source-source-10545f868b3e88), [Letter to the Editor](#source-source-22aba734190d65), [On the largest prime factors of n and n+1](#source-source-27575f46a101c1), [Sur certaines séries à valeur irrationnelle](#source-source-2ee394177d0f38), [On arithmetical properties of Lambert series](#source-source-5c72388a6ca10f), [Metric properties of polynomials](#source-source-61ce6ad8b2f0ff), [On the irrationality of certain series](#source-source-7dc956ce55b7a0), [On the irrationality of certain series: problems and results](#source-source-b378189f39ed98), [On the irrationality of certain Ahmes series](#source-source-e33bdf934f939f)
- **P. Massot**: [leanblueprint](#source-source-944a1a754b1f3a)
- **P. Monticone**: [LeanArchitect: Automating Blueprint Generation for Humans and AI](#source-source-80c9ae60b7f7be)
- **P. Shafto**: [The Network Structure of Mathlib](#source-source-81b67bfd835ac9)
- **P. Song**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **P. Yuditskii**: [Comb functions](#source-eremenko-yuditskii-2012-comb-functions)
- **Palomar Registry**: [About Palomar](#source-source-9733ab875d6048)
- **Paul Erdős**: [Erdős–Gál lacunary-series law of the iterated logarithm (two-part s…](#source-proposed-direct-7f278004ad452a), [Note on normal numbers](#source-proposed-direct-f7f90747134dba), [Some problems and results on the irrationality of the sum of infini…](#source-source-43a734be32736f)
- **Peihao Wu**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Per Runeson**: [Guidelines for Conducting and Reporting Case Study Research in Soft…](#source-source-25efc27ed2130d)
- **Phil McMinn**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Pietro Monticone**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Polymath Project**: [General polymath rules](#source-source-af9e99293e9dd0)
- **Prasanna Balaprakash**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Priyamvad Srivastav**: [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891)
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
- **R. Prenger**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
- **R. Tijdeman**: [On the irrationality of factorial series](#source-source-c835bc94aad831)
- **Rafael Ferreira da Silva**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Rajula Srivastava**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **Raymond Provost**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Renan Souza**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Robert Rosenthal**: [The File Drawer Problem and Tolerance for Null Results](#source-source-7aa96129ebb643)
- **RomanLeLan**: [Retrieval of Chowla 1947 original scan](#source-erdos1049-bloom-chowla-scan-retrieval)
- **Ruey-An Shiu**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **S. Fan**: [Comment on Erdős Problem #269](#source-source-21cdeefea4c8ec), [Comment on Erdős Problem #249](#source-source-99c2f3cb190b95)
- **S. Ghosh**: [Number of Components of Polynomial Lemniscates: A Problem of Erdős,…](#source-source-97b4e6a82335a7)
- **S. Godil**: [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](#source-source-e2bdd690015cad)
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
- **Samuel Abedu**: [Synergizing LLMs and Knowledge Graphs: A Novel Approach to Software…](#source-arxiv-2412-03815)
- **Sang-hyun Kim**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **SayedHassan Khatoonabadi**: [Synergizing LLMs and Knowledge Graphs: A Novel Approach to Software…](#source-arxiv-2412-03815)
- **Sebastian Ullrich**: [Lean 4 theorem prover](#source-lean4-toolchain-v4-29-1), [The Lean 4 theorem prover and programming language](#source-source-b6603e42453ff3)
- **Sergei Gukov**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Shengtong Zhang**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **Shin Yoo**: [The Oracle Problem in Software Testing: A Survey](#source-source-5b5c84cd208fff)
- **Shuze Chen**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Simon Kurgan**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Sophie Szeto**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Steve Fan**: [Möbius-transform identity for the binary totient constant](#source-erdos249-fan-mobius-transform), [Infinite-prime-set irrationality proof and correction chain](#source-erdos269-fan-infinite-p-proof-repair), [Two-prime Hecke–Mahler factorisation and transcendence disclosure](#source-erdos269-fan-two-prime-disclosure), [The van der Corput property for sums of two squares](#source-source-5ee4a583f9ca3f), [Strongly complete sets and a conjecture of Erdős](#source-source-71fb76f6e1363b)
- **Sumit Giri**: [On correlations of certain multiplicative functions](#source-proposed-direct-595203db1f6891)
- **Sunny Hu**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Szabolcs Marka**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **Sébastien Gouëzel**: [A Blueprint for the Formalization of Carleson's Theorem on Converge…](#source-source-984f2b78d220ea)
- **T. Amdeberhan**: [q-Apéry irrationality proofs by q-WZ pairs](#source-source-7935fe19eb831b)
- **T. M. Apostol**: [Introduction to Analytic Number Theory](#source-source-99385343e032a3)
- **T. Matala-aho**: [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f)
- **T. Mizoguchi**: [Toward Auditable AI Scientists: A Hypothesis Evolution Protocol for…](#source-source-4c664304e00cd3)
- **T. Tao**: [The maximal length of the Erdős–Herzog–Piranian lemniscate in high…](#source-source-0e12f93aeac487), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Quantitative correlations and some problems on prime factors of con…](#source-source-685765cbd1ebe2), [Mathematics in the age of AI](#source-source-75e79d15dfab15), [Long gaps between primes](#source-source-d3995db1508bc9)
- **T. Zhu**: [LeanArchitect: Automating Blueprint Generation for Humans and AI](#source-source-80c9ae60b7f7be)
- **Technology**: [National Institute of Standards and Technology](#source-source-e6716218a1ac07)
- **Terence Tao**: [Rational-tail deterministic pair recurrence and open-boundary reduc…](#source-erdos243-tao-tail-pair-recurrence), [Prime-gap summation-by-parts equivalence and conditional route](#source-erdos251-tao-prime-gap-equivalence), [Shifted multiplicative-function correlation program named in the #2…](#source-proposed-direct-4e797194f74404), [Erdős Problems discussion thread #251](#source-source-21738452dcb95c), [AI contributions to Erdős problems](#source-source-e99ce64694b554)
- **Thang Luong**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **The Formal Conjectures Authors**: [Formal Conjectures compatibility surface for Erdős #1049](#source-formal-conjectures-adapter-problem-1049), [Formal Conjectures compatibility surface for Erdős #249](#source-formal-conjectures-adapter-problem-249), [Formal Conjectures compatibility surface for Erdős #251](#source-formal-conjectures-adapter-problem-251), [Formal Conjectures compatibility surface for Erdős #257](#source-formal-conjectures-adapter-problem-257), [Formal Conjectures compatibility surface for Erdős #68](#source-formal-conjectures-adapter-problem-68), [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary), [FormalConjectures.ErdosProblems.243](#source-source-1713b9ad6350bd), [FormalConjectures.ErdosProblems.269](#source-source-573a79feb36d47), [FormalConjectures.ErdosProblems.251](#source-source-b202a3f125817d), [FormalConjectures.ErdosProblems.1049](#source-source-d7a43109c64c0c)
- **The mathlib Community**: [mathlib4](#source-mathlib4-pin-5e932f97), [The Lean mathematical library](#source-source-d8b2a7c411bc2d)
- **Thomas Bloom**: [Retrieval of Chowla 1947 original scan](#source-erdos1049-bloom-chowla-scan-retrieval), [Infinite-prime-set irrationality proof and correction chain](#source-erdos269-fan-infinite-p-proof-repair)
- **Thomas F. Bloom**: [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context), [Erdős Problems discussion thread #251](#source-source-21738452dcb95c)
- **Thomas F. Bloom (site editor)**: [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257,…](#source-erdos-problems-catalog-eight-problem-context)
- **Tianyi Peng**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Timothy Poteet**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **Tony Feng**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Trieu H. Trinh**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Trieu Trinh**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **V. Kovač**: [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-0f1a3708d62674), [On several irrationality problems for Ahmes series](#source-source-4f5fd0d7405e29), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3)
- **V. N. Dubinin**: [Some inequalities for polynomials and rational functions associated…](#source-source-dcbe400c96be59)
- **V. S. Pendyala**: [Shortest paths in polynomial lemniscate sublevel sets and a problem…](#source-source-8710374c3e8c9f), [A Degree-Four Lemniscate Path Theorem](#source-source-951f70d8dfc418)
- **Vasily Ilin**: [TheoremGraph: Bridging Formal and Informal Mathematics](#source-source-45ae653f011748)
- **Venkata Pendyala**: [Quartic case of Erdős #1041](#source-erdos1041-pendyala-quartic)
- **Vjekoslav Kovač**: [Koizumi pseudo-greedy equivalence and computation pointer](#source-erdos243-kovac-koizumi-pointer), [Counterexample to Erdős variable-denominator expectation](#source-erdos251-kovac-variable-denominator-counterexample), [Earlier variants, interval-filling negative variant, and fat-Cantor…](#source-erdos257-kovac-context-bundle), [Older Erdős and Borwein attribution for even/odd supports](#source-erdos257-kovac-older-special-case-attribution), [Irrationality of rapidly converging series: a problem of Erdős and…](#source-source-c742deb980b53c)
- **W. Hayman**: [On the length of lemniscates](#source-source-7f1f2a3fd9238c)
- **W. Koepf**: [Irrationality of certain infinite series II](#source-source-a87fa25f28c7b0)
- **W. R. Alford**: [There are infinitely many Carmichael numbers](#source-source-d14cd7f6920a31)
- **W. Van Assche**: [Irrationality of ζ\_q(1) and ζ\_q(2)](#source-source-6c2fbacaba626f), [Little q-Legendre polynomials and irrationality of certain Lambert…](#source-source-cd126799fede94)
- **W. Zudilin**: [Heine's basic transform and a permutation group for q-harmonic series](#source-source-120bebce1ffe8c), [On the irrationality of generalized q-logarithm](#source-source-ae9859af28fdcd), [New irrationality measures for q-logarithms](#source-source-e5f2924d82c59f)
- **W. van Doorn**: [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641), [Lacunary sequences whose reciprocal sums represent all rational num…](#source-source-892c567092d6f3)
- **Wadim Zudilin**: [Diophantine Problems for q-Zeta Values](#source-proposed-direct-0ef4f73f93ceed)
- **Wei-Yuan Li**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Wenjie Ma**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Will Cook (coverage audit author)**: [Formal Conjectures coverage boundary across the eight-problem corpus](#source-formal-conjectures-eight-problem-coverage-boundary)
- **Woong Shin**: [LLM Agents for Interactive Workflow Provenance: Reference Architect…](#source-arxiv-2509-13978)
- **X. Li**: [The Network Structure of Mathlib](#source-source-81b67bfd835ac9)
- **Xiaomeng Yang**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Xiaoyang Lu**: [Prove2Me: An Open Collaborative Platform for Scaling Math Formaliza…](#source-source-36f533b76bc247)
- **Xujie Si**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Y. Bugeaud**: [Transcendence and continued fraction expansion of values of Hecke--…](#source-source-b9d7160919621f)
- **Y. Jia**: [An analysis and survey of the development of mutation testing](#source-source-3a21eca35f05cf)
- **Y. Li**: [Optimal bounds for an Erdős problem on matching integers to distinc…](#source-source-1b9324cc5f4641)
- **Y. Tachiya**: [Refinement of the Chowla--Erdős method and linear independence of c…](#source-source-317a740451ce03), [Linear independence results for the values of divisor functions series](#source-source-6accca20cd5e44)
- **Y. Zhang**: [Bounded gaps between primes](#source-source-c32d672658410d)
- **YaGuang Li**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yann Bugeaud**: [Adamczewski–Bugeaud subword-complexity method context](#source-proposed-direct-d4ac203509248c)
- **Yi Tay**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yohei Tachiya**: [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9)
- **Youngbeom Jin**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Youyuan Zhang**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Yu-Chen Sun**: [The critical-window profile for d\_k in short intervals](#source-proposed-direct-6f90767d1d01dd)
- **Yu-Sheng Shih**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5)
- **Yu. V. Nesterenko**: [Modular functions and transcendence questions](#source-source-6346eeeac5036d)
- **Yuan Liu**: [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yuri Chervonyi**: [Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on…](#source-source-79afab8abaf9d5), [Towards Autonomous Mathematics Research](#source-source-a028dc6bb31c0c)
- **Yuta Suzuki**: [Refinements of Erdős's irrationality criterion for certain sparse i…](#source-proposed-direct-329775d58148a9)
- **Yutong Wang**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Zaiwen Wen**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **Zeming Sun**: [LeanSearch v2: Global Premise Retrieval for Lean 4 Theorem Proving](#source-source-82459d858b7d75)
- **Zeraoulia Rafik**: [Irrationality of the n=2^m sparse totient subseries](#source-erdos249-rafik-sparse-power-two-subseries)
- **Zhaoyu Li**: [DreamProver: Evolving Transferable Lemma Libraries via a Wake--Slee…](#source-source-7d871bf2920e53)
- **Zichen Lai**: [Advancing Mathematical Research via Human-AI Interactive Theorem Pr…](#source-source-6ade6fbcd34d79)
- **Zijun Yao**: [EurekAgent: Agent Environment Engineering is All You Need for Auton…](#source-source-cc823e517ced81)
- **Zsuzsa Marka**: [End-to-End Testing of Open-Source Hardware Documentation Developed…](#source-arxiv-2309-05942)
- **ani (forum handle; manuscript contains no author declaration)**: [A short-path counterexample for polynomial lemniscates (external cl…](#source-erdos1041-ani-degree-seven-candidate-counterexample)
- **morluto**: [Independent check of candidate degree-seven counterexample](#source-erdos1041-morluto-independent-check)
- **shtuka**: [A Short Path Joining Two Zeros Inside a Polynomial Lemniscate](#source-source-f300911fb03a5c)

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

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:1128](../../paper/systems/open-source-mathematics-strategy.tex#L1128-L1128)

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

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:476](../../paper/systems/cold-clone-to-proof-receipt.tex#L476-L476)

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

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:360](../../paper/systems/cold-clone-to-proof-receipt.tex#L360-L360)

<a id="source-bishop-eremenko-lazebnik-2025-shapes-of-rational-lemniscates"></a>

### [On the shapes of rational lemniscates](https://arxiv.org/abs/2407.14610)

- Source id: `bishop\_eremenko\_lazebnik\_2025\_shapes\_of\_rational\_lemniscates`
- Author or public identity: C. J. Bishop, A. Eremenko, K. Lazebnik
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Topological context: a simple critical point on a level curve is a degree-four vertex of the lemniscate graph, the four-sector picture used in the proof-gap diagnosis. The results are approximation and realisation theorems up to homeomorphism and give no metric or path-length estimate.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Definition 1.2 (lemniscate graph, every vertex of even degree at least four) and Proposition 2.4 (every rational lemniscate is a lemniscate graph with vertices at the critical points on the level set); Corollary 1.6 (a lemniscate graph is realised by a polynomial lemniscate up to a homeomorphism of the plane exactly when it is the boundary of its unbounded face). Numbering checked against arXiv v3.](https://arxiv.org/abs/2407.14610)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1405-L1409) — lines `1405–1409`; excerpt `sha256:f8d7e2c7371688eef7424dd98adc281c517b947894b56f1f3ea3ea04ab41e054`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2960-L2968) — lines `2960–2968`; excerpt `sha256:9e7fd19baa0c4857489776145f8fb3ebcb958571cea10e15db1cb481e3d82be3`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L95-L103) — lines `95–103`; excerpt `sha256:9e7fd19baa0c4857489776145f8fb3ebcb958571cea10e15db1cb481e3d82be3`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:865](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L865-L865)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:224](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L224-L224), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:227](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L227-L227), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2267](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2267-L2267), [cite at paper/reasoning-parts/erdos1041/core.tex:181](../../paper/reasoning-parts/erdos1041/core.tex#L181-L181), [cite at paper/reasoning-parts/erdos1041/core.tex:184](../../paper/reasoning-parts/erdos1041/core.tex#L184-L184), [cite at paper/reasoning-parts/erdos1041/core.tex:2224](../../paper/reasoning-parts/erdos1041/core.tex#L2224-L2224)

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

- [formalization.yaml](../../formalization.yaml#L1-L63) — lines `1–63`; excerpt `sha256:d643f118cca23cffbd77bbec684ab75b67a5db05e6c4dd712cab3d2de6395b22`
- [verification/comparator.json](../../verification/comparator.json#L1-L38) — lines `1–38`; excerpt `sha256:59da13809c33a93943095066b40909da907617aa28592c6201635ba1b55d5e81`
- [verification/comparator-negative-mismatch.json](../../verification/comparator-negative-mismatch.json#L1-L13) — lines `1–13`; excerpt `sha256:43aca5f4da7f5f42baf826e53324c045e4fa11acd20ffd1743609e20b5084157`
- [docs/EXTERNAL\_VERIFICATION.md](../../docs/EXTERNAL_VERIFICATION.md#L4-L14) — lines `4–14`; excerpt `sha256:68faf6651842e8f310a3abb90b6ae3fa71028e22c17f50e16fa88b707adb2c73`

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

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L23-L54) — lines `23–54`; excerpt `sha256:2ff03a3c73bbf0d16b8407a4098ca4e42c941f20de36ecbb2ac007e6fc92a8b8`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L59-L98) — lines `59–98`; excerpt `sha256:e41398ec47e5e177eb90c627543a2ebd43045fb38047a74ca4f41b45e4758993`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L573-L587) — lines `573–587`; excerpt `sha256:65030d24bd92830c0e89a616c55cda5c509544127dae9f395367324baa4f8eb3`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L662-L668) — lines `662–668`; excerpt `sha256:7b396d32e0520f148c4cd2ef0776ea5898ab787c34eeebbb74efbdcf93c45865`
- [lean/Erdos249257/TotientMahlerDefect.lean](../../lean/Erdos249257/TotientMahlerDefect.lean#L935-L1145) — lines `935–1145`; excerpt `sha256:e4bbeef9407526e58653fc7ed307d51530c41af7bd6d225f36388486dc845a6e`
- [formalization.yaml](../../formalization.yaml#L162-L219) — lines `162–219`; excerpt `sha256:b323e9a098414f61b29469d542453a446713a6650efbe384accb4d657f9a1e7e`
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
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L169-L225) — lines `169–225`; excerpt `sha256:4788e4d316aec27743943cf64b21291abb4c14c83ebe583fbafe24fb71fff5ab`
- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L326-L330) — lines `326–330`; excerpt `sha256:c9f8d191bbf7d39a3e75436d9d7036604d3f396d1223d6f8d505668cafc4971e`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L1-L100) — lines `1–100`; excerpt `sha256:2869c3db2da5857a4c9fc56be272d52f5a7b1242f3633bd8ed0b01f0da016724`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L876-L896) — lines `876–896`; excerpt `sha256:e8ae32450cbc9049293293d2f552e05daf3d0a63c406bd2a0968063fa4a14b0d`

<a id="source-erdos1041-ani-degree-seven-candidate-counterexample"></a>

### [A short-path counterexample for polynomial lemniscates (external claim awaiting source assessment)](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-8861)

- Source id: `erdos1041\_ani\_degree\_seven\_candidate\_counterexample`
- Author or public identity: ani (forum handle; manuscript contains no author declaration)
- Kind: `website\_contribution`
- Problems: #1041
- Relationship and boundary: External claim awaiting source assessment. The manuscript titled “A short-path counterexample for polynomial lemniscates” gives an explicit family: t=417/40; A=−5+12t−3t², B=−4+4t+6t², C=t(−8+15t−2t²); ε=s², ρ=1−s^16, a\_s=A−is, b\_s=iB+(9/5)s, c\_s=−C−(162/25)is; F\_s(z)=z^7−1+ε^4(a\_s z^3−conj(a\_s)z^4)+ε^5(b\_s z^2−conj(b\_s)z^5)+ε^6(c\_s z−conj(c\_s)z^6), f\_s(z)=ρ^7F\_s(z/ρ). Theorem 1.1 claims all seven simple zeros have modulus ρ and every path in {|f\_s|\<1} joining distinct zeros has length \>2+(α/2)s². Manuscript has no author declaration and no arXiv identifier. Do not change #1041 status until source/proof assessment.
- Source verification: `external\_claim\_unverified` — External claim and manuscript identity verified; mathematical correctness unreviewed and no local claim/status change permitted.
- Local mapping: `external\_claim\_only` — No local adoption; mutable external manuscript awaiting source/proof assessment.

Exact source locations:

- [Comment posted 7 Sep 2026 by ani; exact HTML element permalink #post-8861](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-8861)
- [Public Overleaf project title \`1041counterexample\`; main.tex viewed 2026-09-12; no \\author command between title/date and document body](https://www.overleaf.com/read/ctmqrqwthkcn#bf8155)
- [Theorem 1.1 and equations (1.1)–(1.2): one-parameter monic degree-7 family; all seven simple zeros have modulus rho=1-s^16\<1; every joining path has length \>2+(alpha/2)s^2](https://www.overleaf.com/read/ctmqrqwthkcn#bf8155)

<a id="source-erdos1041-morluto-independent-check"></a>

### [Independent check of candidate degree-seven counterexample](https://www.erdosproblems.com/forum/thread/1041?order=oldest#post-8925)

- Source id: `erdos1041\_morluto\_independent\_check`
- Author or public identity: morluto
- Kind: `website\_contribution`
- Problems: #1041
- Relationship and boundary: Forum statement that the degree-seven counterexample seems valid. No proof details or independent artifact linked; corroboration only, insufficient for status change.
- Source verification: `external\_claim\_unverified` — External claim and manuscript identity verified; mathematical correctness unreviewed and no local claim/status change permitted.
- Local mapping: `external\_corroboration\_only` — No proof artifact or local adoption; corroborating comment only.

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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L63-L67) — lines `63–67`; excerpt `sha256:c2864518e4865dd44a4a7f0e412686c80f1580a48114e8077d016e2b7ddcb64b`
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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L231-L235) — lines `231–235`; excerpt `sha256:eaf3b2d51c02f396311adf2ef91d0f021cca117e79f8f4b020ac851aa8ba0289`
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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L239-L243) — lines `239–243`; excerpt `sha256:0f62f937441a579688654793f759c8d3a907ac15bb22aa83897d45df1462216a`
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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L514-L520) — lines `514–520`; excerpt `sha256:cb2e5e5ae4a5f38a9e1f721526f90a807386a7ec76a15c8ab4c067b1037e7751`
- [lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean](../../lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L138-L172) — lines `138–172`; excerpt `sha256:df88134179386f6161b138662a0cf1e7faf8a0ff67d5a839a7ac4608d03ad1c2`
- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L390-L421) — lines `390–421`; excerpt `sha256:912d421ce3a607706d9b45fcb033ab97d4d81f834be36a029c3407aca9e05ae8`

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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L133-L137) — lines `133–137`; excerpt `sha256:badb6c16b351f142047e83c1c8631e63319c82edabf1973f16a616deead6f4d6`
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

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L283-L287) — lines `283–287`; excerpt `sha256:02b7a5fb6ec6414051189b65c6c9f2a8dd2efedd07a902ef54cbbb4256862c97`

<a id="source-erdos-problems-catalog-eight-problem-context"></a>

### [Erdős Problems catalogue pages for problems 68, 243, 249, 251, 257, 269, 1041, and 1049](https://www.erdosproblems.com/68)

- Source id: `erdos\_problems\_catalog\_eight\_problem\_context`
- Author or public identity: Thomas F. Bloom (site editor), Thomas F. Bloom
- Kind: `catalogue`
- Problems: #68, #243, #249, #251, #257, #269, #1041, #1049
- Relationship and boundary: Numbering, current-status context, source keys, and discussion hosting only; the site explicitly requests citation of original Erdős sources and disclaims verification of comments. This row confers no result attribution or proof authority. Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
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

Public implementation or evidence coordinates:

- [docs/PRIOR\_ART.md](../../docs/PRIOR_ART.md#L13-L14) — lines `13–14`; excerpt `sha256:aa0115edbe0e59ed8b451f14efbc32d972ac7de0a6a72dd7f26064aeb1e64466`
- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5441-L5452) — lines `5441–5452`; excerpt `sha256:f4a1bd463f398d1bcf67d88f273df4a9fc0dc2d42efadf85db1519f432cadfb5`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L898-L900) — lines `898–900`; excerpt `sha256:5f0b6ad6c1a9049d21841bc0ffd6cf7d1b57c719cf79d0d3de5d351e68db74b0`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1864-L1866) — lines `1864–1866`; excerpt `sha256:e5494a50a0f7c7be61da8c4ebed885104322236b7385212b94cb1ca90db8430f`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L915-L918) — lines `915–918`; excerpt `sha256:f368736822439c8534e80f5aff6ba16c1d13eb3f95e95a7dc6ba80c48fac291b`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3038-L3045) — lines `3038–3045`; excerpt `sha256:a82238cd268701b267206867227541e7cda1a1934fffdb55b471779e3192d009`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1517-L1526) — lines `1517–1526`; excerpt `sha256:d68be54d52bf9e3ed72d19ffc5de70c812d5d9bb4c01596c2f62aa742602b88a`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2459-L2469) — lines `2459–2469`; excerpt `sha256:d811f289543251ac4fe24a5a25d6d306937e5061b9bf9d137aad48604e454a25`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2162-L2171) — lines `2162–2171`; excerpt `sha256:f6313f84ee4cae2831248cfded852aa5b91aa593b75b4c003a6ff8319ed3043c`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L900-L909) — lines `900–909`; excerpt `sha256:2a31cd3b3c721e68cfe80551bfab84e8df13b2751ef98c0cedd2ef9da2795477`
- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1369-L1371) — lines `1369–1371`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2874-L2876) — lines `2874–2876`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L984-L991) — lines `984–991`; excerpt `sha256:43408f7d298cd4d9f67a8bde8169b5811d789752c86ce742c8a1a4f6d69fe4d5`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3181-L3187) — lines `3181–3187`; excerpt `sha256:b995402f056f7f2c322ca73a63c6daabeda8be2242e4999da7b00b8e65a63557`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1530-L1535) — lines `1530–1535`; excerpt `sha256:bb8050123710e542e010c55df517209f1e56e938a1655ebb63df13ec2e2c8c44`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L9-L11) — lines `9–11`; excerpt `sha256:b93ff125a99b72635bb970f16de63ead752a365b8b956999f315d6f346c08fed`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L168-L168) — lines `168–168`; excerpt `sha256:e9329131513727827f691a8adcbddeb8844020368e191c429b44ad5d861c23d0`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L98-L104) — lines `98–104`; excerpt `sha256:b995402f056f7f2c322ca73a63c6daabeda8be2242e4999da7b00b8e65a63557`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L84-L84) — lines `84–84`; excerpt `sha256:abee1ad19a4f7029baf13b3aeb92d9023ec2260a2de0135dc700ad3770cb9f1f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2824-L2824) — lines `2824–2824`; excerpt `sha256:0a42744281855ae29a6800bb29de6d24059a49ac3582e8a3a08e7b704d62af5b`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L44-L51) — lines `44–51`; excerpt `sha256:a82238cd268701b267206867227541e7cda1a1934fffdb55b471779e3192d009`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L52-L52) — lines `52–52`; excerpt `sha256:d30e9d0fcb43e28ef7b77c3b6bc103a2246ad103c759135d548469c0406c1aac`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L598-L598) — lines `598–598`; excerpt `sha256:4bda527bbb4746f493a2fd85d3a740e85652145cfb20dca2bcc3fa8d61b23ba8`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2694-L2694) — lines `2694–2694`; excerpt `sha256:0a42744281855ae29a6800bb29de6d24059a49ac3582e8a3a08e7b704d62af5b`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L102-L112) — lines `102–112`; excerpt `sha256:d811f289543251ac4fe24a5a25d6d306937e5061b9bf9d137aad48604e454a25`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L76-L76) — lines `76–76`; excerpt `sha256:9f04beaac5e7dd3af0894b6b61a24c8fb6607b9301597da0cf33784a2b105954`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L151-L151) — lines `151–151`; excerpt `sha256:182ef11cadd6b767d227a7517c47f53db424cd95808cfcbbf91705ee28ba9d44`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L162-L162) — lines `162–162`; excerpt `sha256:152c640fc79935321d440952ccece0b4e327a6d682b065c2697651660ff80951`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1690-L1690) — lines `1690–1690`; excerpt `sha256:abc060a4e621f266ea418ab11a5d8bebd16a6d47e09579c280edd582cddf6e07`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L21-L30) — lines `21–30`; excerpt `sha256:f6313f84ee4cae2831248cfded852aa5b91aa593b75b4c003a6ff8319ed3043c`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:0af6f35fe8028668266105978bdb9d8032a07243c596ea681fb780a2bad17084`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L1634-L1634) — lines `1634–1634`; excerpt `sha256:d0559e3f93ab362bb16be698bc158dd0b137805f14ac89688540eb87a7ddd97a`
- [paper/reasoning-parts/erdos269/extended\_record.tex](../../paper/reasoning-parts/erdos269/extended_record.tex#L15-L15) — lines `15–15`; excerpt `sha256:18db47165ee95f2eb32707eb80d1c87416fe442904fb4697a88bcce57c181f8e`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L10-L12) — lines `10–12`; excerpt `sha256:e5494a50a0f7c7be61da8c4ebed885104322236b7385212b94cb1ca90db8430f`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L54-L54) — lines `54–54`; excerpt `sha256:6bed281aa83e0e967f07a62c0c4f9e325c6d84433a08920a1e9e738b34aa500a`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:862](../../paper/1049/erdos-1049-rational-base-lambert.tex#L862-L862)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:1347](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1347-L1347)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:668](../../paper/269/erdos-269-three-prime-running-lcm.tex#L668-L668)
- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:87](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L87-L87)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:211](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L211-L211), [cite at paper/reasoning-parts/erdos1041/core.tex:168](../../paper/reasoning-parts/erdos1041/core.tex#L168-L168)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:109](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L109-L109), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2849](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2849-L2849), [cite at paper/reasoning-parts/erdos1049/core.tex:84](../../paper/reasoning-parts/erdos1049/core.tex#L84-L84), [cite at paper/reasoning-parts/erdos1049/core.tex:2824](../../paper/reasoning-parts/erdos1049/core.tex#L2824-L2824)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:94](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L94-L94), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:640](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L640-L640), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2736](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2736-L2736), [cite at paper/reasoning-parts/erdos243/core.tex:52](../../paper/reasoning-parts/erdos243/core.tex#L52-L52), [cite at paper/reasoning-parts/erdos243/core.tex:598](../../paper/reasoning-parts/erdos243/core.tex#L598-L598), [cite at paper/reasoning-parts/erdos243/core.tex:2694](../../paper/reasoning-parts/erdos243/core.tex#L2694-L2694)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:197](../../paper/archive/erdos249-257-main-paper.tex#L197-L197), [cite at paper/archive/erdos249-257-main-paper.tex:4524](../../paper/archive/erdos249-257-main-paper.tex#L4524-L4524)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:110](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L110-L110), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:185](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L185-L185), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:196](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L196-L196), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1725](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1725-L1725), [cite at paper/reasoning-parts/erdos251/core.tex:76](../../paper/reasoning-parts/erdos251/core.tex#L76-L76), [cite at paper/reasoning-parts/erdos251/core.tex:151](../../paper/reasoning-parts/erdos251/core.tex#L151-L151), [cite at paper/reasoning-parts/erdos251/core.tex:162](../../paper/reasoning-parts/erdos251/core.tex#L162-L162), [cite at paper/reasoning-parts/erdos251/core.tex:1691](../../paper/reasoning-parts/erdos251/core.tex#L1691-L1691)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:105](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L105-L105), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1685](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1685-L1685), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1701](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1701-L1701), [cite at paper/reasoning-parts/erdos269/core.tex:54](../../paper/reasoning-parts/erdos269/core.tex#L54-L54), [cite at paper/reasoning-parts/erdos269/core.tex:1634](../../paper/reasoning-parts/erdos269/core.tex#L1634-L1634), [cite at paper/reasoning-parts/erdos269/extended\_record.tex:15](../../paper/reasoning-parts/erdos269/extended_record.tex#L15-L15)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:90](../../paper/68/erdos68-factorial-reasoning-surface.tex#L90-L90), [cite at paper/reasoning-parts/erdos68/core.tex:54](../../paper/reasoning-parts/erdos68/core.tex#L54-L54)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:489](../../paper/systems/open-source-mathematics-strategy.tex#L489-L489), [cite at paper/systems/open-source-mathematics-strategy.tex:673](../../paper/systems/open-source-mathematics-strategy.tex#L673-L673)

<a id="source-eremenko-2007-markov-type-inequality-plane-continua"></a>

### [A Markov-type inequality for arbitrary plane continua](https://arxiv.org/abs/math/0606745)

- Source id: `eremenko\_2007\_markov\_type\_inequality\_plane\_continua`
- Author or public identity: A. Eremenko
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Record of the equality cases of the Eremenko-Lempert derivative bound (restated as Theorem A): its Chebyshev extremals, like the scaled Chebyshev polynomial in the sharp collinear theorem, have every critical value on one level circle. No argument in the #1041 papers uses the derivative bound.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Theorem A (arXiv p. 2) states the sharp bound sup |f'| \<= 2^(1/d-1) d^2 on a connected sublevel set {|f| \<= 1} of a monic degree-d polynomial, conjectured by Erdos and proved by Eremenko and Lempert, with equality exactly for c^(-d) T\_d(2^(1/d-1) c z + b), |c| = 1; Theorem 2 (p. 3) gives the capacity form for a component of the sublevel set.](https://arxiv.org/abs/math/0606745)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1401-L1405) — lines `1401–1405`; excerpt `sha256:ba940c186fb686dbc03385fb5086ca4d9293f7861cacc2f9bbce186f2c1f750e`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2952-L2960) — lines `2952–2960`; excerpt `sha256:e67a45d86316bb43f89f227692bc8553160eb268b4aa44307d64426c872eae9f`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L87-L95) — lines `87–95`; excerpt `sha256:e67a45d86316bb43f89f227692bc8553160eb268b4aa44307d64426c872eae9f`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1024](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1024-L1024)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1292](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1292-L1292), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2951](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2951-L2951), [cite at paper/reasoning-parts/erdos1041/back.tex:86](../../paper/reasoning-parts/erdos1041/back.tex#L86-L86), [cite at paper/reasoning-parts/erdos1041/core.tex:1249](../../paper/reasoning-parts/erdos1041/core.tex#L1249-L1249)

<a id="source-eremenko-lempert-1994-extremal-problem-for-polynomials"></a>

### An extremal problem for polynomials

- Source id: `eremenko\_lempert\_1994\_extremal\_problem\_for\_polynomials`
- Author or public identity: A. Eremenko, L. Lempert
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Original proof (Proc. Amer. Math. Soc. 122 (1994), 191-193) of the sharp bound for |f'| on a connected sublevel set {|f| \<= 1} of a monic polynomial, conjectured by Erdos. Cited for attribution beside its restatement as Theorem A of Eremenko 2007; the 1994 paper itself was not consulted, and the attribution follows Eremenko 2007 (reference \[5\]) and Eremenko's publication list.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1398-L1401) — lines `1398–1401`; excerpt `sha256:259a8d61790b0e66ff3fac1737c3054b87d06cd10bf04dd4e31c2f47b4066851`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2946-L2952) — lines `2946–2952`; excerpt `sha256:0ae78181a0498fd68e97a7b3ddfe1c78c6648940b593286ad413ac1138ac8a5d`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L81-L87) — lines `81–87`; excerpt `sha256:0ae78181a0498fd68e97a7b3ddfe1c78c6648940b593286ad413ac1138ac8a5d`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1022](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1022-L1022)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1290](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1290-L1290), [cite at paper/reasoning-parts/erdos1041/core.tex:1247](../../paper/reasoning-parts/erdos1041/core.tex#L1247-L1247)

<a id="source-eremenko-yuditskii-2012-comb-functions"></a>

### [Comb functions](https://arxiv.org/abs/1109.1464)

- Source id: `eremenko\_yuditskii\_2012\_comb\_functions`
- Author or public identity: A. Eremenko, P. Yuditskii
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Vocabulary and classical characterisation for the sharp collinear theorem: the gap maxima of a real-rooted polynomial with distinct zeros are the moduli of its critical sequence, and the comparison polynomial is the Chebyshev polynomial of an interval. The collinear proof uses only the alternation count and does not depend on Theorem 1.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Section 1 (arXiv v1 pp. 1-2) recalls the equioscillation characterisation of the monic polynomial of least deviation from zero on a compact subset of the real line; Theorem 1 (p. 5) shows that a real polynomial with real zeros is determined by its critical sequence up to a real affine change of variable z -\> az+b with a \> 0.](https://arxiv.org/abs/1109.1464)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1395-L1398) — lines `1395–1398`; excerpt `sha256:6abfd14cec2de6bd2019a8373801459e194451fa2ebafb5358d867cac3527340`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2941-L2946) — lines `2941–2946`; excerpt `sha256:03a47da1118d39631b3bbe345863677d9b0ce95cfb47631e2a424fe4d9b29d98`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L76-L81) — lines `76–81`; excerpt `sha256:03a47da1118d39631b3bbe345863677d9b0ce95cfb47631e2a424fe4d9b29d98`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1008](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1008-L1008), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1016](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1016-L1016)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1276](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1276-L1276), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1284](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1284-L1284), [cite at paper/reasoning-parts/erdos1041/core.tex:1233](../../paper/reasoning-parts/erdos1041/core.tex#L1233-L1233), [cite at paper/reasoning-parts/erdos1041/core.tex:1241](../../paper/reasoning-parts/erdos1041/core.tex#L1241-L1241)

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

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L270-L288) — lines `270–288`; excerpt `sha256:12a5b1f7563cefb7d10a26be861ae84e01bcba9b150a9655b9c3e2aabd93108b`

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

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L362-L426) — lines `362–426`; excerpt `sha256:4db989ccba90a32a255fe9bd93b65967fa391e1cf1c9974d07cfa64d5d0e92c8`

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

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L342-L360) — lines `342–360`; excerpt `sha256:7ff63cde13f349a5f42b41b5bbc6f9160c468a7a7ae2a92d8cd54b5d8afc85d6`

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

- [research/adapters/FormalConjecturesVariants.lean](../../research/adapters/FormalConjecturesVariants.lean#L471-L504) — lines `471–504`; excerpt `sha256:5bd0c8f1316751bbcc0c8dd95f60449cc49b395f5984c254b1db288a24fda020`

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

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L748-L752) — lines `748–752`; excerpt `sha256:9d2bb989c3eea3bf5a65a49fe1b886c24712e515ff22e273c2459b9c97c8d2f4`
- [paper/reasoning-parts/erdos257/a257\_p4.tex](../../paper/reasoning-parts/erdos257/a257_p4.tex#L99-L103) — lines `99–103`; excerpt `sha256:996ee6061c4d2f1caacadecdf0a82739f2582f6ac78ff925e44fc67fa43f8039`

<a id="source-proposed-direct-329775d58148a9"></a>

### [Refinements of Erdős's irrationality criterion for certain sparse infinite series](https://arxiv.org/abs/2601.20743)

- Source id: `proposed-direct-329775d58148a9`
- Author or public identity: Hajime Kaneko, Yuta Suzuki, Yohei Tachiya
- Kind: `literature`
- Problems: #257
- Relationship and boundary: Sparse power-series irrationality criteria for Pisot or Salem bases (Theorems 1-3), with arithmetic-function applications. The #257 note cites the averaged-tail quantity R\_c of (1.7) and Lemmas 1-2 beside its weighted-support theorem as context for averaging the displacement. Divisor-incidence coefficients of Mersenne-Lambert subseries fail the counting hypotheses of Theorems 1 and 3, so the criteria do not apply to those subseries.
- Source verification: `existing\_source\_closure` — The complete bound preprint was read and its pages were checked as images; the source closure records the locators and the counting-hypothesis boundary. This does not certify the paper's mathematics or imply that the note adopts its criteria.
- Local mapping: `not recorded`

Exact source locations:

- [Primary public record metadata verified 2026-09-12.](https://arxiv.org/abs/2601.20743)
- [- \*\*Bound publication identity:\*\* arXiv:2601.20743v1, dated 28 January 2026;](https://arxiv.org/abs/2601.20743)
- [- \*\*Averaged-tail mechanism:\*\* PDF p. 3, equation (1.7), defines](https://arxiv.org/abs/2601.20743)
- [- \*\*Counting hypotheses:\*\* condition (iii) of Theorem 1 (PDF p. 3) and](https://arxiv.org/abs/2601.20743)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L702-L705) — lines `702–705`; excerpt `sha256:8f3549258b94df73f469cb3b206cbbe3516d68f335e2b4a0e92a0ddcc6d38873`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L335-L359) — lines `335–359`; excerpt `sha256:373ff532af045159e1209a05fd97ba3a06545a57c2068e68cd24a26020a24f9d`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1225-L1234) — lines `1225–1234`; excerpt `sha256:e1c9a7e977d277168a7f609b18fd5aa7bb5def6e444adb9dd43868cc0b0e5692`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L295-L319) — lines `295–319`; excerpt `sha256:6bb6ee3e89f79566028b13a30d09ae06a616eb86ecadf1ff44369448a83b8514`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:346](../../paper/257/erdos-257-mersenne-support-subseries.tex#L346-L346)

<a id="source-proposed-direct-4e797194f74404"></a>

### [Shifted multiplicative-function correlation program named in the #249 reasoning surface](https://arxiv.org/abs/1501.04585)

- Source id: `proposed-direct-4e797194f74404`
- Author or public identity: Kaisa Matomäki, Maksym Radziwiłł, Terence Tao, Joni Teräväinen
- Kind: `literature`
- Problems: #249
- Relationship and boundary: This is a public program/context row because the manuscript collectively names three strands rather than asserting one theorem from one paper. The linked primary records identify the named strands: Matomäki–Radziwiłł short intervals, Tao two-point logarithmic Chowla/Elliott, and Tao–Teräväinen odd-order logarithmic Chowla. The manuscript says these results are averaged and do not supply its pointwise input.
- Source verification: `source\_verified` — Public source identity or public contribution text is verified. The stated relation and exact local anchors delimit the use; this does not assert a complete source-to-Lean theorem correspondence.
- Local mapping: `named\_literature\_program\_context`

Exact source locations:

- [Primary public publication record.](https://arxiv.org/abs/1501.04585)

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos249/a249\_invent.tex](../../paper/reasoning-parts/erdos249/a249_invent.tex#L479-L485) — lines `479–485`; excerpt `sha256:9e683237fedf08d11bbc435e64eeb263c3da96068774e42d013a33a4b4cdbe11`

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

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L34-L38) — lines `34–38`; excerpt `sha256:850bf3a64a45b189addbc2d7e6f7754eb1006b5529545b7d23aac5b368ebebe4`

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

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos257/a257\_invent.tex](../../paper/reasoning-parts/erdos257/a257_invent.tex#L155-L162) — lines `155–162`; excerpt `sha256:d92e29e7fde1bd64198327956552f97aa3ff9a67224ded85599054e06067dc56`

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

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos257/a257\_invent.tex](../../paper/reasoning-parts/erdos257/a257_invent.tex#L155-L162) — lines `155–162`; excerpt `sha256:d92e29e7fde1bd64198327956552f97aa3ff9a67224ded85599054e06067dc56`

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

- [paper/reasoning-parts/erdos249/a249\_invent.tex](../../paper/reasoning-parts/erdos249/a249_invent.tex#L315-L322) — lines `315–322`; excerpt `sha256:299874356a6252b7ec4af63715f9d51137728d402b90e74bc5eeb6da5a48dfa0`

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

- [paper/reasoning-parts/erdos249/a249\_invent.tex](../../paper/reasoning-parts/erdos249/a249_invent.tex#L672-L681) — lines `672–681`; excerpt `sha256:36a135afa53fe987590cdeffcc932da60353e1a03efcd7806951d327fd1a463a`

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

Public implementation or evidence coordinates:

- [paper/reasoning-parts/erdos249/a249\_invent.tex](../../paper/reasoning-parts/erdos249/a249_invent.tex#L545-L550) — lines `545–550`; excerpt `sha256:4fb9437cb2f581a6853ea9924d7643654a1eed060ac856c3676124e93f2fdf2e`

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

<a id="source-source-06457731c60720"></a>

### [The Prime Number Theorem](https://doi.org/10.1017/CBO9780511618314.008)

- Source id: `source-06457731c60720`
- Author or public identity: H. L. Montgomery, R. C. Vaughan
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2183-L2189) — lines `2183–2189`; excerpt `sha256:e06e613c21fdb907f3ad19771974b64f69e53a3900727d6b40a487de0e2c0433`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L42-L48) — lines `42–48`; excerpt `sha256:e06e613c21fdb907f3ad19771974b64f69e53a3900727d6b40a487de0e2c0433`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L196-L196) — lines `196–196`; excerpt `sha256:b6fbd16fb60c4a2591194058b1abd9288fc465ff3a874a4fd66f5f719a7a2ad4`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:247](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L247-L247), [cite at paper/reasoning-parts/erdos269/core.tex:196](../../paper/reasoning-parts/erdos269/core.tex#L196-L196)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L674-L679) — lines `674–679`; excerpt `sha256:361c5b2fa1f2778906e262b1d0e58a126d4e7d28ea4d10e58c4b3607ef4706e2`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:486](../../paper/systems/cold-clone-to-proof-receipt.tex#L486-L486)

<a id="source-source-0a6b8c93371570"></a>

### [A problem about Mahler functions](https://arxiv.org/abs/1303.2019)

- Source id: `source-0a6b8c93371570`
- Author or public identity: B. Adamczewski, J. P. Bell
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3146-L3152) — lines `3146–3152`; excerpt `sha256:325fd9971f39e31720c2be3d5a0c3fb9c93d1d5d268e57ecfed14f0e6cab25f6`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L63-L69) — lines `63–69`; excerpt `sha256:325fd9971f39e31720c2be3d5a0c3fb9c93d1d5d268e57ecfed14f0e6cab25f6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2747-L2747) — lines `2747–2747`; excerpt `sha256:ce3fd0079ee84f22a2d17abef53c20ec753607f81e4a199f0f77f697689b6b07`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2772](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2772-L2772), [cite at paper/reasoning-parts/erdos1049/core.tex:2747](../../paper/reasoning-parts/erdos1049/core.tex#L2747-L2747)

<a id="source-source-0aca0e5e4e03c0"></a>

### [Multiplicative Number Theory I: Classical Theory](https://doi.org/10.1017/CBO9780511618314)

- Source id: `source-0aca0e5e4e03c0`
- Author or public identity: H. L. Montgomery, R. C. Vaughan
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1499-L1507) — lines `1499–1507`; excerpt `sha256:ac57c0809e1042c1d45f3cc3c27a707b685b9c0c049f33100d2b980ee40499f7`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2081-L2082) — lines `2081–2082`; excerpt `sha256:c44e132030013c5f8edb13f0a69f4bb3d45e4978267d1ce5a72c5a0a5fca04fb`
- [paper/reasoning-parts/erdos251/extended\_record.tex](../../paper/reasoning-parts/erdos251/extended_record.tex#L123-L124) — lines `123–124`; excerpt `sha256:c44e132030013c5f8edb13f0a69f4bb3d45e4978267d1ce5a72c5a0a5fca04fb`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2432-L2440) — lines `2432–2440`; excerpt `sha256:4b01eff339c66e66b98dc697ebe2c82744ff4c603509c6dbdc134ff471ceb523`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L75-L83) — lines `75–83`; excerpt `sha256:4b01eff339c66e66b98dc697ebe2c82744ff4c603509c6dbdc134ff471ceb523`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2082](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2082-L2082), [cite at paper/reasoning-parts/erdos251/extended\_record.tex:124](../../paper/reasoning-parts/erdos251/extended_record.tex#L124-L124)

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
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1576-L1581) — lines `1576–1581`; excerpt `sha256:6ab1870a7b04b9f3cc30d59640dcc05a0b6fcd49f9ea44245ecb129aba0f4c4e`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:979](../../paper/systems/claim-faithful-publication-systems-paper.tex#L979-L979), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1312](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1312-L1312)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:663](../../paper/systems/open-source-mathematics-strategy.tex#L663-L663), [cite at paper/systems/open-source-mathematics-strategy.tex:900](../../paper/systems/open-source-mathematics-strategy.tex#L900-L900)

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
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L754-L758) — lines `754–758`; excerpt `sha256:b7df2e208b87bda4ef0e65b64ed7fc248f55353da466b2fb43ae947c666e4bdd`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2250](../../paper/archive/erdos249-257-main-paper.tex#L2250-L2250)

<a id="source-source-0e12f93aeac487"></a>

### [The maximal length of the Erdős–Herzog–Piranian lemniscate in high degree](https://arxiv.org/abs/2512.12455)

- Source id: `source-0e12f93aeac487`
- Author or public identity: T. Tao
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: High-degree resolution of the EHP level-lemniscate conjecture; contextual background rather than a shortest-between-zeros path theorem.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Main Theorem 1 proves successively sharper bounds and, in part (iv), the EHP extremal statement for all sufficiently large degrees, with equality characterization.](https://arxiv.org/abs/2512.12455)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2936-L2941) — lines `2936–2941`; excerpt `sha256:0fa51554a857863d50716dc6f4bcaadefc3df358e5ad21588d943a80bdcb25fa`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L71-L76) — lines `71–76`; excerpt `sha256:0fa51554a857863d50716dc6f4bcaadefc3df358e5ad21588d943a80bdcb25fa`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L854-L854) — lines `854–854`; excerpt `sha256:4473567ae963215b952aad3e5d3b8bd450d7fbc046a6e9a84ca5c904ef3c7155`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:897](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L897-L897), [cite at paper/reasoning-parts/erdos1041/core.tex:854](../../paper/reasoning-parts/erdos1041/core.tex#L854-L854)

<a id="source-source-0ec7ca07508557"></a>

### [On the Erdős problem #251](https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf)

- Source id: `source-0ec7ca07508557`
- Author or public identity: ChatGPT 5.4 Pro (orchestrated by V. Kovač)
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1526-L1531) — lines `1526–1531`; excerpt `sha256:900a91b50c25e813d52e226b434f7ed63de8a76a672159d0674e6751533d8f99`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2477-L2483) — lines `2477–2483`; excerpt `sha256:34802f92918c67937f7bcf181bac1f5ca71c9e6528656eafd85d2d4096117c22`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L110-L110) — lines `110–110`; excerpt `sha256:87e96b7013e341a9a7174d67487c068725ab753e218167435945e185e962236f`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L120-L126) — lines `120–126`; excerpt `sha256:34802f92918c67937f7bcf181bac1f5ca71c9e6528656eafd85d2d4096117c22`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L160-L160) — lines `160–160`; excerpt `sha256:f7242784a3fe38e5b822eed59c333e70c230f15323ae162907c378ac59f69c51`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1472-L1472) — lines `1472–1472`; excerpt `sha256:c4bf31aa7c0ed75968bdd75d3778b733e0689dd379b9cc4560880451c0643921`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:238](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L238-L238), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:1525](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1525-L1525)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:194](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L194-L194), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1507](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1507-L1507), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2467](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2467-L2467), [cite at paper/reasoning-parts/erdos251/back.tex:110](../../paper/reasoning-parts/erdos251/back.tex#L110-L110), [cite at paper/reasoning-parts/erdos251/core.tex:160](../../paper/reasoning-parts/erdos251/core.tex#L160-L160), [cite at paper/reasoning-parts/erdos251/core.tex:1473](../../paper/reasoning-parts/erdos251/core.tex#L1473-L1473)

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
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L692-L700) — lines `692–700`; excerpt `sha256:5bf648df15310f8ec341bdeaddd6e394ffc24bab4a40f501ad5003ff02989a26`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:5071](../../paper/archive/erdos249-257-main-paper.tex#L5071-L5071), [cite at paper/archive/erdos249-257-main-paper.tex:5111](../../paper/archive/erdos249-257-main-paper.tex#L5111-L5111)

<a id="source-source-0f1a3708d62674"></a>

### [Irrationality of rapidly converging series: a problem of Erdős and Graham](https://arxiv.org/abs/2601.21442v3)

- Source id: `source-0f1a3708d62674`
- Author or public identity: K. Barreto, J. Kang, S.-h. Kim, V. Kovač, S. Zhang
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1907-L1913) — lines `1907–1913`; excerpt `sha256:cd12daefd19d6365143bf154718d94864fa97ed1c4e4392cd67fea595e1b7ae2`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L53-L59) — lines `53–59`; excerpt `sha256:cd12daefd19d6365143bf154718d94864fa97ed1c4e4392cd67fea595e1b7ae2`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1117-L1117) — lines `1117–1117`; excerpt `sha256:49d761ca3134300ac4615e2d01c5d9a85137ba548b704fc42ad9a411b916ad9e`
- [paper/reasoning-parts/erdos68/extended\_record.tex](../../paper/reasoning-parts/erdos68/extended_record.tex#L81-L81) — lines `81–81`; excerpt `sha256:926abf3e5f2b7941c4e0ffe11315010181da19788043d3d9afb2c35e7d37dacc`
- [paper/reasoning-parts/erdos68/extended\_record.tex](../../paper/reasoning-parts/erdos68/extended_record.tex#L85-L85) — lines `85–85`; excerpt `sha256:2716abf1989988c15fd0d75c4836cdf31e04a69642a0acb06cff6c365904e39c`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1153](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1153-L1153), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1425](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1425-L1425), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1429](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1429-L1429), [cite at paper/reasoning-parts/erdos68/core.tex:1117](../../paper/reasoning-parts/erdos68/core.tex#L1117-L1117), [cite at paper/reasoning-parts/erdos68/extended\_record.tex:81](../../paper/reasoning-parts/erdos68/extended_record.tex#L81-L81), [cite at paper/reasoning-parts/erdos68/extended\_record.tex:85](../../paper/reasoning-parts/erdos68/extended_record.tex#L85-L85)

<a id="source-source-0f61ad0796acdf"></a>

### [Answer to An infinite sum based on the mod-parity of Euler's totient function](https://math.stackexchange.com/a/1211557)

- Source id: `source-0f61ad0796acdf`
- Author or public identity: Erick Wong
- Kind: `website\_contribution`
- Problems: #249
- Relationship and boundary: Direct posted proof that the base-k expansion with nth digit phi(n) mod k is irrational for every integer k\>2. The digit modulus equals the denominator base. This does not prove irrationality of the full binary totient series Theta\_2 or a least-prime-factor theorem.
- Source verification: `source\_verified` — Primary accepted answer and public author identity read and checked. This is a public web contribution; no separate publication or broader priority claim is asserted.
- Local mapping: `not recorded`

Exact source locations:

- [Accepted answer, 29 March 2015: opening statement for every integer k\>2; paragraphs 2–3 establish infinitely many zero and nonzero base-k digits; paragraphs 4–5 give the eventual-periodicity contradiction.](https://math.stackexchange.com/a/1211557)

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L829-L833) — lines `829–833`; excerpt `sha256:c051a6fd92366505b0880e9bef1e556ed2611ec3731d443530ec4ab540b599a1`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:583](../../paper/249/erdos-249-binary-totient-series.tex#L583-L583)

<a id="source-source-10545f868b3e88"></a>

### [Old and New Problems and Results in Combinatorial Number Theory](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf)

- Source id: `source-10545f868b3e88`
- Author or public identity: P. Erdős, R. L. Graham
- Kind: `literature`
- Problems: #243, #249, #251, #257, #269
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
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

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5315-L5318) — lines `5315–5318`; excerpt `sha256:89ad0eb6d9dac773cb478c008d67b4ac6ad8b50cdf587f23feda6a8d1825acf6`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L884-L888) — lines `884–888`; excerpt `sha256:df0e63df25873358641ed4070061c15e5f66adb3d2707f788d4aba4c941addb4`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3011-L3015) — lines `3011–3015`; excerpt `sha256:df0e63df25873358641ed4070061c15e5f66adb3d2707f788d4aba4c941addb4`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L833-L836) — lines `833–836`; excerpt `sha256:3451dd866e80517dacca63cfc17bb749148b4d10abfd461e6010a2773dc28e22`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1444-L1448) — lines `1444–1448`; excerpt `sha256:77deb132053702c64190a6a7499fe28db4f1a53a36a8f410c0069a7178993e57`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2371-L2375) — lines `2371–2375`; excerpt `sha256:77deb132053702c64190a6a7499fe28db4f1a53a36a8f410c0069a7178993e57`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2146-L2152) — lines `2146–2152`; excerpt `sha256:9b9152e1a2b6436e5ae1334e4d32ed81c874388f64e71686751398f2f877fb38`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L885-L891) — lines `885–891`; excerpt `sha256:9b9152e1a2b6436e5ae1334e4d32ed81c874388f64e71686751398f2f877fb38`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1551-L1554) — lines `1551–1554`; excerpt `sha256:851267bb83e0426f3dc46e58eca0ec223ffefbf930eeba52eeeccf56d165f807`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L17-L21) — lines `17–21`; excerpt `sha256:df0e63df25873358641ed4070061c15e5f66adb3d2707f788d4aba4c941addb4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L51-L51) — lines `51–51`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L14-L18) — lines `14–18`; excerpt `sha256:77deb132053702c64190a6a7499fe28db4f1a53a36a8f410c0069a7178993e57`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L74-L74) — lines `74–74`; excerpt `sha256:4c3c5dd1c1ebb3509e07a046edfac9dffdc9e0e6b050cba5793b0f60efd13cf3`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L5-L11) — lines `5–11`; excerpt `sha256:9b9152e1a2b6436e5ae1334e4d32ed81c874388f64e71686751398f2f877fb38`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L53-L53) — lines `53–53`; excerpt `sha256:d0733b0ee5c6accbfe80049f5f21794ad925c50ddd26f96b9cfd62ade1f3a3b8`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:993](../../paper/systems/claim-faithful-publication-systems-paper.tex#L993-L993)
- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:587](../../paper/249/erdos-249-binary-totient-series.tex#L587-L587)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:233](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L233-L233)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:66](../../paper/269/erdos-269-three-prime-running-lcm.tex#L66-L66)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:93](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L93-L93), [cite at paper/reasoning-parts/erdos243/core.tex:51](../../paper/reasoning-parts/erdos243/core.tex#L51-L51)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:193](../../paper/archive/erdos249-257-main-paper.tex#L193-L193), [cite at paper/archive/erdos249-257-main-paper.tex:194](../../paper/archive/erdos249-257-main-paper.tex#L194-L194)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:108](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L108-L108), [cite at paper/reasoning-parts/erdos251/core.tex:74](../../paper/reasoning-parts/erdos251/core.tex#L74-L74)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:104](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L104-L104), [cite at paper/reasoning-parts/erdos269/core.tex:53](../../paper/reasoning-parts/erdos269/core.tex#L53-L53)

<a id="source-source-11b46a0435368f"></a>

### [Simultaneous inequalities among values of the Euler phi-function](https://arxiv.org/abs/math/0603053)

- Source id: `source-11b46a0435368f`
- Author or public identity: Greg Martin
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Attribution of the positive-lower-density ratio-comparison input for nonproportional affine forms to Martin's Theorem 1. - The symmetry-based availability of strict orderings and the source's φ-to-σ transfer in Corollary 4. - The source identity, version, exact public routes, and the locators above for the prior-art comparison. Explicit attribution section names Greg Martin, title, arXiv identifier, and Theorem 1. It states Martin’s result is stronger and subsumes the local independence conclusion; the local file contributes a self-contained elementary proof and explicitly disclaims originality. The theorem docstring explicitly calls the result a corollary of Martin, arXiv:math/0603053, Theorem 1. Explicit source boundary: Martin is identified as the external mathematical comparison/input, while no theorem of Martin is formalized or assumed as an axiom.
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

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L826-L829) — lines `826–829`; excerpt `sha256:3b0475dd33e7a1ea2d089116b3042b48e0583ce9c65fa9d5d35b7bfae3c0d8a6`
- [lean/Erdos249257/AllBaseTotientKernel.lean](../../lean/Erdos249257/AllBaseTotientKernel.lean#L4-L61) — lines `4–61`; excerpt `sha256:a7583f78b57fbb25305024044671d8303e0dfd61da003f0de23f3c82ca558fb4`
- [lean/Erdos249257/AllBaseTotientKernel.lean](../../lean/Erdos249257/AllBaseTotientKernel.lean#L642-L644) — lines `642–644`; excerpt `sha256:f2847f43a004d01715e61f5510732df2e0014e197cb1796803035180a98f88f6`
- [lean/Erdos249257/TotientKernelConditional.lean](../../lean/Erdos249257/TotientKernelConditional.lean#L5-L18) — lines `5–18`; excerpt `sha256:bb1cbd9adcabf879040179a1dda4145da0903770eb95510584365a88131340ba`
- [paper/reasoning-parts/erdos249/a249\_p4.tex](../../paper/reasoning-parts/erdos249/a249_p4.tex#L526-L526) — lines `526–526`; excerpt `sha256:2dbd7f0d45fe7526bd594df5c9ee18003963911c8ad097aea117921cb42671fc`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:580](../../paper/249/erdos-249-binary-totient-series.tex#L580-L580)

<a id="source-source-120bebce1ffe8c"></a>

### [Heine's basic transform and a permutation group for q-harmonic series](https://geodesic.mathdoc.fr/articles/10.4064/aa111-2-4/)

- Source id: `source-120bebce1ffe8c`
- Author or public identity: W. Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Primary source of the linear forms, Lemma 7 with display (23), the direction (14, 12, 14; 27), the thirteen intervals and the constants C\_1 and C\_0 used by the #1049 rational-base theorem. The tracked source closure records the printed locators, the integer-base hypothesis of every stated result, and the attribution ceiling; the rational specialisation is argued in the notes. Primary metadata titles it “Heine’s basic transform and a permutation group for q-harmonic series”; the manuscript’s shorthand “erratum” should not replace that publication identity. The comments explicitly identify Zudilin’s 2004 Heine/q-harmonic paper, printed formulas, lemmas, section, and theorem used by the rational-base contour comparison. Analytic steps are expressly not formalized. Adjacent/source-independent arithmetic comparison to the Heine–Zudilin construction; the comments do not claim the analytic source theorem is formalized.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Reading status: complete publisher PDF read from rendered pages; printed pp. 153–164 are PDF pp. 1–12.](https://doi.org/10.4064/aa111-2-4)
- [Lemma 7, display (23), printed p. 161: the polynomial inclusion used before the integer evaluation (24).](https://doi.org/10.4064/aa111-2-4)
- [Section 5, (24)–(26), printed pp. 161–162: direction (14, 12, 14; 27), C\_1 = 545.5, C\_0 = 221.30008816..., the thirteen intervals, and Theorem 1's bound.](https://doi.org/10.4064/aa111-2-4)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L967-L973) — lines `967–973`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3115-L3121) — lines `3115–3121`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L32-L38) — lines `32–38`; excerpt `sha256:3d622530e87391575051f4e80e3d30e5081ea41b34fdf3c95cb324b83e6b3728`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L62-L62) — lines `62–62`; excerpt `sha256:db93d2af68dcea339033ff0bf8e8df04e6b481b0765913610ddb8209a0f70abe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L213-L213) — lines `213–213`; excerpt `sha256:6f601bf1d1572f94d23aa1f1693395b6dcd7a894654bec48dd6afce44897ce6b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L252-L252) — lines `252–252`; excerpt `sha256:578cf36c905631e1b76289ea892e06b4546c4ef63f52f23ebeacfbaca6933a5b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L431-L431) — lines `431–431`; excerpt `sha256:37cd72a6efc5eb3acb6952cb0f3d42aa44ead04857cca12a24a5735e373cca79`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L455-L455) — lines `455–455`; excerpt `sha256:db231b20665b729f8c7ec2e7f89904ad755b2b3a9ecbfd689a4ced32a99224bb`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L456-L456) — lines `456–456`; excerpt `sha256:a0396c7789ce596deda34f77b100163452fc9398ef65e1308aaa35c78a672fc0`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L466-L466) — lines `466–466`; excerpt `sha256:e6e2039e5a33ba1aaa7cdbfe71df15de66d095edca131fb33ce483539843af7e`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L494-L494) — lines `494–494`; excerpt `sha256:c64b3006eebab2c8cd1bcd1534baa567d51d8bd516b0efb846b8857b40d5d892`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L523-L523) — lines `523–523`; excerpt `sha256:b56e99939457c23e3fa356d1919c8071199573269707da69a7096e7eccdf9304`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L534-L534) — lines `534–534`; excerpt `sha256:306ea250ac23a5042f85be2322d4da1fd831b9b0b09106fd47e55b4f38fe462d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L565-L565) — lines `565–565`; excerpt `sha256:08831681946cb587743ea5652cd44c5d40c121c26979ec401714b5e612a28994`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L892-L892) — lines `892–892`; excerpt `sha256:951d1c71b8e0224f9dfbbe0a3c79c29e8f205d77b569dad902d45af2ca584d25`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L925-L925) — lines `925–925`; excerpt `sha256:32c9e33a6ee7b0d3f3571013f0b5b112589809cbdc59d45b9d9d1a0c364a7b48`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L938-L938) — lines `938–938`; excerpt `sha256:9f19f0b630bd0451eabe2e109df547555b2111948d220cc2c8516ce815b2fed3`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1172-L1172) — lines `1172–1172`; excerpt `sha256:3066de01b9b99a44fe58c88624ccd5b57084b1de5c0e2c2f4799ed6d9d1835bf`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1215-L1215) — lines `1215–1215`; excerpt `sha256:523ececf7f27097e12aac8c6cc4eb679b4311650483bcb0d9697ff8fca228584`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1692-L1692) — lines `1692–1692`; excerpt `sha256:60bc260e6180f4e4c28004912f1df4f348d7d287ce7e7a48d57e26f4120096fa`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1852-L1852) — lines `1852–1852`; excerpt `sha256:0a87fd3031fa5ae394fff12555a14f74004112a45b47b8940ea53deec9e622ec`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2118-L2118) — lines `2118–2118`; excerpt `sha256:e445fa0250477e2d9dfd5398015bc17c9a86914dcf814404ec0df31a5c949f0a`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L748-L752) — lines `748–752`; excerpt `sha256:9d2bb989c3eea3bf5a65a49fe1b886c24712e515ff22e273c2459b9c97c8d2f4`
- [paper/reasoning-parts/erdos257/a257\_p4.tex](../../paper/reasoning-parts/erdos257/a257_p4.tex#L102-L103) — lines `102–103`; excerpt `sha256:1a3428a80495613866e86cff9767044e447247134c53b75bb1100483627d9e2e`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L8-L36) — lines `8–36`; excerpt `sha256:580a0329d38f93ac21807ae3e4b5576bc7cc0a60f32dc890b169224bff93a983`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L121-L143) — lines `121–143`; excerpt `sha256:9cbb2521fc20ab9b5f2b1ef19d400d7a4706ab42e437b60f3d445f245666ebab`
- [lean/ErdosProblems/Erdos1049/RationalBaseContour.lean](../../lean/ErdosProblems/Erdos1049/RationalBaseContour.lean#L312-L317) — lines `312–317`; excerpt `sha256:9d8f3b2b1f69665003c2e2e1011aa3ab2153e1279df369928b397383f2c62c70`
- [lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean](../../lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L8-L15) — lines `8–15`; excerpt `sha256:944f0e0e804396ce17b086bb0755d7c33ca82e608e624be2a2542fcd18124e82`
- [lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean](../../lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L72-L79) — lines `72–79`; excerpt `sha256:519814e5b5744e92c8a9dc9ac2c0c0fd009c2f4c5e71df7e3e2af9a3034f730a`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:65](../../paper/1049/erdos-1049-rational-base-lambert.tex#L65-L65), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:126](../../paper/1049/erdos-1049-rational-base-lambert.tex#L126-L126), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:154](../../paper/1049/erdos-1049-rational-base-lambert.tex#L154-L154), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:160](../../paper/1049/erdos-1049-rational-base-lambert.tex#L160-L160), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:163](../../paper/1049/erdos-1049-rational-base-lambert.tex#L163-L163), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:308](../../paper/1049/erdos-1049-rational-base-lambert.tex#L308-L308), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:371](../../paper/1049/erdos-1049-rational-base-lambert.tex#L371-L371), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:373](../../paper/1049/erdos-1049-rational-base-lambert.tex#L373-L373)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:238](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L238-L238), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:277](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L277-L277), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:413](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L413-L413), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:456](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L456-L456), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:480](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L480-L480), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:481](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L481-L481), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:491](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L491-L491), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:519](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L519-L519), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:548](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L548-L548), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:559](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L559-L559), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:590](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L590-L590), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:917](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L917-L917), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:950](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L950-L950), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:963](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L963-L963), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1197](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1197-L1197), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1240](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1240-L1240), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1717](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1717-L1717), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1877](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1877-L1877), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2143](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2143-L2143), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:3145](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3145-L3145), [cite at paper/reasoning-parts/erdos1049/back.tex:62](../../paper/reasoning-parts/erdos1049/back.tex#L62-L62), [cite at paper/reasoning-parts/erdos1049/core.tex:213](../../paper/reasoning-parts/erdos1049/core.tex#L213-L213), [cite at paper/reasoning-parts/erdos1049/core.tex:252](../../paper/reasoning-parts/erdos1049/core.tex#L252-L252), [cite at paper/reasoning-parts/erdos1049/core.tex:388](../../paper/reasoning-parts/erdos1049/core.tex#L388-L388), [cite at paper/reasoning-parts/erdos1049/core.tex:431](../../paper/reasoning-parts/erdos1049/core.tex#L431-L431), [cite at paper/reasoning-parts/erdos1049/core.tex:455](../../paper/reasoning-parts/erdos1049/core.tex#L455-L455), [cite at paper/reasoning-parts/erdos1049/core.tex:456](../../paper/reasoning-parts/erdos1049/core.tex#L456-L456), [cite at paper/reasoning-parts/erdos1049/core.tex:466](../../paper/reasoning-parts/erdos1049/core.tex#L466-L466), [cite at paper/reasoning-parts/erdos1049/core.tex:494](../../paper/reasoning-parts/erdos1049/core.tex#L494-L494), [cite at paper/reasoning-parts/erdos1049/core.tex:523](../../paper/reasoning-parts/erdos1049/core.tex#L523-L523), [cite at paper/reasoning-parts/erdos1049/core.tex:534](../../paper/reasoning-parts/erdos1049/core.tex#L534-L534), [cite at paper/reasoning-parts/erdos1049/core.tex:565](../../paper/reasoning-parts/erdos1049/core.tex#L565-L565), [cite at paper/reasoning-parts/erdos1049/core.tex:892](../../paper/reasoning-parts/erdos1049/core.tex#L892-L892), [cite at paper/reasoning-parts/erdos1049/core.tex:925](../../paper/reasoning-parts/erdos1049/core.tex#L925-L925), [cite at paper/reasoning-parts/erdos1049/core.tex:938](../../paper/reasoning-parts/erdos1049/core.tex#L938-L938), [cite at paper/reasoning-parts/erdos1049/core.tex:1172](../../paper/reasoning-parts/erdos1049/core.tex#L1172-L1172), [cite at paper/reasoning-parts/erdos1049/core.tex:1215](../../paper/reasoning-parts/erdos1049/core.tex#L1215-L1215), [cite at paper/reasoning-parts/erdos1049/core.tex:1692](../../paper/reasoning-parts/erdos1049/core.tex#L1692-L1692), [cite at paper/reasoning-parts/erdos1049/core.tex:1852](../../paper/reasoning-parts/erdos1049/core.tex#L1852-L1852), [cite at paper/reasoning-parts/erdos1049/core.tex:2118](../../paper/reasoning-parts/erdos1049/core.tex#L2118-L2118)

<a id="source-source-169c3d67838965"></a>

### [À propos de la série ∑\_{n≥1} x^n/(q^n−1)](https://numdam.org/item/JTNB_1996__8_1_173_0.pdf)

- Source id: `source-169c3d67838965`
- Author or public identity: D. Duverney
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3132-L3139) — lines `3132–3139`; excerpt `sha256:2e85c59828644ad3c8fb345c8b459c4f9c86946c02a53b466028be600adf3dcf`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L49-L56) — lines `49–56`; excerpt `sha256:2e85c59828644ad3c8fb345c8b459c4f9c86946c02a53b466028be600adf3dcf`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L247-L247) — lines `247–247`; excerpt `sha256:49510e1a864a805185edeb7b4d7df442d89a7ba8c9b353c4e285195caf16aa5e`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L920-L920) — lines `920–920`; excerpt `sha256:fbce7f2db65bdd8d9f109301fb1bc86d09291626cd9714baf8b44fb0defea1c4`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:272](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L272-L272), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:945](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L945-L945), [cite at paper/reasoning-parts/erdos1049/core.tex:247](../../paper/reasoning-parts/erdos1049/core.tex#L247-L247), [cite at paper/reasoning-parts/erdos1049/core.tex:920](../../paper/reasoning-parts/erdos1049/core.tex#L920-L920)

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

Public implementation or evidence coordinates:

- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3045-L3051) — lines `3045–3051`; excerpt `sha256:631c8248ffd17035b17d23474e85ff6ce39cda1d8357ecb3ddcbd2ad433513b3`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L51-L57) — lines `51–57`; excerpt `sha256:631c8248ffd17035b17d23474e85ff6ce39cda1d8357ecb3ddcbd2ad433513b3`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L689-L689) — lines `689–689`; excerpt `sha256:adfa536049be0e74065800037ce0ba5a0d022d83f1cf5dfdd9d4c0dda34e205f`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L731-L731) — lines `731–731`; excerpt `sha256:adfa536049be0e74065800037ce0ba5a0d022d83f1cf5dfdd9d4c0dda34e205f`

Paper citation usages:

- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:731](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L731-L731), [cite at paper/reasoning-parts/erdos243/core.tex:689](../../paper/reasoning-parts/erdos243/core.tex#L689-L689)

<a id="source-source-176d35cb60b651"></a>

### [On a permutation group related to ζ(2)](https://geodesic.mathdoc.fr/articles/10.4064/aa-77-1-23-56/)

- Source id: `source-176d35cb60b651`
- Author or public identity: G. Rhin, C. Viola
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3152-L3157) — lines `3152–3157`; excerpt `sha256:b75b67635c18f80de0c876644a0d855886ffebd57e78291c56d2b76c6f5fe91f`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L69-L74) — lines `69–74`; excerpt `sha256:b75b67635c18f80de0c876644a0d855886ffebd57e78291c56d2b76c6f5fe91f`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L216-L216) — lines `216–216`; excerpt `sha256:8adebc999545c9df48229cb147487a72adb2aada21714a86818b1e4081a89c83`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1851-L1851) — lines `1851–1851`; excerpt `sha256:5c49ddfe53b2fd3db9c587f08d6f0191b7c956806bdaaf388250ce58e1b8f4dd`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:241](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L241-L241), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1876](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1876-L1876), [cite at paper/reasoning-parts/erdos1049/core.tex:216](../../paper/reasoning-parts/erdos1049/core.tex#L216-L216), [cite at paper/reasoning-parts/erdos1049/core.tex:1851](../../paper/reasoning-parts/erdos1049/core.tex#L1851-L1851)

<a id="source-source-1b9324cc5f4641"></a>

### [Optimal bounds for an Erdős problem on matching integers to distinct multiples](https://arxiv.org/abs/2603.28636)

- Source id: `source-1b9324cc5f4641`
- Author or public identity: W. van Doorn, Y. Li, Q. Tang
- Kind: `literature`
- Problems: #243
- Relationship and boundary: Cited by both #243 manuscripts at the lemma on blocks of consecutive multiples: Theorem 2.1 (PDF p. 2) solves Erdős Problem #650 on matching integers to distinct multiples, and the upper-bound construction of Theorem 3.1 with Claim 3.2 (PDF pp. 4–5) applies Chinese remaindering to moduli that need not be pairwise coprime. The #243 lemma assumes pairwise coprime moduli and carries its own proof; the source states nothing about Erdős #243.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- \*\*Publication identity:\*\* arXiv preprint arXiv:2603.28636v1 \[math.CO\], 8 pages, submitted 30 March 2026. The arXiv record states that the paper solves Problem #650 on Bloom's Erdős problems website.](https://arxiv.org/abs/2603.28636)
- [- \*\*Matching reformulation:\*\* PDF p. 2 recasts \`f(m)\` as the minimum, over \`A\` and \`x\`, of the maximum matching size in the bipartite graph \`G(A, x)\` joining \`a\` in \`A\` to an integer \`b\` in \`(x, x + 2a\_m)\` whenever \`a | b\`.](https://arxiv.org/abs/2603.28636)
- [- \*\*Main theorem:\*\* PDF p. 2, Theorem 2.1: \`f(m) = min(m, ceil(2 sqrt(m)))\` for every positive integer \`m\`.](https://arxiv.org/abs/2603.28636)
- [- \*\*Upper-bound construction:\*\* PDF p. 4, Theorem 3.1, proves \`f(st) \<= s + t\` with the set \`alpha\_(i,j) = M + i + jD\`; Claim 3.2, stated on the same page with its proof ending on p. 5, shows that \`gcd(alpha\_(i,j), alpha\_(k,l))\` divides \`i - k\`. PDF p. 5 applies the generalised Chinese remainder theorem to obtain \`x\_0\` congruent to \`i\` modulo every \`alpha\_(i,j)\`, stating that its compatibility condition is exactly Claim 3.2.](https://arxiv.org/abs/2603.28636)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L896-L900) — lines `896–900`; excerpt `sha256:92db23ab73e16a5ff23047431abcb3eadb8501f56c588a651c01c454513a268d`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3023-L3027) — lines `3023–3027`; excerpt `sha256:d1521927de67d3175dadffc4db2ca2b2786b8297ec43e4eec74b73a350d2d98c`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L29-L33) — lines `29–33`; excerpt `sha256:d1521927de67d3175dadffc4db2ca2b2786b8297ec43e4eec74b73a350d2d98c`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L246-L246) — lines `246–246`; excerpt `sha256:7031adbd8ee1ddab8aa252c4d2184fcfd608e6225a7ebbe27418145af8fd95d2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2004-L2004) — lines `2004–2004`; excerpt `sha256:7031adbd8ee1ddab8aa252c4d2184fcfd608e6225a7ebbe27418145af8fd95d2`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:246](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L246-L246), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:250](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L250-L250)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2046](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2046-L2046), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2050](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2050-L2050), [cite at paper/reasoning-parts/erdos243/core.tex:2004](../../paper/reasoning-parts/erdos243/core.tex#L2004-L2004), [cite at paper/reasoning-parts/erdos243/core.tex:2008](../../paper/reasoning-parts/erdos243/core.tex#L2008-L2008)

<a id="source-source-21738452dcb95c"></a>

### [Erdős Problems discussion thread #251](https://www.erdosproblems.com/forum/thread/251)

- Source id: `source-21738452dcb95c`
- Author or public identity: Thomas F. Bloom, Terence Tao, Joel Land
- Kind: `website\_contribution`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://www.erdosproblems.com/forum/thread/251)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2469-L2477) — lines `2469–2477`; excerpt `sha256:9fca11ccce8bd3e1f8991533614a59cbf280c5e2447338a96e262d81834811f7`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L112-L120) — lines `112–120`; excerpt `sha256:9fca11ccce8bd3e1f8991533614a59cbf280c5e2447338a96e262d81834811f7`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L125-L125) — lines `125–125`; excerpt `sha256:f28be0b3adcc2253d4812f1fa6cabe0e810b0ce5d54dd20f6c99448874e83ceb`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L126-L126) — lines `126–126`; excerpt `sha256:ca264be99e698e30fe7b641cfaabf181f86278e23511ebb4b9e50e749c38d72c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1650-L1650) — lines `1650–1650`; excerpt `sha256:12505b93fd9fe42cc2789467c5e348722fb0f6684320328f30690cdcc31c269c`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:160](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L160-L160), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1685](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1685-L1685), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2482](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2482-L2482), [cite at paper/reasoning-parts/erdos251/back.tex:125](../../paper/reasoning-parts/erdos251/back.tex#L125-L125), [cite at paper/reasoning-parts/erdos251/core.tex:126](../../paper/reasoning-parts/erdos251/core.tex#L126-L126), [cite at paper/reasoning-parts/erdos251/core.tex:1651](../../paper/reasoning-parts/erdos251/core.tex#L1651-L1651)

<a id="source-source-21cdeefea4c8ec"></a>

### [Comment on Erdős Problem #269](https://www.erdosproblems.com/forum/thread/269)

- Source id: `source-21cdeefea4c8ec`
- Author or public identity: S. Fan
- Kind: `website\_contribution`
- Problems: #269
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2211-L2217) — lines `2211–2217`; excerpt `sha256:f007dbc2ffb8702cf5eb2440409154a2d2658374557f27e4e6a62f0249d4b1e3`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L923-L929) — lines `923–929`; excerpt `sha256:c3d5f6339be814f37255329d21c0904ee6dc32da94a4738ebc14a4eaa9cbbcb4`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L70-L76) — lines `70–76`; excerpt `sha256:f007dbc2ffb8702cf5eb2440409154a2d2658374557f27e4e6a62f0249d4b1e3`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L90-L90) — lines `90–90`; excerpt `sha256:95d46b758e468907a6b8d08aa905cf98bfba012636c8037f9e8baa4459defeea`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L197-L197) — lines `197–197`; excerpt `sha256:3281926307fad92583cc89b85bf8fa7cd6b19d3ddaddaa821068b0a2af69b801`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L694-L694) — lines `694–694`; excerpt `sha256:9a2b41a4b6db48cafbf92f453f6670dfc4c262b50b0db42143521debfa3321ba`
- [paper/reasoning-parts/erdos269/extended\_record.tex](../../paper/reasoning-parts/erdos269/extended_record.tex#L31-L31) — lines `31–31`; excerpt `sha256:0e2b2a4cdf9b7fd6c55d499515bea3230f8e6b37602499415da29e171103abed`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:273](../../paper/269/erdos-269-three-prime-running-lcm.tex#L273-L273)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:141](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L141-L141), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:248](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L248-L248), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:745](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L745-L745), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1717](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1717-L1717), [cite at paper/reasoning-parts/erdos269/core.tex:90](../../paper/reasoning-parts/erdos269/core.tex#L90-L90), [cite at paper/reasoning-parts/erdos269/core.tex:197](../../paper/reasoning-parts/erdos269/core.tex#L197-L197), [cite at paper/reasoning-parts/erdos269/core.tex:694](../../paper/reasoning-parts/erdos269/core.tex#L694-L694), [cite at paper/reasoning-parts/erdos269/extended\_record.tex:31](../../paper/reasoning-parts/erdos269/extended_record.tex#L31-L31)

<a id="source-source-22aba734190d65"></a>

### [Letter to the Editor](https://www.fq.math.ca/Scanned/12-4/letter.pdf)

- Source id: `source-22aba734190d65`
- Author or public identity: P. Erdős
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2156-L2162) — lines `2156–2162`; excerpt `sha256:f412b0eda03f33547d4c3246414916c32a30814e1ce1a591c6ac2205b47970aa`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L895-L900) — lines `895–900`; excerpt `sha256:46bc8e13992d2c2c9223061e4f8c1771a68638e58578fcea5b1c9472e2a3729b`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L15-L21) — lines `15–21`; excerpt `sha256:f412b0eda03f33547d4c3246414916c32a30814e1ce1a591c6ac2205b47970aa`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L68-L68) — lines `68–68`; excerpt `sha256:da0ec5c43e5099217a2c0a7b018ec21c9753ba0a204fe88add16178767e7d40d`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:333](../../paper/269/erdos-269-three-prime-running-lcm.tex#L333-L333)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:119](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L119-L119), [cite at paper/reasoning-parts/erdos269/core.tex:68](../../paper/reasoning-parts/erdos269/core.tex#L68-L68)

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
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1448-L1455) — lines `1448–1455`; excerpt `sha256:00273238c13a5b94ca73f9d3af864fdd7b7bdfb42537d0e3b2729afae0c69a55`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2375-L2382) — lines `2375–2382`; excerpt `sha256:00273238c13a5b94ca73f9d3af864fdd7b7bdfb42537d0e3b2729afae0c69a55`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L18-L25) — lines `18–25`; excerpt `sha256:00273238c13a5b94ca73f9d3af864fdd7b7bdfb42537d0e3b2729afae0c69a55`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L186-L186) — lines `186–186`; excerpt `sha256:8512bbc97e99faf26e79d6c8b92de42e4aee99cb8e1f47bc6fcd1006598c138f`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:240](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L240-L240)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:220](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L220-L220), [cite at paper/reasoning-parts/erdos251/core.tex:186](../../paper/reasoning-parts/erdos251/core.tex#L186-L186)

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
- Problems: #243
- Relationship and boundary: Cited by both #243 manuscripts for the shape of approximation criteria for irrationality: Lemma 3.4 (PDF p. 13, proof p. 14) states a quantitative form of the criterion by nonzero integer linear forms tending to zero, applied in the source to values of q-series. The #243 proofs work with the integer tail directly and do not use the lemma; the source states nothing about Erdős #243.
- Source verification: `source\_verified` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- \*\*Publication identity:\*\* arXiv preprint arXiv:2608.26918v1 \[math.NT\], 37 pages, stamped 27 August 2026.](https://arxiv.org/abs/2608.26918)
- [- \*\*Approximation criterion:\*\* PDF p. 13, Lemma 3.4, with proof on p. 14: integer pairs \`(A\_n, B\_n)\` with \`|A\_n| + |B\_n| \<= X^(kappa n^2 + o(n^2))\` and \`0 \< |B\_n xi - A\_n| \<= X^(-lambda n^2 + o(n^2))\` make \`xi\` irrational, and a nonvanishing determinant \`A\_n B\_(n+1) - A\_(n+1) B\_n\` gives \`mu(xi) \<= 1 + kappa/lambda\`.](https://arxiv.org/abs/2608.26918)
- [- \*\*Integrality step:\*\* PDF p. 14, the proof of Lemma 3.4 uses that \`q |B\_n xi - A\_n| = |p B\_n - q A\_n|\` is a positive integer when \`xi = p/q\`.](https://arxiv.org/abs/2608.26918)

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L911-L915) — lines `911–915`; excerpt `sha256:31ea198a9daf259ca23e51740b76f15a0d4e634894d402cf43507d84497249c0`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3034-L3038) — lines `3034–3038`; excerpt `sha256:31ea198a9daf259ca23e51740b76f15a0d4e634894d402cf43507d84497249c0`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L40-L44) — lines `40–44`; excerpt `sha256:31ea198a9daf259ca23e51740b76f15a0d4e634894d402cf43507d84497249c0`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L569-L569) — lines `569–569`; excerpt `sha256:78effce46f0d85b657f03f28eab5391a11b6116dc14df2c704d888167ed99fd2`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:602](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L602-L602)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:611](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L611-L611), [cite at paper/reasoning-parts/erdos243/core.tex:569](../../paper/reasoning-parts/erdos243/core.tex#L569-L569)

<a id="source-source-296ff41148fff7"></a>

### [Regular sequences and the joint spectral radius](https://doi.org/10.1142/S0129054117500095)

- Source id: `source-296ff41148fff7`
- Author or public identity: M. Coons
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Attribution of the theorem that, for a \`k\`-regular sequence, matrices associated to a basis of the kernel span compute the growth exponent through their joint spectral radius, to Coons, Theorem 1, PDF p. 1. - Attribution of the upper bound from any spanning set, and of the comparison between bases and spanning sets, to Proposition 4 (PDF p. 2) and Corollary 7 (PDF p. 3), with the strictness example on PDF p. 4. - The evaluation argument of Appendix A (PDF p. 4): the evaluation vectors of a basis of sequences span the coefficient space. The #249 short note cites these for the basis-versus-spanning-family distinction and for the evaluation argument in its equivalence between finite generation and finite rational dimension of an integer-valued kernel. The source does not concern Euler's totient, and its growth theorem is not applied to the non-regular totient. Locators follow arXiv:1511.07535v1.
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

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L822-L826) — lines `822–826`; excerpt `sha256:dfad4fe35939edaab05c181a64c042dffdf2b6a2ee9e318fdf0f7c37c86c58e0`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L244-L244) — lines `244–244`; excerpt `sha256:ba2623fd0d16d511439ef0687c6297f7daa8de19a37077c607d2130b31b303ec`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L248-L260) — lines `248–260`; excerpt `sha256:a19f3f512e83dcae6f5c0db90a66f47195ed3b0619df9a340797d8966da61a3b`
- [paper/reasoning-parts/erdos249/a249\_p4.tex](../../paper/reasoning-parts/erdos249/a249_p4.tex#L504-L505) — lines `504–505`; excerpt `sha256:e04dc67f318d119bf17a44db675615d6e63a92ebf331a69436baf1f687626e18`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:244](../../paper/249/erdos-249-binary-totient-series.tex#L244-L244), [cite at paper/249/erdos-249-binary-totient-series.tex:251](../../paper/249/erdos-249-binary-totient-series.tex#L251-L251)

<a id="source-source-2a3af2a360bb15"></a>

### [Prime-Support Rigidity and Primitive Pseudo-Greedy Dynamics: Partial Progress on Erdős Problem #243](https://doi.org/10.13140/RG.2.2.36612.08325)

- Source id: `source-2a3af2a360bb15`
- Author or public identity: I. O. Bado
- Kind: `literature`
- Problems: #243
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L900-L905) — lines `900–905`; excerpt `sha256:1c76f00e8eba4632f224cf59dcb814c7ce70a0ee7880a929f3225aa9a611750f`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:142](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L142-L142)

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

<a id="source-source-2ec6bf87654604"></a>

### [Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach zusammenhängende Gebiete](https://archive.org/details/sitzungsbericht1928preu)

- Source id: `source-2ec6bf87654604`
- Author or public identity: G. Pólya
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1415-L1421) — lines `1415–1421`; excerpt `sha256:2b141e0dfde916d0b14a217ccb8e68c841eb01c0d19ad4821cce29b2e13db886`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2867-L2871) — lines `2867–2871`; excerpt `sha256:ce1e5786510942a84010dd9b4dfa71aa0093743c2eec3c0ca8a106d74048de76`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L2-L6) — lines `2–6`; excerpt `sha256:ce1e5786510942a84010dd9b4dfa71aa0093743c2eec3c0ca8a106d74048de76`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L51-L51) — lines `51–51`; excerpt `sha256:3504348a5a6795de7c7de6f6972ca21e44cf849cafd107d5e79beacb3671228f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L579-L579) — lines `579–579`; excerpt `sha256:83e6c51968fbb8c96b358a906f11583b5ed18f56b1f404c8b974e39cdad6e7a1`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1032-L1032) — lines `1032–1032`; excerpt `sha256:f9309efd3b45427b1667226a08d9d80a855001b073e3ef127be6182471cf977a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1116-L1116) — lines `1116–1116`; excerpt `sha256:513d9455ccd8f11d7bcdd4c503ae02528701d9a1e8bef30b6c9cb257b35a2b5f`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:621](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L621-L621), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1414](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1414-L1414)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:622](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L622-L622), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:2916](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2916-L2916), [cite at paper/reasoning-parts/erdos1041/back.tex:51](../../paper/reasoning-parts/erdos1041/back.tex#L51-L51), [cite at paper/reasoning-parts/erdos1041/core.tex:579](../../paper/reasoning-parts/erdos1041/core.tex#L579-L579)

<a id="source-source-2ee394177d0f38"></a>

### [Sur certaines séries à valeur irrationnelle](https://users.renyi.hu/~p_erdos/1958-19.pdf)

- Source id: `source-2ee394177d0f38`
- Author or public identity: P. Erdős
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1436-L1444) — lines `1436–1444`; excerpt `sha256:5219033aacc7429c8bddb2a4b90c7ddffe7412bf06132d235d2142265ff0e13b`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2362-L2371) — lines `2362–2371`; excerpt `sha256:58b2745b6fa7777eed8e8d54cdf9a0771e5e59cd1804234da7a860d3650c7693`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L5-L14) — lines `5–14`; excerpt `sha256:58b2745b6fa7777eed8e8d54cdf9a0771e5e59cd1804234da7a860d3650c7693`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L74-L74) — lines `74–74`; excerpt `sha256:4c3c5dd1c1ebb3509e07a046edfac9dffdc9e0e6b050cba5793b0f60efd13cf3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L146-L146) — lines `146–146`; excerpt `sha256:3464fa577fbdcd9eebe681537bbca0cdcb42e8a72e3cb669c353edafd72f8be3`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L174-L174) — lines `174–174`; excerpt `sha256:03a9e29985c522ca099926dfd0bced463eec03e1672646e247414a5d7e71e4c9`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:233](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L233-L233)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:108](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L108-L108), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:180](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L180-L180), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:208](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L208-L208), [cite at paper/reasoning-parts/erdos251/core.tex:74](../../paper/reasoning-parts/erdos251/core.tex#L74-L74), [cite at paper/reasoning-parts/erdos251/core.tex:146](../../paper/reasoning-parts/erdos251/core.tex#L146-L146), [cite at paper/reasoning-parts/erdos251/core.tex:174](../../paper/reasoning-parts/erdos251/core.tex#L174-L174)

<a id="source-source-317a740451ce03"></a>

### [Refinement of the Chowla--Erdős method and linear independence of certain Lambert series](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf)

- Source id: `source-317a740451ce03`
- Author or public identity: D. Duverney, Y. Tachiya
- Kind: `literature`
- Problems: #249, #257
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

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5383-L5391) — lines `5383–5391`; excerpt `sha256:64ec02486225f54bf2dfac8b56940d1a93a770185477df524459a057b87a721e`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1210-L1225) — lines `1210–1225`; excerpt `sha256:2709aab4a1ed5bcf9e76780349a649d3d43d9f1ec5125a7cecc5eadce27df86d`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L640-L651) — lines `640–651`; excerpt `sha256:dfca4813823f9e6877ab989e482075886ea1c687d9cca66733d6781c929b1cd1`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L748-L753) — lines `748–753`; excerpt `sha256:574840882ce4400f3c704d39cf7123aa174fc3d5c18b3a6a8d254cae363c7601`
- [paper/reasoning-parts/erdos257/a257\_invent.tex](../../paper/reasoning-parts/erdos257/a257_invent.tex#L569-L574) — lines `569–574`; excerpt `sha256:f31d344d66d1d3e0e05db6c555b8086fb7f94ebac1cd8e286afd8e423445e5ee`
- [paper/reasoning-parts/erdos257/a257\_p5.tex](../../paper/reasoning-parts/erdos257/a257_p5.tex#L53-L63) — lines `53–63`; excerpt `sha256:45f418251d7e70c5af4a271bd4dda83c6c2af54af9e36882d4fc28dc4d89e092`
- [paper/reasoning-parts/erdos257/a257\_p5.tex](../../paper/reasoning-parts/erdos257/a257_p5.tex#L383-L387) — lines `383–387`; excerpt `sha256:6149cf3feccb99f13e1dc7f422701f0657eb31bc70f59c9f26b0699391cec919`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L115-L117) — lines `115–117`; excerpt `sha256:1feaacdba37f43f9c96e7c6a45e1ca87289d130ebe38f7fa18d2f87715ca2ac8`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L335-L341) — lines `335–341`; excerpt `sha256:7dd0d8b8beeab740868cbfd3976ebd67b17b3b14fe028224267ba224243f1f5a`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L729-L733) — lines `729–733`; excerpt `sha256:697bc76dfb08a6522b9b904bca48696ca7de30dda22d3a2a09931c3e07108c88`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L295-L319) — lines `295–319`; excerpt `sha256:6bb6ee3e89f79566028b13a30d09ae06a616eb86ecadf1ff44369448a83b8514`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:117](../../paper/257/erdos-257-mersenne-support-subseries.tex#L117-L117), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:341](../../paper/257/erdos-257-mersenne-support-subseries.tex#L341-L341), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:730](../../paper/257/erdos-257-mersenne-support-subseries.tex#L730-L730)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:749](../../paper/archive/erdos249-257-main-paper.tex#L749-L749)

<a id="source-source-318b37ba5af2eb"></a>

### [A theorem on irrationality of infinite series and applications](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf)

- Source id: `source-318b37ba5af2eb`
- Author or public identity: C. Badea
- Kind: `literature`
- Problems: #243
- Relationship and boundary: The exact positive-rational-series inequality/equality criterion in Theorem A, Theorem 2.10, and Corollary 2.2, with the printed locators above. - The fact that Badea's 1993 theorem generalizes the positive-term Sylvester boundary and supplies the stated recurrence consequences for its own hypotheses. - The publication identity, official retrieval routes, publisher's page-level license indication, digest, and page-level locators recorded above.
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

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L880-L884) — lines `880–884`; excerpt `sha256:8a9384c13600f371f64e2f766eab33714ac448cd7c07d6c0b7d31adb38f0385e`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3007-L3011) — lines `3007–3011`; excerpt `sha256:8a9384c13600f371f64e2f766eab33714ac448cd7c07d6c0b7d31adb38f0385e`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L13-L17) — lines `13–17`; excerpt `sha256:8a9384c13600f371f64e2f766eab33714ac448cd7c07d6c0b7d31adb38f0385e`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L623-L624) — lines `623–624`; excerpt `sha256:b8bce3dbb006b380408cee1cb7080191cb231fcd79249a80ab5b4f4bb4da6a10`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:139](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L139-L139)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:665](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L665-L666), [cite at paper/reasoning-parts/erdos243/core.tex:623](../../paper/reasoning-parts/erdos243/core.tex#L623-L624)

<a id="source-source-318ee5e7cf6d74"></a>

### [Bad Polynomials for Newton's Method](https://www.math.stonybrook.edu/preprints/ims92-7.pdf)

- Source id: `source-318ee5e7cf6d74`
- Author or public identity: S. Sutherland
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2883-L2888) — lines `2883–2888`; excerpt `sha256:6fb37824293e7cce52b4b29f61ea541eb82176ad734eda23639823fb1a62191e`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L18-L23) — lines `18–23`; excerpt `sha256:6fb37824293e7cce52b4b29f61ea541eb82176ad734eda23639823fb1a62191e`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L188-L188) — lines `188–188`; excerpt `sha256:e8e376fbbee36687769571c22032fa53c50be7653bf8cc1d475ff347bf8d486a`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:231](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L231-L231), [cite at paper/reasoning-parts/erdos1041/core.tex:188](../../paper/reasoning-parts/erdos1041/core.tex#L188-L188)

<a id="source-source-34b520c561ee3c"></a>

### [Character sums and congruences with n!](https://arxiv.org/abs/math/0403422)

- Source id: `source-34b520c561ee3c`
- Author or public identity: M. Z. Garaev, F. Luca, I. E. Shparlinski
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1880-L1886) — lines `1880–1886`; excerpt `sha256:72373b6f062cddf3c5fe068756219ef9a24618e1ae351afdcd65500bc036628d`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L26-L32) — lines `26–32`; excerpt `sha256:72373b6f062cddf3c5fe068756219ef9a24618e1ae351afdcd65500bc036628d`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L261-L261) — lines `261–261`; excerpt `sha256:0e518720857d7077a3a5e3918fd9223cb6aa2d91a39e690019698a7508c1498b`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1030-L1030) — lines `1030–1030`; excerpt `sha256:b27b56d099544bbbb5abad5374ab18371e01c2ed8e13e41339ca8ab9190a40b5`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1230-L1230) — lines `1230–1230`; excerpt `sha256:1ca74b0b99e561f9885f56899175bbda9fae594560bae170c1a0333b24a30fd6`
- [paper/reasoning-parts/erdos68/extended\_record.tex](../../paper/reasoning-parts/erdos68/extended_record.tex#L111-L111) — lines `111–111`; excerpt `sha256:1b58313724a34091ccaa18a82fb89592517e2c9aea9375c7f9237f594db7eda5`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:297](../../paper/68/erdos68-factorial-reasoning-surface.tex#L297-L297), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1066](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1066-L1066), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1266](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1266-L1266), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1455](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1455-L1455), [cite at paper/reasoning-parts/erdos68/core.tex:261](../../paper/reasoning-parts/erdos68/core.tex#L261-L261), [cite at paper/reasoning-parts/erdos68/core.tex:1030](../../paper/reasoning-parts/erdos68/core.tex#L1030-L1030), [cite at paper/reasoning-parts/erdos68/core.tex:1230](../../paper/reasoning-parts/erdos68/core.tex#L1230-L1230), [cite at paper/reasoning-parts/erdos68/extended\_record.tex:111](../../paper/reasoning-parts/erdos68/extended_record.tex#L111-L111)

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
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1561-L1566) — lines `1561–1566`; excerpt `sha256:c89d595871311eec76167add03b720a82202963564fd46493036b4e96b08de98`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:894](../../paper/systems/claim-faithful-publication-systems-paper.tex#L894-L894), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1320](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1320-L1320)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:780](../../paper/systems/open-source-mathematics-strategy.tex#L780-L780), [cite at paper/systems/open-source-mathematics-strategy.tex:822](../../paper/systems/open-source-mathematics-strategy.tex#L822-L822), [cite at paper/systems/open-source-mathematics-strategy.tex:910](../../paper/systems/open-source-mathematics-strategy.tex#L910-L910)

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
- Relationship and boundary: External scalar Mahler obstruction cited by the papers: the authors explicitly state that the divisor-function generating series is not k-Mahler for any k \>= 2. The elementary simultaneous-2/3 obstruction is retained as an ordinary local proof; the external classification does not rule out all systems using additional functions or all approximation methods.
- Source verification: `source\_verified` — Direct primary-source readback verified the authors, title, Theorem 1.3 statement and its explicitly stated divisor-function consequence in the introduction. This is source verification, not an independent proof audit, Lean formalization, novelty review, or claim of local adoption.
- Local mapping: `exact\_bibliographic\_use` — The current short and long #1049 functional-equation discussions cite the same external scalar exclusion; archived uses remain historical.

Exact source locations:

- [Introduction, Theorem 1.3 on p. 2 and divisor-function consequence on p. 3; authors’ public PDF inspected 12 September 2026.](https://math.smertnig.at/paper/multiplicative-mahler.pdf)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5358-L5363) — lines `5358–5363`; excerpt `sha256:b3f91ee983a8672978d0cb4683a9eac57121a743ff8449aa943c718486e5f24d`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L991-L997) — lines `991–997`; excerpt `sha256:2320b9dc49154910c7ee5a4a4867154c0d1ca5f34cf5c7f5afa6f17e713a2d91`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2754-L2761) — lines `2754–2761`; excerpt `sha256:d7a5601c0bf5ee79e28680c035954f88c9595fe58e44b0961b306093b310bc54`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2779-L2786) — lines `2779–2786`; excerpt `sha256:d7a5601c0bf5ee79e28680c035954f88c9595fe58e44b0961b306093b310bc54`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L105-L110) — lines `105–110`; excerpt `sha256:05bb3c29b6380bcd11a35ad104d589587f9f13182aa1d9fb5b81de34e93cd607`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3188-L3193) — lines `3188–3193`; excerpt `sha256:05bb3c29b6380bcd11a35ad104d589587f9f13182aa1d9fb5b81de34e93cd607`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:846](../../paper/1049/erdos-1049-rational-base-lambert.tex#L846-L846)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2780](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2780-L2780), [cite at paper/reasoning-parts/erdos1049/core.tex:2755](../../paper/reasoning-parts/erdos1049/core.tex#L2755-L2755)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3192](../../paper/archive/erdos249-257-main-paper.tex#L3192-L3192)

<a id="source-source-40bc4064b92788"></a>

### [The area of polynomial images and preimages](https://arxiv.org/abs/math/0302189)

- Source id: `source-40bc4064b92788`
- Author or public identity: E. Crane
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Area and multiplicity estimates for polynomial preimages cited in the Problem 1041 reasoning surface.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Theorems 2 and 3 give the measurable-set preimage area inequality and the stronger multiplicity integral inequality, with equality cases.](https://arxiv.org/abs/math/0302189)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2871-L2874) — lines `2871–2874`; excerpt `sha256:637f267b342a5d120e51f20bb99a2970f890e7aea7947fb4d2f8bfc73e3add60`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L6-L9) — lines `6–9`; excerpt `sha256:637f267b342a5d120e51f20bb99a2970f890e7aea7947fb4d2f8bfc73e3add60`

<a id="source-source-43a734be32736f"></a>

### [Some problems and results on the irrationality of the sum of infinite series](https://doi.org/10.1007/BF01083693)

- Source id: `source-43a734be32736f`
- Author or public identity: Paul Erdős
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the #257 note (Theorem 1, as restated in arXiv:2601.21442 Remark 4(4)) as the growth-condition irrationality lane, settling exactly the supports with limsup c\_n/2^n = infinity, incomparable with the reciprocal-summable class.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1267-L1273) — lines `1267–1273`; excerpt `sha256:0ffa1b9604849fafd2410ef3bb64c295024350a23bcfd1348eac1ae548a50fa2`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:742](../../paper/257/erdos-257-mersenne-support-subseries.tex#L742-L742), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1279](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1279-L1279)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L662-L665) — lines `662–665`; excerpt `sha256:facbf8174f29ec644aa87ad59cf5ec179262bc093a6f37a813598d55c1c8af77`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:465](../../paper/systems/cold-clone-to-proof-receipt.tex#L465-L465)

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
- Relationship and boundary: Prior art for the strict-tail inequality, injectivity of fixed-base Lambert subsums, and their Cantor-set structure, PDF p. 13, Remark 4.1. - The published authors' statement of the unresolved fixed-base subseries question and the prime-support open example, PDF pp. 4–5. - The merged multi-base rational-sum construction under its explicit mass hypothesis, PDF p. 5, Theorem 2.3, with proof pp. 13–14. - The growth and shifted-Sylvester context for Ahmes-series irrationality questions, PDF p. 2 and §§2.1.2–2.1.3. - The publication identity, arXiv version, official routes, digest, and page-level locators recorded above. The docstring explicitly identifies Kovač–Tao Lemma 5.1 and bounds the local result to the elementary interval inequality; the analytic hypotheses and existence/rationality conclusion are not formalized here. Supplement copy of the Kovač–Tao Lemma 5.1 specialization and its explicit non-formalization boundary.
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

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5391-L5395) — lines `5391–5395`; excerpt `sha256:e74d62894afb08f0bf9f352f2a81f1d8436fc4947ccc8847ea8044e669d88d61`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L892-L896) — lines `892–896`; excerpt `sha256:cf37e937376ea8c587dfe7f9020c59e64518678e4042b44e24eee03372b521cc`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3019-L3023) — lines `3019–3023`; excerpt `sha256:cf37e937376ea8c587dfe7f9020c59e64518678e4042b44e24eee03372b521cc`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1468-L1472) — lines `1468–1472`; excerpt `sha256:06a36adeb282bbcc0aa7f139bf3794a9199ab0e54592f27e0497bf11222b1b81`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2400-L2405) — lines `2400–2405`; excerpt `sha256:02d51eec1db3f20d4d8be66c951af79ab561978d94292f20681aebf208944f37`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1242-L1249) — lines `1242–1249`; excerpt `sha256:47be7d5967eb02b0cfe2c4cc13e8e6064ec86800b2070cfc29c580a862eb9aa9`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2189-L2196) — lines `2189–2196`; excerpt `sha256:f484ba9d0732a84a0ef7c0138504704191e48f38031d5dfbfc3eb1932fbf4ce1`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3177-L3181) — lines `3177–3181`; excerpt `sha256:94ba45c785a36cdde046a477ed007cff43a5b8913afbae90ae2d2668457b4f78`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L94-L98) — lines `94–98`; excerpt `sha256:94ba45c785a36cdde046a477ed007cff43a5b8913afbae90ae2d2668457b4f78`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L225-L225) — lines `225–225`; excerpt `sha256:421eb640ce9c740e481314c6317adf6452b2a2c9f83f2d3a1d6d47ae714c0a67`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L25-L29) — lines `25–29`; excerpt `sha256:cf37e937376ea8c587dfe7f9020c59e64518678e4042b44e24eee03372b521cc`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L670-L670) — lines `670–670`; excerpt `sha256:ed15584e6c1e5aad104bf9f61e6ad12fd13f3c3e9a1ef562adbc0a88628a6422`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L673-L673) — lines `673–673`; excerpt `sha256:5e19fd6ae0b682bc04ca032968ce8ee47f5f0b979bdd6f85bcdc41d336ac8fb6`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L681-L681) — lines `681–681`; excerpt `sha256:b189d9cf21e6278eb700a51d4686c09fe843b723fe0afcbae9c5f6fa44b6b21f`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L43-L48) — lines `43–48`; excerpt `sha256:02d51eec1db3f20d4d8be66c951af79ab561978d94292f20681aebf208944f37`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L244-L244) — lines `244–244`; excerpt `sha256:1eaf060df05df129216afd1e30bb11b8752f09144e3d5223018473b9836c3390`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L48-L55) — lines `48–55`; excerpt `sha256:f484ba9d0732a84a0ef7c0138504704191e48f38031d5dfbfc3eb1932fbf4ce1`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L146-L146) — lines `146–146`; excerpt `sha256:79230fdd55c96aabd26bb3143421cd7032b162de08edf11e8c2caf03f85c6c21`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L26-L28) — lines `26–28`; excerpt `sha256:5d6ed14dc2f5bf60d4327ab3742c47166f8aa806f3a82b41be7d830c206f88df`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L692-L705) — lines `692–705`; excerpt `sha256:b6d42331242112d32c82f0792671503ef38b50d4552f68a585be8fd618262030`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateau.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L1698-L1708) — lines `1698–1708`; excerpt `sha256:c989aa24e7d0cd4a81a2207dea6e4647a9e1d349d2fb8a86a8fcd45cc9386fd7`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L603-L613) — lines `603–613`; excerpt `sha256:c989aa24e7d0cd4a81a2207dea6e4647a9e1d349d2fb8a86a8fcd45cc9386fd7`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L157-L157) — lines `157–157`; excerpt `sha256:b0911c07481375d9196e8e76aacf7abd6db17f54f8fc15ee1c48def5ae8e0ba4`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L252-L252) — lines `252–252`; excerpt `sha256:23c36a15d6c427ad9d2c6b84db105b987fe7b32dca6bcd9b66582b73b15a54a7`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L210-L210) — lines `210–210`; excerpt `sha256:976e2b7c6429f891b855d61841e48da146a0153d684a53bc962fc05f7add9649`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L218-L218) — lines `218–218`; excerpt `sha256:63566ee707a904f479db907c82584109453d46c62f4e3815466ac0827609f5ef`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1108-L1108) — lines `1108–1108`; excerpt `sha256:134dddf55c74e49a6bfd8b977f7a852c7f7bc017bb2544b6ef5de21d420f70db`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L244-L244) — lines `244–244`; excerpt `sha256:976e2b7c6429f891b855d61841e48da146a0153d684a53bc962fc05f7add9649`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L252-L252) — lines `252–252`; excerpt `sha256:63566ee707a904f479db907c82584109453d46c62f4e3815466ac0827609f5ef`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1142-L1142) — lines `1142–1142`; excerpt `sha256:134dddf55c74e49a6bfd8b977f7a852c7f7bc017bb2544b6ef5de21d420f70db`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:157](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L157-L157), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:252](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L252-L252)
- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:803](../../paper/257/erdos-257-mersenne-support-subseries.tex#L803-L803)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:250](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L250-L250), [cite at paper/reasoning-parts/erdos1049/core.tex:225](../../paper/reasoning-parts/erdos1049/core.tex#L225-L225)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:712](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L712-L712), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:715](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L715-L715), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:723](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L723-L723), [cite at paper/reasoning-parts/erdos243/core.tex:670](../../paper/reasoning-parts/erdos243/core.tex#L670-L670), [cite at paper/reasoning-parts/erdos243/core.tex:673](../../paper/reasoning-parts/erdos243/core.tex#L673-L673), [cite at paper/reasoning-parts/erdos243/core.tex:681](../../paper/reasoning-parts/erdos243/core.tex#L681-L681)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:835](../../paper/archive/erdos249-257-main-paper.tex#L835-L835), [cite at paper/archive/erdos249-257-main-paper.tex:836](../../paper/archive/erdos249-257-main-paper.tex#L836-L836), [cite at paper/archive/erdos249-257-main-paper.tex:2157](../../paper/archive/erdos249-257-main-paper.tex#L2157-L2157), [cite at paper/archive/erdos249-257-main-paper.tex:4676](../../paper/archive/erdos249-257-main-paper.tex#L4676-L4676), [cite at paper/archive/erdos249-257-main-paper.tex:5067](../../paper/archive/erdos249-257-main-paper.tex#L5067-L5067), [cite at paper/archive/erdos249-257-main-paper.tex:5113](../../paper/archive/erdos249-257-main-paper.tex#L5113-L5113)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:244](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L244-L244), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:252](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L252-L252), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:278](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L278-L278), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1142](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1142-L1142), [cite at paper/reasoning-parts/erdos251/core.tex:210](../../paper/reasoning-parts/erdos251/core.tex#L210-L210), [cite at paper/reasoning-parts/erdos251/core.tex:218](../../paper/reasoning-parts/erdos251/core.tex#L218-L218), [cite at paper/reasoning-parts/erdos251/core.tex:244](../../paper/reasoning-parts/erdos251/core.tex#L244-L244), [cite at paper/reasoning-parts/erdos251/core.tex:1108](../../paper/reasoning-parts/erdos251/core.tex#L1108-L1108)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:197](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L197-L197), [cite at paper/reasoning-parts/erdos269/core.tex:146](../../paper/reasoning-parts/erdos269/core.tex#L146-L146)

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

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2171-L2175) — lines `2171–2175`; excerpt `sha256:7b0b0dd73febcea1a9242a18756e46d2d756b59d9fe81ac7cd8da21e428c8d58`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L30-L34) — lines `30–34`; excerpt `sha256:7b0b0dd73febcea1a9242a18756e46d2d756b59d9fe81ac7cd8da21e428c8d58`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L143-L143) — lines `143–143`; excerpt `sha256:558860d2fb987f19c40ea022ef55298f3c596600a2a465cae5a8e7263d08a42e`
- [paper/reasoning-parts/erdos269/extended\_record.tex](../../paper/reasoning-parts/erdos269/extended_record.tex#L38-L38) — lines `38–38`; excerpt `sha256:7636ce72c5b5d9844abad7aa99d86728f70317c1163f935acba72acf99dda55e`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L193-L194) — lines `193–194`; excerpt `sha256:f7aed53628d03ee04f97abc084a236d388c08b1fea509170db40e9bbe3d6f545`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:194](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L194-L194), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1724](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1724-L1724), [cite at paper/reasoning-parts/erdos269/core.tex:143](../../paper/reasoning-parts/erdos269/core.tex#L143-L143), [cite at paper/reasoning-parts/erdos269/extended\_record.tex:38](../../paper/reasoning-parts/erdos269/extended_record.tex#L38-L38)

<a id="source-source-5752bb5009e4de"></a>

### [The ring of k -regular sequences](https://cs.uwaterloo.ca/~shallit/Papers/as0.pdf)

- Source id: `source-5752bb5009e4de`
- Author or public identity: J.-P. Allouche, J. Shallit
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5344-L5352) — lines `5344–5352`; excerpt `sha256:28fc1b15f89dedfd49214bfcd5a49cc05823f44376740a8e9ad7fc0e987fb378`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L816-L819) — lines `816–819`; excerpt `sha256:867c017fd5e319d7d8dd47a300a5aead007cebebb30c5f3d3b9fcccbf92063e2`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:574](../../paper/249/erdos-249-binary-totient-series.tex#L574-L574)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3184](../../paper/archive/erdos249-257-main-paper.tex#L3184-L3184)

<a id="source-source-57adfd0cdcd8c2"></a>

### [On the largest prime divisor of n!+1](https://arxiv.org/abs/2103.14894)

- Source id: `source-57adfd0cdcd8c2`
- Author or public identity: L. Lai
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited in both #68 manuscripts for two steps of the common-denominator growth estimate and its polynomial-shift extension: the nonvanishing cutoff (Lemma 2.1, which restates Lemma 3 of Luca and Shparlinski with the bound n!+f(n) \> 1) and the common-divisor subtraction at display (2.5). The paper's theorem concerns the largest prime divisor of n!+f(n) and gives no irrationality result for the #68 series.
- Source verification: `source\_verified` — arXiv v1 PDF read in full (11 pages); the publisher PDF text confirms the same lemma and display numbers on the printed pages given. Verifies the two cited steps only.
- Local mapping: `not recorded`

Exact source locations:

- [Lemma 2.1, arXiv v1 p. 2: for nonzero f in Z\[X\] there is n\_0 \>= 2, depending only on f, such that f(n)(n+1)...(n+k) - f(n+k) = 0 has no integer solutions with n \>= n\_0 and k \>= 1, and n!+f(n) \> 1 and f(n) != 0 for n \>= n\_0. The proof refers the first assertion to Lemma 3 of Luca and Shparlinski (2005).](https://arxiv.org/abs/2103.14894v1)
- [Proof of Lemma 2.4, display (2.5), arXiv v1 p. 4: a prime power D dividing both n\_i!+f(n\_i) and n\_j!+f(n\_j) divides f(n\_i)(n\_i+1)...(n\_j) - f(n\_j), which is nonzero by Lemma 2.1 and at most 2x^(C\_1+|I\_1|).](https://arxiv.org/abs/2103.14894v1)
- [Published version, Bull. Aust. Math. Soc. 113 (2026), 390-403, with the same numbering: Lemma 2.1 on p. 392, Lemma 2.4 on p. 393, display (2.5) on p. 394.](https://doi.org/10.1017/S0004972725100543)

Public implementation or evidence coordinates:

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L914-L920) — lines `914–920`; excerpt `sha256:a0d504d3d508af2b875b5dec54bc794358303db8ea0ee2c58d70dd66309055b9`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1919-L1926) — lines `1919–1926`; excerpt `sha256:01d7a9293432c769f7c4e88c31adcbb2ba676eebeeb8a4c4b9bafd808fa4fb28`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L65-L72) — lines `65–72`; excerpt `sha256:01d7a9293432c769f7c4e88c31adcbb2ba676eebeeb8a4c4b9bafd808fa4fb28`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L492-L492) — lines `492–492`; excerpt `sha256:dfe30a3d6989304d9eada5ae6d5f075a7e757937833d6734b2160719386fec6a`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L502-L502) — lines `502–502`; excerpt `sha256:0000e5c2105d821932b1d5c938f44fa35d2b77c5dcd6893d2bff25f0c8d62a86`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L194-L194) — lines `194–194`; excerpt `sha256:5ca1adb6ffb82e2ea61b589c2e98ea08cba156b536884ab859840210a8d8912c`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L274-L274) — lines `274–274`; excerpt `sha256:610f7b518aa36dfe61ffb9e2d76965bf9ac38e8bd7d9dff8cb91bda4b2a59e97`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1233-L1233) — lines `1233–1233`; excerpt `sha256:9354cad1ad2267a087e6ca551a3a34d423bc684537f84c7b28e1aaefa5ab2569`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1236-L1236) — lines `1236–1236`; excerpt `sha256:cf244f8d406dbc2b1691723895810b510a0d4cb83e857833f09d5ad2404fdf9f`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:492](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L492-L492), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:502](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L502-L502)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:230](../../paper/68/erdos68-factorial-reasoning-surface.tex#L230-L230), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:310](../../paper/68/erdos68-factorial-reasoning-surface.tex#L310-L310), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1269](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1269-L1269), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1272](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1272-L1272), [cite at paper/reasoning-parts/erdos68/core.tex:194](../../paper/reasoning-parts/erdos68/core.tex#L194-L194), [cite at paper/reasoning-parts/erdos68/core.tex:274](../../paper/reasoning-parts/erdos68/core.tex#L274-L274), [cite at paper/reasoning-parts/erdos68/core.tex:1233](../../paper/reasoning-parts/erdos68/core.tex#L1233-L1233), [cite at paper/reasoning-parts/erdos68/core.tex:1236](../../paper/reasoning-parts/erdos68/core.tex#L1236-L1236)

<a id="source-source-5911448b65fdf9"></a>

### [On an incomplete argument of Erdős on the irrationality of Lambert series](https://arxiv.org/abs/1206.0340)

- Source id: `source-5911448b65fdf9`
- Author or public identity: J. Vandehey
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3162-L3166) — lines `3162–3166`; excerpt `sha256:ec00799c8a18f226c11ddb3397de2c15b0fb2a0863bb9126f6ebb34db8f890d0`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L79-L83) — lines `79–83`; excerpt `sha256:ec00799c8a18f226c11ddb3397de2c15b0fb2a0863bb9126f6ebb34db8f890d0`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L199-L199) — lines `199–199`; excerpt `sha256:4cba849220b6d89a05527440677a635fe05b976de1d3d125b3c7d9e3b37a61fe`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L202-L202) — lines `202–202`; excerpt `sha256:fd92ac482f370cb8afab84fb13484fe7a5d23e8d666f012ce7c6ae806b86f950`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:224](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L224-L224), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:227](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L227-L227), [cite at paper/reasoning-parts/erdos1049/core.tex:199](../../paper/reasoning-parts/erdos1049/core.tex#L199-L199), [cite at paper/reasoning-parts/erdos1049/core.tex:202](../../paper/reasoning-parts/erdos1049/core.tex#L202-L202)

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

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5307-L5310) — lines `5307–5310`; excerpt `sha256:20b0b33ebb4cd3cbf86a87600342b42670e722c45b2b8f83015e0c8f3160e9da`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1249-L1251) — lines `1249–1251`; excerpt `sha256:12e925bb796b6215db708d25b5d1ab1c5640c351e7f3683e2c91ae968206b259`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3088-L3092) — lines `3088–3092`; excerpt `sha256:cf446c3cbb0c405bcc80ec2c25d599a8a83cd781fed2f9312d32338c1383374d`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L5-L9) — lines `5–9`; excerpt `sha256:cf446c3cbb0c405bcc80ec2c25d599a8a83cd781fed2f9312d32338c1383374d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L81-L81) — lines `81–81`; excerpt `sha256:5c2702a8cde3c232738e8827b542bc16923457da7f595c51367ae5f0782ba8e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L123-L123) — lines `123–123`; excerpt `sha256:1d8fc66588d2076dad018be4bac71a70910db63d9b53ba28738dd383a7359aec`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L264-L264) — lines `264–264`; excerpt `sha256:9eea1156ef32f890b6cd87c8ee4f70d5259f71e8fa56393d9da4e31658916a6d`
- [paper/reasoning-parts/erdos257/a257\_p0.tex](../../paper/reasoning-parts/erdos257/a257_p0.tex#L60-L67) — lines `60–67`; excerpt `sha256:a5026b37639c46148647b3dd64f3197823a05e90edc63e52ca0c70acd91a7046`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L748-L755) — lines `748–755`; excerpt `sha256:216cd24cebd7dc2ee03b275075ee12c235c59319f44725a34321a358ce72c354`
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

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:724](../../paper/257/erdos-257-mersenne-support-subseries.tex#L724-L724)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:106](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L106-L106), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:148](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L148-L148), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:289](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L289-L289), [cite at paper/reasoning-parts/erdos1049/core.tex:81](../../paper/reasoning-parts/erdos1049/core.tex#L81-L81), [cite at paper/reasoning-parts/erdos1049/core.tex:123](../../paper/reasoning-parts/erdos1049/core.tex#L123-L123), [cite at paper/reasoning-parts/erdos1049/core.tex:264](../../paper/reasoning-parts/erdos1049/core.tex#L264-L264)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:115](../../paper/archive/erdos249-257-main-paper.tex#L115-L115), [cite at paper/archive/erdos249-257-main-paper.tex:630](../../paper/archive/erdos249-257-main-paper.tex#L630-L630), [cite at paper/archive/erdos249-257-main-paper.tex:633](../../paper/archive/erdos249-257-main-paper.tex#L633-L633)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1540-L1545) — lines `1540–1545`; excerpt `sha256:573f52e0c7b894eeeb44cdeb82b9844001ad1c0155ff50cf96d645b233996e9d`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:492](../../paper/systems/open-source-mathematics-strategy.tex#L492-L492), [cite at paper/systems/open-source-mathematics-strategy.tex:884](../../paper/systems/open-source-mathematics-strategy.tex#L884-L884)

<a id="source-source-5ee4a583f9ca3f"></a>

### [The van der Corput property for sums of two squares](https://arxiv.org/abs/2606.29185)

- Source id: `source-5ee4a583f9ca3f`
- Author or public identity: Steve Fan, Andrew Lott
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Cited by both #269 papers at the height-fibre regrouping as a comparison: the van der Corput coefficients on sums of two squares sum smooth weights over the representations d=v^2(x^2+y^2), and averaging over v keeps the complete sums in a fixed sector (Corollary 4.4). No input from the paper is used in a #269 argument.
- Source verification: `source\_verified` — The cited preprint's identity, authors, version and the quoted section, lemma, corollary and page locators were directly checked against the v1 PDF. This does not certify the mathematics or imply local adoption.
- Local mapping: `not recorded`

Exact source locations:

- [arXiv v1 (28 June 2026) PDF read in full on 2026-09-15; Section 3, pp. 4-8, defines the coefficients from the representations d=v^2(x^2+y^2); p. 5 explains that averaging over v places the complete sums in a fixed sector; Corollary 4.4, p. 12, proves the sector bound.](https://arxiv.org/abs/2606.29185v1)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2217-L2224) — lines `2217–2224`; excerpt `sha256:faba7205469228a0b3a418034506266ce59c0373f70e31c87da8d2d175fe04b1`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L929-L936) — lines `929–936`; excerpt `sha256:faba7205469228a0b3a418034506266ce59c0373f70e31c87da8d2d175fe04b1`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L76-L83) — lines `76–83`; excerpt `sha256:faba7205469228a0b3a418034506266ce59c0373f70e31c87da8d2d175fe04b1`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L329-L329) — lines `329–329`; excerpt `sha256:8056959fc9b1f66fd554b59906556744acc0dfb1825f85edb3d25b6a2e2cbfbc`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L399-L399) — lines `399–399`; excerpt `sha256:a95522c632d708172c756e2ccc0a8d642ce85126475da95633b40aa0906a264d`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:399](../../paper/269/erdos-269-three-prime-running-lcm.tex#L399-L399)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:380](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L380-L380), [cite at paper/reasoning-parts/erdos269/core.tex:329](../../paper/reasoning-parts/erdos269/core.tex#L329-L329)

<a id="source-source-5ee5f85bd606ee"></a>

### [Continued Fractions](https://store.doverpublications.com/products/9780486696300)

- Source id: `source-5ee5f85bd606ee`
- Author or public identity: A. Ya. Khinchin
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Public bibliographic identity and author record; metadata checked on 2026-09-12. This does not verify a mathematical use.](https://store.doverpublications.com/products/9780486696300)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2395-L2400) — lines `2395–2400`; excerpt `sha256:f3d4bd2ba58ad8313db4eaff5b5408fcdff69ea44d5594c581766ebcbdd68e7c`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L38-L43) — lines `38–43`; excerpt `sha256:f3d4bd2ba58ad8313db4eaff5b5408fcdff69ea44d5594c581766ebcbdd68e7c`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L914-L914) — lines `914–914`; excerpt `sha256:1a21578311ec910b492dfd5ac3f1f15adb4799f596f0741ccb86280e6c55aa81`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:949](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L949-L949), [cite at paper/reasoning-parts/erdos251/core.tex:915](../../paper/reasoning-parts/erdos251/core.tex#L915-L915)

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

Public implementation or evidence coordinates:

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L920-L925) — lines `920–925`; excerpt `sha256:f4b93b64e57ba9e355c17f9d32a33fad008c653623743e63b5eb9337d3d5ad50`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1913-L1919) — lines `1913–1919`; excerpt `sha256:a1597d4571d5a4e76df86c113668ef9c13fb36fc9b633ca25cc16e4c4f974a91`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L59-L65) — lines `59–65`; excerpt `sha256:a1597d4571d5a4e76df86c113668ef9c13fb36fc9b633ca25cc16e4c4f974a91`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L494-L494) — lines `494–494`; excerpt `sha256:e1073ec626d501f919294499c8b24b446ae999d3d127deae66fe3fdabdccc340`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L501-L501) — lines `501–501`; excerpt `sha256:347983f8c64b53210c99c415d4f1f6f743dccf5acd126522a5df5270c2a05c2e`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L193-L193) — lines `193–193`; excerpt `sha256:e21825904da9dd31c07d34f4fffbaf1e000f841c245db07d7be4431a25ff51ba`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L273-L273) — lines `273–273`; excerpt `sha256:1cd908c32a4075358b4a5b28cd867611db27850b3e5d596c47128f14454d5847`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1233-L1233) — lines `1233–1233`; excerpt `sha256:9354cad1ad2267a087e6ca551a3a34d423bc684537f84c7b28e1aaefa5ab2569`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1235-L1235) — lines `1235–1235`; excerpt `sha256:4919897eb071a8d7bba39212c376726b0f4797a611acc5f5c0fdbe9531b41d3d`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:494](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L494-L494), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:501](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L501-L501)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:229](../../paper/68/erdos68-factorial-reasoning-surface.tex#L229-L229), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:309](../../paper/68/erdos68-factorial-reasoning-surface.tex#L309-L309), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1269](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1269-L1269), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1271](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1271-L1271), [cite at paper/reasoning-parts/erdos68/core.tex:193](../../paper/reasoning-parts/erdos68/core.tex#L193-L193), [cite at paper/reasoning-parts/erdos68/core.tex:273](../../paper/reasoning-parts/erdos68/core.tex#L273-L273), [cite at paper/reasoning-parts/erdos68/core.tex:1233](../../paper/reasoning-parts/erdos68/core.tex#L1233-L1233), [cite at paper/reasoning-parts/erdos68/core.tex:1235](../../paper/reasoning-parts/erdos68/core.tex#L1235-L1235)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L668-L671) — lines `668–671`; excerpt `sha256:6e5e795918967c2ca83bcb0a103c3da562b3b3aa08b5719dc822b75f46a612b9`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:468](../../paper/systems/cold-clone-to-proof-receipt.tex#L468-L468)

<a id="source-source-619de19af78c4c"></a>

### [Generating special arithmetic functions by Lambert series factorizations](https://doi.org/10.55016/ojs/cdm.v14i1.62425)

- Source id: `source-619de19af78c4c`
- Author or public identity: M. Merca, M. D. Schmidt
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5331-L5335) — lines `5331–5335`; excerpt `sha256:3a65bfeacf2ad8a25e0f67d84cbd49de341eed686e5744522532edb843972cc8`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L31-L32) — lines `31–32`; excerpt `sha256:140188528cd4d523a62a6c28bd44f3a23efe319654e0e74057b7d9405d24b5e8`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:500](../../paper/archive/erdos249-257-main-paper.tex#L500-L500), [cite at paper/archive/erdos249-257-main-paper.tex:4086](../../paper/archive/erdos249-257-main-paper.tex#L4086-L4086), [cite at paper/archive/erdos249-257-main-paper.tex:4785](../../paper/archive/erdos249-257-main-paper.tex#L4785-L4785)

<a id="source-source-61ce6ad8b2f0ff"></a>

### [Metric properties of polynomials](https://doi.org/10.1007/BF02790232)

- Source id: `source-61ce6ad8b2f0ff`
- Author or public identity: P. Erdős, F. Herzog, G. Piranian
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: The historical formulation of the polynomial short-path question used as the nearest classical boundary in the #1041 Bergman-geodesic dossier. - The unit-disk zero hypothesis, the local definition of \`E(f)\`, and the component-with-two-zeros input described at printed p. 139. - Attribution of that formulation to Erdős, Herzog, and Piranian, with the exact journal, volume, pages, DOI, and receipt/issue dates above. The comment uses the Erdős–Herzog–Piranian scale as a comparison coordinate; it does not assert that the local lemma formalizes their paper.
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

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1371-L1374) — lines `1371–1374`; excerpt `sha256:8a48b0e4aa99b7179cba3135334544de4bd787d26455bdc69f074bafd1695803`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2876-L2879) — lines `2876–2879`; excerpt `sha256:17b9ce182390d749e10c20ef078b7abf4de2319c8819c9796b6ed8eacdf33ae6`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L11-L14) — lines `11–14`; excerpt `sha256:17b9ce182390d749e10c20ef078b7abf4de2319c8819c9796b6ed8eacdf33ae6`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L170-L170) — lines `170–170`; excerpt `sha256:232d22ef9d3f7dddae20fed6168fbaac365ca6dcd9a6354a53e097ecaaafd245`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L877-L877) — lines `877–877`; excerpt `sha256:7017c69d041d5de1602c7d0c0aa782e8f2639bcdd7f243e5daeec0b2da20db57`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L935-L935) — lines `935–935`; excerpt `sha256:ada44e7113aedfe65120a60637f41f11125d8a9f6f73c322c7626c5a9dec27fa`
- [lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean](../../lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean#L47-L52) — lines `47–52`; excerpt `sha256:33cfc2f7e37e3a2c10db006bdf734166bb372b874a1933fa3324a066b6552b44`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:134](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L134-L134), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1319](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1319-L1319)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:213](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L213-L213), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:920](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L920-L920), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:978](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L978-L978), [cite at paper/reasoning-parts/erdos1041/core.tex:170](../../paper/reasoning-parts/erdos1041/core.tex#L170-L170), [cite at paper/reasoning-parts/erdos1041/core.tex:877](../../paper/reasoning-parts/erdos1041/core.tex#L877-L877), [cite at paper/reasoning-parts/erdos1041/core.tex:935](../../paper/reasoning-parts/erdos1041/core.tex#L935-L935)

<a id="source-source-62f9190aeb7d34"></a>

### [On the irrationality of ∑ 1/(q^n+r)](https://doi.org/10.1016/S0022-314X(05)80041-1)

- Source id: `source-62f9190aeb7d34`
- Author or public identity: P. B. Borwein
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
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

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3096-L3100) — lines `3096–3100`; excerpt `sha256:ba25c19782edca439fc59536016a13c5d36a33cd2f359c1c6f2080fb7a229a6d`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L13-L17) — lines `13–17`; excerpt `sha256:ba25c19782edca439fc59536016a13c5d36a33cd2f359c1c6f2080fb7a229a6d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L143-L143) — lines `143–143`; excerpt `sha256:c2aaa0c462b306e178c3f673ec026c7a33d2885dc0bdb20b45061a7ba1d2ad52`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:168](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L168-L168), [cite at paper/reasoning-parts/erdos1049/core.tex:143](../../paper/reasoning-parts/erdos1049/core.tex#L143-L143)

<a id="source-source-6346eeeac5036d"></a>

### [Modular functions and transcendence questions](https://doi.org/10.1070/SM1996v187n09ABEH000158)

- Source id: `source-6346eeeac5036d`
- Author or public identity: Yu. V. Nesterenko
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. The comment explicitly cites Nesterenko (1996) for transcendence of the divisor-series rung and says it is not formalized. The module comment explicitly attributes transcendence of the divisor-series rung to Nesterenko (1996) via E₂(1/2) and marks it cited, not formalized.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5363-L5369) — lines `5363–5369`; excerpt `sha256:77bdb4aaccf3767207aeaa531daa9b36b72b6f99ea6282713f5fedd223ebf6a0`
- [paper/reasoning-parts/erdos249/a249\_p1a.tex](../../paper/reasoning-parts/erdos249/a249_p1a.tex#L344-L344) — lines `344–344`; excerpt `sha256:747da6fbb37188a10edb9105e2c94353783d5cfdd0c69327f19d12704c482230`
- [paper/reasoning-parts/erdos249/a249\_p1b.tex](../../paper/reasoning-parts/erdos249/a249_p1b.tex#L544-L548) — lines `544–548`; excerpt `sha256:1b0f588243d2996619797bb13d0e6110df2fced52fe49f03d0a19033b3d7bf06`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L18396-L18404) — lines `18396–18404`; excerpt `sha256:6d631a23b443180906d917bb60d1a6c65c9fd2a705b5a9ed4ed4e026e91ae20d`
- [lean/Erdos249257/MersenneLambertLadder.lean](../../lean/Erdos249257/MersenneLambertLadder.lean#L15-L27) — lines `15–27`; excerpt `sha256:b17ccf4eb86418af3ba24ecd888e62fe5e23ef5fbf22c02f21fad26eef0562d0`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:529](../../paper/archive/erdos249-257-main-paper.tex#L529-L529), [cite at paper/archive/erdos249-257-main-paper.tex:560](../../paper/archive/erdos249-257-main-paper.tex#L560-L560)

<a id="source-source-6564b203677735"></a>

### [Small gaps between primes](https://doi.org/10.4007/annals.2015.181.1.7)

- Source id: `source-6564b203677735`
- Author or public identity: J. Maynard
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. The countermodel comment names Maynard small/bounded-gap results among theorem families invariant under bounded perturbation; it states a limitation, not a formalization.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1495-L1498) — lines `1495–1498`; excerpt `sha256:1358405e0bd0645ca7abca12c2e3f1406e0c941d1c637f739832e42e53b80a97`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2428-L2431) — lines `2428–2431`; excerpt `sha256:1358405e0bd0645ca7abca12c2e3f1406e0c941d1c637f739832e42e53b80a97`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L71-L74) — lines `71–74`; excerpt `sha256:1358405e0bd0645ca7abca12c2e3f1406e0c941d1c637f739832e42e53b80a97`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1638-L1638) — lines `1638–1638`; excerpt `sha256:1c353b92a6150c3c1fd31caf9ea67c600326deef9ecc2bd683a7fda752871261`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1639-L1641) — lines `1639–1641`; excerpt `sha256:5f61747ac0acd497463a358e52d51e382ac1756c802a14995f9dc17e53475e2a`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L21-L21) — lines `21–21`; excerpt `sha256:07dad1a6dbaa03c54631370154c906de91a50cd710b3b9c6e143f85e14b3c973`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:1279](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1279-L1279), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:1281](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1281-L1281)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1673](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1673-L1673), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1675](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1675-L1675), [cite at paper/reasoning-parts/erdos251/core.tex:1639](../../paper/reasoning-parts/erdos251/core.tex#L1639-L1639), [cite at paper/reasoning-parts/erdos251/core.tex:1641](../../paper/reasoning-parts/erdos251/core.tex#L1641-L1641)

<a id="source-source-685765cbd1ebe2"></a>

### [Quantitative correlations and some problems on prime factors of consecutive integers](https://arxiv.org/abs/2512.01739v2)

- Source id: `source-685765cbd1ebe2`
- Author or public identity: T. Tao, J. Teräväinen
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Attribution to Tao and Teräväinen of the irrationality of the prime-support series at base 2, PDF p. 4, Theorem 1.3 / equation (1.7), with proof on pp. 44–56. - Attribution of the identity between the \`omega\` series and the Lambert prime-support sum, as displayed in PDF p. 4, equation (1.7); the release's own identity bridge remains separately formalised. - Attribution of the quantitative correlation input used in the proof, PDF pp. 24–34, Theorem 3.1, without importing that theorem as a release declaration. - The arXiv version, official retrieval routes, exact digest, and page-level locators recorded above. Source comparison only: the comment aligns the prime-support identity with the Tao–Teräväinen frontier and explicitly declines their analytic input. Source comparison only: the divisor identity is formalized, while the Tao–Teräväinen irrationality input is explicitly not claimed.
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

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5422-L5428) — lines `5422–5428`; excerpt `sha256:f3e98b048d91936f24d3575618c5935a8f710849e94afd0c3c7451115a89db41`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1234-L1242) — lines `1234–1242`; excerpt `sha256:9bd6a4ac3ce8d989e64803da969a9cc0208274609e21b3e829c8b13703504f4e`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L640-L651) — lines `640–651`; excerpt `sha256:dfca4813823f9e6877ab989e482075886ea1c687d9cca66733d6781c929b1cd1`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L1254-L1264) — lines `1254–1264`; excerpt `sha256:f5fb8a3b745a2c9cdda458fb09318e454fffd7f481f16ee58afae4be79a97d8a`
- [paper/reasoning-parts/erdos257/a257\_invent.tex](../../paper/reasoning-parts/erdos257/a257_invent.tex#L388-L400) — lines `388–400`; excerpt `sha256:7ef53f993e91fe109cb6f6239a96266d6de6069c6520d01699336e47d179bd81`
- [paper/reasoning-parts/erdos257/a257\_p5.tex](../../paper/reasoning-parts/erdos257/a257_p5.tex#L59-L63) — lines `59–63`; excerpt `sha256:84126e92b25e21f32af884139ff3674ca28ec4da0be99d314da7e26e60d52332`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9141-L9146) — lines `9141–9146`; excerpt `sha256:c427aea096590bf4f8315ac8e13c2e92925eb10e1f02993b79815bfea6191556`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9651-L9656) — lines `9651–9656`; excerpt `sha256:01736f364c6af6f08a7498583610f9761ec3023900cdc6b3a5a25a416cccbf9e`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:619](../../paper/257/erdos-257-mersenne-support-subseries.tex#L619-L619)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:767](../../paper/archive/erdos249-257-main-paper.tex#L767-L768)

<a id="source-source-6accca20cd5e44"></a>

### [Linear independence results for the values of divisor functions series](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf)

- Source id: `source-6accca20cd5e44`
- Author or public identity: F. Luca, Y. Tachiya
- Kind: `literature`
- Problems: #1049, #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. Comparison/reduction boundary to the Luca–Tachiya mixed-sign periodic-coefficient theorem; the comments explicitly state that the full theorem is not claimed.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5376-L5383) — lines `5376–5383`; excerpt `sha256:690f1f58f32c3dd75fa57e5966f1e713460a42c814f9ab411c04c7e2183ee0b0`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3166-L3172) — lines `3166–3172`; excerpt `sha256:354430e5876812fdea114cb3f1de816f6f07020ab13b9e355babcd01496ccfe4`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L83-L89) — lines `83–89`; excerpt `sha256:354430e5876812fdea114cb3f1de816f6f07020ab13b9e355babcd01496ccfe4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L207-L207) — lines `207–207`; excerpt `sha256:2c897b89adac2b011b3d6ac2d5ea365bf5eb75bf5fafa7a751833dbb731c4afc`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L11735-L11740) — lines `11735–11740`; excerpt `sha256:563923daea706e56c4f2e7175d13053380af2dc3a24ac50d9212c2b0b6d7634e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L12806-L12811) — lines `12806–12811`; excerpt `sha256:448131d83b624b6ce5520dce8ac090fcec58010089d33f41e6a4644fb0ca8a01`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L12962-L12969) — lines `12962–12969`; excerpt `sha256:85e296ca403f80f61aacb885a69266e7645176834ee36a40fbd6e9652cf62bce`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L13680-L13685) — lines `13680–13685`; excerpt `sha256:0de2a3ac66ecee1b3a0e617d573bb7de8678b3975f019984a2d7a83aa43ffbf9`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L14196-L14200) — lines `14196–14200`; excerpt `sha256:12fe3f3b9cef7b6405e234a689ac1e837abfeb24254cb43a2d6815961f8e0b30`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:232](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L232-L232), [cite at paper/reasoning-parts/erdos1049/core.tex:207](../../paper/reasoning-parts/erdos1049/core.tex#L207-L207)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:718](../../paper/archive/erdos249-257-main-paper.tex#L718-L718), [cite at paper/archive/erdos249-257-main-paper.tex:720](../../paper/archive/erdos249-257-main-paper.tex#L720-L720), [cite at paper/archive/erdos249-257-main-paper.tex:724](../../paper/archive/erdos249-257-main-paper.tex#L724-L724), [cite at paper/archive/erdos249-257-main-paper.tex:726](../../paper/archive/erdos249-257-main-paper.tex#L726-L726), [cite at paper/archive/erdos249-257-main-paper.tex:729](../../paper/archive/erdos249-257-main-paper.tex#L729-L729), [cite at paper/archive/erdos249-257-main-paper.tex:3853](../../paper/archive/erdos249-257-main-paper.tex#L3853-L3854), [cite at paper/archive/erdos249-257-main-paper.tex:3859](../../paper/archive/erdos249-257-main-paper.tex#L3859-L3859)

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

<a id="source-source-6c2fbacaba626f"></a>

### [Irrationality of ζ\_q(1) and ζ\_q(2)](https://arxiv.org/abs/math/0604312v1)

- Source id: `source-6c2fbacaba626f`
- Author or public identity: K. Postelmans, W. Van Assche
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. The comment explicitly attributes the q-Padé irrationality result to Postelmans–Van Assche and marks it cited, not formalized. The comment explicitly invokes the Postelmans–Van Assche q-Padé theorem as an external irrationality input and says it is not formalized.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5369-L5376) — lines `5369–5376`; excerpt `sha256:5a1a511c5f97e370e3878ea3ba811d494255649a47bf397f5ba6a6bc5538a1f3`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L18614-L18619) — lines `18614–18619`; excerpt `sha256:1ddc9c03c740ef6c475f6cab866ca8afd592972f666408305d7d85b4399ccba6`
- [lean/Erdos249257/GcdMomentCalculus.lean](../../lean/Erdos249257/GcdMomentCalculus.lean#L31-L37) — lines `31–37`; excerpt `sha256:df63d9348b43000b662da16518b601491c3fd177be47b864cb61bf0db772b86c`
- [lean/Erdos249257/GcdMomentCalculus.lean](../../lean/Erdos249257/GcdMomentCalculus.lean#L210-L216) — lines `210–216`; excerpt `sha256:f2f4533d57864d5d1c1ccb3b19e15365cab99d16e5b432b8737687af0eb24265`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3970](../../paper/archive/erdos249-257-main-paper.tex#L3970-L3971)

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

<a id="source-source-71fb76f6e1363b"></a>

### [Strongly complete sets and a conjecture of Erdős](https://arxiv.org/abs/2607.14071)

- Source id: `source-71fb76f6e1363b`
- Author or public identity: Steve Fan
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Cited by both #269 papers beside the bounded-radix alternative: its Lemma 3.1 makes the exceptional set countable for integer sequences with bounded ratios, and the #269 argument identifies that set for B h\_a as the xi with B h\_a xi eventually integral, which contains S for some B exactly when S is rational. The paper states nothing about #269.
- Source verification: `source\_verified` — The cited preprint's identity, authors, version and the quoted section, lemma, corollary and page locators were directly checked against the v1 PDF. This does not certify the mathematics or imply local adoption.
- Local mapping: `not recorded`

Exact source locations:

- [arXiv v1 (15 July 2026) PDF read in full on 2026-09-15; Lemma 3.1, p. 7, countability of the theta with dist(a\_n theta, Z) -\> 0 for unbounded positive integers with a\_{n+1} \<= lambda a\_n; the paragraph before it credits Eggleston (1952) and Erdős-Taylor (1957); Theorem 1.1 and Corollary 1.2 answer the conjecture listed as Erdős Problem #254.](https://arxiv.org/abs/2607.14071v1)

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2224-L2234) — lines `2224–2234`; excerpt `sha256:6591f6a2f5c12461b4c6f5a379daa0b2e5974bda0b7b7a1919d290e303ecbe83`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L936-L946) — lines `936–946`; excerpt `sha256:6591f6a2f5c12461b4c6f5a379daa0b2e5974bda0b7b7a1919d290e303ecbe83`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L83-L93) — lines `83–93`; excerpt `sha256:6591f6a2f5c12461b4c6f5a379daa0b2e5974bda0b7b7a1919d290e303ecbe83`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L941-L941) — lines `941–941`; excerpt `sha256:f5650658f49332f099ba18d1efff893ea8a24d1fa1e5f5e070be9428da85e16e`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L601-L601) — lines `601–601`; excerpt `sha256:6aa737beb1f1dbcedb949f2b389de77429a1b733a7ec8f6d3cff9daa1c0d72e3`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:601](../../paper/269/erdos-269-three-prime-running-lcm.tex#L601-L601)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:992](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L992-L992), [cite at paper/reasoning-parts/erdos269/core.tex:941](../../paper/reasoning-parts/erdos269/core.tex#L941-L941)

<a id="source-source-741da55b02c5a9"></a>

### [(Non)automaticity of number theoretic functions](https://doi.org/10.5802/jtnb.718)

- Source id: `source-741da55b02c5a9`
- Author or public identity: M. Coons
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Attribution of the theorem that Euler's totient function is not \`k\`-regular for any integer \`k ≥ 2\` to Coons, Theorem 3.2, stated on printed p. 348 and proved on p. 349. - The source-level definition of \`k\`-regularity as finite generation of the \`k\`-kernel over \`ℤ\`, printed p. 348. - The Dirichlet-series identity and proof mechanism used by Coons for the totient non-regularity theorem, printed p. 349. - The published bibliographic identity, official retrieval routes, exact local digest, and conservative rights posture recorded above.
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

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5352-L5358) — lines `5352–5358`; excerpt `sha256:4a7aa0cbb0dba5d29390adbbc95554c796fb3eee93f2efae803d6c97270c9768`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L819-L822) — lines `819–822`; excerpt `sha256:194853409620739b24e9e5f5091f02d4da4f73e1ad951e0d17e4f967d1139524`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L43-L44) — lines `43–44`; excerpt `sha256:e93e9a1a573057be005b8ebb661c5ecca22d1e0bff3fbb42b2512d3f7085d843`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L237-L246) — lines `237–246`; excerpt `sha256:33b525f46eb76dbc41a7fde3ef5d290e0aae4ad21bb44b5cf9e0dc9009986a66`
- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L575-L576) — lines `575–576`; excerpt `sha256:398ca032230c6f56e30b00e6acd398308511c9719a80d6368cab584e770cab4e`
- [paper/reasoning-parts/erdos249/preamble.tex](../../paper/reasoning-parts/erdos249/preamble.tex#L178-L179) — lines `178–179`; excerpt `sha256:0d4b4d5d2a680973d0656d41b77d76e0b096774cd75e73655aeb1334402dc06b`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L169-L169) — lines `169–169`; excerpt `sha256:48a3dc935a9efd4f525b4196ade8751cfd054cab2285d0b3acf1c074f18578f9`
- [paper/reasoning-parts/erdos249/a249\_invent.tex](../../paper/reasoning-parts/erdos249/a249_invent.tex#L727-L733) — lines `727–733`; excerpt `sha256:ada54334fe51c9d8996ba7a8c50ad6589a7ec29353303c2fd70e65fc719dbd60`
- [paper/reasoning-parts/erdos249/a249\_p4.tex](../../paper/reasoning-parts/erdos249/a249_p4.tex#L434-L437) — lines `434–437`; excerpt `sha256:3c22c1483d8b27b07d31075664a6f9d76aeacb994d9934c04e280fe23cd94c3c`
- [paper/reasoning-parts/erdos249/a249\_p4.tex](../../paper/reasoning-parts/erdos249/a249_p4.tex#L521-L522) — lines `521–522`; excerpt `sha256:287e2329dd6f0b29c0f4a3203679ff00fbb12a876b47f08001c265b67446b1e3`
- [paper/reasoning-parts/erdos249/a249\_p5.tex](../../paper/reasoning-parts/erdos249/a249_p5.tex#L595-L595) — lines `595–595`; excerpt `sha256:9bb63e98c41d2fe494420b4de204eb623d74f0573079ceb08b0867b42219d9a8`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:240](../../paper/249/erdos-249-binary-totient-series.tex#L240-L240), [cite at paper/249/erdos-249-binary-totient-series.tex:575](../../paper/249/erdos-249-binary-totient-series.tex#L575-L575)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3187](../../paper/archive/erdos249-257-main-paper.tex#L3187-L3187)

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
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1501-L1505) — lines `1501–1505`; excerpt `sha256:0e32e51882f8449928d597050d67e151bf67b120c65ffffdeb1ad3182cbfbb6a`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:940](../../paper/systems/claim-faithful-publication-systems-paper.tex#L940-L940)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:370](../../paper/systems/open-source-mathematics-strategy.tex#L370-L370), [cite at paper/systems/open-source-mathematics-strategy.tex:982](../../paper/systems/open-source-mathematics-strategy.tex#L982-L982)

<a id="source-source-78565c625f0ea3"></a>

### [On the number of positive integers ≤ x and free of prime factors \> y](https://doi.org/10.1016/0022-314X(86)90013-2)

- Source id: `source-78565c625f0ea3`
- Author or public identity: A. Hildebrand
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2179-L2183) — lines `2179–2183`; excerpt `sha256:5f2f6075d83bb312a4846b05e61dfa0ce46a27bcc5204b3bb36ae704be5bba24`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L38-L42) — lines `38–42`; excerpt `sha256:5f2f6075d83bb312a4846b05e61dfa0ce46a27bcc5204b3bb36ae704be5bba24`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L137-L137) — lines `137–137`; excerpt `sha256:81cc09d42344dba4c01fc04ff310d1a7dcb00b36f50bd511bf86e03f6caa7574`

Paper citation usages:

- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:188](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L188-L188), [cite at paper/reasoning-parts/erdos269/core.tex:137](../../paper/reasoning-parts/erdos269/core.tex#L137-L137)

<a id="source-source-7935fe19eb831b"></a>

### [q-Apéry irrationality proofs by q-WZ pairs](https://arxiv.org/abs/math/9804122)

- Source id: `source-7935fe19eb831b`
- Author or public identity: T. Amdeberhan, D. Zeilberger
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. The comment explicitly compares Van Assche’s diagonal against the Amdeberhan–Zeilberger recurrence and records failure at n=1; this is source comparison, not adoption of the recurrence.
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

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3106-L3111) — lines `3106–3111`; excerpt `sha256:5e80bcb89c7b84fba7acc2b3bfc3cc6b460b903f1bcd6e3fffceae62cd8f68c5`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L23-L28) — lines `23–28`; excerpt `sha256:5e80bcb89c7b84fba7acc2b3bfc3cc6b460b903f1bcd6e3fffceae62cd8f68c5`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L155-L155) — lines `155–155`; excerpt `sha256:75792309c5f22a093e68bc18d6a4e7dd19d522e7ab337a513950b4990527fb0c`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L88-L95) — lines `88–95`; excerpt `sha256:2223d196ea50c7aa4910ff7135c17302d35865756bc58597c18dfb8b05e931ac`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:180](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L180-L180), [cite at paper/reasoning-parts/erdos1049/core.tex:155](../../paper/reasoning-parts/erdos1049/core.tex#L155-L155)

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
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1566-L1571) — lines `1566–1571`; excerpt `sha256:35c50b80ea4e9bece2ad431b8db8fe260367c76ed945564205813263b357e81f`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:126](../../paper/systems/claim-faithful-publication-systems-paper.tex#L126-L126), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:977](../../paper/systems/claim-faithful-publication-systems-paper.tex#L977-L977), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1347](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1347-L1347)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:626](../../paper/systems/open-source-mathematics-strategy.tex#L626-L626), [cite at paper/systems/open-source-mathematics-strategy.tex:706](../../paper/systems/open-source-mathematics-strategy.tex#L706-L706), [cite at paper/systems/open-source-mathematics-strategy.tex:737](../../paper/systems/open-source-mathematics-strategy.tex#L737-L737), [cite at paper/systems/open-source-mathematics-strategy.tex:944](../../paper/systems/open-source-mathematics-strategy.tex#L944-L944)

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

<a id="source-source-7dc956ce55b7a0"></a>

### [On the irrationality of certain series](https://users.renyi.hu/~p_erdos/1969-09.pdf)

- Source id: `source-7dc956ce55b7a0`
- Author or public identity: P. Erdős
- Kind: `literature`
- Problems: #249, #257
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

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5310-L5315) — lines `5310–5315`; excerpt `sha256:87ad1ba0f311b57b61a187d8e3c5bf6b16922e8b73a12590b746f135bbf6f48f`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1258-L1267) — lines `1258–1267`; excerpt `sha256:ad5ccfbcda340d6e818982f18447e527e69cce95965a85312a1c865b3344b858`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L19-L23) — lines `19–23`; excerpt `sha256:b20052cc9aac13a39d09551db2a071d9d9e04bcb94b0e4006e7679ee2329cd33`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L10768-L10777) — lines `10768–10777`; excerpt `sha256:162189e1cf0c892075ed7cffb8ef885d1d9da766b3f16a7a6ae07d5c83afc90e`
- [lean/Erdos249257/CertificateKernel.lean](../../lean/Erdos249257/CertificateKernel.lean#L9741-L9741) — lines `9741–9741`; excerpt `sha256:cdc7c634e30bd34ca3a9b807193c3645b42bcbe20c8c45508b70001c4eae795d`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L132-L136) — lines `132–136`; excerpt `sha256:97fb4fbaf28c47d99e417800ae4398b093aab3336d256f2b9534d0f93cf58c8c`
- [paper/257/erdos257-mersenne-reasoning-surface.tex](../../paper/257/erdos257-mersenne-reasoning-surface.tex#L266-L270) — lines `266–270`; excerpt `sha256:b20052cc9aac13a39d09551db2a071d9d9e04bcb94b0e4006e7679ee2329cd33`
- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L138-L144) — lines `138–144`; excerpt `sha256:ab7fd74fe0eb9c94e53e674e98846dcb41494a1ab47a6b8bed5e364fd738bfb5`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L26-L33) — lines `26–33`; excerpt `sha256:989352be6560cb02802aeb2a564cbd8e365d31c7cd9755f8dcb93af529758e4f`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:134](../../paper/257/erdos-257-mersenne-support-subseries.tex#L134-L134), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:141](../../paper/257/erdos-257-mersenne-support-subseries.tex#L141-L141)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:705](../../paper/archive/erdos249-257-main-paper.tex#L705-L705)

<a id="source-source-7f1f2a3fd9238c"></a>

### [On the length of lemniscates](https://arxiv.org/abs/0805.2295)

- Source id: `source-7f1f2a3fd9238c`
- Author or public identity: A. Eremenko, W. Hayman
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Level-lemniscate upper bound; contextual background rather than a theorem about shortest paths between zeros. The #1041 papers also cite Lemma 5, whose extremal has every critical point on the level curve, as a parallel to the scaled Chebyshev extremal of the sharp collinear theorem.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Introduction and Theorem 1 state the EHP conjecture and prove |E(p)| \<= alpha\_0 d \< 9.173d for monic degree-d polynomials.](https://arxiv.org/abs/0805.2295)
- [Lemma 5 (arXiv v2 p. 5): some extremal polynomial for the level-curve length has all its critical points on E(p) = {|p| = 1}; Lemma 6 (p. 7): some extremal polynomial has connected E(p).](https://arxiv.org/abs/0805.2295)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2923-L2928) — lines `2923–2928`; excerpt `sha256:7331c09baa9a15a659652bbac41137f53a852794fb520657608685d0b161bdb7`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L58-L63) — lines `58–63`; excerpt `sha256:7331c09baa9a15a659652bbac41137f53a852794fb520657608685d0b161bdb7`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L852-L852) — lines `852–852`; excerpt `sha256:06eec9401347e3c0dd864537d4f2ea6a9c860a0eb4161cf8c2d3878c5e0f052e`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1020](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1020-L1020), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1328](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1328-L1329)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:895](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L895-L895), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1288](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1288-L1288), [cite at paper/reasoning-parts/erdos1041/core.tex:852](../../paper/reasoning-parts/erdos1041/core.tex#L852-L852), [cite at paper/reasoning-parts/erdos1041/core.tex:1245](../../paper/reasoning-parts/erdos1041/core.tex#L1245-L1245)

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
- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L643-L648) — lines `643–648`; excerpt `sha256:1f3f3c8f59b09e017af2d71374c7c46368d97929557de076c9b6d0b5f80c83bf`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1395](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1395-L1395)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:446](../../paper/systems/cold-clone-to-proof-receipt.tex#L446-L446)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L665-L668) — lines `665–668`; excerpt `sha256:ebb7c8c62fa7ff44ee571f137c47de8e5508a51405cbdd51807c60b2bad5a1f3`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:465](../../paper/systems/cold-clone-to-proof-receipt.tex#L465-L465)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L671-L674) — lines `671–674`; excerpt `sha256:8662990def0156ee9fa798ccb6915b9367683e2590ac54e5debcf5a71f027cb9`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:468](../../paper/systems/cold-clone-to-proof-receipt.tex#L468-L468)

<a id="source-source-86d1745e2d139b"></a>

### [Irrationality of the reciprocal sum of doubly exponential sequences](https://math.colgate.edu/~integers/aa28/aa28.pdf)

- Source id: `source-86d1745e2d139b`
- Author or public identity: J. Koizumi
- Kind: `literature`
- Problems: #243
- Relationship and boundary: The published source's positive-integer pseudo-greedy framework and its normalized-gap conclusion under the ratio-limit and summability hypotheses. - The exact canonical-coordinate dictionary used by the note to compare Koizumi's \`(c\_n,d\_n,e\_n)\` with its \`(C\_n,D\_n,E\_n)\` state, with the sign convention stated in the note. - Prior art for zero-gap absorption (Lemma 3), eventual nonnegative-gap descent (Proposition 1(2)), and the conditional recurrence statements in Proposition 1/Corollary 4, subject to the published/preprint crosswalk. - The source's publication identity, dates, DOI, official retrieval routes, and exact page-level locators above.
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

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L905-L911) — lines `905–911`; excerpt `sha256:a7fff38b70147af835ec66fe6b2e3f2406eb0739c4c949076fcd9d16cd8929ea`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3027-L3034) — lines `3027–3034`; excerpt `sha256:e5efae2159fedd38b28f94c15c20b2e0e7fbfe89713968189181f2402ba23304`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L33-L40) — lines `33–40`; excerpt `sha256:e5efae2159fedd38b28f94c15c20b2e0e7fbfe89713968189181f2402ba23304`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L586-L586) — lines `586–586`; excerpt `sha256:5f55e922f4e4000c69c443bec4dd3f66f61238dcb912a5f81f4e771c448be455`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L601-L601) — lines `601–601`; excerpt `sha256:221b798d1aad5df29a4d0590491510177e601a46577e9cf4473029732661b81b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L628-L628) — lines `628–628`; excerpt `sha256:5078a17aeb55a1b009a34ca50163f7248edd457704f7f22b741047fd053d4e3b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L633-L633) — lines `633–633`; excerpt `sha256:712f93ad5b4848a4794ef9cdd5643601f29c05fb94281b4ec180fd59a8471088`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L649-L649) — lines `649–649`; excerpt `sha256:01bba2042a372ac238ce77d91f62a6fea18a04334df579f5f6ef7661ad97caca`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L650-L650) — lines `650–650`; excerpt `sha256:d11b7a084474ca7943b0f6468d4efb68b1bcfc4d92558ea5c5bf3bb281034bea`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L653-L653) — lines `653–653`; excerpt `sha256:71060f7d6c73cd364f0c74267bc8d684476c8d1b8212539f3b3a80e1f6231b90`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L659-L659) — lines `659–659`; excerpt `sha256:80ff1c5de38eda3deb617464f28d1489b0602249b272c5d4c980bd809b6d9ca1`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L1603-L1603) — lines `1603–1603`; excerpt `sha256:2ad07416a77899227fd7e2888d66482831b68ceb742e668e0ba07d9514d6ede7`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L1626-L1626) — lines `1626–1626`; excerpt `sha256:eeac143c733145a415a6d53c418cf76281d86d1a95add3fb500723c8b5f17b75`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L1958-L1958) — lines `1958–1958`; excerpt `sha256:defbf180f87e5ba028000d259f179ca3fd71717e5148725119465b34155f9fb2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L1962-L1962) — lines `1962–1962`; excerpt `sha256:bb240f64d97e29cb62798640609aaf6e82822c4dde63673a16ccb026e77fd6e8`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2281-L2281) — lines `2281–2281`; excerpt `sha256:023622060f795bf356ce736a86de990eeeb4f1e751035696204276ab0e835d8f`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2285-L2285) — lines `2285–2285`; excerpt `sha256:8812ed8a7f1053b61926b32196f4c95770e6e55d5b863cf4afce90c7dbd34522`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2298-L2298) — lines `2298–2298`; excerpt `sha256:646ee49259eb30b191c74886cceb51d61b93d0653070c1621a241f120fc627d7`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2344-L2344) — lines `2344–2344`; excerpt `sha256:075ca4776a7543626811b0f79754e35bc339ef0ffdee18fecbe8a672f42727ae`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2346-L2346) — lines `2346–2346`; excerpt `sha256:887bd21b281dce434597c63a46816b5c7649806c1b760cb5928e6a7d6cde15c8`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2612-L2612) — lines `2612–2612`; excerpt `sha256:ade1a9ab17ee7686d6193e846890167f84e666076a76d935baa2a4169820bf32`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2615-L2615) — lines `2615–2615`; excerpt `sha256:663e2c741d9573a39feb67032fb34a9e00cd13d18a94496d64313d05c01ed111`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2623-L2623) — lines `2623–2623`; excerpt `sha256:5ef3af47c1d813f3ef03136859db73357c70bf3bc688b3af1f07c5a89790e242`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:140](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L140-L140), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:343](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L343-L343), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:345](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L345-L345), [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:595](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L595-L595)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:628](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L628-L628), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:643](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L643-L643), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:670](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L670-L670), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:675](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L675-L675), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:691](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L691-L691), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:692](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L692-L692), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:695](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L695-L695), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:701](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L701-L701), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1645](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1645-L1645), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1668](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1668-L1668), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2000](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2000-L2000), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2004](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2004-L2004), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2323](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2323-L2323), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2327](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2327-L2327), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2340](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2340-L2340), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2386](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2386-L2386), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2388](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2388-L2388), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2654](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2654-L2654), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2657](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2657-L2657), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2665](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2665-L2665), [cite at paper/reasoning-parts/erdos243/core.tex:586](../../paper/reasoning-parts/erdos243/core.tex#L586-L586), [cite at paper/reasoning-parts/erdos243/core.tex:601](../../paper/reasoning-parts/erdos243/core.tex#L601-L601), [cite at paper/reasoning-parts/erdos243/core.tex:628](../../paper/reasoning-parts/erdos243/core.tex#L628-L628), [cite at paper/reasoning-parts/erdos243/core.tex:633](../../paper/reasoning-parts/erdos243/core.tex#L633-L633), [cite at paper/reasoning-parts/erdos243/core.tex:649](../../paper/reasoning-parts/erdos243/core.tex#L649-L649), [cite at paper/reasoning-parts/erdos243/core.tex:650](../../paper/reasoning-parts/erdos243/core.tex#L650-L650), [cite at paper/reasoning-parts/erdos243/core.tex:653](../../paper/reasoning-parts/erdos243/core.tex#L653-L653), [cite at paper/reasoning-parts/erdos243/core.tex:659](../../paper/reasoning-parts/erdos243/core.tex#L659-L659), [cite at paper/reasoning-parts/erdos243/core.tex:1603](../../paper/reasoning-parts/erdos243/core.tex#L1603-L1603), [cite at paper/reasoning-parts/erdos243/core.tex:1626](../../paper/reasoning-parts/erdos243/core.tex#L1626-L1626), [cite at paper/reasoning-parts/erdos243/core.tex:1958](../../paper/reasoning-parts/erdos243/core.tex#L1958-L1958), [cite at paper/reasoning-parts/erdos243/core.tex:1962](../../paper/reasoning-parts/erdos243/core.tex#L1962-L1962), [cite at paper/reasoning-parts/erdos243/core.tex:2281](../../paper/reasoning-parts/erdos243/core.tex#L2281-L2281), [cite at paper/reasoning-parts/erdos243/core.tex:2285](../../paper/reasoning-parts/erdos243/core.tex#L2285-L2285), [cite at paper/reasoning-parts/erdos243/core.tex:2298](../../paper/reasoning-parts/erdos243/core.tex#L2298-L2298), [cite at paper/reasoning-parts/erdos243/core.tex:2344](../../paper/reasoning-parts/erdos243/core.tex#L2344-L2344), [cite at paper/reasoning-parts/erdos243/core.tex:2346](../../paper/reasoning-parts/erdos243/core.tex#L2346-L2346), [cite at paper/reasoning-parts/erdos243/core.tex:2612](../../paper/reasoning-parts/erdos243/core.tex#L2612-L2612), [cite at paper/reasoning-parts/erdos243/core.tex:2615](../../paper/reasoning-parts/erdos243/core.tex#L2615-L2615), [cite at paper/reasoning-parts/erdos243/core.tex:2623](../../paper/reasoning-parts/erdos243/core.tex#L2623-L2623)

<a id="source-source-8710374c3e8c9f"></a>

### [Shortest paths in polynomial lemniscate sublevel sets and a problem of Erdős](https://doi.org/10.48550/arXiv.2606.19178)

- Source id: `source-8710374c3e8c9f`
- Author or public identity: V. S. Pendyala
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Direct evidence for the origin-to-boundary filled-sublevel path problem. It is contextual only for corpus problem 1041 unless the paper explicitly explains the relationship.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded` — {'previous\_public\_locator': 'Theorem 1.2 and introductory discussion, pp. 1–2', 'verified\_correction': 'Theorem 1.2 and introductory discussion, printed/PDF pp. 2–3. The source identifies the online problem as #1120.'}

Exact source locations:

- [Introduction, printed/PDF p. 2: states the origin-to-unit-circle shortest-path problem in the filled sublevel set and identifies the distinct level-lemniscate problem.](https://arxiv.org/abs/2606.19178)
- [Definition 1.1 and Theorem 1.2, printed/PDF p. 3: defines S(n) and proves c√log n ≤ S(n) ≤ πn for sufficiently large n.](https://arxiv.org/abs/2606.19178)
- [Reference \[5\], printed/PDF p. 34: identifies the online record as Erdős Problems #1120.](https://arxiv.org/abs/2606.19178)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1384-L1391) — lines `1384–1391`; excerpt `sha256:006b7575e088c1f95193a347caec3ada8681c2e706f2dcd3c3febcde48d3e70d`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1321](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1321-L1321)

<a id="source-source-892c567092d6f3"></a>

### [Lacunary sequences whose reciprocal sums represent all rational numbers in an interval](https://arxiv.org/abs/2509.24971v3)

- Source id: `source-892c567092d6f3`
- Author or public identity: W. van Doorn, V. Kovač
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Prior work cited in the Problem 251 notes beside the interval-filling and divisibility-chain steps of the sparse rationalisation construction. Proposition 8 combines dense filling (Lemma 7) with a divisibility chain among distinguished terms that eventually absorbs every positive integer, so that finite reciprocal sums take every rational value in an interval. The notes use a chain of factorial moduli for eventual congruence preservation of the corrections; the source is cited as a related construction and is not claimed to imply the Problem 251 statement.
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

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1507-L1513) — lines `1507–1513`; excerpt `sha256:520825fff76ae13edf4bf13a5e3ebf355a4a764dc48246e8a6f289f1cabb663c`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2449-L2455) — lines `2449–2455`; excerpt `sha256:520825fff76ae13edf4bf13a5e3ebf355a4a764dc48246e8a6f289f1cabb663c`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L92-L98) — lines `92–98`; excerpt `sha256:520825fff76ae13edf4bf13a5e3ebf355a4a764dc48246e8a6f289f1cabb663c`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L256-L256) — lines `256–256`; excerpt `sha256:aced47a67e42c26231eb70737511e22060c8a227bdeef8365cd5bef03cecb830`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L222-L222) — lines `222–222`; excerpt `sha256:32ea04e51abe835493854beb5440e45e02c513481a497fe6b7ba37f30ad0e4f0`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1068-L1068) — lines `1068–1068`; excerpt `sha256:4bb5c965a6c97930918d73aac6a90230480aa0e07852ddc5f444a141e20b74eb`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L256-L256) — lines `256–256`; excerpt `sha256:32ea04e51abe835493854beb5440e45e02c513481a497fe6b7ba37f30ad0e4f0`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1102-L1102) — lines `1102–1102`; excerpt `sha256:4bb5c965a6c97930918d73aac6a90230480aa0e07852ddc5f444a141e20b74eb`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:256](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L256-L256)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:256](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L256-L256), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1102](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1102-L1102), [cite at paper/reasoning-parts/erdos251/core.tex:222](../../paper/reasoning-parts/erdos251/core.tex#L222-L222), [cite at paper/reasoning-parts/erdos251/core.tex:1068](../../paper/reasoning-parts/erdos251/core.tex#L1068-L1068)

<a id="source-source-8935df46fb4693"></a>

### [The Lambert series factorization theorem](https://doi.org/10.1007/s11139-016-9856-3)

- Source id: `source-8935df46fb4693`
- Author or public identity: M. Merca
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5328-L5331) — lines `5328–5331`; excerpt `sha256:2cc1d6adac4a799350b2f110f64e22883a9a6da730739cce9c316980e35947b3`
- [paper/reasoning-parts/erdos249/a249\_front.tex](../../paper/reasoning-parts/erdos249/a249_front.tex#L29-L30) — lines `29–30`; excerpt `sha256:56e1ac6b69278e9fa06cb47f33076297b2057c32bcc2d977311ed5f788be322d`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:497](../../paper/archive/erdos249-257-main-paper.tex#L497-L497), [cite at paper/archive/erdos249-257-main-paper.tex:498](../../paper/archive/erdos249-257-main-paper.tex#L498-L498), [cite at paper/archive/erdos249-257-main-paper.tex:4085](../../paper/archive/erdos249-257-main-paper.tex#L4085-L4085), [cite at paper/archive/erdos249-257-main-paper.tex:4784](../../paper/archive/erdos249-257-main-paper.tex#L4784-L4784)

<a id="source-source-89b9a294db76bb"></a>

### [The arc length of the lemniscate |p(z)|=1](https://doi.org/10.1090/S0002-9939-1995-1223265-3)

- Source id: `source-89b9a294db76bb`
- Author or public identity: P. Borwein
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2917-L2923) — lines `2917–2923`; excerpt `sha256:67bafe888924ec8db475f42fda3d8d22fd5e0990a9617a787a952754d694b40b`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L52-L58) — lines `52–58`; excerpt `sha256:67bafe888924ec8db475f42fda3d8d22fd5e0990a9617a787a952754d694b40b`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L852-L852) — lines `852–852`; excerpt `sha256:06eec9401347e3c0dd864537d4f2ea6a9c860a0eb4161cf8c2d3878c5e0f052e`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:895](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L895-L895), [cite at paper/reasoning-parts/erdos1041/core.tex:852](../../paper/reasoning-parts/erdos1041/core.tex#L852-L852)

<a id="source-source-8ac37c92429a46"></a>

### Über die einfachen Zahlensysteme

- Source id: `source-8ac37c92429a46`
- Author or public identity: G. Cantor
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L900-L902) — lines `900–902`; excerpt `sha256:f7f783a750919f760d5509a1087835b3e7cbfd988e6d420a29ddd8357a72026c`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1871-L1875) — lines `1871–1875`; excerpt `sha256:03e47315218fee28c4bf66355ea952ff48f9c781e1fbaeeb3d83c6c0bbcb9a85`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L17-L21) — lines `17–21`; excerpt `sha256:03e47315218fee28c4bf66355ea952ff48f9c781e1fbaeeb3d83c6c0bbcb9a85`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L450-L450) — lines `450–450`; excerpt `sha256:dd9a76109764183a9fe95799985a0cd6c89a669403f323d77b3ba19d6145755a`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1226-L1226) — lines `1226–1226`; excerpt `sha256:d4b5fb1dba248888ffd319fc24274a2bcb70de59be08479fc8b9b752fb73f798`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:205](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L205-L205)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:486](../../paper/68/erdos68-factorial-reasoning-surface.tex#L486-L486), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1262](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1262-L1262), [cite at paper/reasoning-parts/erdos68/core.tex:450](../../paper/reasoning-parts/erdos68/core.tex#L450-L450), [cite at paper/reasoning-parts/erdos68/core.tex:1226](../../paper/reasoning-parts/erdos68/core.tex#L1226-L1226)

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
- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L639-L643) — lines `639–643`; excerpt `sha256:bb8a82a2eaf9299171683c436633a3cdfe8688aba06e1bc995a951bd364c907e`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1395](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1395-L1395)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:443](../../paper/systems/cold-clone-to-proof-receipt.tex#L443-L443)

<a id="source-source-951f70d8dfc418"></a>

### [A Degree-Four Lemniscate Path Theorem](https://doi.org/10.48550/arXiv.2606.24875)

- Source id: `source-951f70d8dfc418`
- Author or public identity: V. S. Pendyala
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Direct partial result for Erdős Problem #1041 in degree four. The separate forum contribution announces this preprint and remains a website-contribution row; the literature work itself is directly used by the public #1041 papers.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Theorem 1, PDF p. 1: every monic quartic with its four listed zeros in the open unit disk has two distinct indices joined inside {|f|\<1} by a possibly degenerate polygonal path of length \<2.](https://arxiv.org/abs/2606.24875)
- [Lemma 1, PDF pp. 1–2: four-point radial lemma; proof of Theorem 1, PDF p. 3.](https://arxiv.org/abs/2606.24875)

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1378-L1384) — lines `1378–1384`; excerpt `sha256:46dca09a9b0fb5809f8f4cc07439c501e151481a0c3304742947f4738235bebc`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2897-L2903) — lines `2897–2903`; excerpt `sha256:433341ba84d351b9d52eadb681e82e1b4fd8edf89752e767cd7d9a1b0915c10a`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L32-L38) — lines `32–38`; excerpt `sha256:433341ba84d351b9d52eadb681e82e1b4fd8edf89752e767cd7d9a1b0915c10a`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L204-L204) — lines `204–204`; excerpt `sha256:1ec851451ff3afc8a03f2ce9627c388291130e0150709a0d1912251780bb979f`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L242-L242) — lines `242–242`; excerpt `sha256:b80d03c685f1d8f9618a563d72f37b411f68112263c418010256b4706bc01bcc`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L933-L933) — lines `933–933`; excerpt `sha256:fb236e97c44d5f78380812bdf34804604cbb1b2eb88615d7537a81d827b3d666`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:135](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L135-L135), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:659](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L659-L659), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1320](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1320-L1320)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:247](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L247-L247), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:285](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L285-L285), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:976](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L976-L976), [cite at paper/reasoning-parts/erdos1041/core.tex:204](../../paper/reasoning-parts/erdos1041/core.tex#L204-L204), [cite at paper/reasoning-parts/erdos1041/core.tex:242](../../paper/reasoning-parts/erdos1041/core.tex#L242-L242), [cite at paper/reasoning-parts/erdos1041/core.tex:933](../../paper/reasoning-parts/erdos1041/core.tex#L933-L933)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1505-L1510) — lines `1505–1510`; excerpt `sha256:b08b660d84c300da10b0cff0235eddaac275ba376ce6b7d77fbee66ccfb561fd`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:498](../../paper/systems/open-source-mathematics-strategy.tex#L498-L498), [cite at paper/systems/open-source-mathematics-strategy.tex:808](../../paper/systems/open-source-mathematics-strategy.tex#L808-L808), [cite at paper/systems/open-source-mathematics-strategy.tex:866](../../paper/systems/open-source-mathematics-strategy.tex#L866-L866)

<a id="source-source-96aef073e2ea33"></a>

### [On the irrationality of certain series](https://doi.org/10.1017/S030500410007081X)

- Source id: `source-96aef073e2ea33`
- Author or public identity: P. B. Borwein
- Kind: `literature`
- Problems: #1049, #249, #257
- Relationship and boundary: Attribution to Borwein of the full-support irrationality theorem for \`sum 1/(q^n+c)\` and its alternating companion, printed pp. 142 and 145, with proofs on pp. 142–146. - Attribution of the full-support Mersenne specialization \`q=2\`, \`c=-1\`, printed p. 141 and by Theorem 1 on p. 142. - Attribution of the stronger “not Liouville” conclusion, printed p. 146. - The publication identity, official retrieval routes, exact digest, and page-level locators recorded above.
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

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5322-L5325) — lines `5322–5325`; excerpt `sha256:a2986b3c4ad5444edff29257bbeccf1dbda70fa87ceb63468d3192cdd636ac3b`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3100-L3106) — lines `3100–3106`; excerpt `sha256:62e9f12c9446297c621f7f486af4e1739cd6b6e5b979419191df4d31b8bb4cdc`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L17-L23) — lines `17–23`; excerpt `sha256:62e9f12c9446297c621f7f486af4e1739cd6b6e5b979419191df4d31b8bb4cdc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L169-L169) — lines `169–169`; excerpt `sha256:3db02dadbfb8b1eba6bbbccaefbd67cc49166e13945647c2a97d76dab68cdded`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:194](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L194-L194), [cite at paper/reasoning-parts/erdos1049/core.tex:169](../../paper/reasoning-parts/erdos1049/core.tex#L169-L169)
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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1545-L1551) — lines `1545–1551`; excerpt `sha256:50025897e9875f1e8eb278c5a5c91ea2be1d03b9c7afc2bedf2dcec1c82f6162`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:495](../../paper/systems/open-source-mathematics-strategy.tex#L495-L495), [cite at paper/systems/open-source-mathematics-strategy.tex:669](../../paper/systems/open-source-mathematics-strategy.tex#L669-L669)

<a id="source-source-97b4e6a82335a7"></a>

### [Number of Components of Polynomial Lemniscates: A Problem of Erdős, Herzog, and Piranian](https://arxiv.org/abs/2312.13673)

- Source id: `source-97b4e6a82335a7`
- Author or public identity: S. Ghosh, K. Ramachandran
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2879-L2883) — lines `2879–2883`; excerpt `sha256:c3f90c9e1c7c00acd7dabb104791a3433324b664eedf89d964eda9fe77d7634c`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L14-L18) — lines `14–18`; excerpt `sha256:c3f90c9e1c7c00acd7dabb104791a3433324b664eedf89d964eda9fe77d7634c`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L175-L175) — lines `175–175`; excerpt `sha256:a31377ce95abaee9bd71494227146a76dba56a663a810a6490d255067c2f77cf`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:218](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L218-L218), [cite at paper/reasoning-parts/erdos1041/core.tex:175](../../paper/reasoning-parts/erdos1041/core.tex#L175-L175)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L648-L651) — lines `648–651`; excerpt `sha256:6a2d98ee6e3166e49ad37af7f7fe86c949a4155e4ba493a60d73e7ff90e2c8e9`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1525-L1530) — lines `1525–1530`; excerpt `sha256:a4a2cd5ff74bcf8ec7bc773aba6629192b6c1e90033142603ec6d7509d3e306e`

Paper citation usages:

- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:451](../../paper/systems/cold-clone-to-proof-receipt.tex#L451-L451)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:881](../../paper/systems/open-source-mathematics-strategy.tex#L881-L881)

<a id="source-source-99385343e032a3"></a>

### [Introduction to Analytic Number Theory](https://doi.org/10.1007/978-1-4757-5579-4)

- Source id: `source-99385343e032a3`
- Author or public identity: T. M. Apostol
- Kind: `literature`
- Problems: #269, #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2175-L2179) — lines `2175–2179`; excerpt `sha256:41d6c6f2c2ceeb55582dedbd99f3003f0774006807f24eb9c7d50a8641720580`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L34-L38) — lines `34–38`; excerpt `sha256:41d6c6f2c2ceeb55582dedbd99f3003f0774006807f24eb9c7d50a8641720580`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L193-L193) — lines `193–193`; excerpt `sha256:f1af3289f81080571c3109c6c480c43838a68a8643e4f3567d8da7b027700607`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L194-L194) — lines `194–194`; excerpt `sha256:ae9003df70e006b492fb20f62768c18d36e6b5688b9761956881698ba8882fe8`
- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5325-L5328) — lines `5325–5328`; excerpt `sha256:d83b8379aa5d3a8d993822c9518436371502939df5b9c449f945ffb60730454b`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:495](../../paper/archive/erdos249-257-main-paper.tex#L495-L495), [cite at paper/archive/erdos249-257-main-paper.tex:4084](../../paper/archive/erdos249-257-main-paper.tex#L4084-L4084), [cite at paper/archive/erdos249-257-main-paper.tex:4678](../../paper/archive/erdos249-257-main-paper.tex#L4678-L4678), [cite at paper/archive/erdos249-257-main-paper.tex:4782](../../paper/archive/erdos249-257-main-paper.tex#L4782-L4782)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:244](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L244-L244), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:245](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L245-L245), [cite at paper/reasoning-parts/erdos269/core.tex:193](../../paper/reasoning-parts/erdos269/core.tex#L193-L193), [cite at paper/reasoning-parts/erdos269/core.tex:194](../../paper/reasoning-parts/erdos269/core.tex#L194-L194)

<a id="source-source-99c2f3cb190b95"></a>

### [Comment on Erdős Problem #249](https://www.erdosproblems.com/forum/thread/249)

- Source id: `source-99c2f3cb190b95`
- Author or public identity: S. Fan
- Kind: `literature`
- Problems: #249
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/249/erdos-249-binary-totient-series.tex](../../paper/249/erdos-249-binary-totient-series.tex#L836-L839) — lines `836–839`; excerpt `sha256:0822fac97e86223a8b6f04b6934255a94ff5a1bac5295fa89506967946301d9b`

Paper citation usages:

- `erdos-249-binary-totient-series`: [cite at paper/249/erdos-249-binary-totient-series.tex:544](../../paper/249/erdos-249-binary-totient-series.tex#L544-L544)

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

- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L656-L662) — lines `656–662`; excerpt `sha256:915b21de98fc6d842625837028364b4383eeb5ccd9db3a58c6484bb7d7791545`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1608-L1612) — lines `1608–1612`; excerpt `sha256:7052c9564e3a50f71416b68353c32c939efbb5b719a371014e847871a2e0b349`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1300](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1300-L1300)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:370](../../paper/systems/cold-clone-to-proof-receipt.tex#L370-L370), [cite at paper/systems/cold-clone-to-proof-receipt.tex:457](../../paper/systems/cold-clone-to-proof-receipt.tex#L457-L457)

<a id="source-source-9a38b2d8b0dada"></a>

### [Local gap statistics, telescoping, and normality](https://github.com/StefanRinger/erdos-251)

- Source id: `source-9a38b2d8b0dada`
- Author or public identity: S. Ringer
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Conditional prior work cited beside Land's conditional proof in both Problem 251 notes. Corollary 1.2 claims, under Kuperberg's uniform Hardy-Littlewood Conjecture 1.3, that sum p\_n B^-n is normal to base B for each integer B \>= 2, which gives irrationality at B = 2. The notes cite the claim at that reach; no Problem 251 declaration or proof in this release uses it.
- Source verification: `source\_verified` — Primary preprint PDF (31 pages, dated 11 September 2026, SHA-256 22332707548c833b691a20e9d7e03a548478f49ac85cb5a54a18ba5ec1b5c989, repository commit d2c92e2795) read on 15 September 2026 at the abstract, Section 1, Section 3, Sections 5.2 to 5.4, Section 6 and Appendix C, together with the Lean definition of KuperbergConj13 and the recorded endpoint audit. The proof was not checked in full and the Lean build was not replayed; the stated relation bounds what the notes use.
- Local mapping: `not recorded`

Exact source locations:

- [PDF p. 3, Theorem 1.1 and Corollary 1.2: under the one-sided averaged prime-tuples hypothesis, periodic local polynomial prime-gap series are rational or normal; Corollary 1.2 gives normality of sum p\_n B^-n to base B, and Kuperberg's conjecture suffices for every integer B \>= 2.](https://github.com/StefanRinger/erdos-251/blob/main/paper/prime_gap_normality.pdf)
- [PDF pp. 19-20, Section 5.4: Kuperberg's Conjecture 1.3 (arXiv:2210.09775v2, equation (7)) implies the averaged hypothesis for every fixed kappa.](https://github.com/StefanRinger/erdos-251/blob/main/paper/prime_gap_normality.pdf)
- [PDF pp. 26-28, Appendix C, Proposition C.1 on p. 27: sum p\_n B^-S\_n with S\_n = sum\_{j\<=n} ceil(log\_B log(j+3)) is unconditionally normal to base B.](https://github.com/StefanRinger/erdos-251/blob/main/paper/prime_gap_normality.pdf)
- [KuperbergConj13 is a named Prop matching Conjecture 1.3 of Kuperberg; the recorded audit lean/verification/completed/theorem-types-and-axioms.txt prints CorePeriodicPositionEnd.primePositionSeries\_isNormal\_of\_kuperberg with hypothesis KuperbergConj13 and axioms propext, Classical.choice and Quot.sound.](https://github.com/StefanRinger/erdos-251/blob/main/lean/PrimeGapNormality/Prime/EndAPI.lean)

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L243-L243) — lines `243–243`; excerpt `sha256:323896dce33542d7bd7cd68f31a2c7e24cee89ffada5c03a0bd0d7f4405b611a`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1535-L1540) — lines `1535–1540`; excerpt `sha256:18b752a670839499271bf40d34efd558f0c8b6e362e184f1f87d874563e9802d`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L170-L170) — lines `170–170`; excerpt `sha256:a2f206ac21fff6f2267ad6f8e8356cf9f48e3502f213eec5b7c4fabbe6859d92`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2487-L2501) — lines `2487–2501`; excerpt `sha256:a4410d16482c8375dfec04ae7e1f6a579833905a820d03f4ba0d6f1d652e86fa`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L136-L136) — lines `136–136`; excerpt `sha256:a2f206ac21fff6f2267ad6f8e8356cf9f48e3502f213eec5b7c4fabbe6859d92`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L130-L144) — lines `130–144`; excerpt `sha256:a4410d16482c8375dfec04ae7e1f6a579833905a820d03f4ba0d6f1d652e86fa`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:243](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L243-L243)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:170](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L170-L170), [cite at paper/reasoning-parts/erdos251/core.tex:136](../../paper/reasoning-parts/erdos251/core.tex#L136-L136)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1596-L1601) — lines `1596–1601`; excerpt `sha256:a2823f7bc0eabe07dcb16e2476c88ca0a6ae7777617c24762b0674c83ce2e1da`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:828](../../paper/systems/open-source-mathematics-strategy.tex#L828-L828)

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
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1571-L1576) — lines `1571–1576`; excerpt `sha256:17dfc81b2347996ae518d9ae35b9f4cbbe428802c4df971c821bb500a90d87de`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:977](../../paper/systems/claim-faithful-publication-systems-paper.tex#L977-L977), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1308](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1308-L1308), [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1355](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1355-L1355)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:586](../../paper/systems/open-source-mathematics-strategy.tex#L586-L586), [cite at paper/systems/open-source-mathematics-strategy.tex:637](../../paper/systems/open-source-mathematics-strategy.tex#L637-L637), [cite at paper/systems/open-source-mathematics-strategy.tex:715](../../paper/systems/open-source-mathematics-strategy.tex#L715-L715), [cite at paper/systems/open-source-mathematics-strategy.tex:843](../../paper/systems/open-source-mathematics-strategy.tex#L843-L843), [cite at paper/systems/open-source-mathematics-strategy.tex:956](../../paper/systems/open-source-mathematics-strategy.tex#L956-L956)

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
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1581-L1586) — lines `1581–1586`; excerpt `sha256:d7199ff140a739a7be732b44e20113885c623918791626d0f99bd6c7e2a83cc2`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1312](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1312-L1312)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:663](../../paper/systems/open-source-mathematics-strategy.tex#L663-L663), [cite at paper/systems/open-source-mathematics-strategy.tex:902](../../paper/systems/open-source-mathematics-strategy.tex#L902-L902)

<a id="source-source-a67b8dc01791ec"></a>

### [New estimates for the length of the Erdős–Herzog–Piranian lemniscate](https://arxiv.org/abs/0808.0717)

- Source id: `source-a67b8dc01791ec`
- Author or public identity: Alexander Fryntov, Fedor Nazarov
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Level-lemniscate prior art; contextual background rather than a theorem about shortest paths between zeros.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Introduction surveys the EHP level-lemniscate problem and states the paper proves local maximality of z^n-1 and an upper bound 2n+o(n).](https://arxiv.org/abs/0808.0717)
- [Published version: Linear and Complex Analysis, Amer. Math. Soc. Transl. Ser. 2 226, Amer. Math. Soc., Providence, RI, 2009, pp. 49-60 (Crossref record for DOI 10.1090/trans2/226/05; zbMATH 1181.30002). The long record cites this venue together with arXiv:0808.0717.](https://doi.org/10.1090/trans2/226/05)

Public implementation or evidence coordinates:

- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2928-L2936) — lines `2928–2936`; excerpt `sha256:9ef2695d2a8d25816aec7c48ef5bce71a29f916651b36523244551cd0b67b823`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L63-L71) — lines `63–71`; excerpt `sha256:9ef2695d2a8d25816aec7c48ef5bce71a29f916651b36523244551cd0b67b823`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L853-L853) — lines `853–853`; excerpt `sha256:fd9c0a34811762e7802c34c4f1519eff9d6f7e2f9d58289d888b9f4eb512f6b4`

Paper citation usages:

- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:896](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L896-L896), [cite at paper/reasoning-parts/erdos1041/core.tex:853](../../paper/reasoning-parts/erdos1041/core.tex#L853-L853)

<a id="source-source-a87fa25f28c7b0"></a>

### [Irrationality of certain infinite series II](https://doi.org/10.1524/anly.2011.1094)

- Source id: `source-a87fa25f28c7b0`
- Author or public identity: W. Koepf, D. Schmersau
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1891-L1896) — lines `1891–1896`; excerpt `sha256:65ce1984f1a5bc8f6bf31f7b2dc8c91bbfec5a192332d2d80f497808ac90298d`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L37-L42) — lines `37–42`; excerpt `sha256:65ce1984f1a5bc8f6bf31f7b2dc8c91bbfec5a192332d2d80f497808ac90298d`
- [paper/reasoning-parts/erdos68/extended\_record.tex](../../paper/reasoning-parts/erdos68/extended_record.tex#L55-L55) — lines `55–55`; excerpt `sha256:819b066e2ecb846b8387587d00825a6a7dc47bf98551fff676dcbfe8c196f80a`
- [paper/reasoning-parts/erdos68/extended\_record.tex](../../paper/reasoning-parts/erdos68/extended_record.tex#L58-L58) — lines `58–58`; excerpt `sha256:472d0415e9ece4e42b91516ad66a08857bc40220ee8682d1f1edbcbb1659d49e`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1399](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1399-L1399), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1402](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1402-L1402), [cite at paper/reasoning-parts/erdos68/extended\_record.tex:55](../../paper/reasoning-parts/erdos68/extended_record.tex#L55-L55), [cite at paper/reasoning-parts/erdos68/extended\_record.tex:58](../../paper/reasoning-parts/erdos68/extended_record.tex#L58-L58)

<a id="source-source-aa2d5c249362f1"></a>

### [Zero Coefficients of Rational Power Series and Rational Lambert Series](https://arxiv.org/abs/2604.25151)

- Source id: `source-aa2d5c249362f1`
- Author or public identity: I. Rivin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3172-L3177) — lines `3172–3177`; excerpt `sha256:2d8704f9fd85012ec1f6f999666aeea29f54fc183b19717abba7a33de88a8f71`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L89-L94) — lines `89–94`; excerpt `sha256:2d8704f9fd85012ec1f6f999666aeea29f54fc183b19717abba7a33de88a8f71`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L127-L127) — lines `127–127`; excerpt `sha256:b5343bdda9eb10f05393fa410f344c3530bbc1327366be45d9704d78b9f6444d`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L132-L132) — lines `132–132`; excerpt `sha256:dfa7085590f70ee1f427373ade48dba5016bb3538108b3756725573ffbee56ea`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2749-L2749) — lines `2749–2749`; excerpt `sha256:04460620821776cd394a005083318c889c68c93c4a7b5c16d5dc341484037d26`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:152](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L152-L152), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:157](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L157-L157), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2774](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2774-L2774), [cite at paper/reasoning-parts/erdos1049/core.tex:127](../../paper/reasoning-parts/erdos1049/core.tex#L127-L127), [cite at paper/reasoning-parts/erdos1049/core.tex:132](../../paper/reasoning-parts/erdos1049/core.tex#L132-L132), [cite at paper/reasoning-parts/erdos1049/core.tex:2749](../../paper/reasoning-parts/erdos1049/core.tex#L2749-L2749)

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
- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L679-L683) — lines `679–683`; excerpt `sha256:3a090cc943cde6fe32e768b3fec5c8f9941b86fe85cffb0b1e502eff8703ea31`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1556-L1561) — lines `1556–1561`; excerpt `sha256:cbc96d2ca058731561fda44e70b5d2f239fbaf14f1de0bb2732381fdead4b7fe`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1403](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1403-L1403)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:491](../../paper/systems/cold-clone-to-proof-receipt.tex#L491-L491)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:891](../../paper/systems/open-source-mathematics-strategy.tex#L891-L891)

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
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1551-L1556) — lines `1551–1556`; excerpt `sha256:ba3b7d334c4533a7eb892544f07793a641502451252ef40f9dd35e8d49823e68`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1304](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1304-L1304)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:889](../../paper/systems/open-source-mathematics-strategy.tex#L889-L889)

<a id="source-source-ae9859af28fdcd"></a>

### [On the irrationality of generalized q-logarithm](https://arxiv.org/abs/1601.02688)

- Source id: `source-ae9859af28fdcd`
- Author or public identity: W. Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Primary source of the normalised Hankel determinant V\_N^\* and its q-order inequality, the antecedent of the #1049 sharp-order theorem, and of the Section 2 remark (arXiv v2 p. 4) on non-integer rational bases with an unspecified computable constant. The tracked source closure records the arXiv v2 locators and the attribution ceiling. The comments connect the normalized Hankel construction/order bound to Zudilin’s 2016 generalized q-logarithm paper. The local work sharpens or completes algebraic coefficient statements and does not silently import analytic asymptotics. The definition is explicitly Zudilin’s normalized Hankel determinant within the module whose header identifies the 2016 source and section.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [Reading status: complete arXiv v2 PDF read from rendered pages; page references are to that version.](https://arxiv.org/abs/1601.02688)
- [Section 2, arXiv v2 p. 4, paragraph beginning 'Finally, we remark': non-integer p = r/s under log|r| \> c log|s| with c computable and unspecified.](https://arxiv.org/abs/1601.02688)
- [Section 4, (6)–(8) and Lemma 1, arXiv v2 pp. 6–8: normalised moments, backward-shift operator and the q-order inequality for V\_n^\*.](https://arxiv.org/abs/1601.02688)

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L973-L984) — lines `973–984`; excerpt `sha256:be0da1a7ed806e19dbd7d03c5ebef8d7b1bb7c9df9bb3f56f66f7ac7c36987a1`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3121-L3132) — lines `3121–3132`; excerpt `sha256:3796633e94db161e5510b162d2a9d0f0f8e5ba2d689356d8c5278a6d95c40429`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L38-L49) — lines `38–49`; excerpt `sha256:3796633e94db161e5510b162d2a9d0f0f8e5ba2d689356d8c5278a6d95c40429`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L236-L236) — lines `236–236`; excerpt `sha256:7f7b7e03e5c722d8297c8cf2da6d8eb4158df6a60047dc0a2affeab27fe55bd9`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L923-L923) — lines `923–923`; excerpt `sha256:3e98a97c395214cdb4ed51c973a3d6eac7d63374f7409fd37c5d693242008cc6`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1364-L1364) — lines `1364–1364`; excerpt `sha256:33ee2f9a69f1ef1092a438ef1e40bedf0229f951312ecf0a04112573693455d3`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1374-L1374) — lines `1374–1374`; excerpt `sha256:16a8294cc2c54d3e9c3a0ff2463e78c32cea842f7dc1abc67eeeb715c487cd0e`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1389-L1389) — lines `1389–1389`; excerpt `sha256:9c9f4ab17e2bd61028893e5453258ab9f963a6a4c5391bcfebd52882c8970f9a`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1578-L1578) — lines `1578–1578`; excerpt `sha256:84baaf0fba645123571d368f33d5c2b16dd3bd0252e8bf3531fcf64cfc3604d3`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L3-L12) — lines `3–12`; excerpt `sha256:2c6a0d27c905ea48c1f25e9aa96f3007e323409c7b093d69e63e5d6389c5dd78`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L294-L341) — lines `294–341`; excerpt `sha256:079ff692126bd3e4d34f548fea370a492cd0c13ef7f93ce3fb3dd3ad6697e51f`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L1373-L1380) — lines `1373–1380`; excerpt `sha256:00ffa8698a1534c856de8c5358848f0e1631280815d61cd62dccca5b31c96703`
- [lean/ErdosProblems/Erdos1049/AdelicHeightBridge.lean](../../lean/ErdosProblems/Erdos1049/AdelicHeightBridge.lean#L177-L184) — lines `177–184`; excerpt `sha256:48cded238c23f3b69267c7634831949873ba61edbfc1d81d7be4e4f53a9dfa1f`
- [lean/ErdosProblems/Erdos1049/AllRow/Producer.lean](../../lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L139-L144) — lines `139–144`; excerpt `sha256:d91ba4591cce7012da8fb4b68e2c502744e2a86cbff69f02ac661f05bbbc77f0`
- [lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean](../../lean/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean#L675-L679) — lines `675–679`; excerpt `sha256:f4bd612442f7360245d4b631cbdc499c687fc3d6d13818a39db22dc67e091077`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:308](../../paper/1049/erdos-1049-rational-base-lambert.tex#L308-L308), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:375](../../paper/1049/erdos-1049-rational-base-lambert.tex#L375-L375), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:455](../../paper/1049/erdos-1049-rational-base-lambert.tex#L455-L455), [cite at paper/1049/erdos-1049-rational-base-lambert.tex:467](../../paper/1049/erdos-1049-rational-base-lambert.tex#L467-L467)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:261](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L261-L261), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:413](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L413-L413), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:948](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L948-L948), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1389](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1389-L1389), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1399](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1399-L1399), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1414](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1414-L1414), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1603](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1603-L1603), [cite at paper/reasoning-parts/erdos1049/core.tex:236](../../paper/reasoning-parts/erdos1049/core.tex#L236-L236), [cite at paper/reasoning-parts/erdos1049/core.tex:388](../../paper/reasoning-parts/erdos1049/core.tex#L388-L388), [cite at paper/reasoning-parts/erdos1049/core.tex:923](../../paper/reasoning-parts/erdos1049/core.tex#L923-L923), [cite at paper/reasoning-parts/erdos1049/core.tex:1364](../../paper/reasoning-parts/erdos1049/core.tex#L1364-L1364), [cite at paper/reasoning-parts/erdos1049/core.tex:1374](../../paper/reasoning-parts/erdos1049/core.tex#L1374-L1374), [cite at paper/reasoning-parts/erdos1049/core.tex:1389](../../paper/reasoning-parts/erdos1049/core.tex#L1389-L1389), [cite at paper/reasoning-parts/erdos1049/core.tex:1578](../../paper/reasoning-parts/erdos1049/core.tex#L1578-L1578)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1515-L1520) — lines `1515–1520`; excerpt `sha256:6f2b691dbea0a4758a07048f06dca1acfc4049444971d8bdfab57f8bf75e6a02`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:496](../../paper/systems/open-source-mathematics-strategy.tex#L496-L496), [cite at paper/systems/open-source-mathematics-strategy.tex:874](../../paper/systems/open-source-mathematics-strategy.tex#L874-L874)

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

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L876-L880) — lines `876–880`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3003-L3007) — lines `3003–3007`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L9-L13) — lines `9–13`; excerpt `sha256:7e406b0aaf4be781c7d44c0d88c7d8424cafe45f2e1ee6201c506e6e8ce0de06`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L612-L612) — lines `612–612`; excerpt `sha256:041b2b0724ccd906861e8883f033bba1d825fd23b427fc24c8b01a0224a1788f`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2671-L2671) — lines `2671–2671`; excerpt `sha256:dcf5805cdc2b24f32e9bcb43272cc7feb8a413d7ae8078b50aee921519da62f3`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1896-L1901) — lines `1896–1901`; excerpt `sha256:93b82e07532c595ce8c3e4690e48b8f8b4b955a46be725042a411f3faf1dabad`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L42-L47) — lines `42–47`; excerpt `sha256:93b82e07532c595ce8c3e4690e48b8f8b4b955a46be725042a411f3faf1dabad`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1113-L1113) — lines `1113–1113`; excerpt `sha256:a353bbd5216870d1d4db2700320a361f4a38d8923d21a55f93745248f5957a1e`
- [paper/reasoning-parts/erdos68/extended\_record.tex](../../paper/reasoning-parts/erdos68/extended_record.tex#L72-L72) — lines `72–72`; excerpt `sha256:9a6d1ba3cc568516fc81678999198956a9c082d92662305c9a4757521dbcc86b`
- [paper/reasoning-parts/erdos68/extended\_record.tex](../../paper/reasoning-parts/erdos68/extended_record.tex#L74-L74) — lines `74–74`; excerpt `sha256:49b4c4990a972092e57e88f2cbed81e5d7f8af754494e5211f82ce3f7c241eff`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:560](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L560-L560)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:654](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L654-L654), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2713](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2713-L2713), [cite at paper/reasoning-parts/erdos243/core.tex:612](../../paper/reasoning-parts/erdos243/core.tex#L612-L612), [cite at paper/reasoning-parts/erdos243/core.tex:2671](../../paper/reasoning-parts/erdos243/core.tex#L2671-L2671)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1149](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1149-L1149), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1416](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1416-L1416), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1418](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1418-L1418), [cite at paper/reasoning-parts/erdos68/core.tex:1113](../../paper/reasoning-parts/erdos68/core.tex#L1113-L1113), [cite at paper/reasoning-parts/erdos68/extended\_record.tex:72](../../paper/reasoning-parts/erdos68/extended_record.tex#L72-L72), [cite at paper/reasoning-parts/erdos68/extended\_record.tex:74](../../paper/reasoning-parts/erdos68/extended_record.tex#L74-L74)

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

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1531-L1535) — lines `1531–1535`; excerpt `sha256:65d97a24898b9cf4b66cf98d8960c881e75b5eab750754664bbd7a968dfccc61`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2483-L2487) — lines `2483–2487`; excerpt `sha256:65d97a24898b9cf4b66cf98d8960c881e75b5eab750754664bbd7a968dfccc61`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L126-L130) — lines `126–130`; excerpt `sha256:65d97a24898b9cf4b66cf98d8960c881e75b5eab750754664bbd7a968dfccc61`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L228-L228) — lines `228–228`; excerpt `sha256:c384e283f82a7af357601d537bf3fea0643aec17edef2b2d3fe55664a758a772`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1531-L1533) — lines `1531–1533`; excerpt `sha256:169850d8c7256693be47fa564c61523bcb8732119a4097833460d59e5ed9722e`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L262-L262) — lines `262–262`; excerpt `sha256:c384e283f82a7af357601d537bf3fea0643aec17edef2b2d3fe55664a758a772`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:262](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L262-L262), [cite at paper/reasoning-parts/erdos251/core.tex:228](../../paper/reasoning-parts/erdos251/core.tex#L228-L228)

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
- Relationship and boundary: Attribution to Erdős of the printed open subseries question on p. 105: whether every increasing infinite support gives irrational \`sum\_k 1/(2^ n\_k -1)\`. - Attribution to Erdős of the density/LCM irrationality theorem on p. 106, with proof on pp. 106–108, including its prime-generated LCM specialization. - Attribution of the historical full-support divisor-series context on p. 102 and the squarefree-subsequence question on p. 103. - The publication identity, official retrieval routes, exact digest, and page-level locators recorded above.
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

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5318-L5322) — lines `5318–5322`; excerpt `sha256:ef4a3136894b8a7edf6c08674740c39ae6802868494e203a59f1f0b740884aad`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L893-L898) — lines `893–898`; excerpt `sha256:384777592d7ca1953cae0bd40238b8fd41ad0252431a1f5ebc4ab35e4a06e0fb`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1859-L1864) — lines `1859–1864`; excerpt `sha256:384777592d7ca1953cae0bd40238b8fd41ad0252431a1f5ebc4ab35e4a06e0fb`
- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L888-L892) — lines `888–892`; excerpt `sha256:41e22e226dc64038986bc97224c7c1ea74fb8cc5b4b7ea1ff0ba5a1e7b45d2c2`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L3015-L3019) — lines `3015–3019`; excerpt `sha256:41e22e226dc64038986bc97224c7c1ea74fb8cc5b4b7ea1ff0ba5a1e7b45d2c2`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1455-L1459) — lines `1455–1459`; excerpt `sha256:8d4a8df5b565485d5e5da0fb889c4c30a0c531c8a743b1dbbcb0846f7e3591d9`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2382-L2386) — lines `2382–2386`; excerpt `sha256:8d4a8df5b565485d5e5da0fb889c4c30a0c531c8a743b1dbbcb0846f7e3591d9`
- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2152-L2156) — lines `2152–2156`; excerpt `sha256:a90e34ce2e35d3da0f95095189eabd8008b453ab0d87c7cf0a45afa3570b26a8`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L891-L895) — lines `891–895`; excerpt `sha256:a90e34ce2e35d3da0f95095189eabd8008b453ab0d87c7cf0a45afa3570b26a8`
- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L959-L963) — lines `959–963`; excerpt `sha256:46dc589925f18c98a38b701dc32978cf7bf47298f8b19fc97e2d6eb3b37ddaf2`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3092-L3096) — lines `3092–3096`; excerpt `sha256:5dc4499ba85b2a90c1b7eeae654d404e424be3f9aa288c8eaf30e698ab7cf0e8`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L9-L13) — lines `9–13`; excerpt `sha256:5dc4499ba85b2a90c1b7eeae654d404e424be3f9aa288c8eaf30e698ab7cf0e8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L75-L75) — lines `75–75`; excerpt `sha256:daac0a1d16bf29ee1a7aed78143060b303b0c73e76e968b083ac1748e249105f`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L21-L25) — lines `21–25`; excerpt `sha256:41e22e226dc64038986bc97224c7c1ea74fb8cc5b4b7ea1ff0ba5a1e7b45d2c2`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L51-L51) — lines `51–51`; excerpt `sha256:9c42837d94aa7d1ca926321ef5d654bda8824ed8ae366ebbf300800861bb51e4`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L598-L598) — lines `598–598`; excerpt `sha256:4bda527bbb4746f493a2fd85d3a740e85652145cfb20dca2bcc3fa8d61b23ba8`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L25-L29) — lines `25–29`; excerpt `sha256:8d4a8df5b565485d5e5da0fb889c4c30a0c531c8a743b1dbbcb0846f7e3591d9`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L75-L75) — lines `75–75`; excerpt `sha256:02ed6bcbdbc2c49a0e95f21795213eb082af576912e51a5898223bdd839badc9`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L158-L158) — lines `158–158`; excerpt `sha256:19a056c58763e14581889e2e28ef44c1d735cec40cb254be4158d1b3a4b7b499`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L11-L15) — lines `11–15`; excerpt `sha256:a90e34ce2e35d3da0f95095189eabd8008b453ab0d87c7cf0a45afa3570b26a8`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L53-L53) — lines `53–53`; excerpt `sha256:d0733b0ee5c6accbfe80049f5f21794ad925c50ddd26f96b9cfd62ade1f3a3b8`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L61-L61) — lines `61–61`; excerpt `sha256:b9a175eea36fa063b0845bbf4e2980291a1e39015740f460adf814ebac28ad71`
- [paper/reasoning-parts/erdos269/extended\_record.tex](../../paper/reasoning-parts/erdos269/extended_record.tex#L14-L14) — lines `14–14`; excerpt `sha256:01ea1302f491d05276c72ef1a0c703180655e91678a98fbbb0f98fef9d2dd4d8`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L5-L10) — lines `5–10`; excerpt `sha256:384777592d7ca1953cae0bd40238b8fd41ad0252431a1f5ebc4ab35e4a06e0fb`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L52-L52) — lines `52–52`; excerpt `sha256:104a79c4c79eea46f102eaa2900c4d9ba3c623a39f852f60a382f3690faadb3f`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:61](../../paper/1049/erdos-1049-rational-base-lambert.tex#L61-L61)
- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:234](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L234-L234)
- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:66](../../paper/269/erdos-269-three-prime-running-lcm.tex#L66-L66)
- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:87](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L87-L87)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:100](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L100-L100), [cite at paper/reasoning-parts/erdos1049/core.tex:75](../../paper/reasoning-parts/erdos1049/core.tex#L75-L75)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:93](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L93-L93), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:640](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L640-L640), [cite at paper/reasoning-parts/erdos243/core.tex:51](../../paper/reasoning-parts/erdos243/core.tex#L51-L51), [cite at paper/reasoning-parts/erdos243/core.tex:598](../../paper/reasoning-parts/erdos243/core.tex#L598-L598)
- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:193](../../paper/archive/erdos249-257-main-paper.tex#L193-L193), [cite at paper/archive/erdos249-257-main-paper.tex:195](../../paper/archive/erdos249-257-main-paper.tex#L195-L195)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:109](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L109-L109), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:192](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L192-L192), [cite at paper/reasoning-parts/erdos251/core.tex:75](../../paper/reasoning-parts/erdos251/core.tex#L75-L75), [cite at paper/reasoning-parts/erdos251/core.tex:158](../../paper/reasoning-parts/erdos251/core.tex#L158-L158)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:104](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L104-L104), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:112](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L112-L112), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:1700](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L1700-L1700), [cite at paper/reasoning-parts/erdos269/core.tex:53](../../paper/reasoning-parts/erdos269/core.tex#L53-L53), [cite at paper/reasoning-parts/erdos269/core.tex:61](../../paper/reasoning-parts/erdos269/core.tex#L61-L61), [cite at paper/reasoning-parts/erdos269/extended\_record.tex:14](../../paper/reasoning-parts/erdos269/extended_record.tex#L14-L14)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:88](../../paper/68/erdos68-factorial-reasoning-surface.tex#L88-L88), [cite at paper/reasoning-parts/erdos68/core.tex:52](../../paper/reasoning-parts/erdos68/core.tex#L52-L52)

<a id="source-source-b3b7518e07e159"></a>

### [On the irrationality of certain p-adic zeta values](https://arxiv.org/abs/2505.23088v1)

- Source id: `source-b3b7518e07e159`
- Author or public identity: L. Lai, C. Lupu, J. Sprang
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited in both #68 manuscripts as a comparison for the difference between a common-denominator bound and the denominator after reduction: for their linear forms in p-adic zeta values the lcm-power denominator bound is divided by a quantified product Phi\_n. No result of the paper is applied to the #68 series, and the manuscripts establish no asymptotic saving of this kind for its prefixes.
- Source verification: `source\_verified` — arXiv v1 PDF read in full (24 pages). Locators refer to arXiv v1; the published numbering was not compared.
- Local mapping: `not recorded`

Exact source locations:

- [Lemma 2.1, arXiv v1 p. 3, quoted there from L. Lai, Int. J. Number Theory 21 (2025), Lemma 2.1: if integer linear forms L\_n satisfy max\_i |l\_(i,n)| |L\_n(xi)|\_p -\> 0 along an unbounded set of n and L\_n(xi) != 0 there, then some xi\_i is irrational.](https://arxiv.org/abs/2505.23088v1)
- [Section 5, arXiv v1 pp. 10-14: Lemma 5.3 bounds the coefficient denominators by powers of d\_n = lcm(1,...,n); Lemmas 5.4-5.7 show that the cleared coefficients remain integral after division by Phi\_n, a product of powers of primes in (sqrt(pn), n\].](https://arxiv.org/abs/2505.23088v1)
- [Lemma 7.3, arXiv v1 p. 20, and inequality (8.1), p. 22: Phi\_n = exp(varpi\_p n + o(n)), and varpi\_p enters the inequality under which the rescaled forms Phi\_n^(-1) d\_n^(p-1+s) S\_n, which have integer coefficients, meet the criterion quoted in Lemma 2.1.](https://arxiv.org/abs/2505.23088v1)

Public implementation or evidence coordinates:

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L925-L933) — lines `925–933`; excerpt `sha256:0e1f48f41e46b5c64d0cc85d3164c9734d7fecd48fade710c1be05849766f934`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1926-L1934) — lines `1926–1934`; excerpt `sha256:77ec5a44baf12f7af52bf93ecd994b0c2597959d104f9e8f9bdd08fd52379874`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L72-L80) — lines `72–80`; excerpt `sha256:77ec5a44baf12f7af52bf93ecd994b0c2597959d104f9e8f9bdd08fd52379874`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L556-L556) — lines `556–556`; excerpt `sha256:29c6295fe12a4c23fbbcbfee9ae1abbe9bb1303b92c758ba5c17224ea9366867`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L557-L557) — lines `557–557`; excerpt `sha256:58bff556d3afc6a56c40480db1cf367a4324aa5a5dbf016717484c0015aad37a`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L558-L558) — lines `558–558`; excerpt `sha256:5870c5f434afc159fdfc90a83d0573a2f14fd84eeed7eaebf1387aaa24f8510c`
- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L560-L560) — lines `560–560`; excerpt `sha256:3d474c866d55639e06b1ef14730e4337a021f2fc60cf71e6968d1d248f20eeee`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L337-L337) — lines `337–337`; excerpt `sha256:21b00254a22f32bf11e90837e00d0f531d2814ce4b95f53698972da9cea9aef4`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L338-L338) — lines `338–338`; excerpt `sha256:dbef66b9e3c5d8c0a09d755196b0d01fe8b1ada7e36b96ef9d0a92eec2f71946`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L340-L340) — lines `340–340`; excerpt `sha256:3d474c866d55639e06b1ef14730e4337a021f2fc60cf71e6968d1d248f20eeee`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:556](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L556-L556), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:557](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L557-L557), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:558](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L558-L558), [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:560](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L560-L560)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:373](../../paper/68/erdos68-factorial-reasoning-surface.tex#L373-L373), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:374](../../paper/68/erdos68-factorial-reasoning-surface.tex#L374-L374), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:376](../../paper/68/erdos68-factorial-reasoning-surface.tex#L376-L376), [cite at paper/reasoning-parts/erdos68/core.tex:337](../../paper/reasoning-parts/erdos68/core.tex#L337-L337), [cite at paper/reasoning-parts/erdos68/core.tex:338](../../paper/reasoning-parts/erdos68/core.tex#L338-L338), [cite at paper/reasoning-parts/erdos68/core.tex:340](../../paper/reasoning-parts/erdos68/core.tex#L340-L340)

<a id="source-source-b6603e42453ff3"></a>

### [The Lean 4 theorem prover and programming language](https://doi.org/10.1007/978-3-030-79876-5_37)

- Source id: `source-b6603e42453ff3`
- Author or public identity: Leonardo de Moura, Sebastian Ullrich
- Kind: `software`
- Problems: #249, #251, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5428-L5434) — lines `5428–5434`; excerpt `sha256:693e1e0134f09226af4a4f04bb1f50d763c2bc0c40320ed6d730242cab1263bf`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1481-L1488) — lines `1481–1488`; excerpt `sha256:5efcd594df2c1529f1d749e113f706ddbbc1e3b2abe21b568592e74352af11ae`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2413-L2420) — lines `2413–2420`; excerpt `sha256:5efcd594df2c1529f1d749e113f706ddbbc1e3b2abe21b568592e74352af11ae`
- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1547-L1551) — lines `1547–1551`; excerpt `sha256:1bbd690c4787d1f1d80dd1f1ce42127d2dbec30c78a37ad55889e085911ed906`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1535-L1540) — lines `1535–1540`; excerpt `sha256:10b82bb930fe79ac10a4ea88fdca0fe6cef302ef6284568b8ea7a1bd56f969d0`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L56-L63) — lines `56–63`; excerpt `sha256:5efcd594df2c1529f1d749e113f706ddbbc1e3b2abe21b568592e74352af11ae`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L273-L274) — lines `273–274`; excerpt `sha256:4e7766b5028243ec605f7c1a65b5d48267b0332cf1424f52897938f30cb6624e`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3773](../../paper/archive/erdos249-257-main-paper.tex#L3773-L3773)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:307](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L307-L308), [cite at paper/reasoning-parts/erdos251/core.tex:273](../../paper/reasoning-parts/erdos251/core.tex#L273-L274)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:490](../../paper/systems/open-source-mathematics-strategy.tex#L490-L490)

<a id="source-source-b9d7160919621f"></a>

### [Transcendence and continued fraction expansion of values of Hecke--Mahler series](https://irma.math.unistra.fr/~bugeaud/travaux/BuMLAA.pdf)

- Source id: `source-b9d7160919621f`
- Author or public identity: Y. Bugeaud, M. Laurent
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2196-L2206) — lines `2196–2206`; excerpt `sha256:ed54f1baf48e90f0f605b0afacb805775274f5ba0a98bc29485a8fd68b2fa297`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L909-L920) — lines `909–920`; excerpt `sha256:daaae54b338d03faa10c907e93f25b9083b77395134e37af0b3775350acf0536`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L55-L65) — lines `55–65`; excerpt `sha256:ed54f1baf48e90f0f605b0afacb805775274f5ba0a98bc29485a8fd68b2fa297`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L82-L82) — lines `82–82`; excerpt `sha256:1198cf236a7ddcb62d86567aa20ca17426fc085c89b794da289687bb27ac850d`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L459-L459) — lines `459–459`; excerpt `sha256:1befc559197af20d33b7d88062553e5a2635859bb6d220c3a424f7baf25c04fe`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:321](../../paper/269/erdos-269-three-prime-running-lcm.tex#L321-L321), [cite at paper/269/erdos-269-three-prime-running-lcm.tex:324](../../paper/269/erdos-269-three-prime-running-lcm.tex#L324-L324)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:133](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L133-L133), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:510](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L510-L510), [cite at paper/reasoning-parts/erdos269/core.tex:82](../../paper/reasoning-parts/erdos269/core.tex#L82-L82), [cite at paper/reasoning-parts/erdos269/core.tex:459](../../paper/reasoning-parts/erdos269/core.tex#L459-L459)

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

- [paper/systems/claim-faithful-publication-systems-paper.tex](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1603-L1606) — lines `1603–1606`; excerpt `sha256:00533dbf0653285d403f4d880ae6c06199d42aedaead4cf8e51773d95b99c3ce`
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1520-L1525) — lines `1520–1525`; excerpt `sha256:a61b861ef9dfbc8c5a24e60e162f7b7fa072c019024917cf1a7847ac064e8432`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:692](../../paper/systems/claim-faithful-publication-systems-paper.tex#L692-L692)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:881](../../paper/systems/open-source-mathematics-strategy.tex#L881-L881), [cite at paper/systems/open-source-mathematics-strategy.tex:1282](../../paper/systems/open-source-mathematics-strategy.tex#L1282-L1282)

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
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. The countermodel comment names Zhang bounded-gap results among theorem families invariant under bounded perturbation; it states a limitation of those inputs, not a formalization.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1513-L1517) — lines `1513–1517`; excerpt `sha256:7ffbe3a18fcc2808a45a6fc6d3b8d29670d77d000a80937d21d998f7eba07100`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2455-L2459) — lines `2455–2459`; excerpt `sha256:7ffbe3a18fcc2808a45a6fc6d3b8d29670d77d000a80937d21d998f7eba07100`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L98-L102) — lines `98–102`; excerpt `sha256:7ffbe3a18fcc2808a45a6fc6d3b8d29670d77d000a80937d21d998f7eba07100`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1635-L1635) — lines `1635–1635`; excerpt `sha256:49174f4f955bc156d5dff6e9688b866e0626abb36fea0ef44d690620f0640e33`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L21-L21) — lines `21–21`; excerpt `sha256:07dad1a6dbaa03c54631370154c906de91a50cd710b3b9c6e143f85e14b3c973`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:1276](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1276-L1276)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1670](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1670-L1670), [cite at paper/reasoning-parts/erdos251/core.tex:1636](../../paper/reasoning-parts/erdos251/core.tex#L1636-L1636)

<a id="source-source-c742deb980b53c"></a>

### [Irrationality of rapidly converging series: a problem of Erdős and Graham](https://arxiv.org/abs/2601.21442)

- Source id: `source-c742deb980b53c`
- Author or public identity: Kevin Barreto, Jiwon Kang, Sang-hyun Kim, Vjekoslav Kovač, Shengtong Zhang
- Kind: `literature`
- Problems: none recorded
- Relationship and boundary: Cited by the #257 note: settles Erdős #1051 at the golden-ratio exponent; its d=1 case is Erdős 1975; its interval-filling counterexample method is unavailable at #257 because the Mersenne achievement set is totally disconnected. States nothing about #257.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/257/erdos-257-mersenne-support-subseries.tex](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1273-L1282) — lines `1273–1282`; excerpt `sha256:6a67739920bd09eb64cca1d9522bc299d0dfa3c8b89c32658c42a4e14644dd31`

Paper citation usages:

- `erdos-257-mersenne-support-subseries`: [cite at paper/257/erdos-257-mersenne-support-subseries.tex:756](../../paper/257/erdos-257-mersenne-support-subseries.tex#L756-L756), [cite at paper/257/erdos-257-mersenne-support-subseries.tex:1272](../../paper/257/erdos-257-mersenne-support-subseries.tex#L1272-L1272)

<a id="source-source-c835bc94aad831"></a>

### [On the irrationality of factorial series](https://geodesic.mathdoc.fr/articles/10.4064/aa118-4-5/)

- Source id: `source-c835bc94aad831`
- Author or public identity: J. Hančl, R. Tijdeman
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. Classical normalized-tail integrality for integer-coefficient factorial series. Finite-difference criteria have additional regularity hypotheses. Does not by itself prove irrationality for denominators n!-1.
- Source verification: `source\_verified` — Primary publisher PDF p. 385 visually inspected. This verifies the normalized-tail integrality precedent; it supplies no irrationality proof for individual denominators n!-1.
- Local mapping: `not recorded`

Exact source locations:

- [Section 2, Basic lemmas, printed p. 385: Lemma 2.1 and the following Remark. Integer coefficients and cumulative linear-product denominators; rationality implies denominator-cleared normalized tails are integers. For ordinary factorial denominators the multiplier is eventually unnecessary.](https://doi.org/10.4064/aa118-4-5)
- [Lemma 2.1 and following Remark, printed page 385: normalized-tail integrality for rational integer-coefficient factorial series; separate finite-difference criteria retain their additional hypotheses.](https://www.impan.pl/shop/en/publication/transaction/download/product/83588)

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1901-L1907) — lines `1901–1907`; excerpt `sha256:610aa0bc95650596fdb586b770690523132fd752b2c38d7e71bf028e7f0205dd`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L47-L53) — lines `47–53`; excerpt `sha256:610aa0bc95650596fdb586b770690523132fd752b2c38d7e71bf028e7f0205dd`
- [paper/reasoning-parts/erdos68/extended\_record.tex](../../paper/reasoning-parts/erdos68/extended_record.tex#L98-L98) — lines `98–98`; excerpt `sha256:4509bd5e1770c4bbc704abe603c8fa1e11b21a6f8df091f107f3860fd37f5357`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:207](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L207-L208)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1442](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1442-L1442), [cite at paper/reasoning-parts/erdos68/extended\_record.tex:98](../../paper/reasoning-parts/erdos68/extended_record.tex#L98-L98)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1510-L1515) — lines `1510–1515`; excerpt `sha256:3b1c1f707242e20b5d386d4825b37ac2214783f7d5eabb0ada5326605f0fc4cd`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:498](../../paper/systems/open-source-mathematics-strategy.tex#L498-L498), [cite at paper/systems/open-source-mathematics-strategy.tex:811](../../paper/systems/open-source-mathematics-strategy.tex#L811-L811), [cite at paper/systems/open-source-mathematics-strategy.tex:866](../../paper/systems/open-source-mathematics-strategy.tex#L866-L866)

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
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. Van Assche’s printed diagonal is the object tested by the finite polynomial non-equivalence check. Definitions transcribe the n=0 and first three values of Van Assche’s moving diagonal for the finite comparison in this module. The comment identifies the first three Van Assche diagonal values used by the local finite operator check.
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

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3157-L3162) — lines `3157–3162`; excerpt `sha256:a69c1e38c94f44808cdaf55b4edfad5ceb492e5823620e0dad5fd6b88b51c095`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L74-L79) — lines `74–79`; excerpt `sha256:a69c1e38c94f44808cdaf55b4edfad5ceb492e5823620e0dad5fd6b88b51c095`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L147-L147) — lines `147–147`; excerpt `sha256:db55e75e74985bffb379ecf20c9d2e96d4c7951fc0a715f0d1b50c9f44b4e164`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L150-L150) — lines `150–150`; excerpt `sha256:8444d9a52e9d844dd060541101c5c242fac57224203c9f7d526daee3b4b72c56`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L169-L169) — lines `169–169`; excerpt `sha256:3db02dadbfb8b1eba6bbbccaefbd67cc49166e13945647c2a97d76dab68cdded`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L936-L936) — lines `936–936`; excerpt `sha256:5e2e6c2c874886e16da148e50ad853ae95b8bd51917063f56898eede0c49e406`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L4-L13) — lines `4–13`; excerpt `sha256:9e02e269f490c0d8ee088d184d3cf2b53af45d9b0144a4623c9110e7230e7af9`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L19-L32) — lines `19–32`; excerpt `sha256:ed4a3e5b020b06b3f16f2771e4c9518cf5e0c23e46e275e30a93b5b498f5db23`
- [lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean](../../lean/ErdosProblems/Erdos1049/QAperyDiagonalNonEquivalence.lean#L58-L62) — lines `58–62`; excerpt `sha256:6fab9c0293d1ca17fe26b54f24d0f7366711b09b71d8f6e869df1315fb5c2dbc`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:172](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L172-L172), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:175](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L175-L175), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:194](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L194-L194), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:961](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L961-L961), [cite at paper/reasoning-parts/erdos1049/core.tex:147](../../paper/reasoning-parts/erdos1049/core.tex#L147-L147), [cite at paper/reasoning-parts/erdos1049/core.tex:150](../../paper/reasoning-parts/erdos1049/core.tex#L150-L150), [cite at paper/reasoning-parts/erdos1049/core.tex:169](../../paper/reasoning-parts/erdos1049/core.tex#L169-L169), [cite at paper/reasoning-parts/erdos1049/core.tex:936](../../paper/reasoning-parts/erdos1049/core.tex#L936-L936)

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
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. The comment explicitly compares the n!−1 collision mechanism with Stewart’s small-prime-factor subsequence; this is a source comparison only.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1886-L1891) — lines `1886–1891`; excerpt `sha256:9269a1d95c9cb51a3872a4d5fffc5a6b11d125283281b8f2b64a0a71a94197e9`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L32-L37) — lines `32–37`; excerpt `sha256:9269a1d95c9cb51a3872a4d5fffc5a6b11d125283281b8f2b64a0a71a94197e9`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L150-L150) — lines `150–150`; excerpt `sha256:98e11f1b33ae8960114ddbce12be389f32f1c1b77093e00d348188e21a665344`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1225-L1225) — lines `1225–1225`; excerpt `sha256:d47cc382e7afc7f184344441f0e14f5174027851786e20b58d14e8c99a95145a`
- [paper/reasoning-parts/erdos68/extended\_record.tex](../../paper/reasoning-parts/erdos68/extended_record.tex#L311-L311) — lines `311–311`; excerpt `sha256:f200b0e258f381503d98f0b8572739adf2ab69e2b55df1b570dd5dc74cdcd699`
- [lean/ErdosProblems/Erdos68/PrimeZeroBranch.lean](../../lean/ErdosProblems/Erdos68/PrimeZeroBranch.lean#L3134-L3139) — lines `3134–3139`; excerpt `sha256:c866f4949ed4ad3259541be1ab078fcd2c3b951e2dcb35d831286f21d4ff0dae`

Paper citation usages:

- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:186](../../paper/68/erdos68-factorial-reasoning-surface.tex#L186-L186), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1261](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1261-L1261), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1655](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1655-L1655), [cite at paper/reasoning-parts/erdos68/core.tex:150](../../paper/reasoning-parts/erdos68/core.tex#L150-L150), [cite at paper/reasoning-parts/erdos68/core.tex:1225](../../paper/reasoning-parts/erdos68/core.tex#L1225-L1225), [cite at paper/reasoning-parts/erdos68/extended\_record.tex:311](../../paper/reasoning-parts/erdos68/extended_record.tex#L311-L311)

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
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. The countermodel comment names Ford–Green–Konyagin–Maynard–Tao large-gap results among theorem families invariant under bounded perturbation; it states a limitation, not a formalization.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1462-L1468) — lines `1462–1468`; excerpt `sha256:20d02c5973a1a874c6f11d3b29edf04eb2d58bf4d3e901c20899c984dc5c4939`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2389-L2395) — lines `2389–2395`; excerpt `sha256:6c877b3de5543496434c0302c82515676be3b3947b0761c79da231164ed345a9`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L32-L38) — lines `32–38`; excerpt `sha256:6c877b3de5543496434c0302c82515676be3b3947b0761c79da231164ed345a9`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L763-L763) — lines `763–763`; excerpt `sha256:4825da1c1a4563510f00f6082213673382fbe87eeb61a99a395507739f85527f`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1643-L1643) — lines `1643–1643`; excerpt `sha256:eaaaa84d309b1a0c1d56fc36e531a59a4fa33af5709a256b9b48f214908ca467`
- [lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean](../../lean/ErdosProblems/Erdos251/BoundedPerturbationCountermodel.lean#L22-L22) — lines `22–22`; excerpt `sha256:6fe10d86cfbff9e425bdd6578dd696a5a4e58cae9a09bb6b9e1d399e6bd9e791`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:1013](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1013-L1013), [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:1284](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1284-L1284)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:798](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L798-L798), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1678](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1678-L1678), [cite at paper/reasoning-parts/erdos251/core.tex:764](../../paper/reasoning-parts/erdos251/core.tex#L764-L764), [cite at paper/reasoning-parts/erdos251/core.tex:1644](../../paper/reasoning-parts/erdos251/core.tex#L1644-L1644)

<a id="source-source-d471eacdba0f87"></a>

### [The irrationality of some number theoretical series](https://arxiv.org/abs/1105.1451)

- Source id: `source-d471eacdba0f87`
- Author or public identity: J.-C. Schlage-Puchta
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Prime-gap nonvanishing lemma and irrationality results used in the Problem 251 reasoning surface. The comments explicitly attribute the fixed-polynomial fixed-block statement to Schlage-Puchta, Lemma 4, and distinguish it from a growing-block theorem.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Theorems 2 and 3 state the digit-concatenation rationality criterion and Q-linear independence of 1,S\_0,S\_1,... .](https://arxiv.org/abs/1105.1451)
- [Selberg-sieve setup and Lemma 4 show that a nonzero polynomial in consecutive prime gaps vanishes only on a density-zero set; the proof is included.](https://arxiv.org/abs/1105.1451)

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2440-L2449) — lines `2440–2449`; excerpt `sha256:8a0766b03b9a2ef543169ef625d4116ae5899556dfe31f1e4143a25181f1f2fd`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L83-L92) — lines `83–92`; excerpt `sha256:8a0766b03b9a2ef543169ef625d4116ae5899556dfe31f1e4143a25181f1f2fd`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L149-L149) — lines `149–149`; excerpt `sha256:44ada274e20ce55d61ab78ff7c06ebcad2b2333498afad5d48de89478db07616`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L201-L201) — lines `201–201`; excerpt `sha256:41398d03652804df59566b2c06e0b03211d5231ce61dea455b608037a5c91051`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L653-L653) — lines `653–653`; excerpt `sha256:c636df7f4467f057caa18103dd5e9add9f401f689a916825d6347a2a57ab37d8`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1172-L1173) — lines `1172–1173`; excerpt `sha256:5a4f605adbe4bbba39b889ba7030dcb38ab8b0287c2d1254cca406ab74aa49cd`
- [lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean](../../lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L7-L23) — lines `7–23`; excerpt `sha256:321f1f193ba6cea89edee0e703684bdf6234e2bc38d8b5dc53a6395d1b42cf33`

Paper citation usages:

- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:183](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L183-L183), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:235](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L235-L235), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:687](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L687-L687), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1207](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1207-L1208), [cite at paper/reasoning-parts/erdos251/core.tex:149](../../paper/reasoning-parts/erdos251/core.tex#L149-L149), [cite at paper/reasoning-parts/erdos251/core.tex:201](../../paper/reasoning-parts/erdos251/core.tex#L201-L201), [cite at paper/reasoning-parts/erdos251/core.tex:653](../../paper/reasoning-parts/erdos251/core.tex#L653-L653), [cite at paper/reasoning-parts/erdos251/core.tex:1173](../../paper/reasoning-parts/erdos251/core.tex#L1173-L1174)

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

- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1591-L1596) — lines `1591–1596`; excerpt `sha256:0e1fe3e7471b6a0f3864ce0578266000a9fbb85f892248701cd17ba615c3e182`

Paper citation usages:

- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:728](../../paper/systems/open-source-mathematics-strategy.tex#L728-L728)

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

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3194-L3200) — lines `3194–3200`; excerpt `sha256:c25f49535bb41622d57001597d91a9d0235dce0d09f719c90462c775d4374cb0`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L111-L117) — lines `111–117`; excerpt `sha256:c25f49535bb41622d57001597d91a9d0235dce0d09f719c90462c775d4374cb0`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L114-L114) — lines `114–114`; excerpt `sha256:7ca3faafcf4b5c6e96101f2b67ab383bc16510022d0240ba9237766b8e7af01b`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L136-L139) — lines `136–139`; excerpt `sha256:be4c5ae88c67a0cc23d71ca72524fb2cc5273fdf65a4f0ac220fae55ed91bfb4`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:139](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L139-L139), [cite at paper/reasoning-parts/erdos1049/core.tex:114](../../paper/reasoning-parts/erdos1049/core.tex#L114-L114)

<a id="source-source-d8b2a7c411bc2d"></a>

### [The Lean mathematical library](https://doi.org/10.1145/3372885.3373824)

- Source id: `source-d8b2a7c411bc2d`
- Author or public identity: The mathlib Community
- Kind: `software`
- Problems: #249, #251, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5434-L5441) — lines `5434–5441`; excerpt `sha256:add18eb59b9977acb225b85709240b860573b28552d807c45eec7058c8a77d79`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1488-L1495) — lines `1488–1495`; excerpt `sha256:921d0f1924fcf25d854d8fae83c000baea9f2861378bfd0b72fa87603c9135b4`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2420-L2428) — lines `2420–2428`; excerpt `sha256:f841f06592bb69d248722d3cf2fdd0e24f0e0be3208a88ea688c6f38084dd5b9`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L63-L71) — lines `63–71`; excerpt `sha256:f841f06592bb69d248722d3cf2fdd0e24f0e0be3208a88ea688c6f38084dd5b9`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L275-L275) — lines `275–275`; excerpt `sha256:2e18db0cadc2506770ccc086348627699a4238aef81e62da13be41def3a92a0f`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:3775](../../paper/archive/erdos249-257-main-paper.tex#L3775-L3775)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:309](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L309-L309), [cite at paper/reasoning-parts/erdos251/core.tex:275](../../paper/reasoning-parts/erdos251/core.tex#L275-L275)

<a id="source-source-dcbe400c96be59"></a>

### [Some inequalities for polynomials and rational functions associated with a lemniscate](https://doi.org/10.1007/s10958-013-1432-4)

- Source id: `source-dcbe400c96be59`
- Author or public identity: V. N. Dubinin
- Kind: `literature`
- Problems: #1041
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1409-L1415) — lines `1409–1415`; excerpt `sha256:a417f5753cf9d65bf35cd6a358cb659cef8be7de46f23b0cb3d8b627c402b0e3`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2903-L2917) — lines `2903–2917`; excerpt `sha256:d876dc5e496ee7a4f2cd2da6e77e8675d10922691babb4199e6de90162f2811b`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L38-L52) — lines `38–52`; excerpt `sha256:d876dc5e496ee7a4f2cd2da6e77e8675d10922691babb4199e6de90162f2811b`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L1103-L1103) — lines `1103–1103`; excerpt `sha256:bf660f22b7c2b5ad1586f91c21fc4e625ed74e4ec29b524be165def32d7d016d`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:628](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L628-L628), [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:657](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L657-L657)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:1146](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L1146-L1146), [cite at paper/reasoning-parts/erdos1041/core.tex:1103](../../paper/reasoning-parts/erdos1041/core.tex#L1103-L1103)

<a id="source-source-e13ecb7c94852a"></a>

### [Representations of Real Numbers by Infinite Series](https://doi.org/10.1007/BFb0081642)

- Source id: `source-e13ecb7c94852a`
- Author or public identity: J. Galambos
- Kind: `literature`
- Problems: #68
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L902-L905) — lines `902–905`; excerpt `sha256:ce3aacc46dd9982236f7b68acf0ec1f1c1aca32c57a7ead73b45c724bf7be460`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1875-L1880) — lines `1875–1880`; excerpt `sha256:cedd080125403772538229eaf126fbb69017041066d4453daada9b963109d2db`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L21-L26) — lines `21–26`; excerpt `sha256:cedd080125403772538229eaf126fbb69017041066d4453daada9b963109d2db`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L451-L451) — lines `451–451`; excerpt `sha256:011aac74bb7e11d8f00fd425d894c85b3bd4993c1582a90e39564fc6de6d05d8`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1227-L1227) — lines `1227–1227`; excerpt `sha256:1c5ce347370e0f2e4d75a5e1a7d184f4fe313ae6393bb0e1558a58fbda582611`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:205](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L205-L205)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:487](../../paper/68/erdos68-factorial-reasoning-surface.tex#L487-L487), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1263](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1263-L1263), [cite at paper/reasoning-parts/erdos68/core.tex:451](../../paper/reasoning-parts/erdos68/core.tex#L451-L451), [cite at paper/reasoning-parts/erdos68/core.tex:1227](../../paper/reasoning-parts/erdos68/core.tex#L1227-L1227)

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
- [paper/systems/cold-clone-to-proof-receipt.tex](../../paper/systems/cold-clone-to-proof-receipt.tex#L651-L656) — lines `651–656`; excerpt `sha256:e1fb69819625ee4c623683e8876546bfaeba103a154bb24b05f891cf455291a5`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1300](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1300-L1300)
- `cold-clone-to-proof-receipt`: [cite at paper/systems/cold-clone-to-proof-receipt.tex:368](../../paper/systems/cold-clone-to-proof-receipt.tex#L368-L368), [cite at paper/systems/cold-clone-to-proof-receipt.tex:457](../../paper/systems/cold-clone-to-proof-receipt.tex#L457-L457)

<a id="source-source-e33bdf934f939f"></a>

### [On the irrationality of certain Ahmes series](https://users.renyi.hu/~p_erdos/1964-19.pdf)

- Source id: `source-e33bdf934f939f`
- Author or public identity: P. Erdős, E. G. Straus
- Kind: `literature`
- Problems: #243, #251
- Relationship and boundary: The exact original theorem, its printed indexing, assumptions, conclusion, proof location, and the stated implication between its two criteria. - The classical conditional rationality/recurrence criterion used as the source boundary in the #243 note, including the examples on pp. 132–133. - The source identity, official retrieval route, digest, and page-level locators recorded above. The theorem docstring explicitly says its asymptotic hypothesis is the one in Erdős–Straus Theorem 2.1 after the stated specialization. Supplement copy of the explicit Erdős–Straus Theorem 2.1 hypothesis specialization.
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

Public implementation or evidence coordinates:

- [paper/243/erdos-243-reciprocal-tail-rigidity.tex](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L872-L876) — lines `872–876`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/243/erdos243-reciprocal-tail-reasoning-surface.tex](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2999-L3003) — lines `2999–3003`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/251/erdos-251-prime-gap-dyadic-series.tex](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L1459-L1462) — lines `1459–1462`; excerpt `sha256:4534a543d1afe85f69bf29561cd83f5af60b7189e5f777e680f7faeab2d42b39`
- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2386-L2389) — lines `2386–2389`; excerpt `sha256:4534a543d1afe85f69bf29561cd83f5af60b7189e5f777e680f7faeab2d42b39`
- [paper/reasoning-parts/erdos243/back.tex](../../paper/reasoning-parts/erdos243/back.tex#L5-L9) — lines `5–9`; excerpt `sha256:0cc9c4e626bc8d78dd9f17ee6ad68a9e292db82c4def750c27e314466c80af1b`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L594-L594) — lines `594–594`; excerpt `sha256:cd8c27ae9a8135017858c7376e2262d083102fff1a40102ceb91b626a90f84c1`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L1601-L1602) — lines `1601–1602`; excerpt `sha256:11e0342054d7c4e8c78eb3a2b9cf3e14eb83e8083b84fd50f4647051eaf4635d`
- [paper/reasoning-parts/erdos243/core.tex](../../paper/reasoning-parts/erdos243/core.tex#L2667-L2667) — lines `2667–2667`; excerpt `sha256:5b1834a94ad5fbf151d67607e7d1b9f259aeeeb2f02cf778d733f143e34533dc`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L29-L32) — lines `29–32`; excerpt `sha256:4534a543d1afe85f69bf29561cd83f5af60b7189e5f777e680f7faeab2d42b39`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L239-L239) — lines `239–239`; excerpt `sha256:eaa1d49db16032d9a995bc268a5e64df15540715982aacd7d504bd007c69cab4`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateau.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L1125-L1127) — lines `1125–1127`; excerpt `sha256:1139eed2569eedcc245358cbde7bff884c8a36c06c78b0a38246a82257dae3ec`
- [lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean](../../lean/ErdosProblems/Erdos68/FactorialZeroPlateauSupplement.lean#L30-L32) — lines `30–32`; excerpt `sha256:1139eed2569eedcc245358cbde7bff884c8a36c06c78b0a38246a82257dae3ec`

Paper citation usages:

- `erdos-243-reciprocal-tail-rigidity`: [cite at paper/243/erdos-243-reciprocal-tail-rigidity.tex:540](../../paper/243/erdos-243-reciprocal-tail-rigidity.tex#L540-L540)
- `erdos243-reciprocal-tail-reasoning-surface`: [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:636](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L636-L636), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:1643](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L1643-L1644), [cite at paper/243/erdos243-reciprocal-tail-reasoning-surface.tex:2709](../../paper/243/erdos243-reciprocal-tail-reasoning-surface.tex#L2709-L2709), [cite at paper/reasoning-parts/erdos243/core.tex:594](../../paper/reasoning-parts/erdos243/core.tex#L594-L594), [cite at paper/reasoning-parts/erdos243/core.tex:1601](../../paper/reasoning-parts/erdos243/core.tex#L1601-L1602), [cite at paper/reasoning-parts/erdos243/core.tex:2667](../../paper/reasoning-parts/erdos243/core.tex#L2667-L2667)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:273](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L273-L273), [cite at paper/reasoning-parts/erdos251/core.tex:239](../../paper/reasoning-parts/erdos251/core.tex#L239-L239)

<a id="source-source-e553241a97e580"></a>

### [Arithmetical investigations of a certain infinite product](https://numdam.org/item/CM_1994__91_2_175_0.pdf)

- Source id: `source-e553241a97e580`
- Author or public identity: P. Bundschuh, K. Väänänen
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
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

Public implementation or evidence coordinates:

- [paper/1049/erdos-1049-rational-base-lambert.tex](../../paper/1049/erdos-1049-rational-base-lambert.tex#L963-L967) — lines `963–967`; excerpt `sha256:623747e79169932488ca0b99e1c9df909dedfc28fc4c657e52f3d92b524d2d32`
- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3111-L3115) — lines `3111–3115`; excerpt `sha256:623747e79169932488ca0b99e1c9df909dedfc28fc4c657e52f3d92b524d2d32`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L28-L32) — lines `28–32`; excerpt `sha256:623747e79169932488ca0b99e1c9df909dedfc28fc4c657e52f3d92b524d2d32`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L94-L94) — lines `94–94`; excerpt `sha256:6b9a9140a61bd1b858f2cbfd7a2201e226e80ac6e68674e910574cb3ddade3bc`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L229-L229) — lines `229–229`; excerpt `sha256:1d967e5b79978158028dec08e2da903dffe3ccf2adea4daa8aab1ec945c0074b`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L362-L362) — lines `362–362`; excerpt `sha256:9f8ab6319a7f69bec66a3b5d934fd0f1c4987b6fbc452dd9f31be0818e4f91cf`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L754-L754) — lines `754–754`; excerpt `sha256:821db0226f401eecde809f078e52fe48c1b83dedf30a7d27c9ca623edaa567df`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L914-L914) — lines `914–914`; excerpt `sha256:01c1ac66a7f33792d44a423457acee487c1e732800512e90d7bee1fb3494bef4`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L933-L933) — lines `933–933`; excerpt `sha256:30f757d949ac9157e8f267f8e3d786527c53103fc9398c0a3d0c1341553aa05e`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L1155-L1155) — lines `1155–1155`; excerpt `sha256:19609efc10df322b4467f32e01c06e8968470d9eb8e7d6b858482e82964a1de8`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L2325-L2325) — lines `2325–2325`; excerpt `sha256:d2c829624073677f01d8249e65502cefe988ed95a2fdda5ea915e1dcb2d758bc`

Paper citation usages:

- `erdos-1049-rational-base-lambert`: [cite at paper/1049/erdos-1049-rational-base-lambert.tex:365](../../paper/1049/erdos-1049-rational-base-lambert.tex#L365-L365)
- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:119](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L119-L119), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:254](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L254-L254), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:387](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L387-L387), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:779](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L779-L779), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:939](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L939-L939), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:958](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L958-L958), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:1180](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L1180-L1180), [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:2350](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L2350-L2350), [cite at paper/reasoning-parts/erdos1049/core.tex:94](../../paper/reasoning-parts/erdos1049/core.tex#L94-L94), [cite at paper/reasoning-parts/erdos1049/core.tex:229](../../paper/reasoning-parts/erdos1049/core.tex#L229-L229), [cite at paper/reasoning-parts/erdos1049/core.tex:362](../../paper/reasoning-parts/erdos1049/core.tex#L362-L362), [cite at paper/reasoning-parts/erdos1049/core.tex:754](../../paper/reasoning-parts/erdos1049/core.tex#L754-L754), [cite at paper/reasoning-parts/erdos1049/core.tex:914](../../paper/reasoning-parts/erdos1049/core.tex#L914-L914), [cite at paper/reasoning-parts/erdos1049/core.tex:933](../../paper/reasoning-parts/erdos1049/core.tex#L933-L933), [cite at paper/reasoning-parts/erdos1049/core.tex:1155](../../paper/reasoning-parts/erdos1049/core.tex#L1155-L1155), [cite at paper/reasoning-parts/erdos1049/core.tex:2325](../../paper/reasoning-parts/erdos1049/core.tex#L2325-L2325)

<a id="source-source-e5f2924d82c59f"></a>

### [New irrationality measures for q-logarithms](https://doi.org/10.1090/S0025-5718-05-01812-0)

- Source id: `source-e5f2924d82c59f`
- Author or public identity: T. Matala-aho, K. Väänänen, W. Zudilin
- Kind: `literature`
- Problems: #1049
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L3139-L3146) — lines `3139–3146`; excerpt `sha256:ca3ad143147a5d2804f66fa9a2b445b365c705a19273a1ae8c77f2c257c09062`
- [paper/reasoning-parts/erdos1049/back.tex](../../paper/reasoning-parts/erdos1049/back.tex#L56-L63) — lines `56–63`; excerpt `sha256:ca3ad143147a5d2804f66fa9a2b445b365c705a19273a1ae8c77f2c257c09062`
- [paper/reasoning-parts/erdos1049/core.tex](../../paper/reasoning-parts/erdos1049/core.tex#L253-L253) — lines `253–253`; excerpt `sha256:a9816f01cbbbed3606bb3c7105e1f1bc81607266eee3e3bc860ed90c8624c684`

Paper citation usages:

- `erdos1049-rational-base-lambert-reasoning-surface`: [cite at paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex:278](../../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.tex#L278-L278), [cite at paper/reasoning-parts/erdos1049/core.tex:253](../../paper/reasoning-parts/erdos1049/core.tex#L253-L253)

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
- [paper/systems/open-source-mathematics-strategy.tex](../../paper/systems/open-source-mathematics-strategy.tex#L1586-L1591) — lines `1586–1591`; excerpt `sha256:4fa78969a75193c23aeb06cdd0323df94e0a5887673d1bf5c44d740748d12774`

Paper citation usages:

- `claim-faithful-publication-systems`: [cite at paper/systems/claim-faithful-publication-systems-paper.tex:1387](../../paper/systems/claim-faithful-publication-systems-paper.tex#L1387-L1387)
- `open-source-mathematics-strategy`: [cite at paper/systems/open-source-mathematics-strategy.tex:972](../../paper/systems/open-source-mathematics-strategy.tex#L972-L972)

<a id="source-source-eca9e699590922"></a>

### [On the binary digits of the Erdős--Borwein constant](https://arxiv.org/abs/2605.24160v1)

- Source id: `source-eca9e699590922`
- Author or public identity: J. M. Campbell
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation. The module comments explicitly compare the local synchronization obstruction with Campbell’s quarter-exponent prime-progression result; this is a bounded source comparison, not a formalization claim.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5409-L5415) — lines `5409–5415`; excerpt `sha256:cdaff80cd6c7f5f1646ee2c7a858ab106e0225c3e87b92ca3df2858826a27e1e`
- [paper/reasoning-parts/erdos257/a257\_front.tex](../../paper/reasoning-parts/erdos257/a257_front.tex#L754-L758) — lines `754–758`; excerpt `sha256:b7df2e208b87bda4ef0e65b64ed7fc248f55353da466b2fb43ae947c666e4bdd`
- [lean/Erdos249257/CampbellShiftSynchronization.lean](../../lean/Erdos249257/CampbellShiftSynchronization.lean#L4-L22) — lines `4–22`; excerpt `sha256:d517c238bb94dca26752a32c4273074633c39a9b8af3551e069cb7a282081388`
- [lean/Erdos249257/CampbellShiftSynchronization.lean](../../lean/Erdos249257/CampbellShiftSynchronization.lean#L294-L299) — lines `294–299`; excerpt `sha256:a33a451732d6d625372bccee6302e08dfdb1ec94ea88b2bb9013d5eff55197d4`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:2253](../../paper/archive/erdos249-257-main-paper.tex#L2253-L2254)

<a id="source-source-ef6233b59b95cb"></a>

### [Rational numbers with odd greedy expansion of fixed length](https://arxiv.org/abs/2309.07280)

- Source id: `source-ef6233b59b95cb`
- Author or public identity: J. Louwsma, J. Martino
- Kind: `literature`
- Problems: #68
- Relationship and boundary: General reciprocal-sum numerator valuation formula used as the first valuation layer in the Problem 68 papers.
- Source verification: `source\_verified` — Primary arXiv source acquired and read; exact source locators identify the inspected statement. The stated relation bounds what is used locally.
- Local mapping: `not recorded`

Exact source locations:

- [Lemma 4.1, printed/PDF p. 10: for positive integers x\_1,…,x\_m and prime p, gives the exact p-adic valuation formula for σ\_{m−1}(x\_1,…,x\_m) in terms of v\_p(x\_1⋯x\_m), W\_p=max\_i v\_p(x\_i), and the normalized residual sum.](https://arxiv.org/abs/2309.07280)
- [Proof of Lemma 4.1, printed/PDF p. 10: factors the common p-power from the elementary-symmetric-polynomial sum to obtain the valuation identity.](https://arxiv.org/abs/2309.07280)

Public implementation or evidence coordinates:

- [paper/68/erdos-68-factorial-denominator-irrationality.tex](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L909-L914) — lines `909–914`; excerpt `sha256:bade0d216eca6c368176aac7e67fba295653e53d2dd461bf5a587f72fb873b85`
- [paper/68/erdos68-factorial-reasoning-surface.tex](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1866-L1871) — lines `1866–1871`; excerpt `sha256:914493d46467de68f4694608090ada82775de8b29aeffdda4fe43be291dc4ee7`
- [paper/reasoning-parts/erdos68/back.tex](../../paper/reasoning-parts/erdos68/back.tex#L12-L17) — lines `12–17`; excerpt `sha256:914493d46467de68f4694608090ada82775de8b29aeffdda4fe43be291dc4ee7`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L97-L97) — lines `97–97`; excerpt `sha256:8d44e1afd5543e22611e7b2e88c11f10ad3956cbb21387dfae176623c218e232`
- [paper/reasoning-parts/erdos68/core.tex](../../paper/reasoning-parts/erdos68/core.tex#L1237-L1237) — lines `1237–1237`; excerpt `sha256:186943c5320ca400ba71ec0d287f6d1f2c0b582ed19d097801bbf47073324fc9`

Paper citation usages:

- `erdos-68-factorial-denominator-irrationality`: [cite at paper/68/erdos-68-factorial-denominator-irrationality.tex:587](../../paper/68/erdos-68-factorial-denominator-irrationality.tex#L587-L587)
- `erdos68-factorial-reasoning-surface`: [cite at paper/68/erdos68-factorial-reasoning-surface.tex:133](../../paper/68/erdos68-factorial-reasoning-surface.tex#L133-L133), [cite at paper/68/erdos68-factorial-reasoning-surface.tex:1273](../../paper/68/erdos68-factorial-reasoning-surface.tex#L1273-L1273), [cite at paper/reasoning-parts/erdos68/core.tex:97](../../paper/reasoning-parts/erdos68/core.tex#L97-L97), [cite at paper/reasoning-parts/erdos68/core.tex:1237](../../paper/reasoning-parts/erdos68/core.tex#L1237-L1237)

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
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/1041/erdos-1041-lemniscate-newton-flow.tex](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1374-L1378) — lines `1374–1378`; excerpt `sha256:372ad8d3f82ff0212ee04c7dd5a7269a56a5c9a52cae45f7d05245ccae260a87`
- [paper/1041/erdos1041-lemniscate-reasoning-surface.tex](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L2888-L2897) — lines `2888–2897`; excerpt `sha256:72a88e5a23c5730b248edc8d8bc104d1818c8c71ea25dbdd60a7c6074bb79d61`
- [paper/reasoning-parts/erdos1041/back.tex](../../paper/reasoning-parts/erdos1041/back.tex#L23-L32) — lines `23–32`; excerpt `sha256:72a88e5a23c5730b248edc8d8bc104d1818c8c71ea25dbdd60a7c6074bb79d61`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L193-L193) — lines `193–193`; excerpt `sha256:07fcf468eb97daf59fb2dc81ba8f582132d97355a60f1a6cf9d66f6fa2bef8bb`
- [paper/reasoning-parts/erdos1041/core.tex](../../paper/reasoning-parts/erdos1041/core.tex#L246-L246) — lines `246–246`; excerpt `sha256:a5ff86424ff981f821342dcb825b979ab97b26d9f4fd64602e335a61e6c30611`

Paper citation usages:

- `erdos-1041-lemniscate-newton-flow`: [cite at paper/1041/erdos-1041-lemniscate-newton-flow.tex:1325](../../paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1325-L1325)
- `erdos1041-lemniscate-reasoning-surface`: [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:236](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L236-L236), [cite at paper/1041/erdos1041-lemniscate-reasoning-surface.tex:289](../../paper/1041/erdos1041-lemniscate-reasoning-surface.tex#L289-L289), [cite at paper/reasoning-parts/erdos1041/core.tex:193](../../paper/reasoning-parts/erdos1041/core.tex#L193-L193), [cite at paper/reasoning-parts/erdos1041/core.tex:246](../../paper/reasoning-parts/erdos1041/core.tex#L246-L246)

<a id="source-source-f42f9e04743a4c"></a>

### [A conditional proof of the irrationality of ∑\_{n≥1} p\_n 2^{−n} under a uniform Hardy–Littlewood prime-tuples conjecture](https://github.com/beetree/math_erdos_251)

- Source id: `source-f42f9e04743a4c`
- Author or public identity: J. Land
- Kind: `literature`
- Problems: #251
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/251/erdos251-prime-gap-reasoning-surface.tex](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2405-L2413) — lines `2405–2413`; excerpt `sha256:fd3c426390b219a634332e902baa261a6828da620ce6016c66adeb4d9dd5bf6f`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L48-L56) — lines `48–56`; excerpt `sha256:fd3c426390b219a634332e902baa261a6828da620ce6016c66adeb4d9dd5bf6f`
- [paper/reasoning-parts/erdos251/back.tex](../../paper/reasoning-parts/erdos251/back.tex#L117-L117) — lines `117–117`; excerpt `sha256:f0efe662cb069205ae23e5ac27895f193cd1638b1392cbaba8b0f563f510294d`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L135-L135) — lines `135–135`; excerpt `sha256:6e7e15f9ebc3386d8e0df09d8c222f4031a21e912db44279c6c0df90a0f6f0a6`
- [paper/reasoning-parts/erdos251/core.tex](../../paper/reasoning-parts/erdos251/core.tex#L1652-L1652) — lines `1652–1652`; excerpt `sha256:ad49b5aa94a8d9963ee6dcb001d2d84dc32e0776315128832b860e41fd3a9cf0`

Paper citation usages:

- `erdos-251-prime-gap-dyadic-series`: [cite at paper/251/erdos-251-prime-gap-dyadic-series.tex:241](../../paper/251/erdos-251-prime-gap-dyadic-series.tex#L241-L241)
- `erdos251-prime-gap-reasoning-surface`: [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:169](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L169-L169), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:1687](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L1687-L1687), [cite at paper/251/erdos251-prime-gap-reasoning-surface.tex:2474](../../paper/251/erdos251-prime-gap-reasoning-surface.tex#L2474-L2474), [cite at paper/reasoning-parts/erdos251/back.tex:117](../../paper/reasoning-parts/erdos251/back.tex#L117-L117), [cite at paper/reasoning-parts/erdos251/core.tex:135](../../paper/reasoning-parts/erdos251/core.tex#L135-L135), [cite at paper/reasoning-parts/erdos251/core.tex:1653](../../paper/reasoning-parts/erdos251/core.tex#L1653-L1653)

<a id="source-source-f4ad17717c8fd4"></a>

### [Positive dyadic density for rational weighted binary expansions](https://arxiv.org/abs/2606.24972v2)

- Source id: `source-f4ad17717c8fd4`
- Author or public identity: H. Wang
- Kind: `literature`
- Problems: #249, #257
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `existing\_source\_closure` — scope not separately recorded
- Local mapping: `not recorded`

Exact source locations:

- [- Printed p. 1 gives the title, sole author “HAN WANG”, arXiv version/date,](https://arxiv.org/abs/2606.24972v2)
- [consequence of this source's theorem, not as a result about Erdős #249 or](https://arxiv.org/abs/2606.24972v2)
- [- Printed p. 2, Theorem 1.1 (“Polynomial-window density”), states that for an](https://arxiv.org/abs/2606.24972v2)
- [- Printed p. 3, Corollary 1.2 (“Density and gaps”), states the positive lower](https://arxiv.org/abs/2606.24972v2)
- [sparse-support consequence. Printed p. 3, Lemma 2.1 (“Carries and gaps”),](https://arxiv.org/abs/2606.24972v2)
- [- Printed p. 5, Lemma 2.4 (“Polynomial locking”), gives the rational polynomial](https://arxiv.org/abs/2606.24972v2)
- [Printed p. 5, its proof records the determinant/divisibility step used to](https://arxiv.org/abs/2606.24972v2)
- [- Printed p. 6, equation (7), gives the normalized leading-coefficient map](https://arxiv.org/abs/2606.24972v2)
- [\`mu -\> b^g mu - 1\`; Lemma 2.5 gives the interior/exterior dichotomy and the](https://arxiv.org/abs/2606.24972v2)
- [at-most-one interior successor-gap statement. Printed p. 6, Proposition 3.1](https://arxiv.org/abs/2606.24972v2)
- [- Printed p. 10, the proof of Theorem 1.1 combines the preceding estimates and](https://arxiv.org/abs/2606.24972v2)
- [lines 162–183 contain the source theorem corresponding to printed p. 2,](https://arxiv.org/abs/2606.24972v2)
- [- The printed p. 1 classification and keywords identify the source as Erdős](https://arxiv.org/abs/2606.24972v2)
- [#249 or #257 as a target. The printed p. 2 Theorem 1.1 is conditional on](https://arxiv.org/abs/2606.24972v2)
- [- Printed p. 3, Corollary 1.2 records the source's binary-linear consequence](https://arxiv.org/abs/2606.24972v2)
- [series of #249 or all infinite-support subseries of #257. Printed pp. 5–10](https://arxiv.org/abs/2606.24972v2)
- [theorem to those problems.](https://arxiv.org/abs/2606.24972v2)
- [- The source's final disclosure on printed p. 10 describes AI assistance and](https://arxiv.org/abs/2606.24972v2)
- [a formalisation commit for this source's theorem. It contains no peer-review,](https://arxiv.org/abs/2606.24972v2)
- [boundary, not unresolved implications of its theorem.](https://arxiv.org/abs/2606.24972v2)

Public implementation or evidence coordinates:

- [paper/archive/erdos249-257-main-paper.tex](../../paper/archive/erdos249-257-main-paper.tex#L5395-L5400) — lines `5395–5400`; excerpt `sha256:4caf7a23e043524edc0b28f6c56ff51ffc65fbd8e9bcea766fda7d8bd0b07263`

Paper citation usages:

- `erdos249-257-main`: [cite at paper/archive/erdos249-257-main-paper.tex:923](../../paper/archive/erdos249-257-main-paper.tex#L923-L923), [cite at paper/archive/erdos249-257-main-paper.tex:4674](../../paper/archive/erdos249-257-main-paper.tex#L4674-L4674), [cite at paper/archive/erdos249-257-main-paper.tex:4709](../../paper/archive/erdos249-257-main-paper.tex#L4709-L4709)

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

<a id="source-source-fcf73a15ff9c7c"></a>

### [Arithmetic properties of certain functions in several variables III](https://doi.org/10.1017/S0004972700022978)

- Source id: `source-fcf73a15ff9c7c`
- Author or public identity: J. H. Loxton, A. J. van der Poorten
- Kind: `literature`
- Problems: #269
- Relationship and boundary: Cited by the linked public manuscript(s). The bibliography and citation contexts record the paper's use; no tracked primary-source closure currently verifies a stronger source-level relation.
- Source verification: `bibliography\_only` — scope not separately recorded
- Local mapping: `not recorded`

Public implementation or evidence coordinates:

- [paper/269/erdos269-running-lcm-reasoning-surface.tex](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2206-L2211) — lines `2206–2211`; excerpt `sha256:3c81099ff08107cb9d89690dc701a1f2b33082c551d8970f42b69ffbb1059df4`
- [paper/269/erdos-269-three-prime-running-lcm.tex](../../paper/269/erdos-269-three-prime-running-lcm.tex#L920-L923) — lines `920–923`; excerpt `sha256:193d1746404fe0ae7cf8a8f2af1390886c16891dab719c551712a52d637dabb9`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L64-L64) — lines `64–64`; excerpt `sha256:71a4ed241150929c0412cab2a20ac0c066225fa6cbe0646c42448dbd1503ea94`
- [paper/reasoning-parts/erdos269/back.tex](../../paper/reasoning-parts/erdos269/back.tex#L65-L70) — lines `65–70`; excerpt `sha256:3c81099ff08107cb9d89690dc701a1f2b33082c551d8970f42b69ffbb1059df4`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L81-L81) — lines `81–81`; excerpt `sha256:acdabfb8264f6b811b4caad926e53a6e9674d473c359b53dc4701d1c6c876e43`
- [paper/reasoning-parts/erdos269/core.tex](../../paper/reasoning-parts/erdos269/core.tex#L461-L461) — lines `461–461`; excerpt `sha256:c5b3131b86ecb2aefeb070e8c5f4a98a5a37f0cb54aa34700e06b8aa898bf646`

Paper citation usages:

- `erdos-269-three-prime-running-lcm`: [cite at paper/269/erdos-269-three-prime-running-lcm.tex:324](../../paper/269/erdos-269-three-prime-running-lcm.tex#L324-L324)
- `erdos269-running-lcm-reasoning-surface`: [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:132](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L132-L132), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:512](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L512-L512), [cite at paper/269/erdos269-running-lcm-reasoning-surface.tex:2205](../../paper/269/erdos269-running-lcm-reasoning-surface.tex#L2205-L2205), [cite at paper/reasoning-parts/erdos269/back.tex:64](../../paper/reasoning-parts/erdos269/back.tex#L64-L64), [cite at paper/reasoning-parts/erdos269/core.tex:81](../../paper/reasoning-parts/erdos269/core.tex#L81-L81), [cite at paper/reasoning-parts/erdos269/core.tex:461](../../paper/reasoning-parts/erdos269/core.tex#L461-L461)

## Coverage requiring review

These gaps are shown explicitly so the catalogue cannot be mistaken for complete historical knowledge.

- Registered papers scanned: `21`; TeX source files scanned after local includes: `73`.
- Citation keys without a local bibliography definition: `0`
- Bibliography entries without a curated source link: `1`
- Lean lexical candidates awaiting review: `23`
- Unresolved local TeX includes: `0`

Machine-readable inventories, hashes, unresolved keys, and lexical candidates: [source-attribution-index.json](source-attribution-index.json).
