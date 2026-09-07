# No cofinally growing zero windows (`prop:257-no-growing-zero-windows`)

**Status.** Ordinary observation already proved in
`ElementarySupportConstraints.md` (Zero windows). Recorded here as the r6
long-record destination label. Frozen R
`public-source-redacted://release-final-20260905` is not
mutated. Authored long-record TeX is not mutated.

**Proposition** (`prop:257-no-growing-zero-windows`).
Let \(A\subseteq\mathbb N_{>0}\) be nonempty and \(a_0=\min A\). Every
zero window of the divisor incidence \(c_A(n)=\#\{a\in A:a\mid n\}\) has
length at most \(a_0-1\). In particular there are no cofinally many
super-logarithmic zero windows on a nonempty support.

**Proof.** Every block of \(a_0\) consecutive integers contains a multiple
of \(a_0\), hence a point with \(c_A\ge 1\). ∎

The r6 lag note records that `a257_front.tex` `ssec:route-5` and
`a257_invent.tex` `sec:invent-R5` still write a disjunction whose first
branch is those impossible windows. That branch is empty, so the proposed
sparse/dense split reduces to its universal-certificate branch. The
separate lcm-gap criterion is a different information source and is not
refuted by this observation.

This is a logical diagnosis of an explanatory route, not a claim that every
sparsity method fails, and not a parent-solved claim.
