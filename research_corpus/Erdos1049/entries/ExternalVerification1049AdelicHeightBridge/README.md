# Erdős #1049: sharp adelic height bridge

This Comparator package exposes the strongest coherent checked obstruction
family presently available at the rational base `3 / 2`.

- For every column `l`, the first nontrivial transformed normalized Zudilin
  row has exact initial monomial `-6 X^(l+1)`.  This is a genuine all-column
  partial theorem; rows `j >= 2` and the full all-rank determinant equality
  remain outside the Comparator claim.
- The exact bracket `2^64 < 3^41 < 2^65` drives a uniform rectangular
  Hermite--Padé deficit greater than `3/13` and the cubic Hankel charge ceiling.
- The source scalar-content ceiling and even the scalar-plus-forced-border
  ceiling miss the required `39/41` raw charge; the positive scalar ray has an
  explicit `17/41` relative deficit.
- At bottom depth `41T`, `130T + 2S` binary forms force a four-jet collision.
  The coefficient `130` is exactly optimal for the unit block `T = 1`, using
  the separate direct comparison `2^129 < 3^82`.  No all-`T` optimality claim
  is made.
- The bounded-fibre theorem identifies the exact finite escape interface: if
  analytic remainder fibres have uniformly bounded multiplicity, surplus
  selector entropy produces an equal-jet pair with different remainders.

The family is an exclusion and kernel package, not a solution of Erdős #1049.
It constructs no Hermite--Padé or Zudilin approximation family, proves no
analytic remainder estimate, supplies no remainder-fibre bound for the actual
family, and proves no irrationality statement for the Lambert value at `3 / 2`.

`Challenge.lean` imports only Mathlib and literally reproduces the normalized
moment, height, and four-jet definitions needed by the statements.
`Solution.lean` wraps exact declarations from
`ErdosProblems/Erdos1049/AdelicHeightBridge.lean`.
The deliberate negative provides only the upper power inequality, so
Comparator must reject it as incomplete.

The theorem portfolio is deliberately endpoint-weighted: it omits logarithmic
conversion helpers, polynomial comparison lemmas, the generic power-certificate
compiler, and the internal associated-graded Hankel recurrence. Those are
subordinate proof infrastructure. The first transformed-row endpoint is
included because it is the strongest currently complete source-facing slice
of the staged normalized-Hankel theorem.

Public paper exposition is synchronized in
`paper/erdos-1049-rational-base-lambert.tex` of the public corpus. Public Lean
source registration, portfolio-ledger registration, a pinned immutable source
identity, and terminal Comparator/NanoDa replay remain separate release gates.
The source, Challenge, and Solution pass focused Lean build plus serialized
replay; exact axiom and terminal Comparator/NanoDa receipts remain separate
gates.
