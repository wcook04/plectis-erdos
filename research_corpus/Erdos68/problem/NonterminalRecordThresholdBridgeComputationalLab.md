# Nonterminal record-to-threshold bridge

## Question

The repeated-valuation lane and the predecessor-gap lane were previously
separate. A strict new `q`-adic record in `n! - 1` has a Lean-checked local
effect: its complete prime power enters the actual reduced denominator at
`n + 1`, with a nonzero reduced-numerator projection. Irrationality still
needs a cofinal Archimedean producer, such as the cleared predecessor-gap
threshold.

The discriminating question is whether the first genuinely nonterminal
record is arithmetically isolated from that threshold, or whether both pieces
already compose at its actual successor state.

## Exact computation

`scripts/check_erdos68_nonterminal_record_threshold_bridge.py` independently
replays two exact calculations:

1. Multiplication modulo `971^3` verifies that `971` first divides a displayed
   factorial gap at index `361` and first divides one to second order at index
   `609`. Since `609 != 971 - 2`, this is not a terminal Wilson event.
2. Exact reduced `Fraction` arithmetic iterates the genuine predecessor-gap
   recurrence through `m=610`. At that successor, `971^2` divides the reduced
   denominator, while the reduced numerator is `41085 mod 971^2`. The pure
   integer threshold

   `((m+2)m! - 2)v_m <= m^2(m!-1)u_m`

   holds with a strictly positive margin.

The receipt stores modular values plus SHA-256/bit-length fingerprints of the
1.3-million-bit numerator, denominator, and cleared margin. This keeps the
evidence replayable without placing enormous decimal integers in generated
state.

## Consequence

This opens one finite end-to-end mechanism: a nonterminal repeated record can
feed the actual reduced denominator and a nonzero numerator projection at the
same state where the Lean-consumed Archimedean threshold closes. It rules out
the structural objection that nonterminal records are necessarily detached
from every usable threshold state.

It does not show that the record causes the inequality, that every repeated
record closes it, that such records occur cofinally, or that the series is
irrational. The next analytic target is a quantitative theorem coupling
cofinal repeated-record amplification to the numerator/denominator ratio in
the cleared threshold.
