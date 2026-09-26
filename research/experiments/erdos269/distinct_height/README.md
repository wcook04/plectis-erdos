<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Distinct-height running-LCM sums

For a finite set P of primes, list the integers whose prime factors lie in P
and take the running least common multiple of that list. Summing the
reciprocal of each distinct value of the running LCM once gives

```text
D_P = 1 + sum over the prime powers t = r^n (r in P, n >= 1) of 1/H_P(t),
H_P(t) = product over r in P of r^floor(log_r t).
```

For P = {2, 3, 5} this number,
D = 1 + 1/2 + 1/6 + 1/12 + 1/60 + 1/120 + ... = 1.7796169832947490504...,
is irrational. The [#269 short paper](../../../../paper/269/erdos-269-three-prime-running-lcm.tex)
proves this by hand, and
[DistinctHeightIrrationality.lean](../../../../lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean)
checks the same argument in Lean. Erdős asserted irrationality of these distinct-value sums in a letter
dated 1 January 1973 ([Fibonacci Quarterly 12 (1974), p. 335](https://www.fq.math.ca/Scanned/12-4/letter.pdf))
without printing an argument. The same argument, together with the exact
finite certificates computed here, proves D_P irrational for every set of
three primes at most 31, and for 292 of the 330 sets of four primes at most
31; those results are ordinary proofs with exact computations and have no
Lean proof. The catalogue question of Erdős Problem #269 concerns a different sum,
the one in which a value is counted once for every integer at which it
occurs; these programs say nothing about it.

## How the proof uses a computation

Group the prime powers into the blocks (p^a, p^(a+1)], where p is the least
prime of P. A block ends at p^(a+1) and contains at most one power of each
other prime. With P_a = H_P(p^a), the normalised tail
Y_a = P_a (sum of 1/H_P(t) over t > p^a) satisfies Y_a = G(Y_(a+1)), where G
is one of finitely many increasing affine maps, determined by which powers
lie inside the block and in which order. If the images of the possible tails
under maps of different blocks are disjoint, a tail determines its block. A
rational D_P makes every K Y_a an integer in a fixed bounded interval, so two
tails coincide, the sequence of blocks becomes eventually periodic, and that
contradicts the irrationality of log p / log q. The paper proves this
implication once for every P.

For {2, 3, 5} the separation is a hand calculation: five maps, the tail
bounds 3/10 and 13/15, and four gaps between the images, the smallest 1/900.
For other sets the tail bounds come from a finite automaton that records how
many blocks have passed since each prime last appeared, and the separation
is tested after composing k maps. The test is finite; the proof that a
passing test implies irrationality is in the paper and is not executed here.

## Run it

Python 3.10 or later and the standard library suffice. From this directory:

```sh
python3 separation_235.py --output separation_235.json
python3 sweep.py --size 3 --bound 31 --max-depth 4 --output triple_sweep.json
python3 sweep.py --size 4 --bound 31 --max-depth 5 --output four_prime_sweep.json
python3 certificate.py --primes 2,3,5,7 --max-depth 7 --method both --validate-blocks 400 --output primes_2357.json
python3 test_distinct_height.py
```

| Program | What it computes | Receipt | Time |
| --- | --- | --- | --- |
| [separation_235.py](separation_235.py) | The constants of the {2, 3, 5} proof in exact arithmetic; over the first 3000 blocks, the block data derived from the heights, the tail bounds, decoding of every tail and 40 digits of D | [separation_235.json](separation_235.json) | 4 s |
| [certificate.py](certificate.py) | For one prime set: the automaton, two independent tail envelopes and the depth-k test | [primes_2357.json](primes_2357.json) | 26 s at depth 7 |
| [sweep.py](sweep.py), size 3 | All 165 sets of three primes at most 31: first passing depth, least gap, both methods | [triple_sweep.json](triple_sweep.json) | 3 s |
| [sweep.py](sweep.py), size 4 | All 330 sets of four primes at most 31, to depth 5 | [four_prime_sweep.json](four_prime_sweep.json) | 72 s |
| [test_distinct_height.py](test_distinct_height.py) | Recomputes the triple receipt and the proof constants, checks receipt hashes and negative controls | none | under 1 s |

Times are from one Apple M4 laptop.

## What the receipts contain

**The {2, 3, 5} constants.** The five block types, written by the primes of
the interior powers in increasing order, have maps G(y) = (mu + y)/b with
(b, mu) equal to (2, 1), (6, 3), (10, 3), (30, 13) and (30, 9) for the empty
block, 3, 5, 35 and 53. Every tail lies in [3/10, 13/15]. The images of that
interval are, in increasing order, [31/100, 74/225], [33/100, 29/75],
[133/300, 104/225], [11/20, 29/45] and [13/20, 14/15], for the types 53, 5,
35, 3 and the empty block. The two narrowest gaps, 1/900 and 1/180, both
amount to 13/15 < 3 * 3/10; with the trivial upper bound 1 in place of 13/15
the empty block and the block with one power of 3 would overlap.

**The triples.** Every one of the 165 sets passes: 141 at depth 1, 17 at
depth 2, 4 at depth 3 and 3 at depth 4. The last three are {2, 17, 31},
{2, 23, 29} and {2, 29, 31}; the smallest gap among all passing sets,
about 9.4e-6, belongs to {2, 17, 31}. The outer envelopes and the exact
envelopes give the same depth for every set.

**Four primes.** 292 of the 330 sets pass by depth 5 (184, 34, 28, 42 and 4
at depths 1 to 5). The other 38, among them {2, 3, 5, 7}, are undecided at
depth 5. For {2, 3, 5, 7} the test still fails at depth 7. The largest
overlap is always between the empty block and the block with one power of 3:
it has length 0.024 at depth 1 and about 1.8e-8 at depth 7, and two further
pairs of types still overlap at depth 7. The tails of {2, 3, 5, 7} range over
about [0.188, 0.785], so the largest exceeds three times the smallest; the
{2, 3, 5} proof rests on the opposite inequality 13/15 < 3 * 3/10.

A set without a passing depth is undecided by this automaton at that depth.
The automaton allows every ordering of the interior powers and records the
primes separately, so a finer description of which blocks can follow which
might still separate it.

**Two envelope computations.** The outer envelopes start from
[0, 1/(p-1)] and repeatedly take the hull of the images of the next states,
rounding outwards to multiples of 2^-96; they contain every tail after any
number of rounds, and they are the certificate the paper describes. The
exact envelopes are the least and greatest values of infinite automaton
paths, found by policy iteration and checked by substituting them into
their defining equations. The outer envelopes contain the exact ones.

## Scope

All arithmetic is exact rational arithmetic; no floating-point value enters
a decision. The comparison of the automaton with the actual block words,
and of the tails with their envelopes, covers finitely many blocks and is a
consistency check only. The receipts record the program hashes, and the
test fails if a program changes without its receipt being regenerated.
None of these programs proves irrationality of the repeated sum
R_P = sum over n of 1/[a_1, ..., a_n] that Erdős Problem #269 asks about.
There the numerators that replace mu grow quadratically, the integer tails
that a rational value would produce are unbounded, and the finite-state
argument above has no counterpart.
