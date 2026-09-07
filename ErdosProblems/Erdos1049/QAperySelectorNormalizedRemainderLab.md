# q-Apéry selector normalized-remainder no-go

## The missing consumer

The moving-tail receipts construct, at each displayed start, two noncollinear
integer coefficient pairs `(A_i,B_i)` divisible by

`M_s=2^(3s^2+3s+1) 3^(s+1)`.

Write `(A_i,B_i)=M_s(A_i',B_i')`.  If the Lambert value were `F=a/q`, then

`q(B_i'F-A_i')=B_i'a-qA_i'`

would be an integer.  Noncollinearity proves that the two normalized forms
cannot both vanish.  Therefore an actual irrationality consumer needs **both**
absolute normalized remainders to tend to zero; for a fixed hypothetical `q`,
eventually both must be below `1/q`.

Modular collision and nonvanishing alone say nothing about this size.

## Source and attribution boundary

The Lambert target and q-Apéry approximant family are grounded in the
downloaded primary source Tewodros Amdeberhan and Doron Zeilberger, *q-Apéry
Irrationality Proofs by q-WZ pairs*, Advances in Applied Mathematics 20 (1998),
275--283, `annexes/arxiv-math9804122-amdeberhan-zeilberger/source.tex`,
arXiv:math/9804122.  Its source lines 31--50 define `h_q(1)` and distinguish
the integer-base results from the general q identities; lines 72--95 define
the q-WZ-derived sequences, and lines 196--207 state the source's decay lemma
and integer-base theorem.  The downloaded source does not state the stored
selector pairs, their normalized q = 3/2 remainder bounds, or the present
consumer-level no-go.  Those exact rational brackets, the noncollinearity
argument, and the construction handoff are authored and replayed in this
repository; this note does not claim an all-start selector theorem or
irrationality at q = 3/2.

## Exact replay of the stored selectors

The checker divides every stored pair by its exact modulus and brackets
`B_i'F-A_i'` using a 30000-bit, 24000-term rational bracket for `F(3/2)`.
At every start `s=1,2,3,4`, both absolute lower bounds exceed one.  Their
natural-log lower bounds are approximately

| start | selector 1 | selector 2 |
|---:|---:|---:|
| 1 | 64.006 | 64.006 |
| 2 | 203.662 | 491.979 |
| 3 | 1298.885 | 1566.660 |
| 4 | 2678.087 | 2609.558 |

These are exact rational inequalities; the logarithms only summarize their
scale.  Since both normalized forms are already larger than one, none of these
stored pairs can contradict rationality for any positive denominator `q`.

## Consequence

This eliminates reuse of the stored modular-only LLL/BKZ selector sequence as
the analytic fan-in.  It does not eliminate moving-tail compression or an
adelic construction.  It changes the construction target: normalized real
remainder must be a coordinate of the lattice objective itself, alongside the
2-adic and 3-adic constraints.  A coefficient cap selected without that real
coordinate is not a useful height proxy.

Replay:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_qapery_selector_normalized_remainder.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/scripts/check_qapery_selector_normalized_remainder.py --check
```
