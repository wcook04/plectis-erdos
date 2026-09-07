# Wave-8: Type B assimilation verifiers (Erdős #269)

Exact-arithmetic verifiers for §14 of `../BlockKernelProgrammeLab.md`.
Every predicate is an integer comparison on certified rational brackets of
`log 2, log 3, log 5` (1200-digit `decimal`, 60 guard digits dropped).
No floating point decides any claim. Each certified quantity is computed
under **both** bracket endpoints and returned only when they agree.

| script | checks | scale | result |
|---|---|---|---|
| `exact.py` | engine: `floor_sum`, `C_p`, `T`, `s`, certified convergents | `floor_sum` vs brute force 2000 random cases; `C_p` vs brute force 72 cases; `T` vs brute force `t ≤ 59` | 0 mismatches |
| `astar_scan.py` | `A*(r) = min{A : C_{p_r}(A) odd}` along CF(`log₂3`) | 1097 certified convergents | max `A* = 13`; Geometric(½) fit; wave-7 horizon reproduced |
| `lemma_s.py` | elementary sliver-emptiness vs Lemma S | 156 instances, `A ≥ 0` | 2 failures, both the `A = 0` degeneracy |
| `lemma_s2.py` | same with the corrected hypothesis `A ≥ 1` | 161 instances to `r = 399` | **0 failures**; window tracks `log₂ p_r` |
| `fencing.py` | A22: exact identity `2Ê′ = P·X_a − X_{a+L}` and the `q=1` shadowing of `Q_a S` | 6 blocks, exact `Fraction`s | deviation **equals** `X_{a+L}/P` |
| `algebra.py` | LCM homogenisation; CRT terminal-digit star; dyadic unit ladder; rectangle top-corner forcing | 17 600 / 8 / 397 / 64 instances | 0 violations |

| `pairing.py` | Theorem P (A23) at `w=1/2`, plus the control showing the balance hypothesis is load-bearing | 33 balanced / 643 unbalanced, `i,j ≤ 25` | 0 even; control splits 313/330 |
| `pairing2.py` | Theorem P and the corollary `s(K) ≡ 1 + E₁ + E₂` | 212 balanced pairs, `i,j < 170`, max `N* = 145` | 0 violations of either |
| `pairing3.py` | size of the edge terms vs the shell count | 162 levels to `K = 408` | mean `E₁ = 29.2`, `E₂ = 29.0` vs `s = 56.2` — **not** a general reduction |
| `pairing4.py` | locates the unconditional-odd levels and the alignment obstruction (A25) | `i < 130` | 5 hits: `K = 1, 41, 124, 254, 384` |
| `offsets.py` | offset distribution of the anchor family | 7 511 anchors, `K ≤ 19 015` | one anchor per covered level, 39.5% coverage, offsets equidistributed |
| `ladder.py` / `ladder2.py` | exhaustive two-edge / one-edge anchor search (A24) | `i < 6000`, `K ≤ 19 015` | same 5 hits; `(41,28)` ladder, `3^41 5^28 ≈ 2^130` |

Run: `../../../../../repo-python astar_scan.py` etc. from this directory.

**Claim ceiling.** These verify identities, constants and finite instances.
They prove no part of Erdős #269, and neither SPREAD corner. See §14 and §15.
Theorem P (A23) and its corollaries A24/A25 are proved in §15; (ANCHOR-∞) is open.
