# Erdős 1041: exact positive double-tight continuation through twice row 29

## Exact theorem

Let \(R_{29}\) be the certified right edge of the recentered row-29 cell.
On the complete interval

\[
R_{29}\le t\le 2R_{29},
\]

the unordered positive double-tight carrier has five pairwise-disjoint
upper-half-plane sheets and the complete selected-pair excess is strictly
negative on every sheet.

## Certificate chain

Starting at \(R_{29}\), the first eighteen affine-predictor cells have centres

\[
c_0=\frac{51}{50}R_{29},\qquad c_{j+1}=\frac{207}{200}c_j,
\qquad \rho_j=\frac{c_j}{50}.
\]

They form the previously certified prefix: every cell passes exact Krawczyk,
regularity, upper-fibre exhaustion, weak-sheet sign, and predecessor-overlap
gates.  The weak sheet uses two local support re-anchors per carrier tube.
The other sheets use exact block gradient transports and the chord bound
\(2\arcsin(d/2)\le d/\sqrt{1-d^2/4}\).

The nineteenth scheduled c/50 tube fails the sheet-zero affine gate with

\[
K_a=0.0514712122097>0.05,
\qquad K_\mu=0.00468155115048<0.005.
\]

At the same centre, shrinking to c/52 repairs it exactly:

\[
K_a<0.0484377882,
\qquad K_\mu<0.00441310105,
\qquad \mathcal E_{\rm weak}<-0.105649959.
\]

The weakest of its four robust-sheet signs is
\(\mathcal E<-0.053946570\).

A tempting single c/52 endpoint tube with centre \(104R_{29}/53\) and radius
\(2R_{29}/53\) ends exactly at \(2R_{29}\), but it fails only the sheet-zero
affine gate:

\[
K_a=0.0502451076717>0.05,
\qquad K_\mu=0.00455553837574<0.005.
\]

An intermediate recenter reproduces the same value, proving that this is a
tube-width obstruction rather than predictor drift.  The final gap is instead
covered by three overlapping c/100 cells.  The last is target-locked at

\[
c=\frac{200}{101}R_{29},
\qquad \rho=\frac{2}{101}R_{29}=\frac c{100},
\qquad c+\rho=2R_{29}.
\]

Every new cell passes exact carrier self-map, regularity, five-sheet
exhaustion, weak and robust excess signs, and all five predecessor-overlap
tests.  On the last cell \(K_a<0.0195498506\), its weak-sheet bound is
\(\mathcal E<-0.180223664\), and its weakest robust bound is
\(\mathcal E<-0.501956157\).

## Replay and boundary

The full checker records the connected prefix and suffix.  The smaller suffix
checker reconstructs only the already-certified predecessor geometry and is
the fail-closed replay of the new c/52/c/100 repair:

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_geometric_to_twice.py

./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_c52_endpoint_lock.py
```

This closes exactly the positive carrier interval through \(2R_{29}\).  It
does not certify the remaining interval toward
\(\kappa_+=(1+3\sqrt3)/13\), the other double-tight regular branches, EX-W,
degree five, or unrestricted Erdős 1041.
