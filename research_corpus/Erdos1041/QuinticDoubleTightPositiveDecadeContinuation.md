# Erdős 1041: common five-sheet positive double-tight continuation

## Exact theorem

On the positive regular interval

\[
 \frac{4949}{500000}\le t\le
 \frac{12116785580404918688981310598233490936176657}
      {655360000000000000000000000000000000000000000},
\]

whose decimal endpoints are approximately (0.009898) and
(0.01848874752869403), the unordered double-tight carrier has five
pairwise-disjoint upper-half-plane sheets, and the complete pair excess is
strictly negative on every sheet.

The exact replay is

```bash
python3 research_corpus/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_decade_continuation.py
```

The first common cell overlaps the preceding positive continuation, so this
extends the already certified complete physical upper fibre rather than
introducing an unconnected collection of roots.

## Certificate

The checker uses eighteen rational affine-predictor cells.  Their centres
start at (101/10000), increase by the exact ratio (207/200), and have
radius (t/50).  On every cell and every one of the five sheets it proves:

1. an exact two-variable Krawczyk self-map for the carrier equations;
2. nonvanishing of the carrier Jacobian and strict wall-orientation
   separation;
3. strict upper-half-plane containment and pairwise separation of the five
   root tubes;
4. strict negativity of the exact support--Stieltjes excess after positive
   wall-gradient transport;
5. fixed-parameter Krawczyk uniqueness on every consecutive overlap.

Theorem CV gives exactly five upper-half-plane carrier roots on this regular
interval.  Thus the five certified, pairwise-disjoint tubes exhaust the
physical upper fibre.  The weak sheet is checked cell by cell.  Sheets one
and two use exact two-cell parameter hulls for their sign transport, while
the two near-twin sheets use one exact hull across the full interval.

The weakest recorded sign is on the weak sheet in the last cell:

\[
 \mathcal E<-0.000846889<0.
\]

Across all ninety carrier cells, the weakest regularity and separation
margins are

\[
 |det D_{a,\mu}(E_1,E_2)|>79.8120664,
 \qquad
 |\operatorname{Im}(\overline p q)|>0.00199119464,
\]

and the smallest certified distance between distinct upper root tubes is
greater than (0.0107790003).  All eighty-five consecutive sheet-overlap
Krawczyk tests are strict; the largest displayed overlap ratios are below
(0.125) in the (a) coordinate and below (0.163) in the \(\mu\)
coordinate.

## Boundary

This is an exact common-five-sheet theorem only on the displayed connected
positive interval.  It does not certify the remainder of the positive
carrier interval, the other regular double-tight intervals, the nonregular
event fibres, any other wall topology, degree five, or the unrestricted
Erdős problem.  In particular, no sign is asserted beyond the exact upper
endpoint written above.
