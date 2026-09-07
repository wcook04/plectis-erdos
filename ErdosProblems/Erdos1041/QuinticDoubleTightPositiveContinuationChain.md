# Quintic double-tight positive continuation certificate

## Exact theorem

The ordered double-tight branch certified in
`QuinticDoubleTightPositiveLargeCellChain.md` continues as one regular branch
over

\[
 \frac{40337}{20000000}\le t\le\frac{1001}{100000}
 \qquad (0.00201685\le t\le0.01001),
\]

and its complete pair excess is strictly negative throughout.  The exact
replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_continuation_chain.py
```

Together with the preceding chain, this proves strict negativity on one
connected branch from \(t=0.00096\) through \(t=0.01001\).

## Certificate

The continuation consists of 36 exact rational affine-predictor cells.  It
uses three scales:

1. nine cells with radius \(7t/200\) and centre ratio \(53/50\);
2. twenty-six cells with radius \(t/40\) and centre ratio \(26/25\);
3. the recentered endpoint cell
   \([959/100000,1001/100000]\).

Every cell has an exact two-variable affine Krawczyk self-map, a nonvanishing
carrier Jacobian, a separated wall-orientation cross product, an exact centre
excess, and an exact positive-gradient transport bound on its complete tube.
Every consecutive overlap has a fixed-parameter Krawczyk uniqueness proof.
An additional overlap proof attaches the first continuation cell to the final
cell of the preceding certificate.

The weakest margins in the replay are

\[
 \mathcal E<-0.0025621<0,
 \qquad |\det D_{a,\mu}(E_1,E_2)|>27156,
 \qquad |\operatorname{Im}(\overline p\,q)|>2480.
\]

All Krawczyk correction radii are \(1/20\) and \(1/200\); the largest
recorded residuals remain below \(0.0191\) and \(0.00214\).  The largest
overlap ratios are below \(0.113\) in the \(a\) coordinate and \(0.179\) in
the \(\mu\) coordinate.

## Boundary

This proves a connected interval theorem only for the selected ordered
double-tight wall branch.  It does not certify every double-tight branch, the
entire quintic compact middle, other wall topologies, or the unrestricted
Erd\H{o}s problem.
