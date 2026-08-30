# Quintic double-tight positive large-cell chain certificate

## Exact theorem

On the ordered double-tight carrier of the quintic wall, there is one connected
regular branch over

\[
  \frac{3}{3125}\le t\le \frac{101}{50000}
  \qquad (0.00096\le t\le 0.00202),
\]

and the complete pair excess on this branch is strictly negative throughout.
The branch is the same branch as the already certified cell at
\(t=1/1000\).

The exact replay is

```bash
python3 research_corpus/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_large_cell_chain.py
```

## Certificate structure

The interval is the connected union of fifteen rational cells.  Their centres
are

\[
  t_j=\frac{100+7j}{100000}\quad(0\le j\le14),
\]

and every radius is \(1/25000\).  Consecutive cells overlap by
\(1/100000\).  In each cell the checker:

1. substitutes the affine predictor for \((a(t),\mu(t))\) into the two exact
   carrier polynomials and proves a two-variable Krawczyk self-map;
2. proves that the carrier Jacobian is nonsingular and the oriented wall cross
   product stays separated from zero;
3. computes the centre-fibre excess by exact support--Stieltjes integration;
4. bounds the two positive wall-gradient densities on the complete parameter
   tube and transports the centre sign using exact implicit derivatives;
5. applies a fixed-parameter Krawczyk uniqueness test in every overlap, proving
   that all fifteen local graphs are one branch.

The weakest Krawczyk and regularity margins occur in the first cell:

\[
 K_a<0.006166<0.01,
 \qquad K_\mu<0.000836<0.001,
\]

\[
 |\det D_{a,\mu}(E_1,E_2)|>11455,
 \qquad |\operatorname{Im}(\overline p\,q)|>1938.
\]

The weakest transported sign also occurs in the first cell and is

\[
  \mathcal E<-0.0448<0.
\]

The final cell has \(\mathcal E<-0.0918\).  Every overlap uniqueness ratio is
strictly below one; the largest recorded ratios are
\(K_a/R_a<0.250\) and \(K_\mu/R_\mu<0.393\).

## Boundary

This is a rigorous positive-\(t\) interval theorem for one ordered
double-tight wall branch.  It does not certify the entire double-tight carrier,
the compact middle of the quintic model, any other wall topology, or the
unrestricted Erd\H{o}s problem.  Its role is to replace a point or microscopic
seed by a connected interval of width \(53/50000\) with exact branch identity
and a uniform strict sign.
