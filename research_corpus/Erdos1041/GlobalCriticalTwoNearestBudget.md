# Global two-nearest-root budget at a critical point

## Outcome

Let

\[
f(z)=\prod_{j=1}^n(z-z_j),\qquad |z_j|\le 1,qquad n\ge2,
\]

and let \(c\) be a zero of \(f'\).  Roots are counted with multiplicity.  Then
two roots satisfy

\[
|z_i-c|+|z_j-c|\le2.
\]

In fact, when \(c\) is not itself a root, the two nearest roots to \(c\) have
this property.  This is global: the earlier auxiliary restriction
\(|c|\le1-2/n\) is unnecessary.

This settles the metric-budget subproblem B1 for Erdős #1041.  It does **not**
settle the original problem, because it does not yet put a path between the
selected roots inside \(\{|f|<1\}\).

## Proof

If \(c\) is a root, then it is a multiple root and two copies of that root give
sum zero.  Suppose henceforth that \(f(c)\ne0\).  Rotate so that \(c=t\ge0\),
and write

\[
w_j=z_j-c=d_j e^{i\phi_j},\qquad
0<\delta=d_1\le e=d_2\le\cdots\le d_n.
\]

The critical-point identity is

\[
\sum_{j=1}^n\frac1{w_j}=0. \tag{1}
\]

Put \(m^2=1-t^2\).  The unit-disk constraint gives, for every \(j\),

\[
d_j^2+2t\,\Re w_j\le m^2.
\]

Divide by \(d_j^2\), sum, and use (1):

\[
n\le m^2\sum_{j=1}^n\frac1{d_j^2}. \tag{2}
\]

This also shows \(t<1\): at \(t=1\), its pre-division summed form would say
\(n\le0\).  Since \(\delta\) is the least distance, (2) implies
\(\delta^2\le m^2\), and hence \(\delta\le1\).

The reciprocal balance (1), isolated at a nearest root, gives

\[
\frac1\delta
 =\left|\sum_{j=2}^n\frac1{w_j}\right|
 \le\sum_{j=2}^n\frac1{d_j}
 \le\frac{n-1}{e},
\]

so

\[
e\le(n-1)\delta. \tag{3}
\]

Assume for contradiction that \(\delta+e>2\).  Because \(\delta\le1\), this
forces \(e>1\).  The triangle inequality gives \(e\le1+t\), so the assumed
violation gives \(\delta>1-t\).  Consequently

\[
m^2=1-t^2
   <\delta(2-\delta)
   <\delta e. \tag{4}
\]

Combining (2), the ordering \(d_1=\delta\), \(d_j\ge e\) for \(j\ge2\), and
(4), we obtain

\[
\begin{aligned}
n
&\le m^2\sum_j d_j^{-2}\\
&\le m^2\left(\delta^{-2}+(n-1)e^{-2}\right)\\
&<\delta e\left(\delta^{-2}+(n-1)e^{-2}\right)\\
&=\frac e\delta+(n-1)\frac\delta e.
\end{aligned} \tag{5}
\]

Set \(x=e/\delta\).  The ordering and (3) say \(1\le x\le n-1\).  Therefore

\[
(x-1)(x-(n-1))\le0,
\]

which is exactly

\[
x+\frac{n-1}{x}\le n.
\]

This contradicts (5), completing the proof.

## Formal and computational receipts

The real inequality chain from the disk, diameter, reciprocal-balance, and
inverse-square hypotheses is checked in
[`CriticalTwoRootProximity.lean`](./CriticalTwoRootProximity.lean#L160-L166) as
`two_add_le_two_of_disk_inverse_balance`; the geometric-mean root-selection
consumer is the adjacent declaration
[`exists_two_roots_dist_sum_le_two_mul_geomMean`](./CriticalTwoRootProximity.lean#L229-L234).
The focused replay is

```sh
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py \
  --jobs 2 --project-root formal_math/erdos257_period_noncollapse \
  ErdosProblems.Erdos1041.CriticalTwoRootProximity
```

This formal source checks the metric-budget declarations only; it does not
provide containment of the selected pair in the open lemniscate.

The older quartic descent report appeared to give a normalized first-merge
budget above one.  Exact recovery of its decimal roots and residual-gated
inverse-value continuation shows that report switched branches: the actual
minimum-critical pair lands at roots 0 and 1, with normalized curved length
approximately \(0.7385324012\).  The reproducible regression checker is
`scripts/check_legacy_minimum_critical_descent_regression.py` and its generated
receipt is
`state/formal_math/erdos257_period_noncollapse/erdos1041_legacy_minimum_critical_descent_regression_receipt.json`.

The regression is evidence about the historical computation only; it is not
used in the proof above.

## Consequence for the remaining problem

The critical point supplies the sharp total Euclidean budget everywhere in the
disk.  What remains is purely a containment/selection theorem: select two of
the budgeted roots and realize a path of length at most their critical-point
distance sum inside the open unit lemniscate.  The exact unique-nearest-spoke
example already rules out proving this by asserting that every straight spoke
is contained.  Any completion must use descending inverse branches or another
curved-path mechanism.
