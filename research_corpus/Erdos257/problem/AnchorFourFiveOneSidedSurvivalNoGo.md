# A finite no-go for one-sided survival from the seam laws

Status: exact symbolic countermodel, 2026-08-21.  Monotonicity of every
half-bit seam, the actual period-twenty source digits, and the uniform bound
\(f_b(n)\leq r_{4,5}(n)\) do not force either ancestry flank to survive.
Two separated flanks can both be killed at the same later odd transition.

This is a countermodel to the proposed local survival theorem, not a
counterexample in the actual \(1/465\) corridor tree.  The common prefix
below is not asserted to arise from a valid depth-\(500\) history.

## 1. Exact transition

At rank \(n\), let \(S_{n-1}\subseteq[0,K_{n-1}]\) be the current endpoint
set, where \(K_n=\lfloor n/20\rfloor\).  Fix a common lower-divisor load
\(g_n\).  At an even rank, let the inherited half-bit be the actual monotone
step function

\[
 h_n(q)=\mathbf 1_{q\leq\delta_n};
\]

at an odd rank put \(h_n(q)=0\).  The two children of endpoint \(q\) are

\[
 2q+t_n-g_n-h_n(q)-1,
 \qquad
 2q+t_n-g_n-h_n(q),                                \tag{1}
\]

intersected with \([0,K_n]\).

Start at rank \(500\) with the full endpoint interval

\[
 S_{500}=\{0,1,\ldots,25\}.                         \tag{2}
\]

Use the common selected bits

\[
 \{4,5,11,13,22,23,39,46,169\},                    \tag{3}
\]

setting every other divisor of one of \(501,\ldots,507\), below its
half-rank, to zero.  These bits give the common lower loads

\[
 (g_{501},\ldots,g_{507})=(0,0,0,1,1,4,3).          \tag{4}
\]

Indeed, the contributing bits are respectively none, none, none,
\(\{4\}\), \(\{5\}\), \(\{11,22,23,46\}\), and
\(\{13,39,169\}\).  Thus all seven loads come from one consistent Boolean
prefix; they are not chosen independently at successive ranks.
Every selected rank in (3) is at most \(169\).  This lies well inside the
quantitative common prefix through rank \(247\) supplied at depth \(500\)
by \`AnchorFourFiveCorridorCommonThird.md\`.

The source digits at ranks \(501,\ldots,507\) are all zero, since these
ranks have period-twenty residues \(1,\ldots,7\).  At the even ranks choose
the monotone seam thresholds

\[
 \delta_{502}=1,\qquad
 \delta_{504}=2,\qquad
 \delta_{506}=3.                                    \tag{5}
\]

## 2. Both flanks die

Direct application of (1) gives:

| Rank | \(g_n\) | \(\delta_n\) | Surviving endpoints |
|---:|---:|---:|---|
| 501 | 0 | -- | \(0,\ldots,25\) |
| 502 | 0 | 1 | \(0,1,3,\ldots,25\) |
| 503 | 0 | -- | \(0,1,2,5,\ldots,25\) |
| 504 | 1 | 2 | \(0,1,2,8,\ldots,25\) |
| 505 | 1 | -- | \(0,1,2,3,14,\ldots,25\) |
| 506 | 4 | 3 | \(0,1,23,24,25\) |
| 507 | 3 | -- | \(\varnothing\) |

The seam at rank \(502\) labels the endpoints \(0,1\) as the left ancestry
flank and \(3,\ldots,25\) as the right flank.  These labels are retained.
At rank \(506\), the surviving left endpoints are exactly
\(\{0,1\}\), while the surviving right endpoints are
\(\{23,24,25\}\).

At the next odd rank, there is no half-bit seam and \(g_{507}=3\).  Formula
(1) sends both left endpoints below zero:

\[
 2q-3-b<0\qquad(q=0,1;\ b\in\{0,1\}),
\]

and sends all right endpoints above \(K_{507}=25\):

\[
 2q-3-b>25\qquad(q=23,24,25;\ b\in\{0,1\}).
\]

Thus the same interval-preserving odd transition kills both separated
ancestry flanks simultaneously.

## 3. The source-capacity inequality also holds

For all \(501\leq n\leq507\),

\[
 r_{4,5}(n)=25.
\]

Even after adjoining the possible half-bit and new bit, the largest divisor
load in the construction is \(g_n+2\leq6<25\).  Hence the countermodel
respects the strong large-rank inequality \(f_b(n)\leq r_{4,5}(n)\), not
merely the weaker divisor-count bound.

The exact obstruction is therefore reachability from the earlier corridor
history.  Monotone seam order, source digits, gap growth, and
\(\tau\)-versus-\(r_{4,5}\) capacity alone cannot select an immortal
extremal flank.  A valid one-sided survival theorem must use a further
global invariant tying the common prefix at rank \(500\) to its endpoint
family.

Run

\`\`\`text
./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_one_sided_survival_nogo.py
\`\`\`

for the exact endpoint and ancestry calculation.
