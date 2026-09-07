# The upper-suffix divisor resolvent for \(1/465\)

Status: exact ordinary deductions, 2026-08-21.  The computation in Section 5
is a finite directed-interval audit.  The note does not prove the required
all-depth quotient-row interval.

Put

\[
 x=\frac1{465},\qquad w_d=\frac1{2^d-1},
\]

and let \(b_d\in\{0,1\}\) be the real-greedy word for \(x\).  Write

\[
 H_n=\lfloor 2^nx\rfloor,
 \qquad q_{n,d}=\left\lfloor\frac{2^n}{2^d-1}\right\rfloor,
\]

and define the quotient defect

\[
 Q_n=H_n-\sum_{d\leq n}b_dq_{n,d}.                 \tag{1}
\]

The purpose of this note is to identify exactly how an upper binary suffix
repays the defect in (1).  The resulting identity joins the binary-hole and
divisor-pulse mechanisms without an intermediate estimate.

## 1. The quotient-tail interval

Fix \(N\), put \(M=\lfloor N/2\rfloor\), and let

\[
 B_{N,M}=\sum_{d\leq M}b_dq_{N,d}.
\]

For every \(d>M\), one has \(2d>N\), and hence

\[
 q_{N,d}=2^{N-d}.                                  \tag{2}
\]

The quotient rows with ranks \(M+1,\ldots,N\) are therefore the ordinary
binary coins

\[
 1,2,\ldots,2^{N-M-1}.
\]

They represent every integer from \(0\) to

\[
 C_{N,M}=2^{N-M}-1.                                \tag{3}
\]

Consequently the fixed head \(\{d\leq M:b_d=1\}\), followed by arbitrary
upper-tail choices, represents every integer in

\[
 [B_{N,M},B_{N,M}+C_{N,M}].                        \tag{4}
\]

Let

\[
 Z_{N,M}=\sum_{M<d\leq N}b_d2^{N-d}
\]

be the integer encoded by the actual greedy suffix.  Splitting (1) at
\(M\) and using (2) gives the exact endpoint distance

\[
 \boxed{H_N-B_{N,M}=Z_{N,M}+Q_N.}                  \tag{5}
\]

Thus the interval (4) reaches \(H_N\) precisely when

\[
 Z_{N,M}+Q_N\leq C_{N,M}.                          \tag{6}
\]

This is a sufficient certificate for quotient compactness, not an assertion
that the actual greedy head is the only possible head.

## 2. Exact cancellation of the current greedy bit

It is useful first to take an arbitrary base depth \(M\) and a horizon
\(M+h\), where \(1\leq h\leq M\).  Define the suffix-hole integer by

\[
 J_{M,0}=0,\qquad
 J_{M,h}=2J_{M,h-1}+1-b_{M+h}.                     \tag{7}
\]

Hence

\[
 J_{M,h}=2^h-1-Z_{M+h,M}.
\]

Let \(t_n=H_n-2H_{n-1}\) be the binary digits of \(x\), and put

\[
 s_n=\sum_{\substack{d\mid n\\d<n}}b_d.
\]

The quotient recurrence is

\[
 Q_n=2Q_{n-1}+t_n-s_n-b_n.                        \tag{8}
\]

Subtracting (8) from (7) cancels \(b_n\) exactly.  If

\[
 D_{M,h}=J_{M,h}-Q_{M+h},
\]

then

\[
 \boxed{D_{M,0}=-Q_M,\qquad
 D_{M,h}=2D_{M,h-1}+1-t_{M+h}+s_{M+h}.}            \tag{9}
\]

Because \(h\leq M\), every proper divisor of \(M+h\) is at most \(M\).
The repayment in (9) is therefore determined entirely by the head at depth
\(M\): the new suffix bit has disappeared, and no later selected rank can
enter a divisor pulse before the horizon \(2M\).

Combining (5), (7), and (9),

\[
 D_{M,h}\geq0
 \quad\Longleftrightarrow\quad
 H_{M+h}-B_{M+h,M}\leq2^h-1.                      \tag{10}
\]

Thus (9) is the exact upper-capacity condition for the binary quotient tail.

## 3. The infinite payment identity

For all \(n>M\), define the fixed-head divisor pulse

\[
 s_n^{(M)}=\sum_{\substack{d\leq M\\d\mid n}}b_d. \tag{11}
\]

For \(n\leq2M\), this is the proper-divisor pulse \(s_n\) in (9).  Let

\[
 r_M=x-\sum_{d\leq M}b_dw_d,
 \qquad y_M=2^Mr_M,
 \qquad \alpha_M=\{2^Mx\},                        \tag{12}
\]

and

\[
 \rho_{M,d}=\left\{\frac{2^M}{2^d-1}\right\}
             =\frac{2^{M\bmod d}}{2^d-1},
 \qquad
 F_M=\sum_{d\leq M}b_d\rho_{M,d}.                 \tag{13}
\]

The floor decomposition of (1) gives

\[
 Q_M=y_M-\alpha_M+F_M.                             \tag{14}
\]

The same fractional phases are the discounted future divisor pulses.  For
each selected \(d\leq M\), a geometric series over the multiples of \(d\)
strictly above \(M\) gives

\[
 \sum_{\substack{n>M\\d\mid n}}2^{M-n}
 =\frac{2^{M\bmod d}}{2^d-1}=\rho_{M,d}.           \tag{15}
\]

Also, since \(465\) is odd, its nonterminating binary expansion gives

\[
 \sum_{n>M}2^{M-n}t_n=\alpha_M.                   \tag{16}
\]

Summing (15) over the selected head and combining it with (14)--(16) proves
the resolvent identity

\[
 \boxed{
 \sum_{n>M}2^{M-n}\bigl(1-t_n+s_n^{(M)}\bigr)
 =Q_M+1-y_M.}                                      \tag{17}
\]

Thus the complete future zero-digit and divisor-pulse payment exceeds the
present quotient debt by exactly \(1-y_M\).  The quotient phases and the
divisor/LCM pulses do not merely have comparable size; they cancel globally.

## 4. A finite-horizon bound

For \(1/465\), the first selected rank is \(9\).  Let

\[
 P_M=\sum_{d\leq M}b_d.
\]

After truncating (17) at \(M+h\), the omitted zero-digit contribution is at
most \(2^{-h}\).  For each selected \(d\geq9\), the first omitted multiple is
at least \(M+h+1\), so its omitted geometric tail is at most

\[
 \frac{2^{-h-1}}{1-2^{-d}}
 \leq\frac{256}{511}2^{-h}.
\]

Therefore

\[
 \begin{aligned}
 &-Q_M+\sum_{j=1}^h2^{-j}
       \bigl(1-t_{M+j}+s_{M+j}^{(M)}\bigr)\\
 &\hspace{18mm}\geq
 1-y_M-\left(1+\frac{256}{511}P_M\right)2^{-h}.
                                                               \tag{18}
 \end{aligned}
\]

When \(h\leq M\), the left side of (18) is \(2^{-h}D_{M,h}\).  Hence the
explicit sufficient condition

\[
 \boxed{
 2^h(1-y_M)\geq1+\frac{256}{511}P_M
 \quad\Longrightarrow\quad D_{M,h}\geq0.}          \tag{19}
\]

In particular, the desired half-row capacity at horizon \(2M\) would follow
from

\[
 1-y_M\geq
 \left(1+\frac{256}{511}P_M\right)2^{-M}.           \tag{20}
\]

Equation (20) is an anti-preterminal estimate: it excludes an exponentially
small approach of the scaled real residual to the all-selected boundary.
It is not proved here.  `AnchorFourFiveSharpDefectPulseDichotomy.md` bounds
the scaled residual when a later skip is supplied, while
`AnchorFourFiveOwnershipCompression.md` and
`AnchorFourFiveFirstTypeBreak.md` follow the corresponding positive-cylinder
ownership state through its first nonlocal recuts.  None of those results
supplies the quantitative lower bound in (20).  Thus (17) should not be
presented as a reduction of the full problem; it is the exact law obeyed by
the previously separate mechanisms.

At the half horizon there is a sharper phase form than (20).  Put

\[
 F_{2M}^{(M)}=
 \sum_{d\leq M}b_d
 \left\{\frac{2^{2M}}{2^d-1}\right\}.
\]

Expanding the head floors directly gives

\[
 \boxed{D_{M,M}=2^M(1-y_M)-1+alpha_{2M}-F_{2M}^{(M)}.}
                                                               \tag{20a}
\]

The universal fractional-phase estimate

\[
 \sum_{d=2}^{N}
 \left\{\frac{2^N}{2^d-1}\right\}
 <2\lfloor\sqrt N\rfloor                           \tag{20b}
\]

implies \(F_{2M}^{(M)}<2\lfloor\sqrt{2M}\rfloor\).  For completeness,
(20b) follows by treating \(d\leq\lfloor\sqrt N\rfloor\) with the bound
\(2/3\), and grouping larger \(d\) by \(q=\lfloor N/d\rfloor\).  Within a
fixed group, the complementary residues increase by at least two, so its
geometric contribution is at most \(4/3\).  This is the square-root phase
estimate proved in `ReservoirComparatorAttack.md`.

## 5. Localization at the next greedy zero

There is a direct way to obtain (20) unless the next zero is very close to
the doubled horizon.  Suppose that \(k>M\) is the first rank after \(M\)
with \(b_k=0\).  Greediness at the skipped rank gives

\[
 r_M=\sum_{d=M+1}^{k-1}w_d+r_{k-1}
 <\sum_{d=M+1}^{k}w_d.                             \tag{21}
\]

Moreover,

\[
 w_d-2^{-d}=\frac1{2^d(2^d-1)}<2^{1-2d},
\]

and hence

\[
 \sum_{d>M}(w_d-2^{-d})<\frac23\,4^{-M}.          \tag{22}
\]

Subtracting (21) from the complete dyadic tail and using (22) yields

\[
 \boxed{1-y_M>
 \left(2^{2M-k}-\frac23\right)2^{-M}.}             \tag{23}
\]

Define

\[
 \mu_M=
 \left\lceil\log_2\left(\frac53+2\lfloor\sqrt{2M}\rfloor\right)
 \right\rceil.                                     \tag{24}
\]

If the next zero satisfies \(k\leq2M-\mu_M\), then (20a), (20b), and
(23) imply \(D_{M,M}>0\).  Consequently failure of the
half-row upper-capacity condition is confined to a suffix-almost-one event:
there is no zero after \(M\), or the first such zero lies among the final
\(\mu_M-1=\tfrac12\log_2M+O(1)\) ranks before \(2M\).

This is a one-way exclusion, not a characterization: a late first zero does
not imply capacity failure.  The remaining product-specific task is to show
that the period-20 source and the selected divisor clocks repay the defect
even in this logarithmic terminal corridor.

## 6. The fixed-window conjecture fails

The recurrence (9) can become nonnegative quickly without having a uniform
payment time.  Exact directed dyadic arithmetic finds the first failure of
eight-step solvency at

\[
 M=1298,\qquad Q_M=2.                              \tag{25}
\]

For horizons \(1299,\ldots,1306\), the values of \(D_{M,h}\) are

\[
 -4,-2,-3,-2,-3,-3,-1,-1.                         \tag{26}
\]

The state first becomes nonnegative at delay \(10\), where its value is
\(2\).  Thus no proof may use the
empirically suggested constant eight.  A directed audit through base depth
\(25{,}000\) finds payment delays as large as \(19\); this is finite evidence,
not an asymptotic statement.  The natural quantity is the growing payment
delay

\[
 \ell(M)=\min\{h\geq0:D_{M,h}\geq0\}.              \tag{27}
\]

and (19) bounds it in terms of the anti-preterminal margin \(1-y_M\).

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/upper_suffix_divisor_resolvent_audit.py
```

for the exact finite counterexample and recurrence checks.
