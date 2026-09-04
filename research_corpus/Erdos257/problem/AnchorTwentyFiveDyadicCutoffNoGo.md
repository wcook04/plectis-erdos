# The anchor-25 dyadic cutoff and a finite run-bound no-go

## Status

This note proves an exact equivalence between the dyadic undershoot sought for
the \(1/465\) greedy orbit and the leading run of its anchor-25 coefficient. A
directed exact computation then disproves the first plausible uniform run
bound on the actual orbit. It does not disprove the dyadic undershoot itself:
no violating skip is found through rank \(100000\), but this is only a finite
calculation.

Put

\[
 w_n=\frac1{2^n-1},\qquad x=\frac1{465},\qquad A=2^{25}-1,
\]

and let \(r_m\) be the residual after the real-greedy decision at rank \(m\).

## 1. The exact anchor/dyadic equivalence

Assume that rank \(m\) is skipped. Then

\[
 0<r_m<w_m.                                               \tag{1}
\]

The binary expansion of the upper endpoint after anchor scaling is

\[
 \frac{A}{2^m-1}
 =\sum_{q\geq1}\sum_{i=0}^{24}2^{-(qm-i)}.                \tag{2}
\]

Its first block consists of ones at positions

\[
 m-24,m-23,\ldots,m.
\]

The terminating binary expansion of the scaled dyadic cutoff is exactly this
first block:

\[
 A2^{-m}=\sum_{i=0}^{24}2^{-(m-i)}.                       \tag{3}
\]

Every number in the half-open interval between (3) and (2) therefore has the
same first 25 nonzero binary digits. Conversely, (1) prevents the first
nonzero digit of \(Ar_m\) from occurring before position \(m-24\). Hence

\[
 \boxed{
 r_m\geq2^{-m}
 \quad\Longleftrightarrow\quad
 Ar_m\text{ begins at position }m-24\text{ with }1^{25}.} \tag{4}
\]

Thus the proposed target-specific estimate

\[
 b_m=0\quad\Longrightarrow\quad r_m<2^{-m}                \tag{5}
\]

is not merely analogous to the anchor reachability problem. It is exactly the
assertion that no skipped anchor state reaches the 25-one cylinder.

There is an equivalent reduced-fraction form. Write \(r_m=u/v\) with
\(\gcd(u,v)=1\). All Mersenne denominators are odd, so \(v\) is odd and
equality with \(2^{-m}\) is impossible. The dangerous skipped interval is
equivalent to

\[
 (2^m-1)u<v<2^mu,                                        \tag{6}
\]

or, for the positive odd integer \(g=2^mu-v\),

\[
 1\leq g<u,\qquad \gcd(g,uv)=1.                          \tag{7}
\]

Equation (7) is the exact integer corridor which a residue invariant would
have to exclude. Coprimality alone cannot exclude it; the static family
\(2/(2^L-1)\) has \(g=1\).

## 2. Why the cutoff would close the terminal branch

Let

\[
 T_m=\sum_{n>m}w_n.
\]

Termwise comparison with the dyadic tail gives

\[
 T_m>\sum_{n>m}2^{-n}=2^{-m}.                            \tag{8}
\]

If \(m\) were the final skipped rank on a nonrepresenting greedy branch, its
residual would exceed the remaining capacity \(T_m\). Equations (5) and (8)
would give the contradiction

\[
 r_m<2^{-m}<T_m<r_m.
\]

Thus (5) is a genuine sufficient theorem for excluding the terminal branch,
not another restatement of its full tail inequality.

## 3. The half-period run bound is false on the actual orbit

The first finite data suggest that the interaction of source period \(20\)
and anchor length \(25\) might cap the aligned leading run at \(10\). That
claim is false for the actual \(1/465\) greedy orbit.

Directed dyadic integer arithmetic certifies that rank

\[
 m=24092
\]

is skipped and that the binary expansion of \(Ar_m\) begins at position
\(24068=m-24\) with

\[
 1^{16}0.                                                \tag{9}
\]

The last preceding take is at rank \(24088\); ranks \(24089,\ldots,24092\)
are skipped. Thus the length-16 block is produced by the full actual affine
mask history, rather than by a static denominator countermodel. An extended
directed audit through rank \(100000\) finds a length-17 aligned run at the
skipped rank \(80364\).

The predecessor word makes the exposure mechanism explicit. Immediately
before the take at \(24088\), the anchor coefficient begins at position
\(24063\) with

\[
 1\,0^4\,1^{16}0.
\]

Subtracting the rank-\(24088\) mask and then making four skips exposes the
internal length-16 run at the front. The actual take/skip word over ranks
\(24080,\ldots,24092\) is

\[
 1010111110000.
\]

The extremal state is not a small-carry anomaly. In the product/quotient
coordinates its exact integer data are

\[
 Q_m=2,\qquad K_m=\left\lfloor\frac m{20}\right\rfloor=1204,
 \qquad E_m=K_m-Q_m=1202,                               \tag{10}
\]

and the selected prefix has \(11962\) ranks. The target phase is

\[
 \alpha_m=\left\{\frac{2^m}{465}\right\}=\frac{376}{465}. \tag{11}
\]

Writing \(y_m=2^mr_m\), directed integer bounds give the rigorous enclosure

\[
 \frac{252419230679353}{2^{64}}
 <1-y_m<
 \frac{252419230679354}{2^{64}}.                        \tag{12}
\]

Thus \(1-y_m\) is about \(1.36837\cdot10^{-5}\). If

\[
 F_m=\sum_{\substack{d\leq m\\b_d=1}}
       \frac{2^{m\bmod d}}{2^d-1},
\]

then the exact phase identity \(y_m=Q_m+\alpha_m-F_m\) and (12) put \(F_m\)
between

\[
 1+\frac{376}{465}
 +\frac{252419230679353}{2^{64}}
\quad\hbox{and}\quad
 1+\frac{376}{465}
 +\frac{252419230679354}{2^{64}}.                        \tag{13}
\]

The selected proper divisors of \(m\) are exactly

\[
 19,76,634,1268,6023,12046,                              \tag{14}
\]

so the endpoint divisor pulse is \(6\). Over ranks \(24080,\ldots,24092\),
the quotient defect follows

\[
 3,2,2,4,2,3,4,4,5,7,2,4,2.                            \tag{15}
\]

In particular, the near-boundary event coexists with a large raw-product
carry \(E_m\); neither a small quotient defect nor a large product carry
separates the dyadic seam. The separating quantity in this state is the
strict phase excess

\[
 F_m-(Q_m+\alpha_m-1)=1-y_m>0.                           \tag{16}
\]

A first hypothetical unsafe skip would reverse precisely this sign while
remaining in the numerator-sized coprime corridor (7). This is the exact
target-coupled obstruction: an all-depth proof must show that the selected
divisor phase stays strictly above \(Q_m+\alpha_m-1\) whenever rank \(m\) is
skipped. Formula (10) shows that replacing this phase condition by a bound on
\(E_m\) loses the relevant information.

Neither event violates (5), because both runs stop before length \(25\).
They do show that the repeated length-10 phenomenon and the number
\(\gcd(20,25)\) do not provide a fixed local run bound. The maximum certified
aligned run grows from 16 through rank \(30000\) to 17 through rank \(100000\).
These maxima are finite observations, not an asymptotic claim.

## 4. Exact predecessor law for a first unsafe cylinder

The affine recurrence can manufacture a 25-run from a predecessor with no
25-run. Suppose \(m\geq75\) is an unsafe skip, let \(p=m-g\) be the last
preceding selected rank, and assume \(1\leq g\leq24\). Put

\[
 c=Ar_m,\qquad \widetilde c=A(r_m+w_p).
\]

The unsafe skipped interval and (2)--(3) give

\[
 c=A2^{-m}+\varepsilon,\qquad
 0<\varepsilon<\frac{A}{2^m(2^m-1)}.                    \tag{17}
\]

Likewise,

\[
 \frac{A}{2^p-1}=A2^{-p}+\eta,\qquad
 \eta=\frac{A}{2^p(2^p-1)}.                             \tag{18}
\]

Since \(p=m-g\), \(A<2^{25}\), and \(2^n-1>2^{n-1}\),

\[
 0<\varepsilon+\eta
 <2^{27-2m+2g}\leq2^{-m}.                              \tag{19}
\]

Therefore the first \(m\) binary digits of \(\widetilde c\) are exactly those
of the terminating dyadic number

\[
 A2^{-p}+A2^{-m}.
\]

After multiplication by \(2^m\), its numerator is

\[
 A(2^g+1)
 =2^{25+g}+2^{25}-2^g-1.
\]

Direct binary subtraction gives the forced predecessor word

\[
 \boxed{1\,0^g\,1^{24-g}\,0\,1^g.}                     \tag{20}
\]

For every \(1\leq g\leq24\), each one-run in (20) has length at most \(24\).
Thus absence of a 25-run is not preserved by the actual affine take map: the
overlap of the rank-\(p\) anchor block with the later dangerous block creates
the 25-run by carry. This rules out a backward proof based only on a
shift-invariant forbidden language of leading coefficient words. A viable
backward invariant must retain the overlap gap \(g\) and the ancestry of the
two blocks, including the divisor masks which can enter beyond the first
harmonic.

## 5. Boundary

The anchor formulation has therefore isolated the exact all-depth statement:
exclude the coprime integer corridor (7), equivalently the 25-one cylinder
(4), at every actual skipped state. The period-\(20\) phase and a bounded
amount of leading-word history do not currently do this. A successful
invariant must use the unbounded affine-mask ancestry, most likely the same
divisor pulses which determine where long internal runs are exposed at the
front.

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_twenty_five_dyadic_cutoff_nogo.py

for the rank-\(24092\) certificate and the directed audit through rank
\(30000\). Passing the option --depth 100000 reproduces the length-17
observation.
