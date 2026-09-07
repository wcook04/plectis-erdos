# An actual-polynomial sextic theorem on the natural first-mode cone

Status: ordinary analytic finite-polynomial proof with exact rational budget
checks, 2026-09-05. This transfers the new two-ray mechanism to actual monic
sextics. It does not settle every near-regular sextic or unrestricted Erdős
#1041, and is not Lean checked.

## 1. Statement

Let \(\omega=e^{\pi i/3}\), and let
\[
 a_j=\omega^j(1+e_j),\quad |a_j|\le1,\quad
 f(z)=\prod_{j=0}^{5}(z-a_j),\quad
 E_m=\sum_{j=0}^{5}e_j\omega^{-jm}.
\]
Use a common rotation to put \(E_0=-\Delta\) with \(\Delta\ge0\) real.
Define
\[
 \rho=\max\{|E_1|^{1/5},|E_2|^{1/4}\}.
\]
**Theorem.** If
\[
 0<\rho\le10^{-18},\qquad
 \Delta\le20000\rho^6,\qquad
 |E_1|\ge\frac{13}{25}|E_2|^{5/4},                         \tag{1}
\]
then two distinct roots of \(f\) are joined by two radial segments and a
straight chord inside \(\{|f|<1\}\), with total length at most
\[
                              2-\rho/800<2.               \tag{2}
\]
The radial segments use the *actual* root directions. Their common
truncation radius is \(\rho/200\). The theorem permits roots on the closed
unit circle; in particular it applies to the open-disc roots of #1041.

The power \(5/4\) is the natural balance between the first and second
Fourier modes and the sextic term. This is an actual-polynomial consequence
of `SexticNaturalScaleRaySelector.md`, rather than a claim that scaling
preserves its paired model. The rational constant \(13/25\) exceeds the
sharp model threshold \(K=(49152/9765625)^{1/8}\); that small surplus buys
uniform margins needed for transfer.

## 2. Root geometry controls the finite coefficients

Put \(\eta=\max_j|e_j|\). The disc condition gives
\(2\operatorname{Re}e_j+|e_j|^2\le0\), hence
\[
 \sum_j|e_j|^2\le2\Delta,
 \quad |E_3|^2\le12\Delta,
 \quad |\operatorname{Re}E_3|\le\Delta.                    \tag{3}
\]
Separating real and imaginary root displacements in the Fourier transform
also gives
\[
 |E_4+\bar E_2|\le2\Delta,\qquad
 |E_5+\bar E_1|\le2\Delta.                                \tag{4}
\]
For all the estimates below it is enough to use the weaker size restriction
\(\rho\le10^{-6}\). From (1), (3), (4) and Fourier inversion,
\[
\begin{gathered}
 |E_1|\le\rho^5,\quad |E_2|\le\rho^4,\quad
 |E_3|\le500\rho^3,\quad |E_4|\le2\rho^4,\quad |E_5|\le2\rho^5,\\
 \eta\le\frac{5\Delta+2\rho^5+2\rho^4+500\rho^3}{6}
                                                        <100\rho^3. \tag{5}
\end{gathered}
In particular all roots are nonzero and distinct. For
\(v_j=a_j/|a_j|\),
\[
                  |v_j-\omega^j|\le3\eta.                 \tag{6}
\]

Set
\[
 A=E_1/\rho^5,\quad B=E_2/\rho^4,\quad
 C=\operatorname{Im}E_3/\rho^3,
 \quad U(w)=\operatorname{Re}(Aw+Bw^2+iCw^3-w^6).
\]
Then \(|A|,|B|\le1\), \(|C|\le500\), and \(|A|\ge13/25\). The last
assertion follows because either \(|A|=1\), or \(|B|=1\) and the final
inequality in (1) applies.

## 3. The surplus gives a uniform ray margin

Let \(\varepsilon=1/1000\) and \(k=4/5^{5/4}\). For three antipodal
classes put
\(\alpha_j=\operatorname{Re}(A\omega^j)\),
\(\beta_j=\operatorname{Re}(B\omega^{2j})\). There are two distinct classes
such that
\[
                    |\alpha_j|\ge k(\beta_j+\varepsilon)_+^{5/4}.  \tag{7}
\]
To see this, suppose two classes fail. They have \(\beta_i+\varepsilon>0\) and
\(\beta_j+\varepsilon>0\). The same Gram identities and superadditive power
inequality as in `SexticNaturalScaleRaySelector.md` give
\[
\begin{aligned}
 \tfrac34|A|^2
 &< k^2[(\beta_i+\varepsilon)^2+(\beta_j+\varepsilon)^2
                       +(\beta_i+\varepsilon)(\beta_j+\varepsilon)]^{5/4}\\
 &\le k^2(\tfrac34+3\varepsilon+3\varepsilon^2)^{5/4}.
\end{aligned}
\]
Here \(\beta_i+\beta_j\le|B|\le1\). This would force
\(|A|<K(1+2\varepsilon)^{5/4}<13/25\), a contradiction. The final
comparison is checked by raising to the eighth power, with rational inputs.

Choose the negative first-mode direction in each of these two classes and
call them \(\zeta_0,\zeta_1\). By the exact scalar maximum
\(\sup_{t\ge0}(bt-t^5)=k(b_+)^{5/4}\), (7) implies
\[
                     U(t\zeta_i)\le-\varepsilon t^2
                  \quad(t\ge0, i=0,1).                  \tag{8}
\]
They are not antipodal, so \(|\zeta_1-\zeta_0|\le\sqrt3\).

## 4. A uniform small chord

Put \(u=1/200\), and write
\(x_i=-\operatorname{Re}(A\zeta_i)\ge0\). The first-mode Gram identity
implies \(\max(x_0,x_1)\ge|A|/2\).

If both \(x_i\ge|A|/8\), then on their radius-\(u\) chord the linear term
is at most \(-13u/200\). The remaining terms have total modulus at most
\(u^2+500u^3+u^6\). The rational comparison
\[
                u+500u^2+u^5+\varepsilon u<13/200
\]
therefore bounds the whole chord above by \(-\varepsilon u^2\).

Otherwise label the smaller endpoint first. The first-mode derivative along
\(w(s)=u[(1-s)\zeta_0+s\zeta_1]\) is less than
\(-3|A|u/8\le-39u/200\). All other derivatives have total modulus at most
\(4u^2+3000u^3+12u^6\), and
\[
                        4u+3000u^2+12u^5<39/200.
\]
Thus \(U(w(s))\) is decreasing and is bounded by its first endpoint, which
is at most \(-\varepsilon u^2\) by (8). This includes a zero first-mode
projection at that endpoint. We have proved the common margin
\[
 U\le-\varepsilon u^2=-1/40000000                         \tag{9}
\]
on the chord and on the two model arms for \(u\le t\le32\).

## 5. Exact expansion and the inner actual-polynomial transfer

The origin-anchored expansion of `FormACutQuantitativeExpansion.md`, §3,
is particularly useful here. Put
\[
 N(z)=\sum_{m=1}^{5}E_mz^m-\Delta z^6,
 \qquad P(z)=\frac{N(z)}{1-z^6}.
\]
For \(|z|\le r<1\), \(\eta<1-r\), it states
\[
 \log|f(z)|=\log|f(0)|+\log|1-z^6|+\operatorname{Re}P(z)+R_a(z),
 \quad |R_a(z)|\le
 \frac{6\eta^2r}{(1-r)^2(1-\eta/(1-r))}.                  \tag{10}
\]
This follows directly by factoring
\(f(z)=(z^6-1)\prod_j[1+e_j/(1-z\omega^{-j})]\), subtracting the
logarithm at zero, and summing the geometric Fourier series. The constant
\(\log|f(0)|\le0\) is retained exactly, then discarded only as a favorable
term. It is not replaced by a possibly positive second-order estimate.

For \(z=\rho w\), \(|w|\le R=32\), the following normalized error bounds
follow from (5), (10) and geometric series. Every row is divided by \(\rho^6\).

| term omitted from \(U(w)\) | upper bound |
|---|---|
| anchored nonlinear remainder | \(48\cdot10000R\rho\) |
| fourth Fourier mode | \(2R^4\rho^2\) |
| real part of the cubic Fourier mode | \(20000R^3\rho^3\) |
| fifth Fourier mode | \(2R^5\rho^4\) |
| \(-\Delta z^6\) | \(20000R^6\rho^6\) |
| \(\log|1-z^6|+\operatorname{Re}z^6\) | \(R^{12}\rho^6\) |
| replacement of \(P\) by \(N\) | \(40000000R^6\rho^6\) |

For the final row, the preceding coefficient bounds give
\(|N(\rho w)|/\rho^6<20000000\), and
\(|z|^6/(1-|z|^6)\le2R^6\rho^6\). The log row uses
\(|\log|1-z^6|+\operatorname{Re}z^6|\le|z|^{12}\) on this small disk.

The actual ray directions must also be substituted. On \(|w|\le R\),
the complex polynomial defining \(U\) has derivative norm less than
\(3\cdot10^8\). Replacing model endpoints \(\omega^j\) by actual
directions \(v_j\) moves any arm or chord point by at most \(3R\eta\).
The resulting normalized model error is at most
\(3R\cdot100\cdot3\cdot10^8\rho^3\).

Adding these positive bounds, and using \(\rho\le10^{-6}\), gives the
deliberately loose but fully rational bound
\[
 \rho^{-6}\log|f(z_{\rm actual})|
                          \le U(w_{\rm model})+10^9\rho. \tag{11}
\]
At the theorem's \(\rho\le10^{-18}\),
\(10^9\rho\le10^{-9}<\varepsilon u^2/2\). By (9), the complete actual
chord and both actual arms from \(u\rho\) to \(32\rho\) therefore lie
strictly inside \(|f|<1\). The transfer covers their whole continuous
parameter intervals, not just sampled points.

## 6. Extending the arms to the actual roots

For \(32\rho\le t\le1/2\), take \(z=tv_j\). From (6),
\(|v_j^6-1|\le18\eta\), and hence
\[
 \log|1-z^6|\le
 -t^6+[162\eta^2+1/126]t^6\le-99t^6/100.                \tag{12}
\]
The \(1/126\) comes from
\(t^{12}/[2(1-t^6)]\le t^6/126\).
Using (5), \(t\ge32\rho\), and \(t\le1/2\),
\[
 |P(z)|\le\frac{64}{63}
 \left[\frac{9}{8\,32^5}+\frac{3}{2\,32^4}
                  +\frac{500}{32^3}+20000\rho^6\right]t^6<t^6/50. \tag{13}
\]
The anchored remainder in (10) is at most \(48\eta^2t\), so
\[
                     |R_a(z)|/t^6
                       \le480000\rho/32^5<1/100.         \tag{14}
\]
Together (12)–(14) give \(\log|f(z)|<-24t^6/25<0\).

On the final interval \(1/2\le t\le|a_j|\), use a different exact estimate.
Telescoping the six factors gives
\(|f(z)-(z^6-1)|\le192\eta\) on \(|z|\le1\). Therefore
\[
 |f(tv_j)|\le1-t^6+210\eta<1,                             \tag{15}
\]
since \(210\eta<1/64\le t^6\). All constants in (12)–(15) already hold
under the weaker \(\rho\le10^{-6}\).

Finally (6) gives \(|v_i-v_j|\le\sqrt3+6\eta<7/4\). The constructed
path has length
\[
 |a_i|+|a_j|-2u\rho+u\rho|v_i-v_j|
                         \le2-u\rho/4=2-\rho/800,
\]
proving (2). Its arms reach the actual roots and all three pieces are in
the strict unit lemniscate.

## 7. Position in the frontier

The result closes the finite transfer of a natural first-mode transverse
sector in degree six. The earlier
`SexticAnisotropicCubicCone.md` uses the complementary inequalities
\(|E_1|\le(3/2048)\Delta^{5/6}\) and
\(|E_2|\le(3/2048)\Delta^{2/3}\). If either fails, then
\(\Delta<20000\rho^6\); the two rational constant comparisons are checked
by the verifier. Thus the \(\Delta\) restriction in (1) is automatically
available on that transverse branch.

What is not closed is the residual transverse sector
\(|E_1|<(13/25)|E_2|^{5/4}\), the source-specific finite transfer of the
other radial/cubic branches, or configurations outside the displayed
neighborhood. The sharp coefficient constant \(K\) belongs to the model
ray theorem; this actual-polynomial theorem uses the strictly larger
\(13/25\). No full degree-six or unrestricted #1041 conclusion is asserted.

## 8. Verification and reasoning receipt

Run

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_natural_scale_finite_transfer.py --actual-probe 18
```

The verifier checks the rational absorptions used above. Its optional
240-digit experiment constructs actual inward perturbations of the six roots,
fixes the rotational gauge, checks the theorem hypotheses, selects the two
ray classes and tests the actual polynomial along the complete three-piece
path on a finite mesh. This experiment is a falsifier and regression check;
the proof of continuous containment is (3)–(15). No Lean validation,
independent review or external novelty assessment is claimed.

Candidate attacks compared at entry: #243 requires a global arithmetic
restriction beyond arbitrarily long local clean-rise fixtures; #257 still
requires cofinal control of its exact greedy recurrence; the new #1041 ray
lemma gives a short, checkable route to actual-polynomial containment.
The selected probe was uniform margin after a positive shift of the
second-mode ray projection. Its falsifier was failure of either the shifted
Gram inequality or an explicit normalized error absorption. Both passed.
The exact constant at the model boundary was deliberately not transplanted:
the surplus \(13/25-K\) is used in the proof.

`tao_pipeline_receipt`: model generation → actual-polynomial verification
and internal understanding; artifact: this note and its checker;
understanding delta: the Gram selector survives a positive coefficient shift,
which supplies a common ray/chord margin and a quantitative finite transfer;
verification: ordinary analytic proof plus exact rational inequalities;
publication/review: internal, not independently reviewed;
canonicalization: first-mode sector now has an actual-polynomial theorem;
downstream bottleneck: the residual small-first-mode sector and other finite
branch transfers; next owner: #1041 proof lane.

`tao_writing_review`: theorem note for a reader of the corpus's near-Fekete
work. The strongest claim is (1)–(2), with actual roots and strict containment.
The hard steps are uniform pair selection, a chord with a possible zero
first-mode endpoint, and the quantitative change from model to actual root
directions. The logarithm is anchored at the exact product of root moduli;
the cubic coefficient is not assumed small after normalization. Source
roles and remaining sectors are adjacent to the theorem. Exact constants
and the reproducible numerical falsifier separate proof from computation.
