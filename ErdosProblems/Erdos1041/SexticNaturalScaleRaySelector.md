# A natural-scale two-ray selector for the sextic model

Status: ordinary analytic proof with exact symbolic checks, 2026-09-05.
This strengthens the corpus's first-mode paired-model cone. It is not a
Lean-checked theorem or a nonlinear actual-polynomial transfer theorem.

The subsequent [SexticNaturalScaleFiniteTransfer.md](SexticNaturalScaleFiniteTransfer.md)
does transfer the cone with the slightly larger coefficient constant
\(13/25\) to actual sextics, under its explicit smallness and radial-deficit
hypotheses. Its proof uses the surplus to establish a uniform ray/chord
margin; it does not claim a finite transfer at the sharp constant \(K\).

## The theorem

Put \(\omega=e^{\pi i/3}\) and
\[
 k=\frac4{5^{5/4}},\qquad
 K=k(3/4)^{1/8}=\left(\frac{49152}{9765625}\right)^{1/8}
                =0.5160955849\ldots.
\]
Let \(A,B\in\mathbb C\), \(A\ne0\), and \(C\in\mathbb R\). Assume
\[
                         |A|\ge K|B|^{5/4}.                 \tag{1}
\]
Then each of the two models
\[
\begin{aligned}
 U(z)&=\operatorname{Re}(Az+Bz^2+iCz^3-z^6),\\
 H(z)&=\operatorname{Re}(Az+Bz^2+iCz^3-\bar Bz^4-\bar Az^5-z^6)
\end{aligned}
\]
has two non-antipodal sixth-root directions whose complete radial segments
\(0\le t\le1\) lie in its nonpositive sublevel set. The same two directions
work for both models and for every \(C\). For each fixed triple \((A,B,C)\),
the two rays can be truncated at a sufficiently small positive radius and
joined by a straight chord on which the model is strictly negative. The
resulting path between two sixth roots has length strictly below two.

No uniform positive lower bound on the truncation radius is asserted. In
particular, the radius can tend to zero as \(|C|\) grows. The excluded case
\(A=B=0\) is the separate pure-cubic face.

For \(0<|B|\le1\), (1) is strictly weaker than the older paired-model
condition \(|A|\ge3|B|/4\): \(K<13/25<3/4\) and
\(|B|^{5/4}\le|B|\). The difference is particularly large near zero.

## Exact scalar ray threshold

For a direction \(\omega^j\), put
\[
 a_j=\operatorname{Re}(A\omega^j),\qquad
 b_j=\operatorname{Re}(B\omega^{2j}).
\]
The cubic is invisible on these rays. For the unpaired model,
\[
 U(t\omega^j)=t(a_j+b_jt-t^5).
\]
For \(b\ge0\),
\[
 \sup_{t\ge0}(bt-t^5)=k b^{5/4}.                         \tag{2}
\]
Indeed set \(b=5v^4\). The exact factorization
\[
 t^5-5v^4t+4v^5=(t-v)^2(t^3+2vt^2+3v^2t+4v^3)\ge0
\]
proves the upper bound and equality at \(t=v\). For \(b\le0\), the
supremum is zero. Thus
\[
                       a_j+k(b_j)_+^{5/4}\le0             \tag{3}
\]
is equivalent to safety of the entire unpaired ray \(t\ge0\).

Opposite directions have opposite \(a_j\) and equal \(b_j\). Consider the
three antipodal classes \(j=0,1,2\) and choose the sign of each direction
so its first-mode projection is \(-|a_j|\). It suffices to show that at least
two different classes satisfy
\[
                       |a_j|\ge k(b_j)_+^{5/4}.            \tag{4}
\]
Different classes cannot yield antipodal selected directions.

## The geometric selection step

For any distinct classes \(i,j\), the elementary three-direction identities
give
\[
 |a_i|^2+|a_j|^2+|a_i a_j|\ge\tfrac34|A|^2,              \tag{5}
\]
and
\[
                b_i^2+b_j^2+b_ib_j=\tfrac34|B|^2.          \tag{6}
\]
For (5), the signed identity has either \(+a_i a_j\) or \(-a_i a_j\),
according to whether the representatives are separated by \(2\pi/3\) or
\(\pi/3\). Replacing that signed term by its absolute value can only
increase it. For (6), the doubled directions are always separated by
\(2\pi/3\) modulo a full turn.

Also \(b_0+b_1+b_2=0\), so every class with \(b_j\le0\) already satisfies
(4). If (4) failed in two classes \(i,j\), both would have \(b_i,b_j>0\).
Writing \(p=5/4\), (5) would imply
\[
\begin{aligned}
 \tfrac34|A|^2
 &\le |a_i|^2+|a_j|^2+|a_i a_j|\\
 &< k^2\big((b_i^2)^p+(b_j^2)^p+(b_i b_j)^p\big)\\
 &\le k^2(b_i^2+b_j^2+b_i b_j)^p
  =k^2(\tfrac34|B|^2)^p.
\end{aligned}
\]
The middle inequality is the elementary superadditivity of \(x^p\) on
nonnegative arguments for \(p\ge1\); for example it follows by integrating
the increasing derivative. Rearranging gives \(|A|<K|B|^{5/4}\), contrary
to (1). Hence two classes satisfy (4).

This is the load-bearing change of selector: adjacency is discarded until
after existence is established. Two different antipodal classes are enough
for a strict shortening, and their Gram identities fit the radial threshold's
power law. A worst-case bound on each adjacent projection separately loses
this relationship.

## Transfer of these rays to the paired model

For a selected direction write \(a_j=-x\le0\), \(b_j=b\). Its paired ray is
\[
 R(t)=-x(t-t^5)+b(t^2-t^4)-t^6.
\]
If \(b\le0\), every term is nonpositive on \([0,1]\). If \(b>0\), (3) gives
\(-x+bt-t^5\le0\), while the exact identity
\[
 R(t)-t(1-t^4)(-x+bt-t^5)
                  =-bt^4(1-t^2)-t^{10}\le0                \tag{7}
\]
proves paired ray safety. At \(t=1\), \(R=-1\) directly. Notice that the
high paired modes improve this comparison; they need not be paid as
independent absolute errors.

## A strict small chord, including a zero first-mode endpoint

Let \(\zeta_0,\zeta_1\) be the selected directions and
\(z(u,s)=u((1-s)\zeta_0+s\zeta_1)\). Their angular separation is either
\(\pi/3\) or \(2\pi/3\), so \(|\zeta_1-\zeta_0|\le\sqrt3\).

If both first-mode projections are strictly negative, let their smaller
magnitude be \(c>0\). The first mode is at most \(-cu\) on the chord.
For \(u\le1\), all other terms of either model have total modulus at most
\(Mu^2\), where \(M=2|B|+|C|+|A|+1\). Choosing
\(0<u\le\min(1/2,c/(2M))\) gives a chord bound \(-cu/2<0\).

There can be at most one selected endpoint with zero first-mode projection,
since \(A\ne0\) and the classes are different. Label it \(\zeta_0\), and
write \(\operatorname{Re}(A\zeta_1)=-c<0\). Its second-mode projection is
nonpositive by (3). At \(s=0\) both models are at most \(-u^6\). Along the
chord the first-mode derivative with respect to \(s\) is exactly \(-cu\).
Using \(|z|\le u\) and \(|\partial_s z|\le2u\), all other derivatives have
total modulus at most \(Du^2\) for \(u\le1\), with
\[
                       D=12|B|+6|C|+10|A|+12.
\]
Choose \(0<u\le\min(1/2,c/(2D))\). The derivative of either model is then
at most \(-cu/2\) throughout, so the whole chord remains below \(-u^6\).
This argument includes the case where the second-mode projection also
vanishes at the first endpoint; no false uniform linear margin is used.

The two radial tails and the chord have length
\[
 2(1-u)+u|\zeta_1-\zeta_0|
                  \le2-(2-\sqrt3)u<2.
\]
This proves the theorem.

## Why the constant is the sharp universal complete-ray threshold for U

Normalize \(|B|=1\). Let two positive projections \(b_i,b_j\) tend to
\((\sqrt3/2,0)\), while the third is negative. For \(0<\tau<1\), prescribe
oppositely signed first-mode projections on representatives separated by
\(\pi/3\), with magnitudes
\(\tau k b_i^{5/4}\) and \(\tau k b_j^{5/4}\). The two real equations
uniquely determine \(A\). Both positive classes fail (4), while the third
has exactly one safe direction: its first projection is nonzero. Thus there
is only one safe complete ray. Identity (5), with the chosen signs attaining
equality, gives
\[
 |A|=\frac{2\tau k}{\sqrt3}
 \sqrt{b_i^{5/2}+b_j^{5/2}+(b_i b_j)^{5/4}}\longrightarrow\tau K.
\]
Letting \(\tau\uparrow1\) shows that every proposed smaller universal
threshold fails. The extremal value is a limit; at the zero projection itself
additional rays can become safe. This sharpness is for the unpaired
*complete-ray* selector, not for all paths, and not a sharpness claim for H.

For a concrete witness against the tempting constant \(1/2\), take
\[
 A=-217/500-259i/1000,\qquad B=45/53-28i/53.
\]
Here \(|B|=1\) and \(|A|^2=255437/10^6>1/4\). The two positive
second-mode classes \(j=0,1\) both obey
\(3125a_j^4<256b_j^5\), so neither has a safe ray; the third class has
exactly one. All these inequalities lie in \(\mathbb Q(\sqrt3)\) and are
checked by rational squaring, not a floating sign test. The second violation
is small, about \(1.13\cdot10^{-6}\), which makes it a useful adversarial
fixture. This refutes only the smaller complete-ray threshold.

## Relation to the nonlinear problem

The exponent \(5/4\) is dictated by the change of variable \(z=\rho w\),
\(\rho=|E_2|^{1/4}\): the normalized first coefficient is
\(E_1/\rho^5\). The theorem closes the paired Fourier-model region
\[
                      |E_1|\ge K|E_2|^{5/4}
\]
without pretending that a spatial scaling preserves the paired model.
Indeed scaling the exact tangent pair
\(E_4=-\bar E_2\), \(E_5=-\bar E_1\) and dividing by \(\rho^6\)
produces high coefficients \(-\rho^2\bar B\) and
\(-\rho^4\bar A\), not \(-\bar B\) and \(-\bar A\). The normalized
unit-B chord theorem in `SexticChordRecessionClosure.md` is valid but does
not by itself authorize that replacement.

The present result is proved directly in the original paired coordinates
and separately in the unpaired limit. It does not yet control the actual
root perturbation remainder or reconstruct a strict path for the original
polynomial. The residual mixed Fourier-model region is now
\(|E_1|<K|E_2|^{5/4}\), together with the existing radial/cubic branches and
their source-specific transfer obligations.

## Verification and working receipt

`scripts/check_erdos1041_natural_scale_ray_selector.py` checks the signed
three-direction identities, the radial factorization, the paired comparison,
and the exact constant using symbolic and rational arithmetic. Its optional
phase survey is finite falsification only. The inequalities for all real
parameters, the selection argument, and the small-chord construction are
the ordinary proof above. No Lean or external review is claimed.

The candidate comparison is inherited from `SexticChordRecessionClosure.md`.
The new decisive probe was whether dropping adjacency permits two safe
antipodal classes at the natural coefficient scale. The falsifier was fewer
than two safe classes; a 1,002,001-point phase survey found none, and the Gram
argument then excluded this for all phases. The failed route was transferring
the paired unit-B certificate through a non-pair-preserving spatial scaling.
The representation changed to the original coefficients and their exact ray
threshold; the endpoint-zero case was checked separately.

`tao_pipeline_receipt`: generation → ordinary verification and understanding;
artifact: this proof and its checker; understanding delta: equilateral Gram
identities select two ray classes at the natural power-law threshold and
give the sharp unpaired constant; verification: displayed analytic proof plus
exact algebra checks; review/publication: internal, not independently
reviewed; canonicalization: subsumes the older linear coefficient cone on
\(|B|\le1\); downstream bottleneck: residual small normalized first mode
and actual-polynomial transfer; next owner: #1041 proof lane.

`tao_writing_review`: theorem note for a mathematical reader; strongest claim
is the model connector theorem (1), with sharpness restricted to the
unpaired complete-ray selector. The proof exposes the non-adjacent choice,
the three-direction identities, the superadditive power step and the zero
endpoint argument. Source context: `SexticFirstModeThreeQuarterOverlap.md`
and the Fourier pairing in `SexticFirstModeDominantTangentCone.md`.
External novelty is not assessed. No figure or bibliography is needed for
the algebraic argument; the exact checker makes its identities inspectable.
