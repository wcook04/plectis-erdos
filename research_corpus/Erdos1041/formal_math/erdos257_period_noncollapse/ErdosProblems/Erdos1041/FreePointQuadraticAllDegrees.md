# A weighted free-point inequality in every degree

For finitely many points c_j in the closed unit disc and positive weights
w_j with sum w_j=1, set

    G(z) = product_k |1-conj(c_k) z|^{w_k}.

Then

    sum_j w_j G(c_j)^2 <= 1.

Equality holds precisely when all c_j=0. In particular, with m equal weights
and T_j=(product_k |1-conj(c_j)c_k|)^{1/m},

    sum_j T_j^2 <= m,             sum_j T_j <= m.

This is an ordinary analytic proof, not a Lean-checked theorem. The equal-weight
argument came from the September 4 Type B return; the weighted extension,
Fourier stability bound and endpoint analysis below are the assimilation delta.
No priority or solution of Erdős 1041 is asserted.

## Proof and quantitative defect

First suppose |c_j|<1. Choose the analytic logarithm which is zero at the
origin for each factor and put

    g(z)=exp(sum_k w_k log(1-conj(c_k)z))=sum_{nu>=0} a_nu z^nu.

It is analytic on a neighbourhood of the closed disc, g(0)=a_0=1, and
|g|=G. Let dmu be normalised arclength and
P_c(zeta)=(1-|c|^2)/|zeta-c|^2. Subharmonicity gives

    sum_j w_j |g(c_j)|^2 <= integral |g(zeta)|^2 P(zeta) dmu,
    P=sum_j w_j P_{c_j}.

On the circle, the logarithmic derivative gives the exact identity

    P(zeta)=1-2 Re(zeta g'(zeta)/g(zeta)).

This follows termwise from
P_c(zeta)=1+2 Re(conj(c)zeta/(1-conj(c)zeta)).
Thus orthogonality of circle monomials gives

    integral |g|^2 P dmu
      = integral (|g|^2-2 Re(zeta g' conjugate(g))) dmu
      = 1-sum_{nu>=1}(2nu-1)|a_nu|^2.

There is no fractional Blaschke product or change-of-variable assertion here:
positivity is supplied directly by the weighted Poisson kernels. All series
and differentiated series converge uniformly on the circle in the interior case.
We have proved the stronger bound

    sum_j w_j G(c_j)^2 + sum_{nu>=1}(2nu-1)|a_nu|^2 <= 1.       (1)

For boundary points replace c_j by r c_j and let r increase to one. The finite
left sum is continuous. On each compact subdisc the analytic functions converge,
so every fixed Taylor coefficient converges. Apply (1) to a finite initial
coefficient sum and then take its increasing limit. This proves (1) also with
the coefficients of the limiting analytic g on the open disc.

If equality holds in the quadratic bound, every a_nu for nu>0 vanishes, so
g=1. Hence sum_j w_j conj(c_j)/(1-conj(c_j)z)=0. If a nonzero point occurs,
the rational function has a pole at its reciprocal conjugate; repeated equal
points contribute positive total weight and cannot cancel that pole. Thus all
points are zero. Conversely that configuration gives equality. Weighted
Cauchy--Schwarz proves the corresponding linear inequality and its equality case.

Writing b=sum_j w_j c_j, the coefficient a_1=-conj(b) in (1) gives

    sum_j w_j G(c_j)^2 <= 1-|b|^2.                            (2)

Higher coefficient deficits remain useful when b=0. For example if b=0,
a_2=-sum_j w_j conj(c_j)^2/2, so the deficit is at least
3|sum_j w_j c_j^2|^2/4. The exact second-moment statement follows from the
coefficient expansion, not from floating-point sampling.

## Critical values and the closed auxiliary problem

Let f be monic of degree n>=2, and suppose its roots lie in a disc of radius R.
Its critical points w_1,...,w_{n-1} are counted with multiplicity. Then

    sum_j |f(w_j)|^{2/(n-1)} <= (n-1) R^{2n/(n-1)}.          (3)

For R=0 both sides vanish. Otherwise translate and scale to R=1. The argument
in [FreePointTorusPshReduction.md](FreePointTorusPshReduction.md), sections 2--3,
works for every positive exponent: the symmetric sum of powers of critical
values is continuous plurisubharmonic in the roots, including their collision
locus. Successive maximum principles move the roots to the unit torus.
There |f(w_j)|=product_k |1-conj(w_j)w_k|, and (3) is the equal-weight
quadratic theorem with m=n-1. Scaling gives (3) as written.

Power means now give, for 0<p<=2n/(n-1),

    (1/(n-1)) sum_j (|f(w_j)|^{1/n}/R)^p <= 1.

In particular the all-degree arithmetic-mean assertion (S)_n is closed by
this ordinary proof. The example f(z)=(z-tau)^n-lambda attains the constant.
This replaces FP4 and central-radius restrictions when those are used merely
to prove the arithmetic-mean assertion; their specialised proofs remain valid.

The displayed exponent range is proved. No maximal-exponent claim is made;
optimality of the exponent is a separate question.

## Parent-directed probes and remaining boundary

Three distinct mechanisms were compared: (i) convert the critical-value mean
into a two-arm metric selector; (ii) force a connected-cluster Bergman scalar;
(iii) retain monodromy and choose a grouped lift. The first has the stored
fixed-pair counterexamples and still needs a freely selected pair. The second
fails even for z^n-r^n near r=1, as the companion return proves. The third
proves the parent on an open neighbourhood of those examples but supplies no
universal partial-cluster selector. Thus (3) supplies analytic input, not the
missing topology and length implication. The weighted defect is zero at a
fully collapsed critical configuration, precisely where the grouped lift is
needed; it cannot alone eliminate that regime.

The replay script checks finite rational polynomial instances, exact coefficient
deficits, and the critical-value identity. Such checks are regression/falsification
evidence; the analytic proof above supplies the universal quantifiers.
