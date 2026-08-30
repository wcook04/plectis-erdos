# Erdős 1041: the trace-max pair excess is subharmonic in `mu` on every fixed-phase slice — (EX-U) reduces to the chamber wall plus the `mu = -10` stratum

Date: 2026-08-30.  Checker:
`scripts/check_erdos1041_chamber_wall_reduction.py` (all sections green at
landing).  Consumes `QuinticTraceMaxUniversalChamber.md` (the chamber
`C_5`, identities (U1)–(U6), compactness, real-slice classification) and
does not modify it.  Companion measured geography: wave-1 fleet notes of
this date.

## 1. What this note proves

`QuinticTraceMaxUniversalChamber.md` §7 posed the quintic model metric
obligation as a compact THREE-real-variable certification problem:

```text
(EX-U)   for every simple-hub (mu,phi) in C_5:  mathcal E(mu,phi) <= 0,
```

and suggested a rigorous interval cover of the whole chamber.  This note
removes one real dimension by proof:

> **Theorem A.**  For every fixed `phi`, the function
> `mu -> mathcal E(mu,phi)` is subharmonic on the open set where the two
> rightward arms continue (Lemma 1), which contains the closed slice
> `Omega_phi = {mu : (mu,phi) in C_5}` minus the single point `mu = -10`.
>
> **Corollary B (wall reduction).**
> `sup_{C_5 minus the mu=-10 stratum} mathcal E
>    = sup_W mathcal E`, where
> `W = {(mu,phi) in C_5 : min_j Re(e^{i phi} g(x_j)) = 0}`
> is the chamber WALL (real codimension one).  Together with the
> `mu = -10` limit stratum, (EX-U) is therefore equivalent to:
>
> ```text
> (EX-W)   mathcal E <= 0 on the wall W,   plus
> (EX-10)  the limiting-pair excess bound on the mu = -10 phase arc.
> ```
>
> (EX-10) is exactly the stratum already under exact-certificate attack:
> centre `(mu,phi)=(-10,0)` proved in
> `QuinticMinusTenCentralExcessCertificate.md`; both arc ENDPOINTS are now
> proved (`QuinticMinusTenEndpointExcessCertificate.md`, landed
> concurrently with this note: `mathcal E(-10, +-arctan(1/(2 sqrt2)))
> < -1/80`, the actual limiting curved pair); the arc interior is the
> remaining open part of that stratum.  Since the measured chamber sup of
> `mathcal E` is attained precisely in the limit at those two corner
> points (§6), the certified endpoints pin the extremal value itself; the
> wall away from the corner carries `>= 0.064` measured margin.

No interior interval cover is needed: interior maxima are impossible.

## 2. Two exact identities

All notation is that of `QuinticTraceMaxUniversalChamber.md`:
`F_mu(x) = x^2(x^3+5x^2+10x+10+mu)`, `C_mu(x) = 5x^3+20x^2+30x+20+2mu`,
gaps `g(x_j)` at the roots `x_j` of `C_mu`.

**(N1) Critical values of `F_mu`.**  `F_mu'(x) = x C_mu(x)`, so the
critical points of `F_mu` are `x = 0` (value `0`) and the `x_j`; and

```text
F_mu(x_j) = -g(x_j),
```

because `g == -F_mu mod C_mu` (checker S2).  Hence the rightward ray
`{e^{-i phi} s : s > 0}` passes through a critical value of `F_mu` iff
some `e^{i phi} g(x_j)` is a strictly negative real — impossible on the
closed chamber, where `Re(e^{i phi} g(x_j)) >= 0`.  Sharper (wave-1
verification agent, exact): under (CH) the distance from `-g_j` to the
closed ray is EXACTLY `|g_j|`, so the clearance margin has the closed
form `min_j |g_j|` — the natural interval-engine quantity.

**(N2) Terminal normalizer.**

```text
F_mu(x) - (1+x)^5 = mu x^2 - 5x - 1        (checker S3).
```

On an arm (`F_mu(x(s)) = e^{-i phi} s`) this gives
`(1+x(S))^5 = e^{-i phi} S (1 - e^{i phi}(mu x^2 - 5x - 1)/S)`, hence,
with `x(S) ~ (e^{-i phi} S)^{1/5} zeta` on its tract,

```text
|1 + x(S)| = S^{1/5} + O((|mu|+1) S^{-2/5}),
```

locally uniformly in `mu`.  The correction constant scales linearly with
`|mu|` (checker N6 verifies magnitude and decay per arm); only the limit
`-> 0` is used below.

## 3. Lemma 1 — the march domain and holomorphy

Fix `phi`.  Let `V_phi` be the set of `mu != -10` such that both arms
`x_+(s;mu), x_-(s;mu)` (the two branches of `F_mu(x) = e^{-i phi}s` born
at the double root `x = 0`) continue for all `s in (0, infty)`.

1. **`V_phi` is open and contains `Omega_phi minus {-10}`.**  An arm can
   fail to continue only by running into a critical point of `F_mu`; at
   such `s` the ray value `e^{-i phi}s` equals the critical value
   `-g(x_j)`, which by (N1) forces `Re(e^{i phi}g(x_j)) < 0` — excluded
   on the closed chamber.  A gap-zero point (`g(x_j) = 0`, see §5) is NOT
   excluded and is NOT singular: there the foreign critical value `0`
   sits at `s = 0` only, where the arms are at `x = 0`, a different point
   of the same fibre; the continuation for `s > 0` is untouched.  At
   `mu = -10` the hub itself degenerates (`F_{-10} = x^3(x^2+5x+10)` has
   a TRIPLE root at `0`), which is why that single point is excised.
   Openness: continuation with `F_mu' != 0` along a compact `s`-range is
   an open condition in `mu`, and beyond a fixed `S_0` the arm is in the
   polynomial-dominated tract regime, uniformly for nearby `mu`.
2. **Holomorphy.**  For fixed `s > 0`, `mu -> x_a(s;mu)` is holomorphic
   on `V_phi` (implicit function theorem along the march;
   `F_mu'(x_a(s)) != 0`).  The Puiseux start
   `x_pm = pm sqrt(e^{-i phi} s/(10+mu)) (1 + O(s^{1/2}))` needs
   `10 + mu != 0`, which `V_phi` grants.  The individual arms may swap
   under continuation around a `mu`-loop; the PAIR `{x_+, x_-}` is
   single-valued, and every quantity used below is a pair sum.

## 4. Theorem A — proof

Per arm define the truncated normalized length

```text
v_S(mu) = int_0^S |x_a'(s;mu)| ds  -  S^{1/5},
x_a'(s;mu) = e^{-i phi} / F_mu'(x_a(s;mu)).
```

For each fixed `s`, `mu -> x_a'(s;mu)` is holomorphic and nonvanishing on
`V_phi`, so `|x_a'(s;.)|` is subharmonic there; the `s`-integral (the
integrand is `O(s^{-1/2})` at `0`, locally uniformly) is subharmonic; the
subtracted `S^{1/5}` is a `mu`-constant.  So each `v_S` is subharmonic on
any simply-connected subset of `V_phi` (and the pair sum on all of
`V_phi`).

Convergence: writing `S^{1/5} = int_0^S (1/5) s^{-4/5} ds`,

```text
v_S(mu) = int_0^S (|x_a'(s;mu)| - (1/5) s^{-4/5}) ds ,
```

and on the tract `x = w - 1 + O(1/w)`, `w = (e^{-i phi}s)^{1/5} zeta`,
the two first-order corrections cancel exactly —
`1/|F'(x)| = (1/5)|x|^{-4} |1 + 4/x + ...|^{-1}` has `|x|^{-4}` carrying
`+4 Re(1/w)` from the shift `x = w - 1` and the Wronskian factor carrying
`-4 Re(1/x)` — leaving integrand `O(s^{-7/5})`, locally uniformly in
`mu`.  So `v_S` converges locally uniformly as `S -> infty`; by (N2) its
limit is the arm excess `e_a` (the `|1+x(S)|` and `S^{1/5}` terminal
terms differ by `o(1)`).  A locally uniform limit of subharmonic
functions is subharmonic, and it is continuous.  Summing the pair:
`mathcal E(.,phi) = lim (sum_a v_S)` is subharmonic on `V_phi`.  ∎

The older frozen-terminal-direction rewrite
(`e_a = lim [int_0^S |x'| ds - Re(e^{-i theta_a}(1+x(S)))]`, `theta_a`
the tract direction) also works and makes the approximants MONOTONE
increasing in `S` — useful for numerics — but the normalizer proof above
needs no per-arm direction bookkeeping.

**Sharp rates (remark; wave-1 verification agent).**  The Puiseux
expansion at infinity is `x = X - 1 + 0/X - (mu/5)/X^2 + ...`,
`X = zeta (e^{-i phi} s)^{1/5}` — the `1/X` coefficient VANISHES — so
the actual convergence is faster than the proof needs: the
frozen-direction terminal correction decays like `S^{-1}` (measured
median exponent `-0.985` over 122 arms; exactly
`corr_S -> |c_2|^2 sin^2(gamma) / (2S)`, `c_2 = -mu/5`), the truncation
error obeys the exact invariant `(e - u_S)/corr_S -> 4/5`, and both
`u_S` and the normalizer truncation `v_S` are monotone increasing
(Cauchy–Schwarz).  The slice `mu = 0` is distinguished (`c_2 = 0`,
exponent `7/5`).  These rates are consistency instruments for a future
certified wall engine; the proof above uses only `-> 0` locally
uniformly.

**Degree uniformity (remark).**  Nothing above is quintic-specific.  For
the degree-`n` model `H(w) = w^n + sum_{k <= (n-1)/2} b_k w^k` of
`QuinticStarKernelMechanics.md`, the hub-centred blow-up gives
`F(x) = (1+x)^n - 1 + sum_k beta_k [(1+x)^k - 1]`,
`beta_k = b_k c^{k-n}`, so

```text
F(x) - (1+x)^n = -1 + sum_{k <= (n-1)/2} beta_k [(1+x)^k - 1],
```

a polynomial of degree `<= (n-1)/2 <= n-2` (checker S3b verifies
`n = 4, 6, 7`).  Hence `|1+x(S)| = S^{1/n} + O(S^{-2/n})` on the arms,
and the identical argument shows the model pair excess is
PLURISUBHARMONIC in the joint hub-centred coefficient parameters
`(beta_k)` for each fixed phase, at every degree: `|x'(s;.)|` is the
modulus of a function holomorphic in all `beta_k` jointly, and the
normalizer is a parameter-constant.  Interior maxima in the coefficient
directions are therefore impossible at every degree; only the quintic
wall/stratum bookkeeping (§5) is degree-specific here.

## 5. Corollary B — proof, and the exact gap-zero classification

`Omega_phi` is compact (chamber compactness), `mathcal E(.,phi)` is
subharmonic on the open `V_phi ⊇ Omega_phi minus {-10}` and continuous
there.  Excise a disk `B_eps(-10)` when `-10 in Omega_phi`: the maximum
of `mathcal E(.,phi)` over `Omega_phi minus B_eps` is attained on its
topological boundary, which is contained in
`{mu : min_j Re(e^{i phi} g(x_j)) = 0} union partial B_eps` (interior
points of the slice have every gap strictly right or are interior maxima,
excluded by the maximum principle unless locally constant — in which case
the boundary value is still an upper bound).  Let `eps -> 0` and take the
sup over `phi`: every chamber value is dominated by the wall sup or by
the `mu = -10` limit values.  ∎

**Gap-zero classification (exact).**  `g(x_j) = 0` with `C_mu(x_j) = 0`
forces `x_j (2 mu + 20 - 3 mu x_j) = 0` (bilinear form of `g`), i.e.
`x_j = 0` — which happens iff `mu = -10` — or `x_j = (2mu+20)/(3mu)`;
substituting into `C_mu` and clearing `(3 mu)^3` gives EXACTLY

```text
2 (mu+10)^2 (27 mu^2 + 140 mu + 200)      (checker S4),
```

so besides `mu = -10` the only gap-zero points are
`mu* = (-70 pm 10 i sqrt5)/27 ~ -2.5926 pm 0.8276 i`.  Both lie in the
chamber closure (allowed-phase arc of measure `~1.78`), and BOTH ARE
REGULAR for the arm system (Lemma 1): measured
`mathcal E(mu*, phi_mid) ~ -1.095`, deep in the safe zone (checker N9).
The foreign-collision points `27 mu^2 + 100 mu + 100 = 0`
(`disc C_mu = 0`, `mu ~ -1.852 pm 0.524 i`) are also in-chamber and also
regular (`mathcal E ~ -1.336` nearby); the gap functions branch there but
the chamber conditions and the arm pair are label-free.  So the ONLY
analytic singular stratum of the reduction is `mu = -10`.

## 6. Normalization warning for consumers of the measured law

`TraceMaxRadialExcessLaw.md`'s global sup `-0.0362736374` is for
`E_pair = |c| mathcal E` on the coefficient core
`max(|b_1|,|b_2|) = 1`.  In chamber normalization the tangent point
carries `mathcal E(50+30 sqrt3, -pi/2) = -0.1694610452` (wave-1
profiler, two independent engines agreeing to `2.7e-10`; the tangent hub
has `|c| ~ 0.214`, and `0.214 x 0.16946 ~ 0.03627` — cross-instrument
consistency; this note's cruder 3-cutoff instrument reads `-0.1746`,
within its own tail-extrapolation error at this slow-converging
collinear-value configuration, checker N10 band unaffected).  Wall-sup
certification must be posed for `mathcal E` directly: THE TWO
NORMALIZATIONS HAVE DIFFERENT EXTREMALS.  Measured `mathcal E`
geography (wave-1 profiler; 6,183 real-slice + 3,850 complex-mu wall
evaluations, 0 failures): the chamber sup of `mathcal E` is

```text
sup mathcal E = -0.0602107442,
```

attained only in the LIMIT at the corner
`(mu,phi) -> (-10, +- arctan(1/(2 sqrt2)))` — exactly the mu = -10
arc-endpoint object under concurrent exact certification — approached
linearly (slope `~0.0288` in `|mu+10|`), with `q99 = -0.0668`,
`q95 = -0.0737`, tangent point `-0.16946`, branch-2 maximum `-1.1447`
(at `mu = 50-30 sqrt3`, where the allowed arc is exactly a closed
half-plane), and the real axis a KINK of the 2D wall (off-axis wall
values on circles `|mu+10| = rho` exceed the real slice by `O(rho)`
toward `arg(mu+10) ~ 157.5 deg`).  Two structural facts for the wall
program: `mathcal E(mu, .)` is measured EVEN about the arc centre and
CONVEX in `phi` on every tested arc (so the `phi`-max sits at both wall
endpoints), and INDIVIDUAL arms can have positive excess
(`e_- = +0.6563` at the tangent point) — only pair-level bounds can
close (EX-W).

## 7. What remains, and how to certify it

The remaining (EX-U) burden after this note:

1. **(EX-W)** — `mathcal E <= 0` on the 2-real-dimensional wall `W`.
   The wall is parametrized by `mu` (two real dimensions) with the tight
   gap pinning `phi = -arg(i g_j(mu))` up to the binary orientation; on
   `W` one foreign critical value sits exactly on the boundary line of
   the rotated right half-plane — the same geometry the corpus's tangent
   machinery already certifies pointwise.  A certified 2D cover (interval
   `C_mu`-root isolation + the bilinear gap + validated arm marching), or
   a further analytic principle on `W`, closes it.
2. **(EX-10)** — CLOSED, twice over (same-day updates).  The centre and
   both endpoints carry exact certificates; the concurrent session then
   landed `QuinticMinusTenFullArcExcessCertificate.md` (the whole arc,
   `< -1/100`, 64 phase anchors); and independently the phase-Sturm
   bound (`PhiConvexitySturmBound.md`) plus the endpoint certificates
   give `mathcal E(-10, phi) < -1/80` on the whole arc.  Context: the
   arc is `|phi| <= arctan(1/(2 sqrt2))`; the `mu -> -10` limits of
   `mathcal E` are direction-dependent (`-0.06876` along the
   chamber-side real approach at `phi = 0` — two independent
   computations; an earlier quick probe's `-0.0694` was 8e-4 off —
   versus `~ -1.034` along imaginary approaches), the far real side
   `(-10, alpha_2)` is ray-blocked, and the singularity is genuine, not
   removable.  With this stratum closed and the phase direction handled
   by the Sturm bound, THE ENTIRE REMAINING (EX-U) BURDEN IS (EX-W)
   ALONE — see `CertifiedWallEngine.md` for the costed closure plan.
3. Nothing else: interior maxima are excluded by Theorem A; the gap-zero
   and collision strata are regular interior points of the reduction.

Wave-1 measured geography (fleet, this date; see the wall-geography
notes/checkers when landed): interior spot values
`mathcal E(-50+10i) ~ -0.267`, `mathcal E(-120-30i) ~ -0.288`,
`mathcal E(2-i) ~ -1.277`, `mathcal E(-3+i) ~ -1.051`; sub-mean margins
positive at every tested interior point (checker N7, worst `+1.35e-6` at
matched-cutoff resolution); a disk max-principle demonstration holds with
interior max `-0.2655 <=` boundary max `-0.2650` (checker N8).

## 7b. Adversarial verification addendum (same day, wave-1 falsification agent)

An independent instrument (cancellation-free excess form
`e_arm = int_0^infty |u'|(1 - cos delta) ds - 1`, exact-Puiseux tail,
30-dps mpmath cross-check to `1.5e-14`) ran 175 admissible circle-mean
tests plus 13 finite-difference Laplacians against Theorem A: ZERO
sub-mean violations; margins exceed instrument error by 5–7 orders;
`(mean - value)/r^2` constant to 4–5 significant figures across a
`7.5x` radius range (the `Delta u/4` signature); circles passing within
`7.9e-9` of the continuation-domain boundary stay clean.  Three
strengthenings recorded: (i) the sub-mean limit closes by MONOTONE
CONVERGENCE alone (`u_S` subharmonic, `u_S` increasing to the excess:
`u_S(mu_0) <= mean(u_S) <= mean(limit)`, then `S -> infty`) — the
locally uniform tail bound is needed only for continuity; (ii) since
three continuation walls emanate from `mu = -10` (the cubic gap-zero of
the geography note), no loop around `-10` lies in the march domain, so
each INDIVIDUAL arm is single-valued there — the pair-sum symmetrization
is a convenience, not a necessity; (iii) `mathcal E` attains POSITIVE
values on the march domain outside the chamber (measured `+0.988` at
`(mu, phi) = (-50+10i, 2.0776)`), so subharmonicity alone can never
prove (EX-U): the chamber wall input of Corollary B is load-bearing.
The agent independently reconfirmed `g_3 = -(mu+10)^3/675`, the
`S^{-1}` tail law with coefficient `(9/250)|mu|^2 sin^2(arg mu -
3 theta_a)` (modulus form; `mu = 0` degenerates to `S^{-7/5}`), and the
chamber sup `-0.0602` at the `-10` corner.

## 8. Claim boundary

Theorem A and Corollary B are ordinary proved mathematics, verified
symbolically/numerically by the checker; the subharmonicity proof uses
only the implicit function theorem, the exact identities (N1)–(N2), and
locally uniform limits.  This note does NOT prove (EX-W), (EX-10)'s arc
interior, (EX-U) itself, the real-scale transfer (obligation (b)),
degree five, or unrestricted Erdős 1041.  The measured values quoted are
computational context, not proof.  The `mu = -10` stratum's certificates
are owned by the minus-ten notes; this note only routes the burden.
