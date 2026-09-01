# Erdős 1041 satellite: the complete FP4 theorem and its all-degree auxiliary mechanisms

Date: 2026-08-30.  Origin: main-loop route design (K4-matching Hölder),
proof/falsification campaign (all values on named families exact, all
suprema off them adversarial numerics), followed by the main-loop
central/outer closure proof.  Checker:
`scripts/check_erdos1041_free_point_zero_insertion_fp4.py`.

Context.  FRONTIER §4.1: (S)'s free-point form `FP_m` (previously proved
for `m = 2, 3` — `FreePointMeanInequalityFP3.md`).  This note now proves
`FP_4` completely; `FP_m` for `m >= 5` remains open
(`AggregateN3GateFreeCampaign.md` Result 5 kills the cyclic-Hölder
mirror and leaves the Lorentzian route as a proposal for higher degrees).
Notation: `x_j = 1 - |c_j|^2`, `d_jk = |1 - conj(c_j) c_k|`,
`A_j = x_j prod_{k != j} d_jk`, `S_m = sum_j A_j^{1/m}`.

## 1. Theorem (small-angle insertion; all m) — PROVED

Let `c_1..c_m` be in the closed unit disk and suppose SOME index `i`
has `d_ij <= 1` for EVERY `j` (equivalently `rho_i rho_j <=
2 cos(theta_i - theta_j)` for all `j`; e.g. `c_i = 0`).  Then

```text
FP_{m-1}  ==>  S_m <= m,
```

with equality iff all points are `0`.  Proof: `t_i = (x_i prod_j
d_ij)^{1/m} <= 1` (every factor `<= 1`).  For `j != i`,
`A_j^{(m)} = A_j^{(m-1)} d_ij <= A_j^{(m-1)} = B_j^{m-1}` (`B_j` the
`FP_{m-1}` row terms of the configuration with `c_i` deleted), so
`t_j <= B_j^{(m-1)/m}`; by power-mean concavity and `FP_{m-1}`,

```text
sum_{j != i} B_j^{(m-1)/m}
    <= (m-1) ( sum B_j / (m-1) )^{(m-1)/m}  <=  m-1.
```

Total `<= m`.  Equality forces `t_i = 1` (so `c_i = 0`), all `B_j`
equal, and `FP_{m-1}`-equality, hence all zero.  QED

**Corollary (FP4 on the insertion stratum Z).**  With the landed
`FP_3`: every 4-point configuration in which some point `60°-dominates`
the others (all `d_ij <= 1` from it) satisfies `S_4 <= 4`.  The
`c_i = 0` case is the zero-insertion theorem.

## 2. Theorem (an adaptive log-variance certificate and a uniform central radius; all m) — PROVED

Let `L_*` be the unique positive solution of

```text
exp(L_*) = 1 + 2 L_*,
```

and put

```text
rho_* = sqrt(1-exp(-L_*)) = 0.8457729381...,
L_* = -W_{-1}(-1/(2 sqrt(e))) - 1/2.
```

For every `m`, if `max_j |c_j| <= rho_*`, then `S_m<=m`, with equality iff
all points are zero.  More strongly, the whole radius profile gives a
strictly larger certificate.  Put

```text
L_j = -log(1-|c_j|^2),
M_j = (1/m) sum_k -log(1-|c_j||c_k|),
C(t) = (exp(t)-1-t)/t^2,       C(0)=1/2.
```

The configuration-dependent condition

```text
(1/m) sum_j C(M_j)L_j <= 1                         (ROWCERT)
```

already implies `S_m<=m`.

Proof.  Write `R=max_j|c_j|<1`, `L=-log(1-R^2)`,
`q_r=sum_k c_k^r`, and

```text
T_j = (prod_k |1-conj(c_j)c_k|)^(1/m),   h_j=log T_j.
```

The absolutely convergent logarithmic expansion gives

```text
h_j = -(1/m) sum_{r>=1} Re(conj(c_j)^r q_r)/r,
E := (1/m) sum_{r>=1} |q_r|^2/r,
sum_j h_j = -E.                                      (ENERGY)
```

Cauchy--Schwarz in the `r`-sum gives

```text
h_j^2 <= (E/m)(-log(1-|c_j|^2)),
h_j^2 <= (E/m)L_j.                                  (VAR)
```

The triangle inequality in the same series is sharper row by row:

```text
|h_j| <= (1/m) sum_{r>=1,k} (|c_j||c_k|)^r/r = M_j. (ROW)
```

For `h in [-M,M]`, the power series of `(exp(h)-1-h)/h^2` shows that its
maximum is attained at `h=M`: for `h>=0` all coefficients are positive,
while for `h<0` replacing `h` by `|h|` only increases the series.  Therefore

```text
exp(h_j) <= 1+h_j+C(M_j)h_j^2.
```

After summing and using (ENERGY)--(VAR),

```text
S_m <= m-E(1-(1/m)sum_j C(M_j)L_j) <= m             (ROWCERT).
```

The coarser condition `C(Lmax)Lbar<=1` follows because `M_j<=Lmax` and
`C` is increasing.  The uniform hypothesis has `Lbar<=Lmax`, and
`C(Lmax)Lmax<=1` is exactly `exp(Lmax)<=1+2Lmax`, hence holds through
`L_*`.  At equality in the scalar majorants, each `h_j` is nonnegative;
since `sum h_j=-E<=0`, equality
in the final bound forces every `h_j=0`.  Then `E=0`, all power sums `q_r`
vanish, and Newton's identities force every `c_j=0`.  QED

This is a uniform all-degree neighbourhood, not merely a local asymptotic:
any counterexample to any `FP_m` must contain a point of modulus strictly
larger than `rho_*` and must fail the stronger rowwise certificate (ROWCERT).

## 3. Theorem (FP4, without restrictions) — PROVED

For arbitrary `c_1,c_2,c_3,c_4` in the closed unit disk,

```text
S_4 = sum_j (prod_k |1-conj(c_j)c_k|)^(1/4) <= 4,
```

with equality iff all four points are zero.

The proof is a central/outer dichotomy at the exact rational squared radius
`21/25`.  It composes the logarithmic energy from §2 with the valid
K4-matching Hölder inequality from §5; neither half alone proves FP4.

### 3.1 Central case: `max_j |c_j|^2 <= 21/25`

Retain `h_j=log T_j`, `E`, and `L_j` from §2, so

```text
sum_j h_j = -E,                 sum_j h_j^2 <= E mean_j L_j.       (CV)
```

The crucial improvement is one-sided: an upper bound for `h_j` suffices.
Put

```text
Phi(t) = (exp(t)-1-t)/t^2,       Phi(0)=1/2.
```

Taylor's integral remainder gives
`Phi(t)=int_0^1 (1-s)exp(st) ds`, hence `Phi` is increasing on the whole
real line.  If `R^2=21/25`, `r_j=Rt`, `0<=t<=1`, then

```text
T_j^4 <= (1-r_j^2)(1+r_j R)^3
      = (1-(21/25)t^2)(1+(21/25)t)^3 <= 12/5.             (ENV)
```

The last degree-five polynomial inequality is exact: on each of the eight
intervals `[nu/8,(nu+1)/8]`, the Bernstein coefficients of `12/5` minus the
left side are strictly positive (the minimum is `604219/51200000`; replayed
in checker section 13).  The following rational Taylor estimates are also
exact:

```text
exp(22/25) > sum_{k=0}^4 (22/25)^k/k!
           = 12/5 + 6757/1171875,
exp(11/6)  > sum_{k=0}^7 (11/6)^k/k!
           = 25/4 + 211489/282175488,
exp(11/50) < 1+11/50 + (11/50)^2/[2(1-(11/50)/3)]
           = 17321/13900 < 779/625.
```

The two lower bounds are finite Taylor truncations with positive remainder.
For the upper bound, the terms from degree two onward have successive ratio
at most `(11/50)/3`, so their sum is bounded by the displayed geometric
series.  Thus these are rational certificates, not decimal approximations.

Consequently

```text
h_j <= (1/4)log(12/5) < 11/50,
mean_j L_j <= log(25/4) < 11/6,
Phi(11/50) < 6/11.
```

Since `Phi` is increasing,

```text
exp(h_j) <= 1+h_j+Phi(11/50)h_j^2.
```

Summing and using (CV) gives `S_4<4-E+E=4` whenever `E>0`.
If `E=0`, every power sum vanishes and Newton's identities force all four
points to be zero.  Thus the central case, including its equality statement,
is proved.

### 3.2 Outer case: `max_j |c_j|^2 >= 21/25`

Write `u_j=|c_j|^2`, `Q=sum_j u_j`, `E_2=sum_{i<j}u_i u_j`, and
`X=sum_j(1-u_j)=4-Q`.  Let

```text
D_2 = sum_{i<j} d_ij^2 = 6+Q-|sum_j c_j|^2+E_2.
```

For the three opposite-edge matchings, Cauchy followed by AM--GM gives

```text
(d_12+d_34)(d_13+d_24)(d_14+d_23) <= (2D_2/3)^(3/2).      (M)
```

Set `W` equal to `X` times the product on the left of (M), exactly as in the
K4 Hölder inequality of §5.

Let `a=max_j u_j` and let `s` be the sum of the other three squared radii.
The elementary three-variable inequality

```text
sum_{i<j, i,j != argmax} u_i u_j <= s^2/3
```

therefore yields

```text
W <= B(a,s)
   := (4-a-s) [ (2/3)(6+a+(1+a)s+s^2/3) ]^(3/2).          (B)
```

If `X=0`, then `W=0` and there is nothing to prove.  Otherwise, for
`a>=21/25`, `B(a,s)` decreases in `a`.  After clearing the positive factors,
the derivative sign is the strict positivity of

```text
5a+(5a-7)s+(11/3)s^2 >=
21/5-(14/5)s+(11/3)s^2 > 0.                               (DA)
```

The last quadratic has positive leading coefficient and discriminant
`-1344/25`.

It remains to maximize `B(21/25,s)` for `0<=s<=3`.  Its logarithmic
derivative has the sign of

```text
-(8/1875)(625s^2+675s-882),
```

so the unique maximum is at

```text
s_* = (-27+3sqrt(473))/50.
```

Put `D=171/25+(46/25)s+s^2/3` and `Y=79/25-s`.  Exact reduction modulo
`625s_*^2+675s_*-882=0` gives

```text
3456-Y^2D^3
 = 32157853108929/61035156250
   - 7334791379487 sqrt(473)/305175781250 > 0.             (SLACK)
```

The last sign is exact because

```text
160789265544645^2 - 473*7334791379487^2
 = 406183067764073374294937088 > 0.
```

Hence `B(a,s)<32`, so `W<32`.  The valid K4 matching Hölder inequality
`S_4^4<=8W` now gives `S_4<4` throughout the outer case.  Together with
§3.1 this proves FP4.  The algebraic kernel of the pair-product bound,
monotonicity numerator, stationary equation, and radical slack is encoded in
`FreePointFP4Complete.lean`; its focused elaboration is capacity-deferred
under ticket `rct_7d12319183ffd5cbe167`.  The logarithmic/Taylor and calculus
bridges are ordinary exact analysis, and the independent deterministic replay
passes all thirteen sections.

## 4. Theorem (the matching stratum of FP4) — PROVED

For four points, form the **superunit graph** on `{1,2,3,4}` by declaring
`ij` to be an edge when `d_ij>1`.  If this graph is a matching (equivalently,
it is contained in some perfect matching), then

```text
S_4 <= 4,
```

with equality iff all four points are `0`.

After relabelling, the superunit graph is contained in `{12,34}`, so all four
cross terms `d_13,d_14,d_23,d_24` are at most one.  Put
`r=|c_i|`, `s=|c_j|`, `a=(1-r^2)^(1/4)`, and
`b=(1-s^2)^(1/4)`.  The following two-point estimate is the whole proof:

```text
d_ij^(1/4) (x_i^(1/4)+x_j^(1/4)) <= 2.              (PAIR)
```

Indeed, `d_ij<=1+rs`, `(a+b)^4<=8(a^4+b^4)`, and

```text
2-(2-r^2-s^2)(1+rs) = (r-s)^2 + rs(r^2+s^2) >= 0.
```

Taking fourth powers proves (PAIR).  The cross-edge hypotheses now discard
four factors:

```text
T_1+T_2 <= d_12^(1/4)(x_1^(1/4)+x_2^(1/4)) <= 2,
T_3+T_4 <= d_34^(1/4)(x_3^(1/4)+x_4^(1/4)) <= 2.
```

Summing proves the theorem.  Equality in (PAIR) forces `r=s=0`, so equality
in both pair bounds forces all four points to vanish.

This stratum is not a disguised all-small case.  For example, the rational
disk points

```text
c_1=(54+35i)/100, c_2=(-23+57i)/100,
c_3=(69+54i)/100, c_4=(-24+81i)/100
```

have exactly the two superunit edges `12` and `34`; the checker verifies all
six comparisons in exact rational arithmetic.  Combined with the insertion
theorem, the unresolved FP4 graphs may therefore be assumed to have no
isolated vertex and to contain a vertex of superunit degree at least two.

## 5. The K4-matching route: exactly how far it goes — and its closed-form obstruction

**Valid Hölder (new; sidesteps Result 5).**  K4's edges split into the
three perfect matchings `{12,34}, {13,24}, {14,23}`; each vertex meets
each matching once, so generalized Hölder `(4,4,4,4)` gives

```text
S_4^4  <=  8 (sum_j x_j)(d_12 + d_34)(d_13 + d_24)(d_14 + d_23)
       =:  8 W.
```

Result 5's counting obstruction does not apply (the three columns are
NOT permutations of one multiset; the falsified cyclic chain measured
`4.0e5` vs 256, this one `32.106` vs `32`).

**`W <= 32` is FALSE, with an exact extremal.**  On the family
`{r, r omega, r omega^2, 0}` (`omega = e^{2pi i/3}`, `u = r^2`):
`W(u) = (4 - 3u)(1 + sqrt(1 + u + u^2))^3`, maximized at the unique
root in `(0,1)` of `64u^3 - 48u^2 - 27u + 8` (`u* = 0.2307575...`),
value `W* = 32.1061236...` (cubic minimal polynomial in the checker).
Hence the route's best unconditional yield is
`S_4 <= (8 W*)^{1/4} = 4.0033122...` — a quantitative near-miss.  The
Cauchy–Schwarz polynomial variant fails too, exactly:
`(sum x)^2 prod(d_e^2 + d_f^2) <= 128` peaks at `u* = 3/8` with
`P* = (23/8)^2 (161/64)^3 = 2207665649/16777216 = 131.587...`.

**Obstruction theorem (closed form; the family analogue of Result 5).**
On the same family the truth is EXACTLY

```text
S_4 = 1 + 3 (1 - u^3)^{1/4}  =  4 - (3/4) u^3 + O(u^6),
```

a SIXTH-order deficit (identity `(1-u)(1+u+u^2) = 1-u^3`).  But every
weighted-Hölder bound over the K4 1-factorization (weights
`theta_0 = 1 - 3 theta` on the `x`-column, `theta` on each matching
column, exponents forced by row reconstruction) expands as
`4(1 + C u^2 + O(u^3))` with

```text
32 C = 3 (1/4 - 3 sigma theta)^2/(1 - 3 theta) + 9 theta sigma^2
       + 3/(16 theta) - (3/2) sigma,
min over sigma:  32 C = 1/(8 theta),   theta <= 1/3
==>  C >= 3/256 > 0:
```

a FOURTH-order excess against a sixth-order truth — no member of the
family can prove `FP_4`.  SCOPE (load-bearing): the closed form covers
exactly the SYMMETRIC family parametrized above — a dedicated
`x`-column plus the three matching columns.  Schemes that MERGE `x`
into a `d`-column and/or take a MINIMUM over the three labellings are
outside it and get strictly closer: the best found is the
label-minimized asymmetric `min_k M2(k)` at `S_4 <= 4.0000087`
(`2.19e-6` excess, still violated on the same triangle+origin family),
just ahead of scheme X (`4.0000305`) and `min(X, DEL_2)`
(`4.0000088`).  All suprema in this paragraph off the named families
are adversarial numerics.

**All unweighted row-factor permutations are now dead exactly.**  There is a
larger finite class than the dedicated-`x` matching arrangement: in each row,
permute its four factors `x_j,d_jk` arbitrarily among four Hölder columns.
Generalized Hölder gives

```text
S_4^4 <= prod_{ell=1}^4 C_ell,
C_ell = sum_{j=1}^4 f_{j,pi_j(ell)}.
```

On the exact triangle-plus-origin family, the origin row is `(1,1,1,1)` and
each triangle row is a permutation of

```text
v = (D,D,1,x),   D=sqrt(1+u+u^2),   x=1-u,
```

where `D>=1>=x`.  The aligned column vector `C*=1+3v` majorizes every
other column vector: for every `k`, the sum of the largest `k` entries of a
sum of three permutations of `v` is at most three times the sum of the
largest `k` entries of `v`.  Since `log` is concave, Karamata gives

```text
prod C_ell >= prod C*_ell
             = 4(4-3u)(1+3sqrt(1+u+u^2))^2.                 (UPERM)
```

Thus alignment is the pointwise **best** upper bound in this entire class,
including the minimum over all row permutations.  At the rational point
`u=1/6`, its fourth power is

```text
329/2 + 14 sqrt(43)
  = 256 + (28 sqrt(43)-183)/2  > 256,
```

because `(28^2)43=33712>33489=183^2`.  Therefore even the best
unweighted factor-permutation Hölder assignment gives `S_4<=(...)^(1/4)>4`
on this family and cannot prove FP4.  This strictly enlarges the exact no-go
beyond the symmetric dedicated-`x` family.  It still does **not** cover the
weighted/product-merged `M2`, `X`, or deletion schemes responsible for the
smaller measured excesses above.

## 6. Möbius covariance and the deletion inequality

The exact identity `1 - conj(phi_a(z)) phi_a(w) = (1-|a|^2)(1-conj(z)w)
/ [(1-a conj(z))(1-conj(a) w)]` transports `S_m` under disk
automorphisms; specializing `a = c_i` (which maps `c_i` to `0`, i.e.
INTO the insertion stratum) yields the proved deletion inequality

```text
(*)  for every i:   sum_{j != i} A_j^{1/4} / d_ij  <=  3 A_i^{1/4} / x_i
```

(minimum measured slack `9.2e-4` over 1.6e6 configurations; proof =
Theorem 1 applied in the `phi_{c_i}`-image plus covariance).  It does
not by itself close `FP_4` (the weighting carries no normalization),
but it is the exact bridge between the stratum theorem and the bulk.

## 7. Two new reductions

**PM ladder (root-free).**  For `p >= 1/m`, power-mean gives
`[sum_j A_j^p <= m] ==> FP_m`.  At `p = 1`:

```text
PM_m :  sum_j prod_k |1 - conj(c_j) c_k|  <=  m.
```

`PM_2` is PROVED (`(x_1 + x_2) d_12 <= 2` via `d_12 <= 1 + rho_1 rho_2`
and AM-GM; checker section 6).  Adversarially, `PM_m` HOLDS for
`m = 3, 4, 5` (sup `= m`, origin only) and FAILS for `m >= 6`
(`m = 6`: `7.2516` at `c_1 = 5/7, c_2..c_6 = -1`); the sharp
exponent window `p <= log m / log max A_1` is `2.10 (m=3)`,
`1.4385 (m=4)`, `1.106 (m=5)`, `0.904 (m=6)` — so `PM_4 ==> FP_4` is a
root-free reduction inside the proved-window band.  (`PM_3` does NOT
follow from the naive Hölder `(sum x^3)(sum d^3)^2 <= 27` — false.)

**RM (radial monotonicity) — the strongest lead.**  Conjecture: for
every configuration, `rho -> S_m(rho c)` is nonincreasing on `[0, 1]`.
This implies `FP_m` for ALL `m` (value `m` at `rho = 0`).  Closed form
(checker-verified against differences):

```text
F'(x) = -(1/m) sum_j T_j G_j,   G_j = sum_k zeta_jk,
zeta_jk = (R_jk - x rho_j^2 rho_k^2)/d_jk(x)^2,   R_jk = Re(conj(c_j) c_k),
```

with the UNWEIGHTED sum automatic:
`sum_{j,k} zeta_jk = sum_r x^{r-1} |q_r|^2 >= 0` (power sums `q_r`) —
the first-nonzero-mode expansion
`S_m(x c) = m - |q_{r0}|^2 x^{r0}/(m r0) + O(x^{r0+1})` is its leading
case (verified).  RM survived adversarial differential evolution at
`m = 2..6, 8` (max `F'` = numerical zero, attained only at `x = 0`
with `q_1 = 0`).  Note the complex-`x` function is SUBHARMONIC, so the
maximum principle runs the wrong way: RM is genuinely a real-radial
statement.

**Exact no-go for pairwise rearrangement.**  The tempting strengthening
"`T_j` and `G_j` are similarly ordered", which would combine the unweighted
sum with Chebyshev's inequality, is false already for four distinct real
points.  Take

```text
(c_1,c_2,c_3,c_4) = (-9/10,-3/4,-1/2,-1/4),    x=1/4.
```

Direct rational evaluation gives

```text
A_1 = 454859867/819200000 < A_2 = 2588047/4194304,
G_1 = 1170425808/454859867 > G_2 = 26878032/12940235.
```

Since `T_j=A_j^(1/4)`, this proves
`(T_1-T_2)(G_1-G_2)<0` exactly.  The full weighted sum remains positive
(`sum_j T_j G_j = 5.88327...`), so this is not an RM counterexample.  It
does sharpen the proof target: RM needs a genuinely global compensation
identity or weighted power-sum representation; pairwise covariance and a
plain rearrangement argument cannot supply it.

## 8. Claim boundary

PROVED: **FP4 without restrictions**, by the exact central/outer dichotomy
of §3.  Its scalar algebraic kernel is Lean-authored with focused elaboration
capacity-deferred, while the full deterministic exact checker is green.
Also proved: Theorem 1
(all `m`), its FP4-on-Z corollary (consuming landed `FP_3`), the all-degree central-radius theorem through
`rho_*=0.8457729381...` (and its stronger rowwise adaptive form), the matching-stratum theorem and its sharp two-point estimate
(PAIR), the Hölder validity `S_4^4 <= 8W`, the two exact
falsifications with algebraic extremals, the exact `S_4` identity and
the obstruction constant `C >= 3/256` on the SYMMETRIC
(dedicated-`x`-column) family — merged/label-minimized schemes are
outside its scope and are only measured — the Möbius covariance
identity, `PM_2`, the `F'` closed form, and the exact rational
pairwise-comonotonicity no-go for RM; also the majorization theorem and exact
`u=1/6` obstruction (UPERM), which retire **every unweighted** four-column
row-factor permutation.  The two positive strata reduce any unresolved FP4
configuration before the complete proof to the outer shell `max|c_j|>rho_*`, failure of (ROWCERT), and to a superunit graph
with minimum degree at least one and maximum degree at least two; these are now
subordinate structural lemmas rather than residuals.  COMPUTED (adversarial,
not proof): every sup off the named families — `min_k M2(k)`'s
`4.0000087`, scheme X's `4.0000305`, `PM_{3,4,5}`, the RM sweeps, the
deletion-route corrected figure `4.00146`; also one UNADJUDICATED
near-boundary row: the off-stratum deletion scheme at exponent `p = 3`
measured `4 + 4.2e-10` at a tiny near-origin configuration — not
separated from float noise, recorded so nobody promotes `DEL_3|off-Z`
without adjudicating it.  The former RM, PM4, and Lorentzian-Gram routes are
no longer FP4 obligations; RM and the Lorentzian coordinate remain possible
all-degree routes.  `FP_m` remains open for `m>=5`.  The general torus/psh
implication is now landed in `FreePointTorusPshReduction.md`, so this theorem
proves degree-five (S).  Conjecture (S) still does not imply the parent.
Nothing here proves unrestricted Erdős 1041.  PRIORITY CAVEAT: no literature
search; claim "proved in this directory" only.
