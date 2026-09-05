<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Short lemniscate paths from a small critical value

## The result

Let `f` be a squarefree monic complex polynomial of degree `n>=2`, and set
`mu=min_{f'(c)=0}|f(c)|>0`. If `mu<=13/25`, two distinct roots are joined by
a rectifiable curve of length strictly below `2` inside `{|f|<1}`. There is
no restriction on the locations of the roots.

Equivalently, every squarefree monic polynomial has a root connector inside
`{|f|<(25/13)mu}` of length below `2((25/13)mu)^(1/n)`. Apply the first
statement to `s^(-n)f(sz)`, with `s=((25/13)mu)^(1/n)`, and scale back.
Repeated root occurrences admit the constant curve.

This is an ordinary analytic proof with an exact rational computational
certificate. It is not Lean formalized. The analytic estimates and the
rational inequalities checked by the program are stated below. The threshold
is a sufficient condition; it does not settle Erdős #1041 for all polynomials
whose roots lie in the open unit disc.

The argument combines two consequences of the absence of a short path.
The roots must be far apart in the hyperbolic metric of their lemniscate
component, yet a point on the first merger must see a large sum of their
Green functions. Packing forces many roots into that component. Their
inverse radial lifts and intervening boundary arcs then force its area to
grow beyond Pólya's area cap before the level reaches one.

## 1. Geometry at a regular level

For `0<a<=1`, write

```text
delta(a) = -log(1-exp(-1/a)),
tau(a)   = -log tanh(1/a),
lam(d)   = -log tanh(d/2),
D(a)     = 4 artanh(sqrt(tanh(1/a))),
d_low(a) = lam(delta(a)/2).
```

Hyperbolic distance on the unit disc has curvature `-1`, so pseudohyperbolic
distance `rho` corresponds to `d=2 artanh(rho)`. Notice
`cosh(D(a)/2)=exp(2/a)` and `lam(lam(d))=d`.
The failure geometry used below is

```text
(i)   d(b_i,b_j)>=D(a) for i!=j,
(ii)  d_j=d(0,b_j)>=d_low(a),
(iii) sum_j lam(d_j)>=x.
```

## 2. From a missing path to the area inequality

Here is the analytic chain consumed by the certificate. The strict-path and component conventions are included explicitly.
Let `f` be squarefree and let `mu>0` be its least critical-value modulus.
Choose a critical point at level `mu` and two descending inverse arcs into
distinct one-root components of `{|f|<mu}`. Their union is a compact connected
set `Gamma` containing two roots, with `|f|<=mu`. Below `mu`, each
component maps conformally onto the value disc because it contains no
critical point. Distinct local inverse arcs at the first critical point enter
distinct such components: two inverse images of a nearby regular value in
one component would contradict its degree one. At a regular level
`mu<t<1`, let `C_t` be its ancestor, let `k` be its number of roots, and put
`x=log(t/mu)`, `a=Area(C_t)/pi`. Pólya's area inequality gives
`a<=t^(2/n)<1`. The regular component is a Jordan domain, and a Riemann map
turns `f/t` into a degree-`k` finite Blaschke product.

For a Riemann map `phi`, its derivative has Bergman squared norm
`Area(C_t)`. The radial restriction of the Bergman kernel gives

```text
length(phi([0,r]))^2 <= a log(1/(1-r^2)).
```

Moving two preimages to `-s,s` instead gives

```text
length(phi([-s,s]))^2 <= 4a artanh(s^2),
```

because the corresponding kernel integrals are `-log(1-r^2)` and
`4 artanh(s^2)`. A path shorter than `2` therefore exists if any root pair
has hyperbolic distance below `D=4 artanh(sqrt(tanh(1/a)))`. Failure gives
condition (i).

Failure also gives an `h in Gamma` whose intrinsic distance to every root
is at least `1`. Otherwise the relatively open sets
`{h in Gamma : dist_C_t(h,a_j)<1}` cover `Gamma`. If two such sets meet,
concatenating their paths gives length below `2`; if only one is nonempty,
it contains the other root of `Gamma` and already gives a shorter path.
Connectedness excludes a disjoint cover by several nonempty sets. Sending
this `h` to zero, the one-root estimate gives
`rho_j>=sqrt(1-exp(-1/a))`. Thus `d_j>=d_low(a)`, condition (ii), and the
Blaschke product identity gives
`sum_j lam(d_j)=log(t/|f(h)|)>=x`, condition (iii).
Notice that distance **at least** `1`, not strictly greater than `1`, is
all this argument supplies and all the non-strict failure inequalities need.

For completeness, the metric part uses all root lifts in `C_t` together.
At a direction avoiding the finitely many critical-value arguments, lift
the value radius from `0` to `t exp(i theta)` from each of the `k` roots.
Split the lifts at level `mu`, and let `A_0` be the sum of the areas of their
one-root lobes below `mu`. If `phi(z)=sum_l b_l z^l` maps a unit disc onto
such a lobe, Cauchy--Schwarz in the radial variable and Parseval give

```text
mean_theta (int_0^1 |phi'(r exp(i theta))| dr)^2
    <= sum_{l>=1} l^2 |b_l|^2/(2l-1)
    <= sum_{l>=1} l |b_l|^2 = Area(lobe)/pi.
```

Summing and applying Cauchy--Schwarz bounds the mean total low lift length
by `sqrt(k A_0/pi)`. At a regular intermediate level `u`, let `P_C(u)`
be the total level perimeter inside this fixed `C_t`, and let `A_C(u)` be
the enclosed area there. The argument principle and coarea formula give

```text
P_C(u)^2 <= 2 pi k u A_C'(u).
```

Indeed, on the level curve `|dz|=u d(arg f)/|f'|`, its total argument
variation is `2 pi k`, and Cauchy--Schwarz gives the inequality. Integrating
`P_C(u)/(2 pi u)` from `mu` to `t` bounds the mean high lift length by
`sqrt(k x (pi a-A_0)/(2 pi))`. Combining the low and high bounds gives

```text
mean total lift length <= sqrt(k a (x+2)/2) =: M.
```

Some regular direction has total lift length at most `M`. Order its `k`
boundary endpoints cyclically and form `k` root connectors, each using two
lifts and the intervening boundary arc. The entire construction is in
`closure(C_t) subset {|f|<1}`. Under failure all these lengths are at least
`2`; hence `2k<=2M+P(t)`. At the outer level the same perimeter inequality
reads `P(t)^2<=2 pi^2 k a'(x)`. Rearrangement yields

```text
a'(x) >= (1/(2 pi^2)) [2 sqrt(k)-sqrt(2a(x+2))]_+^2.
```

This proves the differential inequality on every regular interval of the
ancestor. At merger levels the ancestor gains area, which strengthens the
integrated comparison below. A contradiction before `t=1` proves a path
strictly shorter than `2` in the open unit lemniscate, without any restriction
on where the polynomial roots lie.

## 3. Bounds on the number of roots

All bounds here apply to the same failure configuration (i)--(iii). Their
maximum may therefore be used as a lower bound for its integer size `k`.

### The ordered-distance bound

The one-root bound gives `k>=2x/delta(a)`. Pairwise separation gives more.
Order the distances `d_1<=...<=d_k`. The triangle inequality gives
`d_1+d_2>=D`. For fixed `d=d_1`, the largest possible Green sum under these
necessary constraints is

```text
lam(d)+(k-1)lam(max(d,D-d)).
```

Here `d_low<D/2`. The displayed expression is convex on `[d_low,D/2]`
because `lam''(d)=cosh(d)/sinh(d)^2>0`; beyond `D/2` it is decreasing.
Consequently

```text
sum_j lam(d_j) <= max(delta/2+(k-1)lam(g), k tau/2),
g=D-d_low.
```

Inverting the two branches gives
`k>=min(1+(x-delta/2)/lam(g), 2x/tau)`. This is a relaxation of the
geometric constraints, so it does not require the maximizing profile to be
realizable. For arithmetic evaluation, `g=2lam(tau/2)-lam(delta/2)`.
The function `g(a)` decreases on `0<a<=1`: putting `u=exp(-1/a)` and
`v=1/a>=1`, its derivative with respect to `v` is
`4/sqrt(1-u^4)-1/sqrt(1-u)>0`, since `u<1/2`. Thus rounding the area up
also gives an upper bound for `lam(g)`.

### A packing bound

Put `E=exp(2/a)-1`. The open hyperbolic balls of radius `D/2` about the
roots are disjoint and have area `2pi E`. At most one contains the observer
`0`. For every other ball the mean-value property of the Green function
`G(z)=-log|z|` identifies `lam(d_j)` with its average over the ball.
By radial rearrangement, the integral over their union is bounded by the
integral over a ball of the same area centered at `0`. If this union has
`N` balls, put `C=1+NE`. Direct integration gives

```text
(1/(2pi)) int_{B(0,R)} G dA_hyp
    = (C-1)/2 * log((C+1)/(C-1)) + log((C+1)/2),
cosh R=C.
```

The first term is at most `1`. If one ball contains `0`, bound that root's
contribution by `delta/2` and take `N=k-1`; otherwise take `N=k` with no
extra term. Inverting these two alternatives gives the valid lower bound

```text
k >= min(1+2(exp(E(x-delta/2)-1)-1)/E,
           2(exp(Ex-1)-1)/E).                         (P)
```

The minimum, not the maximum, is required because the two cases are
alternatives. The bound `k>=2` is retained when a displayed expression is
negative.

### Circle slices retain the geometry

A stronger family of inequalities records disjointness on each hyperbolic
circle about the observer. Define

```text
w(d,r)=arccos(clamp((cosh d cosh r-cosh(D/2))/(sinh d sinh r),-1,1)).
```

The circle of radius `r` meets the ball about `b_j` in an arc of angular
measure `2w(d_j,r)`. The hyperbolic law of cosines gives this formula,
and disjointness gives `sum_j w(d_j,r)<=pi` for every `r>0`.
The clamp includes balls containing the observer: if `d<D/2`, all circles
with `r<D/2-d` lie wholly in the ball and `w=pi`. Replacing this by a
half-circle would be wrong.

Choose any positive radii `r_i` and nonnegative weights `sigma_i`, and put

```text
S=sum_i sigma_i,
U=sup_{d>=d_low} [lam(d)-sum_i sigma_i w(d,r_i)].
```

When `U>0`, summing the defining upper bound over the roots yields

```text
x <= sum_j lam(d_j) <= kU+pi S,
k >= (x-pi S)/U.                                      (CS)
```

No optimality of the chosen weights is needed. This is why a floating-point
linear program may propose them without being part of the proof: only the
resulting rational upper bounds on `S` and `U` are used.

## 4. Exact certificate

The companion [Python checker](../../experiments/erdos1041_low_critical_path_certificate.py)
uses `fractions.Fraction` for all accepted inequalities. It takes the maximum
of `2`, the ordered and one-root bounds, `(P)`, and `(CS)`, rounding each
lower bound up because `k` is an integer. Its numerical bounds are directed:

- exponentials use Taylor sums and geometric tails; repeated squaring extends
  their range, and capping a lower exponential at `exp(64)` remains safe;
- `delta` and `tau` use positive power series, with upper geometric tails;
- square roots use integer square roots, and all rounded bounds retain their
  required direction;
- the rational brackets for `pi`, `log(2)`, and `1/(2pi^2)` are checked from
  Machin's identity and the positive series for `2 artanh(1/3)`.

To bound `U`, the checker subdivides the distance interval. On `[u,v]`,
`lam(d)<=lam(u)`. The cosine defining `w(d,r)` has derivative of the sign
of `cosh(d)cosh(D/2)-cosh(r)`, so it has at most one interior minimum.
Thus the minimum of the clamped half-width on a cell occurs at an endpoint.
Use the lower of the two certified endpoint widths and an upper bound for
`lam(u)`. Beyond `max_i r_i+D/2` every width vanishes, and monotonicity of
`lam` bounds the tail. The largest cell or tail bound certifies `U`.

The widths are bounded from below by
`w=2arcsin(sqrt(clamp(om,0,2)/2))`, where
`om=(cosh(D/2)-cosh(d-r))/(sinh d sinh r)`. The arcsine has a positive
series; near one, use `arcsin(z)=pi/2-arcsin(sqrt(1-z^2))` with the
opposite directed bounds. The area table is rounded up: both `D(a)` and
`d_low(a)` decrease in `a`, so a dual certified at a larger area is valid
at every smaller area.

### Propagating a lower bound on area

Let `A(x)=Area(C_(mu exp x))/pi` be the area of the chosen ancestor component.
Between its finitely many merger levels it is absolutely continuous; mergers
can only add area. Thus its derivative inequality integrates across a cell
with an additional nonnegative jump contribution.

Fix `xl <= x <= xr` and a trial area `m<=1`. If `A(x)<=m` throughout the
cell, every failure configuration obeys the weaker geometric constraints at
area `m`: the separation radius and the minimum distance from the observer
both decrease as the area parameter grows. The certified arity floor evaluated
at `(xl,m)` therefore remains valid for every point of the cell. Using `xr`
and `m` in the subtracted term of the boundary-hop inequality gives

```text
A'(x) >= g_cell_lower(xl,xr,m)   almost everywhere while A(x)<=m.
```

Suppose a certified lower bound at the left endpoint is `A(xl)>=ai`, and put
`h=xr-xl`. A trial value `m` satisfying

```text
m < ai + h*g_cell_lower(xl,xr,m)
```

is a strict lower bound for `A(xr)`. Indeed, if `A(xr)<=m`, monotonicity of
the actual area implies `A(x)<=m` on the cell. Integration, including the
nonnegative merger jumps, would give `A(xr)>=ai+h*g_cell_lower(xl,xr,m)>m`,
a contradiction. This argument needs no monotonicity of the *computed*
lookup across independently optimized area cells.

The checker starts its lower endpoint at `ai` and raises it only after this
test succeeds. An arbitrary upper search endpoint affects precision, not
validity. In particular, a predictor is not a certified lower endpoint:
`ai+h*g_cell_lower(xl,xr,ai+h*g_cell_lower(xl,xr,ai))` can overshoot when the
computed lower lookup increases. The exact `--comparison-audit` regression
exhibits this failure for a lower oracle beneath a decreasing true envelope.
The revised initialization avoids it. Every returned value is rounded down.

Finally `A(x_s)>=10^(-6)` follows from `k>=2`, `A<=1`,
`x_s=3/10^5`, and the explicit positive `start_shift` bound. The step argument
propagates a lower bound for *every* trajectory above that initial value.
Only this one start is needed; a grid of larger initial areas adds no coverage.
The reported hitting time is rounded upward before the final exponential
threshold test. The test at `m=1` certifies that the area cap has been exceeded before
`mu exp(x)=1`, yielding the contradiction.

## 5. Replay and conclusion

From the repository root, run

```sh
python3 experiments/erdos1041_low_critical_path_certificate.py --comparison-audit
python3 experiments/erdos1041_low_critical_path_certificate.py --geometry-audit
python3 experiments/erdos1041_low_critical_path_certificate.py --quick
python3 experiments/erdos1041_low_critical_path_certificate.py
```

For the stated replay, install NumPy and SciPy in a Python environment
(`python3 -m pip install numpy scipy`). They accelerate proposal generation. The standard-library fallback
still certifies each proposed dual but may give a weaker final threshold;
inspect `all_degree.mu_threshold` rather than assuming the requested mode's
usual result. The program prints the threshold it actually certifies.

The full audited replay uses 18 area-table levels, 14 radii per dual, 126
certified duals, step `1/400`, and the single initial lower area `10^(-6)`.
It certifies

```text
X = 635762889599/1000000000000 < 0.6357629,
(13/25) exp(X) < 1.
```

Every area trajectory permitted by failure exceeds `1` by `X`, while
Pólya gives area at most `1` until level `1`. This contradiction proves the
stated path theorem. Quick mode gives `X=664373027131/1000000000000` and
threshold `51/100`.

The geometry audit includes an exact full-circle case. The comparison audit
includes a nonmonotone lower lookup that made the earlier predictor-based
initialization overshoot; the revised step raises its lower endpoint only by
a valid end-area test. These small regressions supplement the full certificate.
Neither floating optimizers nor numerical estimates of a possible best
threshold prove an optimality bound.

## Source and attribution

This note assembles the low-critical potential, connected-cluster separation,
hyperbolic packing and circle-slice arguments developed in Will Cook's
AI-assisted mathematical research programme. The circle-slice and area-step
corrections and the self-contained assembly were made in the source audit of
5 September 2026. The general inputs are the Riemann mapping theorem, the
Bergman kernel, the argument principle, coarea and Pólya's area inequality.


Pólya's input is `Area{|f|<=t}<=pi t^(2/n)` for a monic polynomial. See
G. Pólya, *Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach
zusammenhängende Gebiete*, Sitzungsber. Preuss. Akad. Wiss., Phys.-Math. Kl.
(1928), 228--232 and 280--282. The original path problem is Problem 5 in
P. Erdős, F. Herzog and G. Piranian, *Metric properties of polynomials*,
J. Analyse Math. **6** (1958), 125--148,
[DOI:10.1007/BF02790232](https://doi.org/10.1007/BF02790232).
