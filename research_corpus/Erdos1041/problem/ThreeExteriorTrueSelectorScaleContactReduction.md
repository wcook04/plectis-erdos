# Erdős 1041: the true three-ray selector has a sharp scale-contact equation

## Result

Fix `n in {5,6}` and a three-zero finite Blaschke configuration

```text
B_lambda(z)=unit product_(k=1)^3 (z-lambda a_k)
                              /(1-lambda conj(a_k)z),
```

on an interval of common scales on which the zeros stay in the open unit
disc and the boundary-speed condition remains strict.  Write

```text
p(lambda)=lambda^3 product_k |a_k|,
R(lambda)=R_n(p(lambda)),
V_j(lambda)=max_(lambda|a_j|<=q<=1)
              q^(-n)|B_lambda(q u_j)|,
u_j=a_j/|a_j|,
Y_j=V_j/R,                 H=min_j Y_j.                (1)
```

Let `q_j` be an interior optimizing radius for `V_j`, chosen among multiple
optimizers to maximize the scale derivative, and put

```text
C_j=sum_k P_(q_j lambda a_k)(u_j).                     (2)
```

For the regular triangle of radius

```text
s=lambda(product_k|a_k|)^(1/3),
```

let `q_*` be its optimizing radius and set

```text
C_*=3(1+(q_*s)^3)/(1-(q_*s)^3).                       (3)
```

Then the exact relative envelope derivative is

```text
d/d log lambda log Y_j=C_j-C_*.                       (4)
```

Consequently suppose `lambda_c` is a first upward failure scale for the
**true**, nonsmoothed selector: there are scales decreasing to `lambda_c`
from above at which `H>1`, while `H(lambda_c)=1`.  If

```text
A={j:V_j(lambda_c)=R(lambda_c)}                        (5)
```

is the active set, then

```text
V_j(lambda_c)>=R(lambda_c)             for every j,
max_(q in Opt_j) [C_j(q)-C_*]>=0       for every j in A. (6)
```

In particular, for every active ray there is an optimizing radius satisfying

```text
V_j=R,       partial_q log(q^(-n)|B(q u_j)|)=0,
C_j>=C_*.                                            (7)
```

Thus the remaining nonregular first contact is not only the value/KKT system
from the capacity-continuation reduction.  It also obeys one sharp
value-speed inequality on every active minimum ray.  Unlike a soft-min
scale derivative, (4) has no factor `V_j/(V_j-1)` and no averaging weights.

## Proof

For one zero, the two exact Poisson identities are

```text
q partial_q log rho(q u,lambda a)
 =1/2[P_(lambda a/q)(u)+P_(q lambda a)(u)],            (8)

partial_(log lambda) log rho(q u,lambda a)
 =1/2[P_(q lambda a)(u)-P_(lambda a/q)(u)].            (9)
```

At an interior optimizer of the attached profile, (8) summed over the three
zeros gives

```text
sum_k[P_(lambda a_k/q_j)(u_j)+P_(q_j lambda a_k)(u_j)]
 =2n.                                                  (10)
```

The envelope theorem, (9), and (10) therefore give

```text
partial_(log lambda) log V_j=C_j-n.                   (11)
```

The same calculation on the regular triangle gives

```text
partial_(log lambda) log R=C_*-n,                     (12)
```

where the three contracted Poisson terms sum to (3).  Subtracting (12) from
(11) proves (4).  At an optimizer switch, Danskin's formula replaces `C_j`
by the largest contracted speed among the active optimizing radii, exactly
as stipulated above.

Now assume the first-failure hypothesis.  Since `H(lambda_c)=1`, definition
(1) gives the first half of (6), and `A` is nonempty.  For every `j in A`,
the failure sequence has

```text
Y_j(lambda)>=H(lambda)>1,
```

whereas `Y_j(lambda_c)=1`.  Hence the upper right Dini derivative of
`log Y_j` at `lambda_c` is nonnegative.  Danskin's formula and (4) give the
second half of (6).  Below the regular saturation endpoint one has `R>1`,
so an active equality ray cannot be represented only by the fixed endpoint
`q=1`; an interior optimizer exists and (7) follows.

## Why this is stronger than the soft-min contact

The negative-power soft minimum is useful for smooth local curvature, but
its derivative averages all rays and carries the potentially large factors
`V_j/(V_j-1)`.  A failure of the desired theorem is a failure of `H`, not of
that auxiliary mean.  Passing directly to `H` shows that a genuine first
failure must make **each cheapest ray** decay no faster than the regular
barrier.  Therefore a certificate may exclude contact by proving only

```text
V_j=R and q-stationarity  ==>  C_j<C_*                 (13)
```

for one active minimum ray, rather than controlling a global soft-min scale
sign on configurations far below the barrier.

## Exact boundary

Proved here: the relative scale identity (4), its optimizer-switch form, and
the necessary contact conditions (6)--(7).  The regular orbit satisfies
equality in (7); the existing finite mixed-kernel and terminal cubic theorems
exclude a nonregular contact in their respective regular collars.

Still open: exclude (7) on the compact nonregular middle region, prove the
full finite three-exterior selector, and prove unrestricted Erdős 1041.  This
note is a sharper reduction inside the existing adaptive-minray mechanism,
not a new theorem family and not a parent closure.

The subsequent `ThreeExteriorUniqueActiveContactExclusion.md` consumes this
system together with fixed-product configuration stationarity and removes the
entire smooth one-active-ray cell.  Thus (7) now needs certification only on
multi-active selector switches and the named constraint/optimizer boundaries.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_true_selector_scale_contact.py
```

```text
tao_pipeline_receipt:
  input_stage: finite three-exterior continuation plus exact scale-envelope identity
  output_stage: true-selector first-contact reduction
  artifact: ThreeExteriorTrueSelectorScaleContactReduction.md plus symbolic replay
  human_understanding_delta: a genuine selector failure is constrained ray-by-ray; every active minimum ray must meet the regular barrier and have contracted Poisson speed at least the regular speed
  verification_state: ordinary exact proof plus symbolic identity replay
  publication_or_review_state: source-level research reduction, not independently reviewed
  canonicalization_state: subordinate contact theorem in the existing adaptive-minray family
  unresolved_downstream_bottleneck: exclude the value-stationarity-speed system on the compact nonregular middle region
  next_stage_owner: finite compact contact atlas or analytic value-speed tradeoff
```
