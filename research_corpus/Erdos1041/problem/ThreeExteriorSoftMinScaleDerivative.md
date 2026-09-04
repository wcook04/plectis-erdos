# Erdős 1041: soft-min selector and exact scale-envelope derivative

## Result

Let

```text
B_lambda(z)=unit product_(k=1)^m (z-lambda a_k)/(1-lambda conj(a_k)z),
u_j=a_j/|a_j|,
E_j(lambda,q)=q^(-n)|B_lambda(q u_j)|,
V_j(lambda)=max_(lambda|a_j|<=q<=1) E_j(lambda,q),
```

where `n>m`, every scaled zero stays in the open unit disk, and the boundary
speed satisfies

```text
C_lambda(u):=sum_k P_(lambda a_k)(u)<n.                 (1)
```

At an interior optimizing ray parameter `q_j`, put

```text
C_j^+=sum_k P_(q_j lambda a_k)(u_j).
```

Then the envelope derivative is exactly

```text
d/d log lambda log V_j = C_j^+-n < 0.                  (2)
```

The same conclusion holds as an upper-Dini derivative at optimizer switches;
if the endpoint `q=1` is active, `V_j=1`.  Thus every optimized attached-ray
barrier is nonincreasing under common outward scaling.

For `p>0`, set `x_j=V_j-1` and define the negative-power soft minimum

```text
M_p=(m/sum_j x_j^(-p))^(1/p).                          (3)
```

Whenever all `x_j>0`, with

```text
omega_j=x_j^(-p)/sum_k x_k^(-p),
```

one has

```text
d/d log lambda log M_p
 =sum_j omega_j [V_j/(V_j-1)](C_j^+-n).                (4)
```

Also

```text
min_j(V_j-1)<=M_p.                                     (5)
```

Consequently, if `R_n(lambda^m product|a_k|)` is the regular `m`-gon
comparator and

```text
M_p<=R_n-1,                                            (6)
```

then the required adaptive-ray selector follows.  Equation (4) converts
scale propagation of (6) into one explicit Poisson-deficit inequality; it
does not assert that this last inequality always has the desired sign.

For the active three-exterior problem, `m=3`.  If `s` is the common regular
radius and `q_*` its optimizer, the contracted regular speed is

```text
C_*=3(1+(q_*s)^3)/(1-(q_*s)^3),                        (7)
```

and hence

```text
d/d log lambda log(M_p/(R_n-1))
 =sum_j omega_j [V_j/(V_j-1)](C_j^+-n)
  -[R_n/(R_n-1)](C_*-n).                              (8)
```

This is the exact scale-sign target.  Computation is useful for selecting a
degree, capacity range, or exponent `p`, but no sampled sign is part of the
theorem.

## Proof

For one zero `a=r exp(i phi)`, write `c=cos(theta-phi)` and

```text
N=q^2+r^2-2qrc,       D=1+q^2r^2-2qrc.
```

For the pseudohyperbolic factor `rho=|(q exp(i theta)-a)/
(1-q conj(a)exp(i theta))|`, direct differentiation gives

```text
q partial_q log rho
 =1/2[(q^2-r^2)/N+(1-q^2r^2)/D]
 =1/2[P_(a/q)(u)+P_(qa)(u)],                           (9)

r partial_r log rho
 =1/2[P_(qa)(u)-P_(a/q)(u)].                          (10)
```

At an interior maximizer of `E_j`, stationarity in `q` says

```text
1/2 sum_k[P_(lambda a_k/q_j)(u_j)
          +P_(q_j lambda a_k)(u_j)]=n.                (11)
```

The envelope theorem and (10)--(11) now give (2).  Moreover the Poisson
semigroup identity gives

```text
sum_k P_(q lambda a_k)=P_q*C_lambda,
```

so (1) implies `C_j^+<n`.  At a multiple optimizer, Danskin's formula takes
the maximum of the active branch derivatives, all of which are negative;
the moving left endpoint has value zero and the right endpoint has the fixed
value one.  This proves the monotonicity assertion.

Differentiating (3) with respect to `log x_j` gives exactly `omega_j`.
Combining this with (2) proves (4).  Inequality (5) is the elementary fact
that a negative-order power mean is at least its smallest entry.  Formula
(7) follows by summing the three Poisson kernels at the regular root
directions; (8) follows from (4) and the regular instance of (2).

## Equality Hessian and exponent leverage

The smoothing exponent is genuine proof leverage rather than a change of
target.  At a regular equality point `x_1=...=x_m=e`, if
`sum_j x_j'=0`, exact differentiation gives

```text
M_p''=(1/m)sum_j x_j''
       -(p+1)/(m e) sum_j (x_j')^2.                   (12)
```

Increasing `p` strengthens the negative variance payment while (5) remains
valid.  If `p=p(lambda)` is allowed to vary, one also has

```text
partial_p log M_p
 =(1/p)sum_j omega_j log(x_j/M_p)<=0,                  (13)
```

so an adaptive exponent can be tested without losing the selector
implication.  Equations (12)--(13) are reductions, not global sign claims.

## Exact boundary

Proved here: the factor identities (9)--(10), the stationary elimination,
the scale derivative (2), monotonicity of each individual optimized barrier,
the soft-min implication, derivative (4), the regular comparison formula,
and the equality Hessian.

Still open: the sign of (8) on the full finite three-exterior configuration
space, the global soft-min inequality (6), the unrestricted finite selector,
the terminal-block theorem, and Erdős 1041.  Numerical screening indicates
that a global one-signed version of (8) is plausible in degree five but false
in a low-capacity degree-six pocket; this remains computational evidence only.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_softmin_scale_derivative.py
```

```text
tao_pipeline_receipt:
  input_stage: finite three-exterior selector and scale-homotopy search
  output_stage: exact reduction
  artifact: ThreeExteriorSoftMinScaleDerivative.md plus symbolic checker
  human_understanding_delta: optimizer stationarity converts the raw scale derivative into a contracted Poisson-speed deficit, while negative-power means smooth the adaptive selector without changing its implication
  verification_state: ordinary exact proof plus symbolic identity replay; global scale signs remain computational
  publication_or_review_state: source-level research reduction, not independently reviewed
  canonicalization_state: scale-envelope and soft-min reduction in the existing three-exterior family
  unresolved_downstream_bottleneck: prove a contact-level or range-restricted sign for (8), or certify the remaining compact nonregular contacts directly
  next_stage_owner: finite three-exterior selector proof lane
```
