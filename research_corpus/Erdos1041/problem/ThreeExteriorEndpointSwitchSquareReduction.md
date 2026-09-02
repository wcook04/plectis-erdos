# Erdős 1041: the GP3 endpoint switch is an exact square correction

## The reduction

Let `a,b,c>0` be the three coefficients in the weighted-cosine problem

```text
min_(A+B+C=0) a cos A+b cos B+c cos C.                 (1)
```

Suppose the reciprocal-triangle inequality fails at `a`, namely

```text
1/a >= 1/b+1/c,
F:=bc-a(b+c)>=0.                                      (2)
```

The stationary and endpoint formulae for (1) are

```text
M_stat=-1/2(ab/c+ac/b+bc/a),
M_end =a-b-c.                                         (3)
```

They obey the exact identity

```text
M_end-M_stat = F^2/(2abc).                            (4)
```

Indeed, after multiplication by `2abc`, (4) is just

```text
2abc(a-b-c)+a^2b^2+a^2c^2+b^2c^2
  =[bc-a(b+c)]^2.                                    (5)
```

The endpoint value is therefore the continuous stationary rational formula
plus a nonnegative perfect-square correction.  Equality in (4) holds exactly
on the reciprocal-triangle switching surface `F=0`.

## Consequence for the three-exterior surplus

In `ThreeExteriorGreenPolarization.md`, write the angle-independent tangent
part as `R` and the three positive tangent weights as `a,b,c`.  The two radial
surpluses are

```text
S_stat=R+(a+b+c)/2+M_stat,
S_end =R+(a+b+c)/2+M_end.                             (6)
```

On the endpoint cone (2), equations (4) and (6) give

```text
S_end=S_stat+F^2/(2abc).                              (7)
```

Thus the endpoint branch is not an unrelated second four-variable
inequality.  Any stationary lower bound may be reused, and the only extra
currency is the explicit squared distance `F^2` from the switching surface.
This explains why a whole-box Bernstein expansion of `S_end` can expose
negative controls only near `F=0`: there the endpoint and stationary
formulae agree to second order.

Equation (7) does not prove either surplus nonnegative on the full ordered
cone.  In particular `S_stat` can be negative outside the reciprocal-triangle
region, and then the square must be spent quantitatively.  The surviving
proof obligation is the branch-aware inequality

```text
S_stat >= -F^2/(2abc)       whenever F>=0,             (8)
```

plus its two cyclic copies.  This is a strict reduction of the old endpoint
atlas target, not GP3, the optimized fixed-ray selector, or unrestricted
Erdős 1041.

## Replay

Run

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_endpoint_switch_square.py
```

The checker verifies (4)--(7) symbolically and at exact rational endpoint and
switch specimens.

```text
tao_pipeline_receipt:
  input_stage: branch-aware GP3 endpoint certificate search
  output_stage: exact algebraic reduction
  artifact: ThreeExteriorEndpointSwitchSquareReduction.md plus symbolic/rational checker
  human_understanding_delta: the endpoint and stationary cosine branches differ by one explicit perfect square, so the former atlas only needs to pay the negative stationary part away from the switch
  verification_state: exact symbolic identity and rational regressions
  publication_or_review_state: source-level research reduction, not independently reviewed
  canonicalization_state: subordinate reduction inside the existing three-exterior GP3 family
  unresolved_downstream_bottleneck: prove S_stat >= -F^2/(2abc) on the endpoint cone and finish the positive ordered atlas
  next_stage_owner: active GP3 atlas proof lane
```
