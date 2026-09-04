# Erdős 1041: assimilation of the eight 2026-08-31 parent-proof returns

Status: source-current proof audit plus one strengthened ordinary theorem and
one sharp method obstruction.  The eight raw returns are preserved, with
digests, in
`state/formal_math/type_b_return_batches/erdos1041_20260831_full_parent_candidates/intake.json`.
They are advisory inputs, not proof authority.  None of the seven purported
parent proofs closes unrestricted Erdős 1041.

Replay the exact scalar gates with

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_type_b_return_assimilation_20260831.py
```

The coarea, area, variational, and lollipop steps remain ordinary mathematics
as written below; the checker does not relabel them as Lean theorems.

## 1. Terminal dispositions

| Return | Disposition | First load-bearing boundary |
|---|---|---|
| 01 | `blocked_external` | Its "complete-block cyclic product theorem" is the open admissible-product theorem `(AP)` under a new name.  The subsequent fractional port-measure and gluing steps are conditional on that missing theorem. |
| 02 | `strengthened_and_landed` | The weighted-disc union, inverse-square mean-shift descent, critical disc, and squared-action estimates are valid but already present in `BarycentricEnvelope.md`.  The exact surviving gap is that a square-sum bound does not imply the required length-sum bound. |
| 03 | `blocked_external` | The hard-regime connector theorem `(H)` and the all-degree near-Fekete connector `(N)` are asserted rather than proved.  The Fekete product, collar, closure, and strictification steps after them are valid conditional consequences. |
| 04 | `blocked_external` | The carrier principle assumes the open inequality `C(U_c) <= k_c |P(c)|^(1/n)`.  Its exact source-current form is the still-open `2 Lambda + perimeter < 2d` consumer in `PartialClusterPreimagePerimeterIdentity.md`. |
| 05 | `superseded_by_stronger_route` | The two-pole straight-spoke theorem is valid but is the source-current `BarycentricEnvelope.md` threshold.  The claimed equivalence with a top-two mass condition is false; see §2. |
| 06 | `strengthened_and_landed` | The entrance-energy lemma, weighted radial fan-in, optimal one-cell selector, and antichain water filling are valid.  Sections 3–5 below sharpen the theorem with actual area and determine its sharp method boundary. |
| 07 | `rejected_exactly` | The asserted attached entrance-energy theorem already supplies glued root curves whose total carrier length is at most the moved degree.  Arclength parametrisation reduces its hypotheses to the target carrier inequality itself. |
| 08 | `campaign_context_only` | This is a thread/packet trace.  It preserves source and campaign context but adds no independent theorem. |

Thus the batch is not discarded: Return 06 changes the live radial/monodromy
frontier, while Returns 01, 03, 04, and 07 identify the same missing
attachment-compatible carrier from four directions.

## 2. Exact correction to Return 05

Return 05 proves the following valid sufficient statement.  At a nonroot
critical point, let the reciprocal-energy weights be ordered as
`p_1 >= p_2 >= ...`.  If

```text
p_2 >= (n-1)/(2n),
```

then the two selected straight spokes stay below the critical level and their
total Euclidean length is at most `2 |P(c)|^(1/n)`.  This is the occupied
two-pole threshold of `BarycentricEnvelope.md`.

The return also calls `p_1+p_2 >= (n-1)/n` an equivalent description of the
whole regime.  It is not equivalent.  At `c=0`, take reciprocal vectors

```text
u_1=3,
u_2=(-5+i sqrt(29))/3,
u_3=(-4-i sqrt(29))/3,
```

and scale every `u_j` by `2`; put `a_j=-1/(2u_j)`.  Then the critical-balance
sum is zero, the root moduli squared are `1/36,1/24,1/20`, and the normalized
weights are

```text
(p_1,p_2,p_3)=(9/20,3/10,1/4).
```

Hence `p_1+p_2=3/4 >= 2/3`, while `p_2=3/10 < 1/3`.

## 3. Actual-area weighted radial fan-in

Use Return 06's notation.  Let `W` be a unit-level component, let
`tau_i` be the singleton entrance levels, and let `Q` be a nonincreasing
absolutely continuous survival function with `Q(1)=0`.  Put

```text
Q_i=Q(tau_i),
L_Q=sum_i Q_i,
S_Q=sum_i Q_i^2,
D(s)=#{i: tau_i<s},
K_Q=2 pi int_0^1 D(s)s(-Q'(s)+Q(s)/(pi s))^2 ds.
```

Return 06 bounds the total shell area by Pólya through the capacity.  Keeping
the actual normalized area

```text
alpha_W=Area(W)/pi
```

instead gives the strictly stronger theorem

> **Theorem A (actual-area radial fan-in).** If
>
> ```text
> pi alpha_W K_Q < 4(L_Q^2-alpha_W S_Q),                 (A1)
> ```
>
> then `W` contains a root-to-distinct-root path of length below `2` inside
> the unit lemniscate.

Indeed, if `x` is the singleton entrance area divided by `pi`, then the moved
shell area is exactly at most `pi(alpha_W-x)`.  The expected excess is bounded
by

```text
2(sqrt(x S_Q)-L_Q)+sqrt(pi(alpha_W-x)K_Q).
```

The same one-variable minimisation as in the return gives `(A1)`.  Replacing
`alpha_W` by the larger capacity square recovers the returned theorem.

For an attachment-compatible antichain with total moved degree `D` and
`eta_v=1-(a_v/b_v)^(2/pi) >= eta_0`, the corresponding stronger consumer is

```text
eta_0(D/alpha_W-1) >= pi.                               (A2)
```

Thus scalar area is sufficient on every antichain violating `(A2)`; no
independent child worst case is inserted.

## 4. Sharp radial-method obstruction

The method has a universal necessary condition which is absent from the
return.  Put

```text
h(s)=-Q'(s)+Q(s)/(pi s),       beta=1/pi.
```

Since `Q(1)=0`,

```text
Q(t)=t^beta int_t^1 h(s)s^(-beta) ds.
```

Let

```text
A(s)=sum_(tau_i<=s) tau_i^beta.
```

Then

```text
L_Q=int_0^1 h(s)s^(-beta)A(s) ds.
```

Cauchy--Schwarz against `K_Q`, followed by
`A(s)^2/D(s) <= sum_(tau_i<=s) tau_i^(2/pi)`, gives

```text
L_Q^2 < (k/4) K_Q,                                     (R1)
S_Q >= L_Q^2/k.                                        (R2)
```

Consequently every successful capacity-form radial selector must satisfy

```text
(pi+1) kappa^2 < k,                                    (R3)
```

where `kappa=cap(cl W)`.  To see this, the returned criterion would imply

```text
pi kappa^2 K_Q
  < 4(L_Q^2-kappa^2 S_Q)
  <=4(1-kappa^2/k)L_Q^2,
```

while `(R1)` makes the left side strictly larger than
`4 pi kappa^2 L_Q^2/k`.

This obstruction is sharp for the method.  If all `k` sheets enter at one
level `tau`, put `eta=1-tau^(2/pi)`.  Exact Euler minimisation gives

```text
K_Q >= 4k Q(tau)^2/eta,
```

with equality for the hyperbolic-sine survival function in Return 06.  Hence

```text
there exists a Q satisfying the capacity criterion
iff kappa^2 < k eta/(pi+eta).                           (R4)
```

As `tau` decreases to zero, the right side tends to `k/(pi+1)`, proving the
sharpness of `(R3)`.

The quadratic `P_r(z)=z^2-r^2`, `0<r<1`, is the exact natural friction.  Its
unit lemniscate is connected, `kappa=1`, and both sheets enter at `tau=r^2`,
so no radial selector can satisfy the returned criterion.  Nevertheless the
segment `[-r,r]` is contained and has length `2r<2`; equivalently the grouped
translated lollipop of `GroupedCriticalClusterMonodromy.md` closes it.  Thus a
translated/grouped or otherwise polynomial-specific input is logically
necessary; improving only the scalar radial budgets cannot prove the parent.

## 5. Finite exact selector reduction

For distinct ordered entrance levels `tau_1<...<tau_k`, write
`q_j=Q(tau_j)`, `q_(k+1)=0`, and

```text
r_j=(tau_j/tau_(j+1))^(1/pi).
```

Intervalwise Euler minimisation gives

```text
K_Q >= 4 sum_(j=1)^k
  j (q_j-r_j q_(j+1))^2/(1-r_j^2).                     (R5)
```

Repeated levels are grouped first.  Equality is attained when the resulting
interval minimisers join to a nonincreasing survival function.  Therefore the
search for the best radial selector is a finite quadratic test, not an
open-ended functional search.

In the actual-area form, failure on one `d`-sheet cell `a<s<b` forces

```text
alpha_W > d eta/(pi+eta),
eta=1-(a/b)^(2/pi).                                    (R6)
```

For total moved degree at least five and `alpha_W<=1`, simultaneous failure
forces rapid merging:

```text
eta_0 < pi/(D-1).
```

## 6. Source-current frontier after assimilation

The batch narrows, but does not close, the target.  A counterexample must evade
the critical-value separation theorem, the two-pole straight criterion, and
the actual-area fan-in test on every attachment-compatible antichain.  The
unavoidable residual is low moved degree (`2,3,4` at high area/capacity) and/or
rapid critical merging.  The exact complementary target is one of:

```text
2 Lambda(alpha,W)+P(W) < 2 deg(W),
an attachment-compatible age/cluster estimate,
or a translated/grouped connector using polynomial-specific exterior data.
```

No unrestricted theorem, degree-five theorem, universal carrier, or novelty
claim follows from this report.
