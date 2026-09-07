# Erdős 1041: the integrated entropy sum rule on the trace-maximal ray — an exact negative currency for the excess inequality

Date: 2026-08-30.  Origin: main-loop proof (this session), independently
re-verified by a subagent (symbolic + numeric).  Checker:
`scripts/check_erdos1041_trace_max_entropy_budget.py`.

## Novelty labels (read first)

- The POINTWISE fibre product identity and its `<= 1` contraction under
  a half-plane hypothesis are LANDED: `MinimalHubArmBudgetRefutation.md`
  Lemma 1 (`prod_{f(z)=w} f'(z) = n^n prod_k (f(c_k) - w)`, FRONTIER §3)
  and `TiedNewtonFaceFibreProduct.md` (2)+(5) (the shifted form with
  monotonicity; its hub-shift remark makes the trace-maximal case
  automatic).  Restated here only for use.
- The INTEGRATED form — the closed-form entropy integral and the sum
  rule below — is new to this directory (no occurrence of the constant
  `pi/sin(pi/n)` or of `Re delta^{1/n}` in any owner file).
- The angular quadratic (Pólya) budget is LANDED in value:
  `SixReturnJointAssimilation20260826.md` §1.7 proves the `<= nR`
  action bound from the same Jacobian + Pólya inputs, and a later
  duplicate was already routed `superseded_by_exact_corpus_theorem`.
  Section 3 below records only the EQUALITY refinement of that lane,
  credited there, because the checker uses it as a two-sided test.
- The support–oscillation lemma of section 4 is the general-arm
  total-variation form of `TurningLengthBound.md`'s constant-sign
  theorem; `RayDirectionScopeLimit.md` §3b names TV as exactly the
  quantity a general bound must control AND measures that a TV bound is
  insufficient by itself at 5/24 directions of its cusp model.  It is
  landed here as a lemma with that scope caveat, not as a route.

## 1. Setting

`H` monic of degree `n`, critical points `c_1..c_{n-1}` with
multiplicity, `v` a TRACE-MAXIMAL critical value
(`Re v >= Re H(c_k)` for all `k`), `delta_k := v - H(c_k)` (so
`Re delta_k >= 0`, one of them `0`).  Parametrize the outward rightward
fibre `H(z) = v + t^n`, `t > 0`, with branches `z_j(t)` and inverse
speeds `q_j(t) = n t^{n-1} / H'(z_j(t))`.  The landed product identity
gives, pointwise,

```text
prod_{j=1}^n |q_j(t)| = prod_{k=1}^{n-1} t^n / |t^n + delta_k| <= 1,
```

with strict inequality as soon as some `delta_k != 0` (checker section
2: identity to `2.3e-14`, contraction on random low-mode quintics).

## 2. Theorem (integrated entropy sum rule)

For `Re delta >= 0`, `delta != 0`, and `n >= 2`:

```text
int_0^oo log|1 + delta / t^n| dt = (pi / sin(pi/n)) Re(delta^{1/n})
```

(principal root; checker section 3 verifies to `1.6e-21` including
purely imaginary `delta`).  Proof: differentiating under the integral,
`d/d delta int_0^oo Log(1 + delta/t^n) dt = int_0^oo dt/(t^n + delta)
= (pi/n) csc(pi/n) delta^{1/n - 1}` (the standard Beta evaluation,
analytic on the slit plane containing `{Re delta >= 0} \ {0}`);
integrate from `0` and take real parts.  Consequently, summing the
pointwise identity over the fibre and integrating:

```text
sum_{j=1}^n int_0^oo log|q_j(t)| dt
    = - (pi / sin(pi/n)) * Delta_n(H, v),
Delta_n(H, v) := sum_{k=1}^{n-1} Re (v - H(c_k))^{1/n}  >=  0.
```

`Delta_n` vanishes iff ALL critical values coincide with `v` — i.e.
exactly on the maximal-collision stratum.  (Checker section 4: the
integrated identity to `4.8e-12` on random quintics, fibre-summed.)

**Why this is (EX)-facing — with the same-day measured caveat.**  The
excess obligation of FRONTIER §4.3(a) (`e_i + e_j <= 0` for the
trace-max value-ray arms) is an `L^1` statement about TWO selected
sheets; the sum rule is the exact `L^1` log-budget of ALL `n` sheets,
strictly negative with the explicit magnitude
`(pi/sin(pi/n)) Delta_n`.  CAVEAT (measured,
`TraceMaxRadialExcessLaw.md`): on the quintic core a Delta_5-coercive
`(EX+)` holds numerically for the rightward arms only in the
sup-driven form `kappa = 0.017` (correlation `-0.64`), and is FALSE
for the radial arms; the binding invariant is the HUB MODULUS `|c*|`
(correlation `-0.99`).  So the sum rule's role is as the exact
all-sheet budget inside an allocation argument routed through `|c*|`,
not as a standalone coercive envelope.  What the sum rule does NOT do
by itself: allocate the negative budget to the two sheets born at the
hub (arithmetic vs geometric mean); that allocation is the remaining
mathematical step and is exactly where
`FixedBlockQuadraticBudgetEquivalence.md`'s moved-block average and
section 5's two-sheet quadratic bound aim.

## 3. The angular quadratic budget (equality form; credit §1.7)

For monic `P`, base point `w_0`, `A(t) := Area{|P - w_0| < t^n}`, and
fibres `P = w_0 + t^n e^{i theta}` with branches `z_j(t, theta)`:

```text
(1/2pi) int_0^{2pi} sum_j int_0^T (|d z_j/dt|^2 - 1) dt dtheta
    = (n/2pi) ( B(T)/T + int_0^T B(t)/t^2 dt ),      B := A - pi t^2,
```

and `B <= 0` by Pólya (`cap{|P - w_0| <= s} = s^{1/n}`), so the
right side is `<= 0`; letting `T -> oo` gives the global form
`(n/2pi) int_0^oo B/t^2 dt <= 0`.  Boundary terms vanish SHARPLY
(subagent-verified): Grönwall on the exterior map gives
`B(t) = -pi |c_2|^2 / t^2 + O(t^{-4})` with
`c_2 = (n-1) a_{n-1}^2/(2n^2) - a_{n-2}/n` (independent of `w_0`), and
`c_2 = 0` iff `P` is a pure n-th power — exactly the equality case
`I = 0`; the theta-averaged integrand decays like `n |c_2|^2 t^{-4}`.  Derivation: the change of variables
`A'(t) = n t^{2n-1} int sum_j |P'(z_j)|^{-2} dtheta` plus
`|d z_j/dt|^2 = n^2 t^{2n-2}/|P'(z_j)|^2` gives the per-level identity
`(1/2pi) int sum_j |dz_j/dt|^2 dtheta = n A'(t)/(2pi t)`; integrate by
parts.  This is the equality refinement of the `<= nR` action theorem
of `SixReturnJointAssimilation20260826.md` §1.7 (same inputs; the
inequality half is THEIRS).  Checker section 5 verifies the equality
two-sidedly (fibre sums vs Monte-Carlo area, `0.1%`-level agreement)
on random cubics/quartics.  The known obstruction of that lane is
unchanged: the two short sheets it selects need not lie in one safe
monodromy block.

## 4. Support–oscillation lemma (general arm, TV form)

Let `gamma` be unit-speed `C^1` from hub `h`, `gamma'(s) = u e^{i
theta(s)}` with `|theta| <= alpha < pi`, `gamma(S) = R(S) u + o(1)`,
`R -> oo`.  Then, with `Osc := min( int (sin theta)_+ ds,
int (sin theta)_- ds )` (zero iff the transverse motion is one-signed),

```text
e_u(gamma) = lim (S - R(S))
           <= tan(alpha/2) ( |Im(conj(u) h)| + 2 Osc ) - Re(conj(u) h).
```

Proof: `S - R(S) = int (1 - cos theta) ds - Re(conj(u) h) + o(1)`
(project the endpoint identity), `1 - cos theta = |sin theta|
tan(|theta|/2) <= tan(alpha/2)|sin theta|`, and
`int |sin theta| = |int sin theta| + 2 Osc` with
`int sin theta -> -Im(conj(u) h)`.  Adjacent-pair corollary: for tract
directions `u_pm = e^{i(phi +- delta)}` bracketing the hub
(`h = r e^{i(phi + psi)}`, `|psi| <= delta`), the two Im-terms sum to
`2 r sin delta cos psi` and the Re-terms to `2 r cos delta cos psi`, so
one-signed arms with `alpha <= pi - 2 delta` (i.e. `tan(alpha/2) <=
cot delta`) give `e_+ + e_- <= 0`; at `delta = pi/n` the admissible
turning is `pi - 2pi/n` (108° at `n = 5`).  SCOPE (from
`RayDirectionScopeLimit.md`): when the transverse motion is NOT
one-signed the `2 Osc` debt is real and a TV-only bound is measured
insufficient at 5/24 directions of the cusp model — this lemma prices
the debt, it does not waive it.  (Checker section 6.)

## 5. Two-sheet quadratic bound

For two branches with midpoint/difference `m, d`:
`|gamma_+'| + |gamma_-'| <= 2 sqrt(|m'|^2 + |d'|^2)` and
`2(sqrt X - 1) <= X - 1`, so the PAIR excess is controlled by the
quadratic (Dirichlet-type) energy `int (|m'|^2 + |d'|^2 - 1)` — the
bridge from section 3's quadratic budget to the `L^1` pair excess
(checker section 7).  The block-allocation step (which two sheets, on
which angular window) is the open part; see
`FixedBlockQuadraticBudgetEquivalence.md` for the landed equivalence
that the MOVED-block average is the right target.

## Claim boundary

Section 2's integral formula and sum rule are ordinary proved
mathematics (derivation above; 25-dps checker).  Section 3's equality is
proved but its lane (and inequality) is credited to
`SixReturnJointAssimilation20260826.md` §1.7 — no novelty claim there.
Sections 4–5 are elementary lemmas landed for reuse with their known
insufficiency scopes.  Nothing here proves (EX), allocates the entropy
budget to a specific sheet pair, or touches the parent theorem.
PRIORITY CAVEAT: no literature search; the entropy integral is
classical-flavoured (Mahler/Jensen adjacent); claim "new to this
directory" only.
