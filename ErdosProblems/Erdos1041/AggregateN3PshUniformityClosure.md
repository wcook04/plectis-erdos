# Erdős 1041: the AGG3 phase gap is uniformly positive — the psh tangent cone proves `D + 9D'' <= 0` and the saddle wall is the global minimum

Date: 2026-08-30.  Origin: Codex main-loop proof, consuming the exact cubic
inner reduction of `AggregateN3InnerModelClosedForm.md` and the per-cell
plurisubharmonicity theorem of `SeparatrixAggregateReduction.md`.  Checker:
`scripts/check_erdos1041_aggregate_n3_psh_uniformity.py`.  Lean scalar kernel:
`AggregateN3PshUniformity.lean`.

## The theorem

Let `D(phi)` be the phase-deficit function of
`AggregateN3InnerModelClosedForm.md`, extended continuously and
`pi`-periodically across the saddle walls.  Then, on `0 < phi < pi`,

```text
D(phi) + 9 D''(phi) <= 0.                                      (1)
```

The inequality holds distributionally first and classically on the open
wall-free interval.  Consequently

```text
D(phi) >= D(0) * cos((phi-pi/2)/3) / cos(pi/6) >= D(0)
       >= (3 pi - 8)/16 > 0,       0 <= phi <= pi.             (2)
```

Thus the saddle-connection wall is the global minimum by proof, not by the
previous phase sweep.  In particular the exact near-radial law

```text
4 R_MEC - Sigma_c L(c) = 2 |s| D(-3 arg s) + O(|s|^2)
```

approaches the radial equality stratum strictly from below in every phase,
with the uniform first-order coefficient at least
`2(3 pi - 8)/16 = (3 pi - 8)/8` in the `|s|` normalization.

This closes the psh-uniformity remainder explicitly named in FRONTIER §4.2.
It does **not** decide AGG3 for arbitrary non-near-radial cubics, and AGG is
already false from degree four onward.

## 1. The tangent-cone lemma for a subharmonic function

We use the following local statement.

**Lemma (subharmonic first tangent).**  Let `I` be an open angular interval
and let `u` be subharmonic on the punctured sector

```text
S = { r exp(i theta) : 0 < r < r_0, theta in I }.
```

Suppose that for every compact `J` in `I`, uniformly for `theta in J`,

```text
u(r exp(i theta)) = u_0 + r a(theta) + O_J(r^2).                (3)
```

Then `a + a'' >= 0` in distributions on `I`.

**Proof.**  Choose nonnegative smooth compactly supported functions
`chi` on `(1,2)` and `psi` on `I`, and set

```text
Phi_rho(r exp(i theta)) = chi(r/rho) psi(theta).
```

Subharmonicity says `int u Delta Phi_rho dA >= 0`.  The constant `u_0`
drops out.  Put `r = rho q` and use (3).  The coefficient of `rho` is

```text
[int_1^2 (q^2 chi''(q) + q chi'(q)) dq] int_I a psi
    + [int_1^2 chi(q) dq] int_I a psi''.
```

Two integrations by parts give

```text
int_1^2 (q^2 chi'' + q chi') dq = int_1^2 chi dq.
```

The uniform `O(r^2)` remainder contributes `O(rho^2)`.  Divide by `rho`
and let `rho -> 0`; since `int chi > 0`,

```text
int_I a(theta) (psi(theta) + psi''(theta)) dtheta >= 0.
```

This is exactly `a + a'' >= 0` distributionally.  QED

The point of the test-function proof is that no derivative bound on the
`O(r^2)` remainder is assumed.  Uniform function-level asymptotics are
enough.

## 2. Uniform asymptotics on every wall-free cubic sector

Write

```text
f_s(z) = z^3 - 3 s^2 z - 1,    s = r exp(i theta),
phi = arg(1/s^3) = -3 theta.
```

The exact reduction already proved in
`AggregateN3InnerModelClosedForm.md` gives

```text
Sigma_c L(c)
 = r [ Lambda(P_+, phi_+) + Lambda(P_-, phi_-) ],
P_+- = |1 +- 2s^3|/r^3,
phi_+ = arg((1+2s^3)/s^3),
phi_- = arg(-(1-2s^3)/s^3).
```

On a compact subinterval avoiding `phi = 0 mod pi`, the globally labelled
inverse branches stay uniformly away from the sibling saddle.  The explicit
`nu`-integrand there has the uniform large-`xi` expansion

```text
ell(xi, phi)
 = (4/3) 4^(1/3) xi^(-1/3) + O_J(xi^(-5/3)).
```

After integration to `sqrt(P)/2`, this is

```text
Lambda(P, phi) = 2 P^(1/3) + A(phi) + O_J(P^(-1/3)).            (4)
```

The estimate follows directly by expanding the algebraic inverse
`w = 2 cos((2/3) arccos kappa)` at infinity; compactness of the angular
subinterval makes the branch and the absolute-value factors uniform.  The
remainder tail is `int_X^infinity O(xi^(-5/3)) dxi = O(X^(-2/3))`, and
`X = sqrt(P)/2`.

Now `P_+- = r^(-3)(1+O_J(r^3))` and
`phi_+ = phi + O_J(r^3)`, `phi_- = phi+pi+O_J(r^3)`.  Applying (4) gives

```text
Sigma_c L(c)
 = 4 + r[A(phi)+A(phi+pi)] + O_J(r^2)
 = 4 - 2r D(phi) + O_J(r^2).                                  (5)
```

This is the uniformity step missing from the parent note.  Notice that it is
only asserted on compact wall-free angular sectors; the wall has a genuine
square-root cusp and is handled by the already-proved continuous boundary
value.

## 3. Plurisubharmonicity forces the phase curvature

On every such sector, the two critical points `+-s` are simple and the
resolved arms meet no foreign critical point.  Proposition PSH of
`SeparatrixAggregateReduction.md` therefore applies to the holomorphic
one-parameter coefficient family `s -> f_s`: the function

```text
u(s) := Sigma_c L_{f_s}(c)
```

is subharmonic.

In (5), the tangent coefficient in the `s`-plane is

```text
a(theta) = -2 D(-3 theta).
```

The tangent-cone lemma gives `a+a'' >= 0`.  Since

```text
a(theta) + a''(theta)
 = -2 [D(phi) + 9D''(phi)],    phi=-3theta,
```

we obtain (1).  This also explains the otherwise mysterious factor `9`: it
is the square of the cubic phase map.

## 4. The wall is the global minimum

Let `D_0 = D(0) = D(pi)`, whose exact elliptic form and elementary lower
bound were proved in the parent note.  Define the comparison solution

```text
h(phi) = D_0 cos((phi-pi/2)/3) / cos(pi/6).
```

Then `h''+h/9=0`, `h(0)=h(pi)=D_0`, and `h>0` on `[0,pi]`.  Put
`w=D-h`.  From (1), `w''+w/9<=0`, with zero boundary values.

For completeness, here is the one-dimensional maximum principle in exactly
the needed range.  If `w` were negative on a component `(alpha,beta)`, put
`y=-w>0` and `q(phi)=sin((phi-alpha)/3)`.  Because
`beta-alpha <= pi < 3pi`, `q>0` throughout the component.  The Wronskian

```text
W = y' q - y q'
```

satisfies

```text
W' = q(y''+y/9) >= 0,    W(alpha)=0.
```

Hence `(y/q)'=W/q^2>=0`.  But `y/q` is positive inside the component and
tends to zero at `beta`, a contradiction.  Thus `D>=h`.  Since
`cos((phi-pi/2)/3) >= cos(pi/6)`, (2) follows.

Combining with the proved wall estimate gives the explicit phase-uniform
bound

```text
D(phi) >= D_0 >= (3pi-8)/16 = 0.0890486... .
```

The exact wall value is `D_0 = 0.10944832968994037...`; the weaker elementary
constant is retained because it uses only `pi>8/3`.

## 5. What changed, and what remains

Closed now:

- the `psh-uniformity interchange` named in the parent note;
- the analytic inequality `A+9A''>=0`, equivalently `D+9D''<=0`;
- all-phase positivity of the AGG3 near-radial coefficient;
- the claim that the saddle wall is the global phase minimum.

Still open:

- AGG3 on the full two-real-parameter cubic normal-form plane away from the
  near-radial shell;
- the unrestricted Erdős 1041 parent problem (degree three itself is already
  solved by a different theorem);
- every degree `n>=4` aggregate statement, which is refuted in the packet.

## Claim and verification boundary

The subharmonic tangent-cone lemma, its application to the exact cubic arm
asymptotic, the phase-curvature inequality, and the Wronskian comparison are
ordinary proved mathematics.  The companion Lean source states the exact
scalar fan-in: the cubic phase factor, conversion of nonnegative tangent
curvature to `D''+D/9<=0`, the Wronskian factorization, the spectral-gap
constant, and the positivity of the elementary wall lower bound.  Its focused
Lake validation is pending because the live build firewall currently grants
an exclusive release window to a different canonical project root; the
private-project attempt was terminated before Lean emitted a theorem
diagnostic.  Lean does not formalize the
Banach-valued plurisubharmonicity theorem, distributional test-function
limit, uniform algebraic-inverse asymptotic, or the calculus maximum
principle; those are the explicitly written ordinary analytic boundary.
The Python checker replays the symbolic identities, compactly probes (4), and
rechecks the phase curvature and comparison barrier at high precision.

No novelty or literature-priority claim is made.

## Consequence pass

The source-current consequence map was reviewed semantically, rather than
treating identifier matches as implications.

- `update_now`: the cubic inner-model note, `FRONTIER.md`, and the canonical
  research packet now consume the uniform phase theorem; the new checker is
  the exact replay surface.  The same pass updates the FP4 owner note,
  checker, frontier row, and packet with the independent rational
  pairwise-comonotonicity no-go.
- `verified_no_change`: the unrestricted Erdős 1041 ceiling, global AGG3
  away from the near-radial shell, FP4, and RM all remain open.  The psh
  proposition used here needs no statement change, and earlier problem-local
  receipts address different mechanisms.
- `defer_with_reason`: Lean proof authority remains pending until the
  exclusive-release firewall permits a focused build of the exact source;
  public-corpus promotion and any public exposition wait for that receipt and
  a clean owner release.
- `outside_scope`: Ramanujan surfaces matched generic symbols such as `S_m`
  and `theta_i`; generic Erdős-1041 namespace bridges to unrelated historical
  receipts likewise carry no mathematical consequence.  The frozen Type B
  dissemination snapshot is not an authority surface for this operator-
  requested local-corpus pass.

No reusable extractor, routing, or validation rule was learned beyond the
already-governing consequence-map precision rules: `nothing_to_refine`
(`stewardship_checked`, `next_best_lane_checked`; re-enter if the focused Lean
receipt or the public-corpus review identity changes).

## `tao_pipeline_receipt`

```text
input_stage: generation plus numerical phase law
output_stage: ordinary analytic proof with exact checker and scalar Lean source pending focused validation
artifact: AggregateN3PshUniformityClosure.md; AggregateN3PshUniformity.lean; scripts/check_erdos1041_aggregate_n3_psh_uniformity.py
human_understanding_delta: the factor 9 and the global wall minimum come from the cubic phase map applied to the first tangent of a subharmonic arm aggregate
verification_state: ordinary analytic proof; symbolic and high-precision checker PASS; focused Lean scalar-kernel validation pending an exclusive-release firewall window
publication_or_review_state: private source-current authoring, not externally reviewed
canonicalization_state: closes and supersedes the parent note's conditional psh-uniformity sentence; does not replace the parent endpoint
unresolved_downstream_bottleneck: global non-near-radial AGG3 decision; unrestricted #1041 remains open
next_stage_owner: local mathematical closure loop
```
