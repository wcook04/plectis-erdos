# Greedy complementarity does not by itself coerce zero flux

Status: exact algebra plus an adversarial greedy countermodel family. No Lean
claim is added. The aim is to test obstacle, quadratic-energy, and least-action
mechanisms against the homogeneous mode.

## 1. Exact obstacle law

Write `w_n = 1/(2^n-1)`, let `r_n` be a greedy residual after rank `n`, and
let `b_n` be its take bit. The checked decision and update laws are
`succ_mem_greedyMersenneSupport_iff`
([GreedyAchievementSet.lean:1270](../../Erdos257PeriodNoncollapse/GreedyAchievementSet.lean#L1270)) and
`greedyMersenneRemainder_succ`
([GreedyAchievementSet.lean:1038](../../Erdos257PeriodNoncollapse/GreedyAchievementSet.lean#L1038)):

```text
b_n = 1 iff w_n ≤ r_(n-1),    r_n = r_(n-1) - b_n w_n.
```

The genuine complementarity inequalities are one-sided,

```text
b_n(r_(n-1)-w_n) ≥ 0,    (1-b_n)(w_n-r_(n-1)) > 0,
```

not a zero-product KKT condition. Squaring the update gives the exact
nonlinear dissipation identity

```text
r_(n-1)^2-r_n^2 = b_n w_n^2 + 2b_n w_n r_n.              (A)
```

If `g = lim r_n`, summation gives

```text
r_0^2-g^2 = sum_(b_n=1) (w_n^2+2w_n r_n).                (B)
```

Every right-hand summand is nonnegative, and this uses the take decision,
not merely the linear carry equation.

## 2. Exact greedy positive-flux countermodel

Fix `M≥2`, write

```text
T_M = sum_(n≥M) w_n,
g_M = (w_(M-1)-T_M)/2 > 0,
x_M = T_M+g_M = (w_(M-1)+T_M)/2.
```

Strict superincreasingness, `mersenneTail_lt_weight`
([GreedyAchievementSet.lean:180](../../Erdos257PeriodNoncollapse/GreedyAchievementSet.lean#L180)), gives
`T_M < w_(M-1)`, so the greedy orbit for `x_M` skips below `M`. Induction then gives

```text
r_n = g_M + T_(n+1)  (n≥M),
```

and every rank `n≥M` is taken. Thus the cofinite Boolean support `{n:n≥M}`
is an exact greedy/complementary orbit with positive limiting residual `g_M`.
It satisfies (B) with `g_M`, not zero.

More generally, for any function `F` on nonnegative residuals, the complete
obstacle contribution telescopes:

```text
F(r_0)-F(r_N) = sum_(n≤N,b_n=1) [F(r_n+w_n)-F(r_n)].     (C)
```

No finite-energy proof formed only by summing a local take/skip potential can
therefore force the residual limit to vanish: this cofinite path closes at
`F(r_0)-F(g_M)`. This includes convex quadratic and entropy choices whenever
the terms are defined.

The countermodel changes the external target from `1/21` to `x_M`; it does
not refute a theorem that genuinely uses the period-six source. It proves the
needed separation: complementarity plus Booleanity plus Mersenne weights has
no standalone zero-flux content. A successful principle must be source-
sensitive and global, not a local obstacle inequality.

## 3. Carry energy retains the boundary

For the actual target, `twentyOneGreedyCarry_succ` and
`twentyOneGreedyCarry_zero`
([BooleanMobiusCarry.lean:1517](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L1517)) give, for `u_N=C_N/2^N`,

```text
u_N-u_(N+1) = 21 f_A(N+1)/2^(N+1) ≥ 0.                  (D)
```

Hence the square law is exactly

```text
u_0^2-u_N^2 = sum_(j=1..N) (u_(j-1)-u_j)(u_(j-1)+u_j).  (E)
```

If `u_N→lambda`, its right side is `u_0²-lambda²`; positive dissipation is
compatible with positive flux. The proposed time energy `sum_(n≤N)u_n²`
does grow as `lambda²N`, but (E) controls only an endpoint. Boolean
idempotence `X_n²=21X_n` is likewise pointwise zero after subtraction and
cannot pay for that time-energy term.

## 4. Adversarial exact computation

Rational arithmetic through rank 160 gives 70 takes for actual `1/21`; its
last 20 bits are `11001110110011010011`. For artificial targets
`x=(w_7+sum_(8≤n≤H)w_n)/2`, with `H=24,48,96`, exact greedy calculation
verifies the literal prefix `0^7 1^(H-7)` each time. These are finite
truncations of the cofinite positive-flux construction. No candidate local
square, entropy, or take/skip exchange inequality changes sign on either
family. This is a falsification receipt, not a proof by computation.

## 5. Consequence

The viable least-action theorem must compare Boolean supports with the same
period-six source while retaining divisor incidences, and establish a
source-sensitive global estimate such as `sum_(n≤N)(C_n/2^n)^2=o(N)`.
Nothing in greedy complementarity, carry monotonicity, Boolean idempotence,
or their single-site energies supplies it.
