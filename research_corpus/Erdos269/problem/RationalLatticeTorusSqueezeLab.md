# Erdős #269 — all-scale lattice reduction, and the retraction of the torus squeeze

Status: **reduction sharpened and Lean-landed; the claimed torus endgame is
RETRACTED as invalid.** No irrationality or transcendence claim is made here.
Support {2,3,5}. Companion Lean module:
`ErdosProblems.Erdos269.RationalLatticeReduction`. Checkers:
`scripts/check_erdos269_tail_orbit_separation.py`,
`scripts/check_erdos269_prime_power_boundary_ladder.py`.

## 0. Object

`H(s) = 2^⌊lg s⌋ 3^⌊log_3 s⌋ 5^⌊log_5 s⌋` (`threePrimeHeight 2 3 5`), shells
`A_a = {s = 2^i 3^j 5^k : 2^a ≤ s < 2^{a+1}}`, shell masses `m_a`, value

    S := Σ_{smooth s ≥ 2} 1/H(s) = T_1 ,   T_a := Σ_{n ≥ a} m_n .

Landed machinery: `X_{a+1} = b_a X_a − d_a` for `X_a := B_a·T_a`,
`B_a := H(2^a)/2`, radix `b_a = H(2^{a+1})/H(2^a) ∈ {2,6,10,30}`, digit
`d_a = (H(2^{a+1})/2)·m_a ∈ ℕ`, `d_a ≥ 1`, `X_1 = S`.
Numerically `S = 0.809319352389316…`.

## 1. RETRACTION — the torus squeeze of wave 2026-08-23 is invalid

The earlier version of this note claimed the endgame was solved: define, for a
phase `τ ∈ T²`, the reading series

    G_A(τ) := Σ_{j≥0} d_{A+j} / Π_{i≤j} b(T^i τ)

with digits frozen at the *absolute* indices `A+j` and radices read off the
rotation orbit, assert the "orbit realization" `G_A(τ_a) = X_a` for all `a`,
lift `q·G_A ∈ ℤ` to the whole torus by orbit density, and then contradict the
infinite range of `G_A` along a coordinate segment against a finite integer box.

**Step 2 of that chain is false.** `G_A(τ_a) = X_a` holds only when `a = A`.
For `a ≠ A` the series reads absolute-index digits against orbit-`a` radices,
and the digits are not phase functions at all: `d_n` grows like `n²`, while any
function on the compact torus is bounded. Exact-digit falsifier
(`check_erdos269_tail_orbit_separation.py`, digits validated against
big-integer brute force):

| a | X_a | G_1(τ_a) | defect |
|---|---|---|---|
| 1 | 0.809319352389316 | 0.809319352389316 | 0 |
| 2 | 0.855916114335898 | 0.538856461107848 | 0.317 |
| 3 | 1.55916114335898 | 0.731856356687118 | 0.827 |
| 10 | 13.5253797320243 | 2.15527172964513 | 11.37 |
| 40 | 154.762070287932 | 2.22749398244592 | 152.5 |

The structural reason, in covariance form: the functional equation needs
`Φ(Tθ) = b_0(θ)Φ(θ) − d_0`, whose right-hand side has numerator `d_{n+1}` at
depth `n`, whereas a frozen-digit `Φ(Tθ)` still starts at `d_0`. A phase shift
must move the *digit source* as well as the radix word. The three-prime digit
is a lattice count at the translated scale, so it cannot be frozen.

Consequence: §3 (ℤ-valued cocycle on the whole torus) and §4 Step D
(infinite range inside a finite lattice box) of the retracted note are void.
Steps A–C of the old §4 remain true statements *about `G_A` for fixed `A`*,
but they carry no information about `S`, because `q·G_A ∈ ℤ` was never
established off the diagonal. **Do not re-derive this route.** Any valid torus
argument must translate the complete source and either retain or rigorously
eliminate the non-compact scale variable.

Independently reached by two parallel Type B returns on the same day.

## 2. What is true, and now Lean-landed

**Divisibility.** For every smooth `s < 2^a`: `H(s) | H(2^a)/2`.
(`threePrimeHeight_smooth_dvd_heightNormalizer235`.)

**Prefix clearing.** `B_a · P_a ∈ ℤ` where `P_a := Σ_{i<a} m_i`.
(`heightNormalizer235_mul_windowMass_eq_int`.)

**All-scale lattice.** If `S = p/q` then for *every* `a ≥ 1`,
`q·X_a = p·B_a − q·(B_a P_a) ∈ ℤ`. Rationality places the entire orbit on one
fine lattice simultaneously; there is no "exceptional scale".
(`qsmul_normalizedTailState_eq_int_of_value_eq_rat`.)

**Boundary clearing at every prime power (new).** For `p ∈ {2,3,5}`, `m ≥ 1`
and every smooth `x < p^m`: `p·H(x) | H(p^m)`. Hence the same clearing holds at
*all three* prime-power boundary families, not only at powers of two, and
rationality forces `q·U_{p,m} ∈ ℤ` for `U_{p,m} := (H(p^m)/p)·T(p^m)`.
(`smoothHeight_mul_prime_dvd_boundaryHeight`; exact check: 1,134 (p,m,s)
triples, 0 failures.)

**The collision target (new).** If `S = p/q` then two *distinct* scales carry
tail states differing by an integer: pigeonhole on `(1/q)ℤ/ℤ`. Contrapositive:

> if the normalized tail states `X_a` are pairwise incongruent mod 1, `S` is
> irrational.

(`exists_normalizedTailState_collision_of_value_eq_rat`.) This is the correct
general-denominator target. The classical "exceptional integral state" branch
is the sub-case `X_a ≡ 0`; it can only ever reach `q = 1`, whereas the
collision statement covers every denominator at once. Equivalently
`X_{a'} − X_a ∈ ℤ ⟺ (B_{a'} − B_a)·S ∈ ℤ`, so a single collision *proves*
rationality — the criterion is an iff, not a one-way sufficient condition.

## 3. The boundary ladder (verified, not yet in Lean)

Order all powers of 2, 3, 5 as `r_1 < r_2 < …`, let `p_j` be the prime of `r_j`,
`C_j := #{s smooth : r_j ≤ s < r_{j+1}}`, and `U_j := (H(r_j)/p_j)·T(r_j)`. Then

    U_{j+1} = p_j U_j − C_j .

Verified: 200 consecutive ladder steps, 0 failures; and at dyadic boundaries the
ladder reproduces the dyadic states exactly (`U` at `2^5` = 5.64900580461722 =
`X_5`; at `2^20` = 26.7732560404321 = `X_20`). Two independent representations,
15-digit agreement.

Why this form is better: the multiplier is a **prime** in `{2,3,5}` rather than
a composite radix in `{2,6,10,30}`, and the digit `C_j` is an *unweighted*
lattice-point count in one inter-boundary gap rather than a `{1,3,5,15}`-weighted
count over a dyadic block. It is the most elementary form of the arithmetic that
must be attacked.

**Cocycle equivalence.** `S ∈ ℚ` iff there are `Q ≥ 1`, an index `J`, and a
polynomially bounded integer sequence `(n_j)_{j≥J}` with `n_{j+1} = p_j n_j − Q C_j`.
Forward: take `n_j = Q U_j`. Backward: a competing orbit differs by `w_{j+1} = p_j w_j`,
which grows at least like `2^{j−J}` unless `w_J = 0`, while both compared orbits
grow polynomially. So no spurious finite-window carry can masquerade as the
tail — any polynomially bounded integer cocycle *is* the genuine tail.

**Jump identity.** With `A(x) := #{s smooth : 2 ≤ s < x}`,

    S = Σ_{p∈{2,3,5}} Σ_{m≥1} (p−1)·A(p^m)/H(p^m),

the `A`-weighted refinement of the landed telescope
`Σ_p (p−1) Σ_m 1/H(p^m) = 1`. Exact finite form at a boundary `R`:
`Σ_{2≤s<R} 1/H(s) = Σ_{p^m≤R} (p−1)A(p^m)/H(p^m) + A(R)/H(R)`; verified exactly
at 29 boundaries below 20,000, 0 failures. This exhibits `S` as three
one-dimensional prime-power series whose coefficients are three-dimensional
irrational-simplex lattice counts — and shows directly why no one-slope
Hecke–Mahler theorem applies: two independent logarithmic ratios survive in
each component.

## 4. Two-sided state bounds, and a negative measurement

Upper (rigorous, all starts): `N_n ≤ (n+2)²` and `H_a/H(s) ≤ 2^{−r}` on shell
`a+r` give `0 < X_a ≤ a² + 6a + 11`.

Lower (rigorous, all starts): every `(j,k)` with `j·log₂3 ≤ a/2` and
`k·log₂5 ≤ a/2` contributes one shell point, so

    X_a ≥ (1/60)·(⌊a/(2log₂3)⌋+1)·(⌊a/(2log₂5)⌋+1) = Ω(a²).

So `X_a` is genuinely unbounded and approximately quadratic. This is what kills
bounded-carry and fixed-finite-automaton arguments *cofinally*, and it is the
precise reason the local "zero-gap kill" step is wrong: `X_a ∈ ℤ` is equivalent
to `b_a | X_{a+1}`, not to `X_{a+1} = 0`, and `X_{a+1} < b_a` fails for all
large `a`. (That step was already repaired in-tree as
`zero_gap_digit_separation`, a quantitative separation `z ≥ anchor + 1`.)

**Negative measurement — the two-sided annulus buys nothing.** Combining the
bounds, an integral start forces the log-window residue
`ρ_{a,L} = (−E_{a,L}) mod Q_{a,L}` into `[lower(a+L), upper(a+L)]` rather than
merely below `upper`. Measured over 120 starts at the minimal window with
`Q > upper`: 77 excluded by the one-sided test, **0 additional starts excluded
by the lower bound**, 43 inconclusive. The lower bound is a factor ≈ 37 below
the upper one, so it trims a negligible slice of an already-thin target. Do not
invest in the two-sided form expecting an exclusion gain.

## 5. Mod-1 statistics of the tail orbit

Over `a ≤ 1200` (digits exact, truncation bound ≈ 1e−47):

* all 1200 fractional parts `{X_a}` are pairwise distinct; min gap 8.834e−07 at
  `(a,a') = (830, 979)`; hence any rational `S` has denominator `q ≥ 1.1e6`;
* min distance to ℤ is 9.697e−04 at `a = 545`, decaying like `≈ 1/a`;
* 20-bin χ² = 8.0 on 19 df, and `|Weyl(h)| = 0.0139, 0.0074, 0.0114` for
  `h = 1,2,3` against `1/√N = 0.0289` — i.e. *better* than square-root
  cancellation.

`{X_a}` therefore behaves like a low-discrepancy equidistributed sequence.
Since equidistribution mod 1 implies infinitely many distinct values, it implies
irrationality by §2 — so **equidistribution of `{X_a}` mod 1 is now a sufficient
target**, and it is consistent with the landed genericity results (irrationality
exponent 2.005, Gauss–Kuzmin partial quotients). It is not a proof: proving
equidistribution requires an `o(1)` handle on `X_a mod 1`, and the smooth-count
error terms in the natural asymptotic `X_a ≈ κ a² g(τ_a)` are of size `Θ(a)`.

Note the certificate ceiling is unchanged: the landed Farey/first-hit lane
already excludes denominators below ≈1.64e90 and has 13,109 certified partial
quotients; the separation bound above is far weaker and is reported only as an
independent cross-check of the orbit computation.

## 5a. The correct torus object — fiber decomposition (new, verified)

§1 retracts a torus argument. There *is* a genuine torus object here; the
retracted note simply had the wrong one. Group the smooth numbers by **odd
part**: the fiber of `w = 3^j 5^k` is `{2^i w : i ≥ 0}`. Doubling multiplies `H`
by `b ∈ {2,6,10,30}`, and **along a fiber every Cantor digit is 1**. So

    (F1)  S + 1 = Σ_{j,k≥0} T_{j,k},   T_{j,k} = Σ_{i≥0} 1/H(2^i w).

Each `T_{j,k}` is an all-ones Cantor series with bounded radices, hence
**irrational** by the companion theorem (`PurePowerIrrationality.lean`); the
`(0,0)` fiber is exactly `1 + Σ₂ = 1.5931259677635827…`. So `S` is a lattice sum
of irrational fiber values.

    (F2)  H(w)·T_{j,k} = Φ(θ_{j,k})    for ONE bounded Φ : T² → [1.0395, 1.5932],
          θ_{j,k} = ({k·log₃5}, {j·log₅3}).

The phase **factorises**: the 3-coordinate depends only on `k`, the 5-coordinate
only on `j`. Measured: 196 fibers, `max |ΔΦ|/|Δθ| = 1.394` on close pairs — `Φ`
is a genuine, Lipschitz-scale function of the phase, not a scale-dependent
family.

    (F3)  b(s)·Φ(s) = b(s) + Φ(2s).

This is exactly the covariance the retracted argument wanted, and here it
**holds** — max defect 7.8e−15, machine epsilon. It holds for `Φ` and fails for
the dyadic state for one reason only: fiber digits are constant, dyadic-shell
digits are lattice counts growing like `n²`.

    (F4)  X_a = ½[ Σ_{s∈A_a} Φ(s)/u_s  +  Σ_{w odd-smooth, w ≥ 2^{a+1}} H(2^a)Φ(w)/H(w) ],
          u_s = H(s)/H(2^a) ∈ {1,3,5,15}.

The dyadic tail state is a weighted average of one fixed torus function over the
shell, plus a correction from fibers whose odd part already lies above the shell.
Verified to `≤ 4e−14` relative at `a = 3,…,32`. **The correction is not
optional**: dropping it is a 0.6–2.2% error (my first derivation omitted it and
was wrong by exactly that). This identity is also the structural explanation of
`X_a = Θ(a²)`: `|A_a| = Θ(a²)` terms, each of size `Θ(1)` because `Φ` is bounded
below by 1.

Checker: `scripts/check_erdos269_fiber_torus_decomposition.py`.

## 5b. How far the separation reaches — partial fiber sums, and the exact wall

The separation argument does **not** stop at one fiber. For a finite fiber set
`F`, write `G_a` for the shell digit of `S_F = Σ_{w∈F} T_w`. Then

    Y_a := B_a·(tail of S_F above 2^a) = (1/b_a)·Σ_{i∈F} g_i(a)·Φ(s_i(a)),
    g_i(a) = b_a/(2u_i(a)) ∈ {1,3,5,15},   G_a = Σ_i g_i(a),

so `Y_a ∈ (1/b_a)·[m·G_a, M·G_a]` where `[m,M] = [1.0395, 1.5932]` is the range
of `Φ`. Two states with the same radix letter and digits `G ≠ G′` are therefore
**separated** as soon as

    max(G,G′)/min(G,G′) > M/m = 1.5326.

A right-special factor of the finite word `W_a = (b_a, G_a)` with such a pair of
same-radix extensions then gives `0 < |Y_a − Y_{a′}| ≤ C·2^{−L}`, and since
`Y_a = B_a·S_F − (integer)`, `S_F` is irrational.

Measured (`--fiber-counts`, 900 scales, window search to L = 25):

| fibers | alphabet | window | radix | digits | ratio | irrational by this argument |
|---|---|---|---|---|---|---|
| 2 | 9 | 1 | 10 | 6, 10 | 1.667 | yes |
| 3 | 15 | 1 | 10 | 7, 11 | 1.571 | yes |
| 5 | 31 | 1 | 10 | 13, 21 | 1.615 | yes |
| 8 | 57 | 1 | 10 | 16, 36 | 2.250 | yes |
| 13 | 90 | 1 | 10 | 29, 53 | 1.828 | yes |
| 21 | 136 | 1 | 10 | 49, 77 | 1.571 | yes |
| 34 | 196 | 1 | 10 | 74, 114 | 1.541 | yes |

So **every partial fiber sum tested is unconditionally irrational**, and `S` is
the limit of exactly these. (`|F| = 1` is not covered by this dyadic-frame test
— the single fiber has too small a digit alphabet — but is covered by the other
route, which reads the fiber's own all-ones radix word.)

**The wall, quantified.** The required ratio is fixed at `M/m = 1.5326` while the
observed best ratio drifts down as `F` grows: `1.667 → 1.541` by 34 fibers. The
digit sums `G_a` concentrate as more fibers are added, so the separation margin
is being consumed. That is the precise sense in which the argument approaches
`S` and cannot reach it: not a missing idea, but a ratio crossing a threshold.
Two ways to push the wall back, both open: narrow `[m,M]` by conditioning `Φ` on
the shell phase rather than using its global range, or find same-radix
right-special extensions at larger `L` with a better ratio than the first hit.

**What this does and does not buy.** It gives the corpus a correct torus cocycle,
proves every fiber value irrational, proves every tested partial fiber sum
irrational, and recasts `S` as `Σ_{j,k} Φ(θ_{j,k})/H(3^j5^k)`. It does not prove
`S` irrational: the argument needs a finite alphabet, and the full sum's shell
digits grow like `a²`.

## 5c. The digit word — the measurement `TorusCocycleAndDiophantineTypeLab.md` did not take

That lab proves the **radix** word `(b_a)` is a rank-2 torus coding with factor
complexity **exactly `p_b(n) = (n+1)²`** for `n = 1…22`, and correctly concludes
that the Adamczewski–Bugeaud stammering lane is closed: the word is too regular.
It measured the radix word. The **digit** word was never measured, and it is the
object whose complexity is unconstrained.

Criterion (§2's collision target in complexity form). A length-`n` window of the
joint word `W = (b_a, ε_a)`, `ε_a = ⌊b_a·{X_a}⌋`, is a function of
`({X_a}, b_a,…,b_{a+n-1})`. Under `S = p/q` the fractional part takes at most `q`
values, so

    p_W(n) ≤ q·p_b(n) = q·(n+1)²   for every n,

hence **`q ≥ p_W(n)/(n+1)²`**, and **if `p_W(n)/(n+1)²` is unbounded then `S` is
irrational.**

Measured (`probes/erdos269_digit_word_complexity.py`, literal source word via the
lab's own fast engine, `a ≤ 60,000`, `θ` by exact rational truncation at depth 26
— truncation error 1.7e−14 against letter slack 3.5e−08, so the letters are exact):

| n | p_b = (n+1)² | p_W (digit word) | ratio | q ≥ | saturated |
|---|---|---|---|---|---|
| 1 | 4 | 48 | 12.0 | 12 | no |
| 2 | 9 | 660 | 73.3 | 73 | no |
| 3 | 16 | 9,233 | 577.1 | 577 | no |
| 4 | 25 | 41,881 | 1675.2 | 1675 | no |
| 5 | 36 | 57,523 | — | — | yes (sample cap) |

`p_b(n) = (n+1)²` is reproduced exactly at every `n`, independently confirming the
lab. The digit word grows by factors **13.75, 13.99** before saturating at the
sample size — i.e. like `≈14ⁿ`, not like `n²`.

**What this changes.** The stammering closure is a statement about `p_b`. It says
nothing about `p_W`, and `p_W` is the word the criterion actually constrains. The
proof obligation is now a single sharp inequality on an explicitly computable
word: show `p_W(n)/(n+1)² → ∞`. Equivalently — since `p_W(n)/p_b(n)` is the
average number of distinct `{X_a}` values per depth-`n` radix cylinder — show
that unboundedly many tail states share a radix cylinder.

### The cell ceiling — the missing inequality in exactly checkable form

Inside a radix cylinder `u = (b_a,…,b_{a+n-1})` the map `θ_a ↦ θ_{a+n}` is
`x ↦ {∏u · x}`, and the `ε`-window names **which of the `∏u` equal cells** `θ_a`
occupies. So `∏u` is an exact per-cylinder ceiling, and

    p_W(n) ≤ Σ_{u ∈ L_b(n)} ∏u,

with equality exactly when the `θ`-orbit visits **every cell of every radix
cylinder**. Measured (`a ≤ 80,000`, θ by exact rational truncation at depth 27,
error 5.1e−15 against letter slack 3.5e−08):

| n | p_b | cell ceiling | p_W measured | hit fraction | sample-limited |
|---|---|---|---|---|---|
| 1 | 4 | 48 | **48** | **1.000000** | no |
| 2 | 9 | 660 | **660** | **1.000000** | no |
| 3 | 16 | 9,600 | 9,454 | 0.984792 | yes |
| 4 | 25 | 110,160 | 50,854 | 0.461638 | yes |

At `n = 1` the ceiling is `2+6+10+30 = 48` and it is attained **exactly**; at
`n = 2` the ceiling `660` is attained **exactly**. `n = 3` reaches 98.5% with
only 5,000 scales per cylinder against cells numbering up to `30³ = 27,000`, and
`n = 4` is straightforwardly sample-starved — both are resolution limits, not
gaps in the orbit.

**Why this is the whole problem.** If the ceiling is attained then
`p_W(n)/(n+1)² = ` average of `∏u ≥ 2ⁿ → ∞`, and the collision criterion of §2
makes `S` irrational. So the open obligation now reads:

> the proper-digit word attains its cell ceiling — equivalently, the normalized
> tail orbit `{X_a}` visits every cell of every radix cylinder.

That is a covering statement about an explicitly computable orbit, exactly
verified at every depth the sample resolves, and **strictly weaker than
equidistribution**: superquadratic growth of `p_W` suffices, full saturation is
not needed. It is the same analytic input the escape and projective branches
reduce to, now stated as a covering property rather than as anti-concentration.

**Claim boundary.** `p_W` is measured, not bounded below; this is not a proof.
The finite denominator bound `q ≥ 2034` from this lane is far weaker than the
landed Farey lane (≈1.64e90) and the certified continued fraction (≈1e6768), and
than the all-denominator collision certificate below; it is reported because the
mechanism is different, not because the number is large.

### All-denominator collision certificate

`probes/erdos269_collision_certificate.py`, 200,000 scales, θ by exact rational
truncation at depth 26 (error 1.7e−13): all 200,000 fractional parts pairwise
distinct, minimum gap **3.7153e−12** at `(a,a′) = (199108, 36830)` — 21.7× the
truncation error, so distinctness is certified. Since distinct `θ` are `≥ 1/q`
apart under rationality,

    q ≥ 2.46 × 10¹¹,  for EVERY denominator.

This is the first certificate attached to the covering obligation rather than to
the `Q = 1` fibre: the window-residue rigidity machine of
`DyadicWindowComputationalLab.md` refutes first indices `A ≤ 6000` on the
integral branch only, and that lab's own 2026-08-23 correction records that the
branch is just the `Q = 1` case.

## 5d. Why the fiber proof cannot transfer — a structural no-go in the finest frame

The fiber theorem needs three things: constant Cantor digits, a bounded tail
state, and right-special factors with separated extensions. `S` has the first.
It provably lacks the other two, and the cleanest place to see that is the finest
possible reindexing.

Enumerate the smooth numbers `s_1 < s_2 < …` (`s_n ≥ 2`) and set
`r_n = H(s_n)/H(s_{n−1})`, `H(s_0) = H(1) = 1`. The height jumps **only** at prime
powers, so `r_n = p` when `s_n = p^k` and `r_n = 1` otherwise, giving

    S = Σ_{n≥1} 1/(r_1 r_2 ⋯ r_n),     r_n ∈ {1,2,3,5}.

Verified **exactly in ℚ** against the height sum (130,901 smooth numbers below
`2^140`; 99.78% of letters are `1`). So `S` *is* an all-ones Cantor series over a
four-letter alphabet, and the entire problem is carried by the single word `(r_n)`.

**(i) The states are unbounded.** `V_n = Σ_{k≥0} 1/(r_n⋯r_{n+k}) ≥` the length of
the run of `1`s starting at `n`, and those runs are the counts of smooth numbers
between consecutive prime powers — which grow like `a²`. Measured: 280 runs,
**max 2,698**, last five `2371, 289, 2698, 861, 438`. Interval confinement
`V ∈ (1/r, 2/r)` is therefore unavailable.

**(ii) No usable repeated factor.** Shrinking a gap needs a repeated factor whose
radix product `P` is large, and `P` only grows across prime-power letters, so the
factor must span several full runs. Those never repeat:

| full runs spanned | positions | distinct patterns | repeats |
|---|---|---|---|
| 1 | 285 | 224 | 61 |
| 2 | 284 | 282 | 2 |
| 3 | 283 | 283 | **0** |
| 4 | 282 | 282 | **0** |

Run lengths grow, so gap patterns are eventually all distinct — no right-special
separation exists at any depth where `P` is large enough to matter.

**The conclusion worth keeping.** Checked in three independent frames — dyadic
shells (digits `≍ a²`), the prime-power ladder (gap counts `C_j ≍ a²`), and this
finest enumeration (runs `≍ a²`) — the same unboundedness appears, and it traces
to one thing: **the smooth counting function grows**. The obstruction to #269 is
not a missing technique. The fibers are exactly the sub-objects with one point per
dyadic scale, which is why the theorem reaches them and stops there.

Probe: `probes/erdos269_all_ones_frame_nogo.py`.

## 6. Retired attacks — do not redo

1. **Frozen-digit torus squeeze** (this note, §1). Invalid covariance.
2. **Continuity squeeze / oscillation decay.** `G_A` jumps at the Beatty walls by
   factor-3/5 tail rescalings; measured grid oscillation grows like poly(A)
   (8.5 at A=3, 359 at A=20). No small global modulus; `ω_A` does not tend to 0.
3. **Prefix-matching constancy.** Equality only within cells; across shallow
   walls the jump is `O(q·poly)`, never `< 1/2`.
4. **Segment walk with summable wall jumps.** Any long path crosses the shallow
   walls `V₀/W₀`, whose cost is `O(q·poly(A))`; total variation too lossy.
5. **Max/min recursion.** Yields only weak inequalities; positivity does not
   collide with them.
6. **Mod-r ratchet.** Pointwise divisibility does not upgrade across scales;
   quotients lose the modulus.
7. **Haar integration of FE.** One scalar recurrence among means; consistent with
   everything.
8. **de Bruijn chain on the word language.** Needs bounded hitting times of
   cylinders, i.e. an effective Diophantine lower bound for the clustering of
   `{i·log₃2}` that is not available.
9. **Gottschalk–Hedlund shape.** The FE is multiplicative; logs break
   integrality.
10. **Two-sided residue annulus.** Measured gain zero (§4).

## 7. Claim ceiling

No three-prime irrationality or transcendence theorem is proved. What is proved
and Lean-checked here: the all-scale rational lattice, prime-power boundary
clearing in the division-free form `p·H(x) | H(p^m)`, and the collision target.
What is verified computationally but not formalized: the jump identity, the
boundary-ladder recurrence and its cocycle equivalence, the two-sided state
bounds, and the mod-1 statistics. The surviving proof obligation is
anti-concentration: exclude every collision `X_{a'} − X_a ∈ ℤ`, equivalently
prove that the source residues avoid the permitted quadratic band cofinally, for
every denominator — not more finite exclusions.
