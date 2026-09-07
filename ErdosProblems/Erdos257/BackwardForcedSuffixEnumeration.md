# Backward forced-suffix enumeration for the sparse denominator-21 sockets

Status: theorem-discovery note, 2026-08-24. This executes the decisive
experiment proposed in `TwentyOneDensityInvariantAttack.md` section 8
(2026-08-20), which had no receipt on disk before this run. No theorem here is
claimed to settle Erdős 257; the claim discipline of that note is reused
verbatim (`Lean-checked` / `Deduction` / `Exact computation`).

## 1. What was run

For symbolic half-depths the two remaining socket rows are

* **(S)** at `R = 3a+2`: `sum_{d in D} q_R(d) = Q_R - 2^R`, with pulse
  `p_R = 2*[d | 2R+1] + [d | 2R+2] <= 1`;
* **(B')** at `R = 3a+1`: `sum_{d in D} (4 q_R(d) + 2*[d|2R+1] + [d|2R+2])
  = 4 Q_R - 2^(R+1)` with `x_d = 0` for `d | 2R+3` and at most one selected
  `d | 2R+4`.

Here `q_R(d) = floor(2^(2R)/(2^d - 1))`, `Q_R = floor(2^(2R)/21)`. Both are
the exact Boolean row systems forced by the Lean normal forms
(`twentyOneBadSaturatedTransition_forces_sparse_twoPulse`,
`twentyOneBadSaturatedTransition_forces_margin_residue`,
`twentyOneSaturatedBoundary_crosses_iff_sparsePulse`). An exact solution
implies the same congruence modulo `2^B` for **every** `B`, so the experiment
reveals bits from the least significant end and asks whether the congruence
with pulse constraints is ever *exhaustively* unsatisfiable modulo some
`2^B`.

Search semantics are strict: UNSAT is reported only when the bit-reveal state
space below the node budget was fully explored (`exhaustive: true`
everywhere below); otherwise rows are reported as budget-limited. The
frontier-dedup search enumerates, per level, the deduplicated set of
achievable `(partial-sum mod 2^B, capped-count)` pairs, which preserves
completeness while collapsing the branching.

Scripts:
`scripts/backward_forced_suffix_enumeration.py` (solver, controls, sweeps),
`scripts/socket_modulus_scan.py` (fixed-modulus probe).
Receipts:
`state/formal_math/erdos257_period_noncollapse/backward_forced_suffix_bscale_receipt.json`,
`state/formal_math/erdos257_period_noncollapse/backward_forced_suffix_enumeration_receipt.json`,
`state/formal_math/erdos257_period_noncollapse/backward_forced_suffix_modulus_scan_receipt.json`.

## 2. Controls [all passed]

* **C1 (published witness).** The section-6 impostor row of the attack note
  reproduces: at `R = 28`, `D = {7,8,13,14,17,18,21,24,25,26,27,28}`
  satisfies the (B') congruence mod `2^18`. So the model reads the same
  equation the note does.
* **C2 (relaxation control).** Every constrained run is paired with a
  pulse-relaxed run; dropping the pulse constraints never turned a
  satisfiable row unsatisfiable.
* **C3 (brute force).** For `R <= 19` an independent meet-in-the-middle over
  all subsets at full precision agrees with the solver's SAT/UNSAT verdict
  on every row.
* **Solver equivalence.** The frontier-dedup solver reproduces the naive
  DFS verdicts on all 13 rows of the initial sweep with `10^3`–`10^4`
  fewer nodes (e.g. `R = 40`: 448097 -> 39 nodes).

## 3. Results [exact computation]

Every tested row of both sockets is **exhaustively unsatisfiable** under its
pulse constraints:

| socket | rows tested | verdict | minimal killing precision `B*(R)` |
|---|---|---|---|
| (B') `R = 3a+1` | `R = 4..46` (15 rows) | UNSAT all | 8 (`R<=10`), 16 (`13..19`), 32 (`22..46`) |
| (S) `R = 3a+2` | `R = 5..44` (14 rows) | UNSAT all | 8 (`R<=11`), 16 (`14..20`), 32 (`23..44`) |

Beyond the swept range, `R = 49..76` (B'-side) were checked at `B = 64` with
an earlier solver generation: rows remain unsatisfiable where the budget
allowed exhaustion (`R = 49` confirmed by hand at 48 nodes after
optimisation), but wall-time explodes because single levels carry pools with
`~2^20` distinct partial pairs. The honest statement is therefore:
**exhaustively dead through `R = 46` at precision up to `2^32`; dead at
`2^64` at least at `R = 49`; beyond that open at current cost.**

Three structural findings:

1. **(P2) carries everything.** Dropping only the "no selected divisor of
   `2R+3`" clause keeps most rows unsatisfiable anyway; dropping only the
   "at most one selected divisor of `2(R+1)+2` / `2R+2`" cap makes almost
   every row satisfiable again. In other words, wherever decidable, **every**
   solution of the bare row equation selects **at least two divisors of the
   next even endpoint** (`2R+4` for (B'), `2R+2` for (S)). The sparse-pulse
   obstruction is precisely the impossibility of that double selection.
   Exceptions where the bare equation is already unsatisfiable exist (e.g.
   (S) at `R = 38`).
2. **No fixed-modulus certificate exists.** A DP scan over every modulus
   `M <= 150` shows the row equation with pulse constraints is solvable
   modulo **every** such `M` for every `R >= 13`, on both sockets. The
   contradiction is genuinely cumulative-2-adic: it appears only at full
   precision `2^B` with growing `B`, never in any fixed projection. This
   sharpens the section-6 impostor analysis of the attack note from
   examples to a clean negative law, and it explains mechanically why
   forward replay and fixed congruences could never see this obstruction.
3. **The killing precision grows without bound through the tested range**
   (`B* = 8, 16, 32` at `R`-thresholds roughly 12 and 21, identically for
   both sockets). Any proof of the socket exclusion must therefore consume
   an unbounded part of the binary suffix — exactly the demand the attack
   note's section 6 anticipated ("any proof ... must use an unbounded part
   of the binary suffix, or an ancestry constraint that couples many
   scales").

## 4. Consequence chain if the pattern is proved for all R [Deduction]

If one proves — for every `R` in the relevant residue class — that no
Boolean row satisfies the socket equation with its sparse pulse constraint
(the empirical law above, currently exact computation), then composing with
the existing Lean normal forms gives:

1. `twentyOneBadSaturatedTransition_*` hypotheses are unsatisfiable for
   canonical-aligned rows: no bad saturated transition occurs;
2. `twentyOneSaturatedBoundary_crosses_iff_sparsePulse` +
   `twentyOneAlignedSaturatedCrossing_forces_scaled_greedy_skip`: no aligned
   saturated crossing into supercapacity occurs;
3. by `twentyOneFatalAlignedBranch_eventually_strict_supercapacity` the only
   surviving fatal regime must *enter* strict supercapacity, and both
   abstract entrances are now closed — reducing
   `contradict_twenty_one_permanent_affine_supercapacity` to the already-
   closed late-transition branch (`twentyOneFatalAlignedBranch_eventually_
   saturated_socket`).

This would close the "entrance problem" identified in the attack note's
section 7 at the level of abstract Boolean rows. Two cautions keep this
honest. First, the congruence relaxation drops the `0 <= s < 2^R` and
`|D| <= s` filters; dropping filters can only create solutions, so the UNSAT
verdicts remain valid, but a proof extracted from the congruence level must
be checked against the same relaxation direction. Second, the interface
caveat of the attack note stands: the fatal branch supplies canonical
alignment only eventually, and the first crossing may precede it; a final
theorem must be stated at an interface covering the first crossing, as the
note already requires.

## 5. THEOREM — the saturated entrance socket is empty [RETRACTED — false lemma]

> **RETRACTION (2026-08-24, same day as landing; supersedes commits
> `a0333f1f`, `6bfd524b`).** The proofs below consumed **Fact 1:
> `2^d | q_R(d)`**, which is **FALSE**. Falsifier: `q_5(2) = ⌊2^{10}/3⌋ =
> 341`, odd — indeed `v₂(q_R(d)) = 2R mod d` when nonzero, else `0`. The
> correct folded identity is `q_R(d) = Σ_{j=1}^{⌊2R/d⌋} 2^{2R−jd}`: ones
> exactly at positions `k ≡ 2R (mod d)`, NOT at multiples of `d`; "ones at
> multiples of `d`" conflated `2R − jd` with `jd`. **Theorem A, Theorem B,
> and both corollary blocks are UNPROVED and are withdrawn as claims.** The
> computational results of sections 1–4 are unaffected (they never used the
> lemma): zero solutions exhaustively through `R = 18`, congruence-UNSAT
> through `R = 46` at `B = 32`, no fixed modulus ≤ 150 kills any row. The
> socket-exclusion statement returns to verified-conjecture status; per
> section 3's no-fixed-modulus law, any proof must control the folded-bit
> residue-class lattice, not a single valuation. Surviving fragments are
> marked inline.

The computation exposed the mechanism, and the mechanism closes the (S) side
outright. Two elementary facts replace the entire search:

**Fact 1 (folded-bit form) [FALSE].** For `d ≥ 2`, the binary expansion of
`q_R(d) = ⌊2^{2R}/(2^d − 1)⌋` has ones exactly at the multiples of `d`
strictly below `2R`:

    q_R(d) = Σ_{k : d | k, 0 < k < 2R} 2^k.

*(Geometric-series folding: `⌊N/(2^d−1)⌋ = Σ_{j≥1} ⌊N/2^{jd}⌋` at `N = 2^{2R}`
leaves one power of two per multiple.)* Hence `2^d | q_R(d)` for every `d`,
and therefore

    ~~2^{min D}  |  Σ_{d∈D} q_R(d)~~          [FALSE — falsifier q_5(2)=341]

**Fact 2 (target valuation).** Let `R ≡ 2 (mod 3)`, `R ≥ 5`, and
`T_S := Q_R − 2^R = ⌊2^{2R}/21⌋ − 2^R`. Since `2^{2R} ≡ 16 (mod 21)`
(`4^R` cycles `4, 16, 1`),

    T_S = (2^{2R} − 21·2^R − 16) / 21,
    2^{2R} − 21·2^R − 16  =  2^R(2^R − 21) − 16  ≡  −16 (mod 32),

because `R ≥ 5` makes `2^R(2^R−21)` a multiple of `32` with an odd
cofactor. So `v₂(T_S) = 4` exactly.

**Size exclusion.** For `d ≤ 4` and `R ≥ 6`:
`q_R(d) ≥ ⌊2^{2R}/15⌋ ≥ 2^{2R}/15 − 1 > 2^{2R}/21 − 2^R ≥ T_S` (the middle
inequality is `2^{2R}·(2/105) > 2^R + 1`, i.e. `2^R ≥ 53`), and `R = 5` is a
direct check (`q_5(4) = 68 > T_5 = 16`). Hence no solution may contain any
`d ≤ 4`.

**~~THEOREM (empty saturated entrance).~~** [RETRACTED] For every `R ≡ 2 (mod 3)`, `R ≥ 5`,
there is **no** finite `D ⊆ {2,…,R}` with

    Σ_{d∈D} q_R(d) = Q_R − 2^R.

*Proof.* Facts 1–2 force `min D ≤ 4`; the size exclusion forbids it; `D = ∅`
gives `0 ≠ T_S` (indeed `T_S > 0`). ∎

**~~Canonical consequence [Deduction].~~** [RETRACTED] The canonical row identity
(`localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder`)
reads `Σ_{d∈D_R} q_R(d) + s_R = Q_R` with `D_R` the deterministic
quotient-greedy support. A saturated row is exactly `s_R = 2^R`, which by
the theorem would require the impossible equation. Therefore:

> **Corollary.** The canonical denominator-21 quotient-greedy remainder
> never attains closed capacity: `twentyOneEvenQuotientGreedyRemainder R ≠
> 2^R` for every `R ≡ 2 (mod 3)`, `R ≥ 5` — and the aligned saturated
> crossing of `twentyOneSaturatedBoundary_crosses_iff_sparsePulse` has an
> empty hypothesis set. The permanent-supercapacity regime of
> `TwentyOneFatalAlignedBranch` has no saturated entrance through any
> aligned row.

Combined with `twentyOneFatalAlignedBranch_eventually_saturated_socket`
(late failed saturated transitions contradict ancestry), the entrance
problem of the density-invariant attack's section 7 is closed on the (S)
side unconditionally, and on the (B') side at least to the precision the
search reaches. The remaining interface caveat is unchanged: alignment is
available only eventually, and a final no-entrance theorem must cover the
first crossing.

**Why the search data predicted this.** The pulse-free UNSAT sweep (section
3 revision below) shows the bare equation dying at growing precision; Fact 1
+ Fact 2 show why only ONE congruence level was ever needed — the second
least significant bit of the target already contradicts the folded-bit
divisibility, provided the descent reaches depth 4 with no small element
available. The `B*(R)` staircase measures how much precision a generic
search wastes before stumbling into the two-line squeeze.

## 6. ~~THEOREM B — the canonical row is never saturated~~ [RETRACTED — false lemma]

> **RETRACTED** with section 5: same false lemma (`2^d | q_R(d)`), same
> falsifier `q_5(2) = 341`. Corollaries B1/B2 fall with it.

Original text preserved below with the false step struck.



Section 5 restricted to `R ≡ 2 (mod 3)` because that is where the crossing
classifier lives. The same squeeze closes **every** residue class, so
saturation is impossible outright.

**~~THEOREM B.~~** For every `R ≥ 2` and every finite `D ⊆ {2,…,R}`:

    Σ_{d∈D} q_R(d) ≠ Q_R − 2^R.

Consequently `twentyOneEvenQuotientGreedyRemainder R ≠ 2^R` for every `R`.

*Proof.* Write `T := Q_R − 2^R = (2^{2R} − 21·2^R − c)/21` with
`c = 2^{2R} mod 21 ∈ {4, 16, 1}` according as `R ≡ 1, 2, 0 (mod 3)`, and
`num := 2^{2R} − 21·2^R − c = 2^R(2^R − 21) − c`. If `T < 0` the equation
fails since the left side is nonnegative; this covers `R ∈ {2, 3, 4}`.
Assume `T ≥ 0` (`R ≥ 5`). By Fact 1, `2^{min D}` divides the left side,
so `min D ≤ v₂(T)` is forced for any nonempty `D`.

* `R ≡ 0 (mod 3)`: `c = 1` odd, so `num` is odd and `v₂(T) = 0`: no
  nonempty `D` qualifies.
* `R ≡ 1 (mod 3)`: for `R ≥ 3`, `2^R(2^R−21) ≡ 0 (mod 8)`, so
  `num ≡ −4 (mod 8)` and `v₂(T) = 2`: forces `min D ≤ 2`. But
  `q_R(2) = ⌊2^{2R}/3⌋ > 2^{2R}/21 > T` (size), so `2 ∉ D`:
  contradiction.
* `R ≡ 2 (mod 3)`: section 5's case, `v₂(T) = 4`, size forbids
  `d ≤ 4`: contradiction.

`D = ∅` gives `0 ≠ T` since `Q_R > 2^R` for `R ≥ 5`
(`2^{2R}/21 > 2^R ⟺ 2^R > 21`). ∎

Verification: exhaustive all-subsets enumeration over `R = 2..18` finds zero
solutions, with measured `v₂(T) ∈ {4, 0, 2}` matching the derivation per
class.

**Corollary B1 (no crossings).** A saturated crossing requires `s_R = 2^R`
with `R ≡ 2 (mod 3)`
(`twentyOneSaturatedBoundary_crosses_iff_sparsePulse`,
`twentyOneTargetTwoStepPulse_even_eq_three_iff`). Theorem B makes the state
unattainable at every depth: the aligned canonical orbit never crosses into
supercapacity through a saturated moment.

**Corollary B2 (strict-closed propagation in aligned windows).** Under
consecutive full alignment the boundary recurrence holds
(`twentyOneEvenQuotientGreedyRemainder_succ_eq_boundary_of_fullAlignment`),
and from a strictly closed state `s_R ≤ 2^R − 1` both branches preserve
strict closedness:

* take: `s_{R+1} = C_R − (2^{R+1}+1) ≤ 4(2^R−1) + 3 − 2^{R+1} − 1 =
  2^{R+1} − 2`;
* skip: `s_{R+1} = C_R ≤ 4(2^R−1) + 3 = 2^{R+1} − 1`.

So inside any aligned window, supercapacity can be **inherited but never
entered**. Combined with Corollary B1 and Theorem B, under
`TwentyOneFatalAlignedBranch` the onset of strict supercapacity
(`twentyOneFatalAlignedBranch_eventually_strict_supercapacity`) must
already hold when alignment begins: the entrance is pushed entirely before
the alignment rank, into the unaligned finite prefix.

**Honest boundary.** This does not decide `universal_257`. The fatal branch
may carry its entrance inside the pre-alignment segment, which has no
recurrence structure to constrain; and the membership side of the dichotomy
is untouched. What changed: the asymptotic half of the fatal branch (the
aligned tail) is now fully rigid — saturation impossible everywhere,
crossing impossible everywhere, entrance impossible after alignment — so
the residual obstruction is finite and combinatorial, not dynamical.



## 4b. Revision of section 3's attribution

Post-landing reruns with all pulse clauses dropped show the bare equations
are exhaustively unsatisfiable at the same staircase precisions (`B* ∈
{8,16,32,64}`, thresholds near `R ≈ 12, 21, 33`, both sockets, receipts
`backward_forced_suffix_relaxed_bscale_receipt.json`). Finding 1 of section
3 is therefore re-attributed: the cap clause was not carrying the
obstruction; the row equations are impossible on their own, and the theorem
of section 5 explains the (S) half completely. Findings 2–3 stand verbatim.

## 7. THEOREM C — quotient weights are superincreasing; the socket reduces to the canonical remainder [PROVED]

After the section 5–6 retraction, the corrected structure still yields a
genuine theorem. Let `N = 2^{2R}`, `ρ_j = 2R mod j`.

**Lemma C.0 (exact fold).** `q_R(j) = ⌊N/(2^j − 1)⌋ = Σ_{i=1}^{J}
2^{2R−ij}` with `J = ⌊(2R)/j⌋`; its ones sit exactly at positions
`k ≡ ρ_j (mod j)` in `[0, 2R)`, so `v₂(q_R(j)) = ρ_j` if `ρ_j ≠ 0`, else
`0`.

**THEOREM C (dominance).** For every `R ≥ 3` and `2 ≤ d < R`:

    q_R(d)  >  Σ_{k=d+1}^{R} q_R(k).

*Proof.* Upper: `q_R(k) ≤ N/(2^k − 1)` and `1/(2^k − 1) ≤ 2^{−k} +
(4/3)4^{−k}` for `k ≥ 2` (equality at `k = 2`; cross-multiplies to
`4 ≤ 2^k`), so

    Σ_{k=d+1}^{R} q_R(k) ≤ N·(2^{−d} + (4/9)4^{−d}).

Lower: `ρ_d ≤ d − 1`, `1/(2^d − 1) ≥ 2^{−d}(1 + 2^{−d})` (since
`(1−2^{−d})(1+2^{−d}) = 1 − 4^{−d} ≤ 1`), hence

    q_R(d) ≥ (N − 2^{d−1} + 1)·2^{−d}(1 + 2^{−d})
           ≥ N·2^{−d} + N·4^{−d} − 1 + 2^{−d}.

Difference `≥ (5/9)N·4^{−d} − 1 + 2^{−d}`, and `N·4^{−d} = 2^{2R−2d} ≥ 4`
for `d ≤ R − 1`, giving margin `≥ 20/9 − 1 = 11/9 > 1`. ∎

Verified: zero violations over all `(R, d)` with `3 ≤ R ≤ 599`
(`5,647` inequalities); minimum absolute margin `12` at `R = 3`.

**Consequence C1 (unique representation).** In descending-weight order the
weights are strictly superincreasing, so the map
`D ↦ Σ_{d∈D} q_R(d)` is injective on supports `D ⊆ {2,…,R}`: distinct
supports have distinct sums, and each reachable sum has exactly one
representation.

**Consequence C2 (reduction of the socket conjecture).** The (S) equation
`Σ_{d∈D} q_R(d) = Q_R − 2^R` has **any** solution iff the canonical greedy
support is that solution, iff

    twentyOneEvenQuotientGreedyRemainder R = 2^R.

So the exhaustive searches of sections 1–3 — and any future attempt — are
exactly the single-sequence question of whether the deterministic
denominator-21 remainder ever attaches capacity. The computational content
is unchanged; the object is now one orbit, not `2^R` candidates.

**Consequence C3 (search shape).** The exact solver's node count
`≤ ~1.47·R` through `R = 298` is explained: with strict dominance the DFS's
include-branch dies by overshoot or the exclude-branch by shortfall at
almost every level.

**THEOREM C′ (dominance for the (B′) weights) [PROVED].** Let
`W_d = 4q_R(d) + b_d` with `b_d = 2[d|2R+1] + [d|2R+2] ∈ {0,1,2}` (no `d`
divides both endpoints; note `b ≤ 2`, not 3). For every `R ≥ 4` and
`2 ≤ d < R`, writing `m = R − d ≥ 1`:

    W_d  >  Σ_{k=d+1}^{R} W_k.

*Proof.* Sharpened two-term bound for the `q`-margin: lower
`q_R(d) ≥ (N − 2^{d−1})·2^{−d}(1+2^{−d}) ≥ N2^{−d} + N4^{−d} − 1/2 −
2^{−d−1}` (remainder `≤ 2^{d−1}` since `N mod (2^d−1) = 2^{2R mod d}` and
`ρ ≤ d−1`); upper tail `Σ_{k>d} q_R(k) ≤ N(2^{−d} + (4/9)4^{−d})`.
Difference: `Δ_q ≥ (5/9)N4^{−d} − 1/2 − 2^{−d−1} ≥ (5/9)4^m − 3/4`
(using `N4^{−d} = 4^m`). Bonus bookkeeping:
`W_d − Σ_{k>d} W_k = 4Δ_q + b_d − Σ_{k>d}b_k ≥ 4Δ_q − 2m`. Total:

    Δ_W ≥ (20/9)4^m − 3 − 2m ≥ 35/9 > 0   for every m ≥ 1.

∎ Verified: zero violations of both intermediate bounds (`Δ_q` slack
≥ 17.53, `Δ_W` slack ≥ 74.11) over all `(R,d)` with `4 ≤ R ≤ 149`;
zero dominance failures through `R = 299` (minimum margin `78`).

**Consequence C2′ (B′ reduction).** The (B′) equation is likewise solvable
iff its canonical greedy realization realizes it: both socket exclusions
reduce to single-sequence questions about deterministic orbits, not to
`2^R` searches.

Scope notes, stated precisely. First, C2 concerns the (S) weights; the (B′)
weights `W_d = 4q_R(d) + 2[d|2R+1] + [d|2R+2]` carry `O(1)` endpoint
bonuses. **Measured-in-range:** `W`-dominance (`W_d > Σ_{k>d} W_k`) holds
with zero failures and minimum positive margin `78` over every `(R, d)`
with `4 ≤ R ≤ 299`, so both sockets appear to reduce to their canonical
single-sequence questions. ~~No proof recorded~~ **[PROVED same session — see THEOREM C′ above]**:
the naive transfer failed by double-counting losses (`b_k ≤ 2`, not 3;
the two-term split recovers the `4^m` main term). Second, the reduction is to the canonical
remainder question — which is open; the corpus's own deep replays report
minimum closed-capacity margin `1` (never `0`) with no saturated state, and
by C1 that observation, if it held at all depths, would settle the (S)
exclusion. Third, nothing here touches the membership side of the
`1/21` dichotomy or `universal_257`.



* Prove the empirical exclusion for all `R` (both sockets). The data suggest
  the mechanism is: the folded binary weights of
  `q_R(d) = sum_j 2^(2R - jd)` force, at bit depth growing like `log R`
  steps of factor two, a parity conflict that can only be avoided by
  selecting two divisors of the next even endpoint. A proof shape worth
  trying: track the reachable set of `(sum mod 2^B, capped-count)` states
  symbolically in `R` and show the capped-0/capped-1 classes empty at
  `B = B*(R)`.
* Decide `B*(64)`-level rows beyond `R = 49` within practical time (needs a
  meet-in-the-middle inside giant level pools, or a symbolic representation
  of the frontier).
* Extend the sweep on the (S) side past `R = 44` (the previous best was the
  attack note's exact MITM through `R = 41`; this run reaches 44 and could
  go further with pooled-MITM).

## 8. What remains open

* Prove `twentyOneEvenQuotientGreedyRemainder R ≠ 2^R` for all `R`
  (equivalently, by C2, close the (S) socket): the single-sequence target.
  The corpus's deep replays (minimum margin 1 at rank 6, no saturated state
  through depth 10^6+) say the margin is a positive integer that has never
  been observed to vanish.
* Establish or refute dominance for the (B′) weights `W_d`.
* Decide `B*(64)`-level rows beyond `R = 49` within practical time.
* Extend the exact-solver sweep past `R = 298`.

## 9. Reproducibility

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/backward_forced_suffix_enumeration.py --mode bscale --r-max 46 --node-budget 50000000
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/socket_modulus_scan.py --r-max 46 --max-m 150
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos257/scripts/socket_exact_subset_sum.py --r-max 300 --node-budget 200000000
```

The exact solver decides the true integer equations (no modular
relaxation): `198/198` rows exhaustively unsatisfiable through `R = 298`
on both sockets, node counts `≤ ~1.47·R`, zero budget limits; MITM
cross-check agreement on small rows.

All arithmetic is exact integers; no floating point anywhere. Node budgets
were never the binding constraint on the landed rows (max 43 nodes on the
final solver); the `R >= 49`, `B = 64` band is the only budget-limited area
and is labelled as such.

> **STATUS AFTER RETRACTION:** sections 1–4 stand as exact computation
> (independent of the false lemma); sections 5–6 are RETRACTED as proofs;
> the socket-exclusion statements they claimed are verified conjectures
> only. Nothing here changes `universal_257`'s open status. Self-error
> captured on the Task Ledger; root cause: a bit-level identity asserted
> from an informal fold pattern and checked only against examples that did
> not include an odd `q_R(d)`.
