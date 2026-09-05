# Erdős #243: eight rigidity criteria from the 2026-09-05 return batch

Status: proof note. Lean authority for section 3 is
`ErdosProblems/Erdos243/PrimitiveRecordBarrier.lean`; the other sections are
ordinary proofs over the Lean core of `ReciprocalTailRigidity.lean`,
`DynamicCancellation.lean`, `SlowRiseBarrier.lean`, `LcmCriticalBoundary.lean`
and `CumulativeLcmTransfer.lean`. Nothing here settles Erdős #243.

Return batch `erdos243_20260905_eight_return_stream_01`. Each result cites the
return section whose proof was audited in this pass, or carries a proof where the
statement is new here. Corrections to the returns are consolidated in section 9;
claims that failed verification, or that reduce to an existing corpus row, live
in the batch coverage ledger.

## 0. Dictionary

Koizumi, arXiv:2504.05933, Lemma 15. Canonical state: `E_n ≡ D_n (mod C_n)`
centred in `[−C_n/2, C_n/2)`, `a_n = (D_n − E_n)/C_n + 1`, `C_{n+1} = C_n − E_n`,
`D_{n+1} = a_n D_n`, `E_n = D_n − (a_n − 1)C_n`, under normalised vanishing (NV):
for every `K`, eventually `K|E_n| < C_n`. The selector is the nearest integer;
the floor selector `⌊v_n/u_n⌋ + 1` forces `e_n ≥ 0` and deletes the negative
branch, the only branch in which #243 is open (r05 section 1).

Primitive coordinates: `G_n = gcd(C_n, D_n)`, `u_n = C_n/G_n`, `v_n = D_n/G_n`,
`e_n = E_n/G_n`, `h_n = G_{n+1}/G_n`, `w_n = a_n u_n − v_n = u_n − e_n`,
`h_n u_{n+1} = w_n`, `h_n v_{n+1} = a_n v_n`, `h_n = gcd(w_n, a_n^2)`,
`gcd(u_n, u_{n+1}) = 1`. `H_n = max_{j≤n} C_j`, `R_n = max_{k≤n} u_k`,
`B_n = H_n − C_n`, `r_n = H_{n+1} − H_n`, `ℓ(x) = log₂ log₂ max(4, x)`,
`δ_n = (a_n^2/a_{n+1} − 1)_+`.

## 1. Critical-boundary integer-rounding rigidity

**Theorem 1 (linear barrier).** Let `F_n > 0`, `r_n = F_{n+1}/F_n`,
`η_n = n(r_n − 1) − 1` eventually positive and nonincreasing to `0`, and let
`X_n` be positive integers with `X_{n+1} ≤ r_n X_n`. If `M = ⌈X_n/n⌉` satisfies
`Mη_n < 1` at some index `n`, then `X_k ≤ Mk` and `X_{k+1} − X_k ≤ M` for every
`k ≥ n`.

*Proof.* `r_k(Mk) = M(k+1) + Mη_k < M(k+1) + 1` using `η_k ≤ η_n`, and `X_{k+1}`
is an integer below the left side; then
`X_{k+1} − X_k ≤ (r_k − 1)X_k ≤ (1 + η_k)M < M + 1`. ∎

**Lemma 2 (r01 section 2, (15) and (16)).** With
`Ψ(x) = (frac(x)^2 − frac(x))/2`, `θ = frac(s)`, `R = A/B`, `Δ = A − Bθ`:
`Ψ(t) − Ψ(s) ≤ (θ − 1/2)(t − s) + (t − s)^2/2` for all real `s, t`, by concavity
of `Ψ(x) − x^2/2`; and `θ ≥ 1/2 − 1/(16R) + (Ψ(s+Δ) − Ψ(s))/A − Δ^2/(2A)` for
`A, B > 0` and `R > 1/4`, by completing the square.

**Theorem 3 (divergent-reciprocal envelope rigidity; r01 Theorem 2, audited line
by line).** Assume (8) `η_n > 0` eventually nonincreasing to `0` and
`d_n = F_{n+2} − 2F_{n+1} + F_n > 0`; (9) `n^2d_n/(F_nη_n) → 1`;
(10) `d_{n+1}/d_n = 1 − 1/n + O(η_n/n + 1/n^2)`; (11) `∑ 1/F_n = ∞`. Then
positive integers with `c_{n+1} ≤ r_n c_n` eventually satisfy `c_n ≤ Mn` and
`(c_{n+1} − c_n)_+ ≤ M` eventually. Mechanism: dominate by the maximal floor
orbit and apply Theorem 1; failing that, the exact loss identity
`Y_{n+1} = Y_n − θ_n/F_{n+1}` with `Y_n = X_n/F_n` gives
`∑ θ_n/F_{n+1} ≤ Y_N < ∞`, which (16) and (11) exhaust.

**Theorem 4 (critical-boundary rigidity; r01 Theorem 1).** Let
`a_{n+1}/a_n^2 → 1`, `∑ 1/a_n ∈ ℚ`, `F` satisfying (8) to (11). If eventually
`a_n^2/a_{n+1} ≤ F(n+1)/F(n) − K_0/a_n`, then `C_n ≤ Mn` and `(−E_n)_+ ≤ M`
eventually, hence `a_{n+1} = a_n^2 − a_n + 1` eventually; in particular under
`δ_n ≤ 1/n + ∑_{j≤m} 1/(n l_1(n)⋯l_j(n))` for any fixed `m ≥ 1`. The bridge is
exact, `C_{n+1}/C_n = a_n − 1/x_n = a_n^2/a_{n+1} + O(1/a_n)`; the envelope
`F(x) = x∏_{j≤m}l_j(x)` has discretisation margin `(α(n)/(2n^2))(1 + o(1))`
absorbing that error since `1/a_n = o(α(n)/n^2)`; Theorem 3 then discharges the
hypothesis of `bounded_negative_part_rigidity`.

**Evidence** ordinary proofs verified this pass over
`bounded_negative_part_rigidity`, with exact replay of the barrier and of (15),
(16). **Relation** Theorem 4 strictly contains and supersedes
`one_over_n_threshold_verified`, since `δ_n = 1/n + 1/(n log n)` has
`limsup nδ_n = 1`; Theorem 3 uses no arithmetic of `D_n` and escapes the cap of
`SlowNegativePartRigidity.md` Proposition 7. **Not proved** the onset index is
`exp^{(m+1)}(2C_N/F_N)`, so Theorem 3 is qualitative with no explicit constant,
and the route stops at `∑ 1/F_n < ∞`, where the maximal floor orbit survives.

## 2. The B-shifted excess-mass obstruction

**Theorem 5 (r01 Theorem 4 and (47)).** On a canonical orbit that is not
eventually Sylvester, for every integer `B ≥ 0` there are `κ_B > 0`, `K_B` with
`∑_{n<T}(−E_n − B)_+/C_n ≥ κ_B log C_T − K_B` for all large `T`, so the sum
diverges for every fixed `B`; hence `∑_n(−E_n − B)_+/C_n < ∞` for some `B`
implies `a_{n+1} = a_n^2 − a_n + 1` eventually, and the two are equivalent since
a Sylvester tail has eventually zero shifted mass. Two exhaustive cases: a block
modulus `m` dividing `C_s` and `D_s` persists into every later `E_n`, so every
positive jump is a positive multiple of `m` and `κ_B = 1 − B/m`; otherwise the
orbit avoids the shifted CRT block `[x, x+B)` at height `x ∈ [P, 2P)`, whose
walls `τ_k = x + kP + B` have `H(t) = (1/P)log t + O(1)` and where a step
crossing `h ≥ 1` walls has `d − c ≥ (h−1)P + B + 2`, giving `κ_B = 1/P`.

**Evidence** ordinary proof verified this pass over `bounded_crt_block`,
`common_divisor_persistence_and_multiplier_overlap` and
`lcm_freshness_budget_and_pairwise_coprimality`, replayed exactly on random
forbidden-block walks. **Relation** the exact `B`-shifted generalisation of
`summable_negative_mass_sylvester_consumer` (`B = 0`), subsuming
`bounded_negative_part_rigidity`, incomparable with
`slow_negative_part_rigidity`; Lean target
`summable_shifted_negative_mass_sylvesterNext_eventually`. **Not proved** `κ_B`
in Case 2 is orbit-dependent and can be astronomically small, and the bound
constrains cumulative mass only, not the depth of a single excursion.

## 3. Primitive record two-unit rigidity

**Theorem 6 (canonical; r07 sections 1 to 5).** Let `a_n` be strictly increasing
positive integers with `a_{n+1}/a_n^2 → 1` and `∑ 1/a_n ∈ ℚ`. If at every
sufficiently late record-setting step (`u_{n+1} > R_n`) one has
`u_{n+1} − u_n ≤ 2`, then `a_{n+1} = a_n^2 − a_n + 1` eventually. No hypothesis
is imposed at non-record steps and no bound is imposed on `h_n`.

Four ingredients, each verified this pass.

- **Lemma 7 (valuation no drop; r07 Lemma 1).**
  `ν_p(v') = ν_p(a) + ν_p(v) − min(ν_p(w), ν_p(a) + ν_p(v))`; a drop from
  `l = ν_p(v)` forces `ν_p(a) = l` and `p^{l+1} | w`, and full erasure forces
  `p^{2l} | w`. Lean: `primitive_valuation_no_drop`.
- **Lemma 8 (protection; r07 Lemma 2).** If `P = p^l | v_s` and `w_n < pP`
  throughout an interval from `s`, then `P | v_n` throughout and at its
  successor, so `p ∤ u_n` there. Lean: `protectedPrimePower_persists`.
- **Lemma 9 (odd cut; r07 Lemma 3).** With `w_n ≤ (3/2)u_n` from `s`, `p` odd,
  `p^l | v_s`, `H` an odd multiple of `p` with `R_s < H` and `3H < 2p^{l+1}`: if
  every record-setting step from `s` has jump at most two then `u_n < H` for all
  `n ≥ s`. The first crossing is a global record, `p | v_τ` kills the landing
  `u_τ = H`, and the remaining jump-2 crossing `(H−1, H+1)` has both endpoints
  even, against `gcd(u_n, u_{n+1}) = 1`. Lean: `odd_record_cut`.
- **Lemma 10 (supply; r07 Lemmas 5 to 7, r08 Lemma 4).** For every `R`, `A`
  there are arbitrarily large `N` with an odd prime `p > R` and `l ≥ 1` such
  that `p^l ‖ v_N` and `p^l > A(u_N + 1)`, from `log R_n = o(n)`,
  `log a_n = κ2^n + o(1)`, `a_j > (3R_{j+1})!` and the freshness budget.

Zero absorption makes failure of the endpoint equivalent to `e_n ≠ 0` for all
large `n`, which with `|e_n|/u_n → 0` gives `u_n → ∞`; Lemma 10 supplies an
arbitrarily late odd protected source and Lemma 9 bounds `u_n` from it on.

**Corollary lattice.** In increasing hypothesis strength: `e_n ≥ −2` at every
step (r03 (A)); `(u_{n+1} − u_n)_+ ≤ 2` at every step (r08 Theorem 1, identical
to r05 (B)); every record-setting jump at most two (r07). Each implies the next,
so Theorem 6 implies all three. **Corollary 11 (r08 Corollary 6):** eventual
Sylvester recurrence holds if and only if `#{n : h_n = 1 and e_n ≤ −3} < ∞`.
**Corollary 12 (r08 Corollary 10 is an equivalence):** with
`Q_n = (A_n/a_n)(a_n^2/a_{n+1} − 1)`, the exact identity
`E_n + qQ_n = D_n(1/a_{n+1} − (a_n − 1)∑_{k≥n+2}1/a_k)` gives
`e_n = −qQ_n/G_n + o(1)`, so `limsup qQ_n/G_n = limsup(−e_n)` exactly and
`limsup qQ_n/G_n < 3` is equivalent to `e_n ≥ −2` eventually.

**Separate axis.** The odd lattice (r08 Theorem 5), the one-unit lattice (r08
Corollary 8 = r03 (C)), eventual periodicity of `e_n` (r03 (B), r08 Corollary 9)
and finite cyclic menus (r08 Theorem 7) need the hypothesis at every clean step
and weaken only to epoch records. The cap at two is structural: `B` protected
moduli need `∏_{s≠i}p_s ≤ (2/3)p_i^{l_i}` for every `i`, impossible for `B ≥ 3`
with squarefree fresh multipliers.

**Three-rise crossing fixtures.** Three exact families give clean primitive rises
of size three across a protected odd prime: r03 section 8 (`u = p−1`,
`v = p(p−4)`, `a = p−2`, `p ≡ 2 mod 3`, one step); r07 section 8 (`p^2 | v`, two
steps); r08 section 6 (`p^3 | v`, two steps). The instances `(10, 10527, 1054)`
and `(10, 89177, 8919, −3, 1)` reproduce exactly. Family-limit wording: for fixed
`p` the ratio `a'/a^2` tends to `u/u' = 1 − 3/(u+3)`, bounded away from `1`, and
only the joint limit `p → ∞` gives `a'/a^2 → 1`, measured at `0.7683` for
`p = 11` and `0.99703` for `p = 1009`; no member is an orbit segment obeying the
rate hypothesis. Lemma 10 with r07 Theorem 8 along a disjoint subsequence of
sources gives `∑_{n record}(−e_n − 2)_+ = ∞`, strengthening Corollary 11.

**Evidence** Lemmas 7, 8, 9 and the composition to Theorem 6 are Lean-checked in
`PrimitiveRecordBarrier.lean` with the supply of Lemma 10 as an explicit
hypothesis, axiom audit clean of `sorryAx`; Lemma 10 and the corollary lattice
are ordinary proofs verified this pass; the fixtures are exact computations.
**Relation** incomparable with `bounded_rise_reduced_tail_excluded` and
`slow_rise_reduced_tail_excluded`, which allow any fixed rise bound and require
`h_n = 1`; the new content is arbitrary cancellation with a record-only
hypothesis. **Not proved** anything at jumps of size three; r07 Theorem 8 is an
open comment in the Lean module; and the open prime supply of
`bounded_lcm_negative_arithmetic_core` does not close by an index-shift wrapper
over `CumulativeLcmTransfer`, which extracts no prime factor from a possibly
`B`-smooth multiplier and whose index alignment `m_i | D_t` breaks under
reindexing to a fresh subsequence.

## 4. The record-excess dichotomy

**Theorem 13 (r04 Theorem 1).** With `K = limsup_n(H_{n+1} − H_n)/ℓ(H_n)`, on a
nonterminating canonical orbit either `G_n` is unbounded and `K = ∞`, or `G_n`
stabilises at `g` and `K ≥ g·v_T/φ(v_T)` for every late `T`, so `K > g ≥ 1`.
Hence `K = 0` or `K > 1`, and `K ≤ 1` implies eventual Sylvester recurrence. Four
steps, each verified this pass: the drawdown ladder `r_n = (−E_n − B_n)_+`,
`B_{n+1} = (B_n + E_n)_+`, whence `r_n ≤ (−E_n)_+` (r04 (13)); the record trap,
where a divisor of `C_t` and `D_t` at a record locks into every later `r_s`, so a
pairwise-coprime block of moduli above `B` dividing `D_T` contradicts `r_n ≤ B`
below height `2P + B` (r04 Lemmas 2, 3); the rescaling `sup_n G_n = ∞ ⟹ K = ∞`,
forcing a primitive tail with pairwise-coprime multipliers (r04 Proposition 5);
and Euler amplification, where pre-sieving with `x ≡ 0 (mod v_N)` makes a block
of length `B` cost only `φ(v_N)/v_N·B` fresh moduli, giving `K_u ≥ v_N/φ(v_N)`
with the ratio strictly increasing (r04 Proposition 6).

**Corollary 14 (inclusive log-log boundary; r04 (34)).**
`limsup(−E_n)_+/ℓ(C_n) ≤ 1` implies eventual Sylvester recurrence, since
`r_n ≤ (−E_n)_+` and `ℓ(H_n) ≥ ℓ(C_n)` give `K ≤ 1`; every counterexample has
`limsup(−E_n)_+/ℓ(C_n) > 1` strictly. **Corollary 15 (r04 (30)).** `K < ∞` with
nontermination implies `∑_{p∈P}1/p < ∞` for `P` the prime support of the
stabilised primitive denominator; divergence is not forced, since `P` is a
disjoint union of the multipliers' prime supports and the Fermat family is
pairwise coprime, doubly exponential, with a rapidly convergent such sum.

**Proposition 16 (sharp gap constant; r04 Proposition 8).** For pairwise-coprime
`m_0 < m_1 < ⋯ ≥ 2` with `ℓ(m_j) = j + O(1)`, `σ = ∏(1 − 1/m_j) > 0` and
`A = {u ≥ 1 : no m_j divides u}`, `limsup(u_{n+1} − u_n)/ℓ(u_n) = σ^{-1}`; the
upper bound splits the window at its own length, and the lower bound pre-sieves
by `∏_{j<J}m_j`. **Witness 17 (Fermat).** For `m_j = 2^{2^j} + 1`,
`∏_{j<J}m_j = 2^{2^J} − 1` exactly, so `σ_J → 1/2` and the gap constant is
exactly `2`; also `m_{j+1} = m_j^2 − 2m_j + 2`, differing from the Sylvester
recurrence, so the family has the right lacunary scale without satisfying the
feedback system.

**Evidence** ordinary proofs verified this pass over the Lean core, with the
identities, the `B = 20`, `R = 6` block and the Fermat witness as exact
computations. **Relation** Corollary 14 strengthens `slow_negative_part_rigidity`
on two axes, the drawdown-corrected record increment as observable and the
inclusive boundary, and upgrades `counterexample_loglog_negative_excursions` from
`≥ 1` to `> 1` strictly; Proposition 16 supersedes
`primitive_crt_limsup_rise_constant` and sharpens
`SlowNegativePartRigidity.md` Proposition 7 from `O(log u)` to
`σ^{-1}ℓ(u) = Θ(log log u)`, with `σ^{-1}` family-dependent. **Not proved** any
upper bound on `K`; the branch `K = ∞` stays open, and Proposition 16 makes the
coprimality route sharp for its own class.

## 5. Polynomial-profile rigidity

**Theorem 18 (r02 Theorem 1).** There are no integers `A ≥ 1`, `b`, `c`, `N`
with `C_n = A(n^2 + bn + c)` for all `n ≥ N`, and none with
`C_n = A(2n^2 + bn + c)`. An exact polynomial profile pins
`gcd(C_n, D_n) = A d(P)`, so `u_n = P(n)/d(P)` and all tail multipliers are
pairwise coprime (r02 Proposition 5), adjacent coprimality holds at every integer
argument, and the parity lemma forces the normalised leading coefficient into
`{1, 2}`, leaving six translation classes `k^2`, `k^2+k+1`, `k^2+k−1`, `2k^2−1`,
`2k^2+2k+1`, `2k^2+2k−1` with forbidden words `(1,0,1)` mod 3, `(1,0,1)` mod 3,
`(7,8,0,5)` mod 11, `(3,3,0,1)` mod 7, `(1,0,3)` mod 5, `(2,0,2)` mod 3, each
unrealizable by the exact finite-state transport and each modulus minimal over
moduli up to 40 and lengths 3 and 4. The ring primitives are r06 Lemmas 4, 5, 6;
the quartic identity `d_0^2(d_0 + c_1)^2 + c_0^2c_1c_3 = 0` at a numerator zero
separates a true feedback orbit from an independently chosen square root, and the
mod-11 word passes the square test and fails the quartic.

**Theorem 19 (rational-root profiles; r02 Theorem 7 merged with r06
Proposition 3).** If `P ∈ ℚ[X]` is nonconstant with a root modulo all but
finitely many primes, then `lower-density{n : C_n ≠ P(n)} ≥ 1/p` for some prime
`p` dividing some `D_t`; in particular no eventual polynomial profile of any
degree has a rational root. The proof composes
`common_divisor_persistence_and_multiplier_overlap` with
`lcm_freshness_budget_and_pairwise_coprimality`. **Theorem 20 (density; r06
Theorems 8, 9).** For every monic integer quadratic `Q` there are `m ≥ 3`, `t`,
`l ∈ {3,4}` with `l ≤ m` making `(Q(t), …, Q(t+l−1)) mod m` unrealizable, and for
`P = λQ` with `λ ∈ ℚ^×`, `lower-density{n : C_n ≠ P(n)} ≥ 1/m`; monicity is
unused, so the bound holds for every integer quadratic admitting a forbidden
block. **Corollary 21 (r06 Corollary 11 extended).** No exact integer orbit
satisfies `E_n = −sn + β` eventually for `s = 1, …, 7` and any `β`, since `2C_n`
is then the integer quadratic `(s, −(s+2β), 2K)`.

**Structural boundary (this pass).** Over a prime modulus every zero-free
numerator word is realizable, so every prime-modulus certificate contains a
numerator zero; over composite moduli this fails (2 zero-free forbidden 3-words
mod 4, 1,120 at length 3 mod 25), so composite moduli are a stronger and
unexploited resource. `C_n = A(4n^2 − 2n − 1)` escapes both returns and has no
forbidden block of length 3 or 4 at any modulus up to 200, while the length-5
block `(28,1,11,0,26)` mod 29 excludes it: block length is a real parameter
alongside the modulus.

**Evidence** ordinary proofs verified this pass, with the nine finite-field
certificates and the classification searches replayed exactly by
`check_feedback_word_realizability.py`. **Relation** r02 Proposition 5
strengthens `lcm_freshness_budget_and_pairwise_coprimality` under a much stronger
hypothesis; Theorems 18 and 20 are new; `C_n = c + n` is the degree-one instance
already excluded by `constant_negative_orbit_excluded`; r06 Lemma 1 restates
`common_divisor_persistence_and_multiplier_overlap`. **Not proved** the shape
hypothesis on `C_n`, which no known argument supplies; a density version at prime
moduli is structurally blocked, since each source prime eventually either never
meets the numerator or always meets it, and the blocked-successor fraction on 900
exact orbits decays like `1.5/p`.

## 6. The height dichotomy and the critical boundary at λ ≥ 1

**Lemma 22 (fresh prime insertion; r05 Lemma 1).** If `ρ_j = 1` and `p^E ‖ a_j`
then `p ∤ h_j`, `p ∤ u_{j+1}` and `p^E ‖ v_{j+1}` exactly.

**Theorem 23 (dichotomy; r05 (19), sharpened to the running record).** On any
counterexample, `limsup u_n/n = ∞` or `limsup P^+(v_n)/R_n = ∞`, with `P^+` the
largest prime factor; equivalently, if the primitive numerator grows at most
linearly then for every `K` there are infinitely many `s` with a prime `p | v_s`
and `p > K R_s`. Fresh indices have density one and `R(n) = o(n)`; for each late
fresh `j` pick `p_j | a_j`, so `p_j | v_{j+1}` and `p_j ≤ K R_{j+1}`; the `p_j`
are pairwise distinct, since equal primes at fresh `j < j'` contradict
`ρ_{j'} = 1`, and `n − o(n)` distinct primes below a linear function of `n`
contradicts `π(x) = o(x)`.

**Proposition 24 (critical boundary; r05 (51)).** If `nδ_n → λ ∈ (0, ∞)` on a
counterexample then `limsup(−e_n)_+ = ∞`. From
`E_n/C_n + δ_n = 1/a_n + O(1/a_n^2)`, `α_n = −e_n/u_n ∼ λ/n`, so `α_n → 0` and
`α_{n+1}/α_n → 1`; a bounded primitive negative alphabet then forces the exact
integer identity `h_n m_{n+1} = m_n`, so `m_n` is eventually constant and
`h_n = 1` eventually, which is the Lean-checked
`bounded_rise_reduced_tail_excluded`. **Free lemma:** under eventual centring
`|e_n| < u_n/2` every strict primitive rise is cancellation-free, since
`h_n ≥ 2` gives `u_{n+1} < (3/4)u_n`, so "clean" may be dropped from every rise
hypothesis in r03, r05, r07 and r08.

**Evidence** Lemma 22 is an ordinary proof verified this pass plus exhaustive
exact computation over 1,111,992 prime instances; Theorem 23 and Proposition 24
are ordinary proofs verified this pass. **Relation** Theorem 23 is new and
supplies r07 Theorem 8 with protected prime powers in the bounded-height branch;
Proposition 24 is new exactly at `λ ≥ 1`, being weaker than
`one_over_n_threshold_verified` for `λ < 1` and generalising
`constant_negative_orbit_excluded` at `λ = 1`. **Not proved** any rate in either
branch of Theorem 23, and Proposition 24 is silent when `nδ_n` fails to converge;
r05 Theorem (A) is closed by `bounded_rise_reduced_tail_excluded` whenever
`h_n = 1` eventually.

## 7. Unconditional square transport

**Lemma 25 (primitive square transport; desk S1).** Let `d_n` be the largest
divisor of `u_{n+1}` coprime to `G_{n+1}`. Then
`h_n e_n e_{n+1} ≡ v_n^2 (mod d_n)` and `gcd(v_n, d_n) = 1`, with no cleanliness
and no coprimality hypothesis.

*Proof.* `E_{n+1} ≡ a_n^2 E_n (mod C_{n+1})` from the defect identity. For
`d | d_n`, `d | C_{n+1}` and `gcd(d, G_{n+1}) = 1`, hence `gcd(d, G_n) = 1` since
`G_n | G_{n+1}`; substituting `E_m = G_m e_m` and cancelling units gives
`h_n e_n e_{n+1} ≡ (a_n e_n)^2 (mod d)`. Since `d | u_{n+1} | w_n = u_n − e_n`,
`u_n ≡ e_n (mod d)`, and `a_n u_n = v_n + w_n` gives `a_n e_n ≡ v_n (mod d)`. A
prime `p | d_n` dividing `v_n` would divide `a_n v_n = h_n v_{n+1}`, while
`p ∤ h_n` since `h_n | G_{n+1}` and `p ∤ v_{n+1}` since `p | u_{n+1}` and
`gcd(u_{n+1}, v_{n+1}) = 1`. ∎

**Theorem 26 (defect charge).** Call `n` a Legendre defect if
`(e_n e_{n+1} | p) = −1` for some prime `p | d_n`. Lemma 25 gives
`(h_n | p) = −1` at every such `p`, so `h_n > 1`, hence `G_{n+1} ≥ 2G_n` and the
defect indices below `N` number at most `log₂ C_N`, which is `o(N)` under (NV);
so `e_n e_{n+1}` is a quadratic residue modulo every prime dividing `d_n` at
density one. **Corollary 27.** If `|h_n e_n e_{n+1}|` is a perfect square and
`e_n e_{n+1} < 0`, then `−1` is a quadratic residue mod `d_n`, so every odd prime
factor of `d_n` is `≡ 1 (mod 4)` and `4 ∤ d_n`; that set has density zero.

**Evidence** ordinary proofs verified this pass, replayed exactly on 498
primitive frames from 60 canonical orbits: zero transport and unit-clause
failures, 465 Jacobi confirmations, 90 sign-change non-residue and 219 same-sign
residue confirmations, and 34 defect steps all with `h_n > 1` a non-residue.
**Relation** Lemma 25 strictly generalises the `R2CumulativePayment.md` statement
`−u_n u_{n+2} ≡ (a_n u_n)^2 (mod u_{n+1})`, which needs `h_n = h_{n+1} = 1`;
Theorem 26 sharpens R2's "one of the adjacent payments" to `h_n` alone and
replaces a density-zero bound by the explicit `log₂ C_N`; it is the second
landing mechanism `SlowNegativePartRigidity.md` section 7 records as missing.
**Not proved** anything from the landing form of the r04 hint, which is vacuous
since a landed `p` divides every later `E_m` (332 of 332 landed slots vacuous,
309 of 309 unlanded slots non-vacuous); as a standalone constraint the invariant
leaves `u^{1−o(1)}` admissible errors per step and admits walks with rises of
order `u`, and on the true orbit it is an identity, since `e_{n+1}` is already
determined by `v_n mod u_{n+1}`.

## 8. The good-prime wall and the supply diagnosis

**Theorem 28 (good-prime wall; desk S2).** Let `N ≤ T < τ` and let
`p_0, …, p_{B−1}` be distinct primes, each dividing `D_T`, none dividing `C_τ`.
Put `P = ∏p_r` and assume `C_T < P` and `2P + B ≤ C_τ`. Let `x ∈ [P, 2P)` be the
CRT block with `p_r | x + r` and `t = min{n > T : C_n ≥ x}`. Then `t ≤ τ`,
`C_{t−1} < x`, and `C_t ≥ x + B`, that is `−E_{t−1} > B` at height
`C_{t−1} < 2P`.

*Proof.* `C_τ ≥ 2P + B > x` and `τ > T` give `t ≤ τ`; minimality with
`C_T < P ≤ x` gives `C_{t−1} < x`. If `C_t < x + B` then `r := C_t − x ∈ [0, B)`
and `p_r | C_t`, while `p_r | D_T | D_t`, so `commonDivisor_persists` gives
`p_r | C_τ`, against the hypothesis. ∎

**Lemma 29 (badness is an up-set).** For `p | D_T`, `p | C_n` for some `n ≥ T`
implies `p | C_m` for every `m ≥ n`; so the primes of `D_T` the walk can reach
below a ceiling `τ` are exactly those dividing `C_τ`, their product divides
`gcd(C_τ, D_τ)`, and above `z_0` there are at most `log C_τ/log z_0` of them.
**Corollary 30 (unconditional dichotomy).** For any counterexample, any `T ≥ N`
and any distinct primes `p_0, …, p_{B−1} | D_T` with `P > C_T`: either some `p_r`
divides `C_n` for all large `n`, or there is `n` with `C_n < 2P` and `−E_n > B`.
The corpus kills the first branch by size; Lemma 29 kills it by count, which
works for primes of any size including `2`. **Corollary 31 (conditional).** If
for arbitrarily large `z` there is `T` with `C_T < z^{B/2}` such that `D_T` has
at least `3B + 3` prime divisors in `(√z, z]`, with
`B = ⌊(π(z) − π(√z) − 3)/3⌋`, then `limsup(−E_n)_+·log log C_n/log C_n ≥ 1`, a
gain of order `log C_n/(log log C_n)^2` over the unconditional log-log clause.

**The log-log constant is a modulus artefact.** Theorem 28 with `3B+3` comparable
primes and the corpus Theorem 3′ with `B` primes in `(B, z]` both reach
`log C_n/log log C_n` from the same supply, while Theorem 4 of
`SlowNegativePartRigidity.md` instantiates the block moduli as whole fresh
multipliers of size `exp(λ2^{n_r})`; one prime factor per fresh multiplier lowers
the wall by an exponential.

**Evidence** Theorem 28, Lemma 29 and Corollary 30 are ordinary proofs over
Lean-checked corpus rows, Corollary 31 is proved conditional on its supply
hypothesis, and the 24 engineered landings with zero counterexamples, the fixture
safety checks and the multiplier census are exact computations. **Relation**
Theorem 28 slots beside `slow_rise_landing_barrier` as the count-based way to
kill the landing branch, dropping every hypothesis about what follows the
crossing and applying to finite segments; it uses `D_T | D_n`, which fails in
primitive coordinates. **Not proved** the supply of Corollary 31: with whole fresh multipliers the
bad-set count is about `2^{B−1}` while only about `T + B` moduli exist, and `a_j`
prime for every `j` is consistent with every hypothesis, where Theorem 28
degrades to exactly `log₂ log₂ C_n`. The log-log scale is thus the worst case of
this barrier family over supplies, and no wall argument beats it without a lower
bound on the smooth part of the multipliers; the multiplier census (median
smallest prime factor 103 at 31 to 60 digits over 1,450 multipliers) is an
observation and not a lemma. Two no-gos: the literal landing-class hint is
vacuous, since exactly one integer of any block is reachable at every step of a
deterministic orbit; and the record-count budget adds nothing beyond
`m < C_t/K`, since all landing moduli divide `gcd(C_τ, D_τ)`.

## 9. Corrections to the returns

r01 prints `1/4` in (16) after discarding a completed square; the sharp constant
is `1/2 − 1/(16R)`, giving `7/16` at `R_n → 1`. r01 Case 2 uses
`h ≤ d − c − B` where its own display gives `h − 1 ≤ (d − c − B − 2)/P`, so the
Case 2 constant is `1 − o(1)` on geometrically growing `C_n`, and the moduli may
be any `B+1` pairwise-coprime divisors of `D_N` above `B+1`. r03 section 4
already proves the clean-step form of Theorem 6 once `w_n ≤ u_n + 2` is replaced
by `w_n ≤ (3/2)u_n`. r07 uses per-jump capacity `(d−2)_+` where the sharp value
is `⌊(d−1)/2⌋`. r08 calls the threshold `3` of Corollary 12 merely sufficient
where it is an exact transcription. In r04 Proposition 5 the block moduli must be
selected at fresh indices `≥ N`, repaired by `T = N + ⌈(1+ε)B⌉` with unchanged
counts; r04 Lemmas 2 and 3 rest on `commonDivisor_persists`,
`exists_consecutiveMultiples_between` and `slowRise_landing`, the new content
being the running-maximum clause, the record trigger and Propositions 5, 6, 8;
and Proposition 8 is asymptotic, the ratio `3.0` at `u = 4` being the `ℓ(4) = 1`
artefact. For `x^2+x+1` the certificate `(1,0,1)` mod 3 gives density `1/3` in
place of r06's `1/7`, and the minimal certificate modulus never exceeds 41 over
8,241 monic pairs where r06's construction reaches 919. r05's sieve needs the
first `k` primes, since `{3, 5, 17, 257}` has `∏(1 − 1/p) = 0.50001`, and
repairing its crossing threshold with Lemma 7 replaces the fixed period bound `L`
by `√(2u_r)/(6B)`.

## 10. Wave-2 phase-map and clean-rise desks, and the strong-form survey

**Result 10.1 (phase map; desk S3, ordinary proof plus exact probe).** On every clean step the congruence a_n^2 = e_(n+1) e_n^(-1) (mod u_(n+1)) is an identity. By Thue's lemma every unit modulo N is a ratio of two integers of absolute value at most sqrt(N), so the statement "the multiplier is resonant" carries no information whenever 2|e_n e_(n+1)| >= u_(n+1); on the measured orbits this is 77 percent of clean steps. Where it carries information it says that |e_n| is a continued-fraction denominator of a_n^2/u_(n+1) whose successor partial quotient is about u_(n+1)/|e_n e_(n+1)|. Survival at a clean step is therefore a large-partial-quotient event of that size. Unconditionally gcd(e_n, u_(n+1)) = 1. The resonance data is unique up to sign and imposes no compatibility between consecutive steps. The burn identity of Section 1 is circular with its envelope hypothesis, so the rounding theorem is strictly conditional. Evidence: scripts/erdos243_phase_map_resonance_probe.py, 18,774 orbits, 78,098 steps, 0 failures. Not proved: any frequency statement about the partial quotients of a_n^2/u_(n+1) along an orbit.

**Result 10.2 (cost of a clean rise; desk S4, ordinary proof plus exact fixtures).** The cancellation-free family with E = -1 extends to E = -m for every m: heights c_n = c + n m, invariant D_n = (a_n - 1) c_n - m, multipliers a_n = 1 + c_(n+1) k_n with k_0 = lambda prod_(j=2)^(H+1) c_j. For every m >= 3 and every H this gives exact orbits with H consecutive clean rises of size m, zero payment, and normalised error m/c as small as desired; the smallest instance (C_0, D_0) = (10, 21735997) has seven consecutive (e, h) = (-3, 1) steps, and the family is verified to H = 40 at c = 100003. The payment budget satisfies sum_(n<N) log h_n <= log C_N = o(N), so a charge per clean rise bounds the number of clean rises of size at least three below N only by O(log C_N). No clean step is a Legendre defect, because Theorem 7.2 forces h_n > 1 at a defect. Evidence: scripts/erdos243_clean_rise_cost_probe.py. Consequence: the implication named in Section 3 as the single missing ingredient (a lower bound on the cancellation cost of a large clean rise) is false as stated; a closing argument needs either many more than log C_N such rises or a charge that scales with the remaining budget.

**Result 10.3 (strong-form survey; finite computation only).** Conjecture: the nearest-integer pseudo-greedy expansion of every rational terminates. This implies Erdos #243. Over 127,638,150 orbits (every p/q with q <= 20000, random q to 1e16, the tie-flipped rule, improper x_0 > 1, and the corpus family (11, 11(33+79833600k)-1) for k < 20000) no orbit failed to reach E = 0 and none hit the computational horizon. The longest orbit has 32 steps; the extremal family member k = 5386 has 34 steps with a negative run of length 31. At 48-bit q the law of E_n/C_n is uniform on [-1/2, 1/2) to four digits, and absorption at height C correlates with the number of divisors of C (correlation 0.894 in logarithms), which is the cumulative-LCM transfer observed as a rate. Scripts: scripts/erdos243_orbit_engine.py, erdos243_strong_termination_survey.py, erdos243_primitive_residue_lab.py, erdos243_rate_hypothesis_stress.py, all with --quick. Not proved: anything; this is evidence for a conjecture strictly stronger than the target.

**Lean status of Sections 1 to 3.** PrimitiveRecordBarrier.lean kernel-checks the valuation-no-drop lemma, protected prime-power persistence, the odd record cut, and the composed consumer recordRiseTwo_sylvesterNext_eventually with the prime-power supply as an explicit hypothesis. IntegerRoundingBarrier.lean kernel-checks the periodic quadratic inequality, the pointwise phase bound in the sharp form with no ratio hypothesis, the division-free linear barrier and its rise corollary, and the counter-model shifted_negativeRelativeMass_consumer_false showing that the B-shifted summability consumer of Section 2 is not a state-system theorem: C_n = B n + 1, E_n = -B satisfies every division-free hypothesis with zero shifted mass and never terminates, so Section 2 holds only on the canonical orbit through its arithmetic dichotomy. Both modules build through the owner route with exit code 0 (2026-09-05).

## 11. Remaining implication

A counterexample must satisfy all of the following at once.

1. **Primitive clean record jumps of size at least three, infinitely often.** By
   Theorem 6 and Corollary 11, `#{n : h_n = 1 and e_n ≤ −3} = ∞`, and every
   sufficiently late odd protected source is crossed by a record-setting jump of
   size at least three; strict rises are cancellation-free under centring.
2. **Record increments strictly above the log-log scale.** By Theorem 13 and
   Corollary 14, `limsup(H_{n+1} − H_n)/ℓ(H_n) ≥ g∏_{p∈P}(1 − 1/p)^{-1} > 1`
   strictly, hence `limsup(−E_n)_+/ℓ(C_n) > 1` strictly.
3. **Divergent B-shifted excess mass for every fixed B.** By Theorem 5,
   `∑_n(−E_n − B)_+/C_n = ∞` for every integer `B ≥ 0`.
4. **No polynomial profile.** By Theorems 18, 19, 20 and Corollary 21, `C_n`
   agrees with no eventual quadratic of normalised leading coefficient `1` or
   `2`, no rational multiple of an integer quadratic admitting a forbidden block,
   and no polynomial with a root modulo almost every prime, and `E_n` follows no
   linear template `−sn + β` for `1 ≤ s ≤ 7`.
5. **Rises of order log C/log log C once the multipliers have enough prime
   factors.** By Corollaries 30 and 31, `3B+3` distinct prime divisors of `D_T`
   in `(√z, z]` with `C_T < z^{B/2}` force `−E_n > B` below height `2z^B`, and
   `B ≍ log C/log log C` forces rises of that order.
6. **Fine-structure conditions.** `h_n e_n e_{n+1} ≡ v_n^2 (mod d_n)` at every
   step, with the residue clause of Theorem 26 at all but `log₂ C_N` indices
   below `N`, and the height dichotomy of Theorem 23.

The problem is now equivalent to excluding cofinally many clean primitive record
jumps of size at least three. The single implication that would close it from
this batch is a lower bound on the cancellation cost of a large record jump, or
an upper bound on record jumps. A large clean rise costs nothing in `G_n` by
definition, so the attack falls on `v_{n+1} = a_n v_n`: every prime power of a
fresh `a_n` enters `v_{n+1}` and becomes a new protected source, so each clean
record jump manufactures the source that demands the next one. Making that
self-reproduction contradictory is the route this batch has not taken.

## 12. Receipts

Checkers under `ErdosProblems/Erdos243/scripts/`, stdlib only, exact arithmetic,
one JSON status line with `evidence_class`, `--quick` on each:
`check_erdos243_integer_rounding_barrier.py` (section 1),
`check_erdos243_record_two_unit_barrier.py` (section 3),
`check_erdos243_record_excess_dichotomy.py` (section 4),
`check_feedback_word_realizability.py` (section 5),
`erdos243_legendre_locking_probe.py` (section 7),
`erdos243_good_prime_wall_probe.py` (section 8). Invoke with
`./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/scripts/<name> --quick`.

Section 1: the envelope identities hold exactly (398 quick, 1,998 full, zero
failures); the exact integer floor orbit from `N = 100` with `C_N/F_N = 21/20`
engages the barrier at `n = 227` with `M = 6`, and `X_k ≤ 6k`,
`X_{k+1} − X_k ≤ 6` hold to the end with `X_T/T = 5.9862` quick and `5.9982`
full; (15) and the sharp (16) each have minimum slack exactly `0`, the printed
constant `1/4` leaving `1/8`.

Section 3: over the r07 range (4,325 states, 6,928 state-prime combinations, 386
valuation drops, 346 erasures) and the wider range (14,515 states, 25,459
combinations, 1,277 drops, 1,127 erasures) the valuation identity and both
thresholds hold with zero failures; the odd cut has zero violations over 57,730
quick and 430,644 full triples; the fixture families and both instances reproduce
exactly. Lean authority `PrimitiveRecordBarrier.lean` with
`primitive_valuation_no_drop`, `protectedPrimePower_persists`, `odd_record_cut`,
`exists_oddMultiple_trapHeight`, `numerator_bounded_of_oddPrimePower`,
`centeredZero_forces_unit`, `sylvesterStep_of_centeredZero_pair`,
`recordRiseTwo_sylvesterNext_eventually`; kernel receipt `lake env lean`, rc 0,
22 seconds, 0 errors, axiom audit clean.

Section 4: identities (13), (31), (32) hold exactly on 4 orbits quick and 9 full
with the Lipschitz bound of (32) everywhere; the `B = 20`, `R = 6` CRT
reconstruction equals the quoted `521026757646` and excludes all twenty
positions; the Fermat product identity, the recurrence
`m_{j+1} = m_j^2 − 2m_j + 2`, and the maximal gap ratio `1.8116` at `u ≥ 1000`
against `σ^{-1} = 2` all hold.
