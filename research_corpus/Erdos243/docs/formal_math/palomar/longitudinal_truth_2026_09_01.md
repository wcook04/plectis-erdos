# Longitudinal truth: how far up each hill the corpus actually is, 2026-09-01

Second discovery pass, one agent per problem, each reading the cockpit, the problem directory,
the papers and patches, and the entry surfaces, with declaration statements read but no proof
bodies and no builds. This document is the synthesis; the per-problem reports are in the session
transcript (`22e9a3b6`). It corrects two rows of `situation_map_2026_09_01.md` (section 6 below).

The operator's question was longitudinal: not "what is proved" but "how far up the hill, and what
would a number theorist in this area find surprising". Equivalences are recorded and deprioritised.

## 1. The one-line truth per problem

| Problem | Furthest genuine advance | Class | Longitudinal? |
|---|---|---|---|
| #257 | Every infinite `A` with `Σ 1/a < ∞`, every integer base `b ≥ 2`: `Σ_{a∈A} 1/(b^a−1)` is irrational. Erdős 1968 printed the pairwise-coprime theorem for every `t ≥ 2` and stated coprimality is superfluous without printing it; the climb is removing coprimality, and the base generality is his. | Lean, public | **Yes** |
| #243 | Any counterexample has canonical centred errors negative infinitely often, unbounded along negatives, with divergent normalised negative mass (bounded-negative rigidity, arithmetic past the `1/n` rate wall, composed with Koizumi's bridge). | Lean state theorem + paper bridge | **Yes** |
| #1041 | Sharp constant 2 in every degree `n ≥ 3` under one critical-spectrum inequality (`S = 4`, `3` for `n ≥ 4`, `2` for `n ≥ 6`, sharp since `C(5,2) > 1`); plus the unconditional constant-factor `(71/10) μ^{1/n}` bound for every polynomial. | Paper proofs + Lean kernel; untracked in git | **Yes** |
| #68 | None. Finite exclusions `q ∤ 299999!` and `q > 10^12039`; the target shrunk to a summable window (`O(m^-2)`), never entered through 22,000. | Lean equivalences + computation | No |
| #249 | None. Rationality forces a tempered carry of dyadic rank `≥ 2^e−1` against the proved kernel rank `2^e+1`; `q > 10^12039`. | Lean necessary conditions + computation | No |
| #251 | None. Rational-tail normal form pinned to one located obstruction; explicit countermodel closing gap-profile arguments; `q > 10^12041`. | Lean + computation | No |
| #269 | None. Two-branch reduction on the actual orbit (`B = 1` corner decidable per index, refuted to 6000; `B > 1` corner a lattice statement, certified to `10^105`); `q > 10^6768`. | Lean + computation | No |
| #1049 | None, and one negative structural step: the homogenisation ceiling shows every content lane on the fixed diagonal is capped at `a > b^2`, so the two uncapped lanes are named. | Paper + computation | No |

Three of eight problems carry a real climb. Five carry the sharpest known reduction plus a
finite exclusion, and their agents said so without hedging. Nothing is closable from what is on
disk; every agent located the real obstacle and cited where the corpus already recorded it.

## 2. The holy-shit tier

Results a specialist would stop on, across problems, with public status.

1. **#257 reciprocal-summable irrationality with no coprimality hypothesis, every integer base.** Public, canary passed. Prior art (audit 2026-09-02, `prior_art_adjudication_2026_09_02.md`): Erdős 1968 printed the coprime case for every base and stated the extension; matched to his statement, strictly stronger than his printed theorem.
2. **#1041 critical-value separation with exact thresholds `4/3/2`**, a sufficient condition for the sharp constant in every degree, by a short covering plus Pólya area–capacity argument. Not public; the entry directory and its Lean source are **untracked in git**.
3. **#1041 `(S)_n` for `n ≤ 5`**, the arithmetic-mean strengthening of Schur–Fekete with equality on `(z−τ)^n − λ`, via a psh reduction to the root torus and `FP_4`. Paper only; may be classical.
4. **#249 explicit rational basis of the totient 2-kernel, rank exactly `2^e+1`.** Lean, reserve, public nowhere. Non-`k`-regularity of `φ` for every `k ≥ 2` is Coons 2010 (JTNB 22, Thm 3.2), strictly stronger than any `k = 2` corollary, and no Lean declaration in the package claims non-regularity; the explicit basis and exact rank have no located antecedent (audit 2026-09-02).
5. **#249 all-rung strict log-concavity `Θ_r Θ_{r+2} < Θ_{r+1}^2`** of the signed Möbius–Mersenne ladder, killing any nonnegative Stieltjes representation. Lean, no entry at all.
6. **#269 kernel rank phase transition**: two generators give an outer product (every 2×2 minor zero), three give nonsingular minors of every order uniformly in the third layer; the single binary carry is the whole difference. Lean, half public. The running-LCM identity for every `k` and the two-prime factorisation with transcendence via Hecke–Mahler are Steve Fan's (erdosproblems.com/269, 26 June 2026); the rank statements are the addition (audit 2026-09-02).
7. **#1049 sharp all-rank Hankel order `N(N−1)(2N−1)/6`** with leading coefficient `(N!)^2(N+1)!/2^N` in Zudilin's construction, where the antecedent proves only `≥`. The antecedent is Zudilin 2016 (Res. Number Theory 2, Art. 15, §4), not Zudilin 2004. Exactness is verified by exact computation for `N ≤ 7`; general `N` is ordinary mathematics, partly formalised. Paper, row 1 in Lean; the launched entry ships row 1 only.
8. **#243 bounded-negative rigidity and the CRT bounded-rise barrier** as a standalone integer statement. Lean, reserve.
9. **#68 companion-orbit boundary**: `S ∈ ℚ ⟺ ⌊m! C⌋ ≡ −2 (mod m)` for all large `m`, with `C = Σ 1/(n!(n!−1))`; the generic form holds for every `x + (e−2)`, so for Erdős's whole family `Σ 1/(n!+t)` after a sign adjustment. Lean, **uncommitted** (`CompanionOrbitRationality.lean`, +458 lines).
10. **#257 exact `1/21` fatal-branch dichotomy** with forced affine normal form; and the general rational membership criterion. Lean, reserve.

## 3. What is half-formed and closable in hours to days

Ordered by value per hour. Each is a specific artefact.

| Problem | Item | Closes it | Size |
|---|---|---|---|
| #1041 | Separation theorem: commit the untracked entry and source, apply the patch, launch | scoped commit + patch + replay | hours |
| #68 | `CompanionOrbitRationality.lean` +458 uncommitted; the reserve Solution transports declarations that do not exist at HEAD | scoped commit + focused build | hours |
| #68 | Unconditional constant-only miss certificate: prove `scaledPrefixFrac m = m!·C − δ_m`, `0 < δ_m < 1` for `m ≥ 4` | a geometric-ratio lemma | hours |
| #249 | `FullDepthRayAmplifier` landed in Lean, packaged, in zero packet rows; replay was blocked at 5.7 GB free, disk is now 21 GiB | packet row + replay + launch | hours |
| #251 | Free-pair reduction to Lean: the pieces (`tailShift_integral_iff_orderOf_dvd`, `exists_odd_den_state`) exist; a named corollary and the equivalence `Irr ⟺ (P)` are missing | ~50 lines | hours |
| #251 | Countermodel series value `= 32` as a `tsum` theorem (currently a Python receipt) | ratio bound `25/32` is in the note | hours |
| #269 | Cubic width `X_m ≤ 40(m+4)^3`, which the `IntegralBranchWidth.lean` docstring already claims and the file does not contain | poly-geometric tsum bound | hours to a day |
| #269 | Telescope `Σ_p (p−1) Σ_n 1/H(p^n) = 1` in Lean | one-line difference identity | hours |
| #257 | The `1/3` certificate lemma (iteration 44) in Lean: pure inequality chain; finite certificates then decide each `(A, r)` | ~200 lines | hours to a day |
| #1049 | Casoratian closed form and telescoping in Lean; then the gcd cap `≤ 2j log 3` | rational algebra | a day |
| #1049 | Power-certificate compiler is Lean-checked and in the public source but not in the entry's comparator | one comparator line | trivial |
| #243 | Koizumi bridge in Lean so bounded-negative rigidity becomes a theorem about #243 itself with one added hypothesis | pseudo-greedy expansion + Lemma 15 + Cor. 10 | days |
| #257 | Iteration-45 positive-density point in Lean: the splitting lemma is elementary, the Borwein irrationality-measure input can be a hypothesis | hundreds of lines | days |
| #1041 | `FP_5` with a directed-rounding certificate (currently IEEE double); then `(S)_6` | re-run MOD rigorously | a day |

## 4. Can anything be closed, and what has not been tried

No problem is closable from disk. The untried attacks the agents extracted from the corpus's own
structure, in order of expected payoff:

- **#1049: the `0.40568…` contour.** Demoted to a hypothesis at `1bdd16b600` because no derivation was on disk. On 2026-09-02 a reconstruction landed as `ErdosProblems/Erdos1049/ZudilinRationalHomogenisationDerivation.md` with probes `formal_math/probes/erdos1049_zudilin_*.py`: the constant is exactly `C_0/C_1 = 1/μ` where `μ = 2.46497868…` is the irrationality-exponent bound of Zudilin 2004 Theorem 1 (direction `(14,12,14;27)`, `m = 15`; `C_1 = 1091/2`, `C_0 = 266 − (3/π²)(225 − J)`), and the rational-base homogenisation consumes only Zudilin's Lemma 7 and Lemma 2, with the forms reconstructed exactly for `n ≤ 3`. An independent adversarial pass the same day attacked seven points (Lemma 7 as printed in `Z[p]`, degree bookkeeping, the Archimedean side, nonvanishing, the conclusion, consistency with Bézivin–Borwein and Bundschuh–Väänänen, hidden integer-base use) and broke none; receipts in `state/formal_math/erdos257_period_noncollapse/erdos1049_contour_adversary/`. So `F(31/4)` and every `F((31/4)^r)` are irrational (`log 4/log 31 = 0.4037`, outside Bundschuh–Väänänen's `0.3987`) at evidence class: authored theorem conditional on Zudilin 2004 Lemma 7 and Lemma 2, not kernel-checked, not published, priority unsearched beyond Bundschuh–Väänänen. This moves #1049 from "no climb" to a conditional climb: a new irrational base. Next: Lean for the finite part (`θ* > 81/200` from finite `ψ'` sums) and a paper section with the exact lemma dependence.
- **#1041 degree 5**: combine the separation theorem with the hub reduction `min_c L(c) ≤ 2`; in degree `≥ 7` the parent reduces to a compact cluster regime, and a cluster-resolved cover through the same area–capacity estimate is the natural next step. Weeks.
- **#257**: push the iteration-45 splitting lemma from a point to a class (every `A` whose even part is cofinite in `2ℕ` and whose odd part is Liouville-tailed), the only route that stacks the all-base theorem on the divergent region; and an Erdős-1948-style parity argument on `τ_A` restricted to residue classes, the `(★)` target nobody has attempted.
- **#68**: the odd-index parity cutoff (no odd `D_m = −1` after 23 through 300,000) is the one unexplained finite pattern with a Lean-checked closing consumer; a Type B ask.
- **#249**: run the Balasubramanian–Giri–Srivastav shifted correlation through the first-harmonic pivot; or treat `Θ_2` as the Möbius-weighted Duverney–Tachiya Lambert series and test whether their Padé construction survives a bounded non-periodic weight.
- **#251**: exploit state compression directly: under rationality one tail value recurs `≫ X/log X` times in `(X, 2X]` on a finite state space, and the hitting index `M` is free.
- **#269**: `KERNEL-STAR` as a computational construction; conditioning the fibre function on shell phase to push the wall `1.5326` below the observed `1.541`.
- **#243**: feed Erdős–Straus's own LCM prefactor into the LCM-state route as the unbounded-case supply; run the cascade on a second seed family.

## 5. Papers: three copies disagree on four problems

Every agent found the same shape. The papers live in the **retired** repository
`wcook04/plectis-lean-erdos249-257` (and its microcosm mirror), not in the release repository;
the seven `.patch` files target that retired base and some fail to apply; for #68, #243, #251,
#269 there are two or three divergent copies; the microcosm mirror serves the older text. No
paper leads with its longitudinal point except #257. The release repository has no `paper/`
directory at all. Specific stale claims: #249 abstract's `7.96×10^34` versus `10^12039`; #249
`prob:fulldepth` calls a producer merely sufficient when Lean now has the equivalence; #269
`prob:bridge269` is listed open and is closed by Lean; #1041's tex omits the degree-three
theorem, the separation theorem, the area constant, and cites three entry directories that do not
exist; #68's working-tree revision leads with an equivalence against the framing rule.

## 6. Corrections to `situation_map_2026_09_01.md`

- **§4 row for #68 was wrong.** `3t^3 < 2(R+1)` at `t ≥ 2^32` is the *stronger* constant; `t^3 < 8(R+1)` at `t ≥ 4096` is weaker and already consumed by the shipped little-o theorem. The unshipped complement is the method's own ceiling `sharp_radius_satisfies_square_log_constraint`.
- **§6 for #1049 was wrong.** "Step 1 closed" is conditional on the all-level monodromy premise `(M)/(C5)`, certified only at `N ≤ 3`; the packet's own statement field is stale in the unconditional form.
- **§8 for #1041**: `STRONGEST_RESULTS.json` does not exist and never did; `FRONTIER.md` warns readers off a phantom.
- **#251 constants**: `10^602` and `10^12041` are both real packet rows; the second supersedes the first. Never publish `10^602`.

## 7. Hygiene found by every agent

- Uncommitted or untracked strongest results: `Erdos68/CompanionOrbitRationality.lean` (+458), `ExternalVerification1041FirstMergeCriticalValueSeparation/` and its source module, `AllScaleLattice`'s seven foreign edits, the foreign `AdelicHeightBridge.lean` row-2 probe (which is correct: `3^2·4/2 = 18`).
- Metadata self-contradictions: `68StrictSuccessorCarry` README says signal 20, its yaml says 98 "summit" for an equivalence; `MovingFactorScaleSplit` 28 vs 84; every launched entry's private `palomar_qualification` block still reads pre-submission.
- Docstrings that overclaim: `IntegralBranchWidth.lean` (width bound absent), `PurePowerIrrationality.lean` (conditional criteria only), `PeriodMultipleEscape.lean` header ("not known necessary" after the equivalence landed).
- Three conventions for the #269 value coexist; the packet's `claim_ceiling` quotes stale partial-quotient counts.
- Fifteen `Totient*.lean` modules are #249 mathematics filed under the #257 namespace, including the strongest #249 theorem. Filing, not mathematics; leave the names.
- Shared machinery filed under one problem: the certified continued-fraction engine (#68/#249/#251), the bounded-radix dichotomy (#269, belongs in `Shared/`), the companion-orbit theorem (#68, applies to `Σ 1/(n!+t)`).

## 8. The continuous workflow, designed and not run

Four lanes, each a bounded loop over a work list drawn from this document, run as serial
workers under launchd with sentinels, never as harness-owned background jobs.

| Lane | Input | Unit of work | Model | Stop |
|---|---|---|---|---|
| Promotion | reserve directories in `situation_map` §3 and §9 | full-strength abstract under the claim contract, add to `launch_core`, re-export, push, submit | sonnet for abstracts, the exporter and drain for the rest | typed hold reason or Palomar failure |
| Hygiene | section 7 above | one scoped commit per item, with the docstring or metadata made true | sonnet | list empty |
| Formalisation | section 3 above, hours-scale items first | one Lean theorem per unit, focused build under the governed wrapper, then packet row and entry | fable | build red twice on the same unit |
| Attack | section 4 above | one probe per unit with a stated falsifier, recorded in the problem's lab and packet | fable, and Type B for the two research asks | falsifier fires or a week elapses |

Rules the evening taught: builds only through `lean_fast_build.py`, the replay only through the
governed wrapper, jobs only under `launchctl submit` with `exit 0` drivers, one Palomar submission
verifying at a time, registration always shown to the operator. The papers are rebuilt from the
release repository once the promotion lane has moved the entries, never before.

## Evidence boundary

Statements read as source, not rebuilt; every "Lean" above repeats an entry's or packet's own
validation claim except the nineteen launch entries, which built and replayed today. erdosproblems.com
was fetched live for #243, #251, #269 and read from annex snapshots or the papers' transcription for
the rest. Prior-art boundaries carried from earlier audits and not re-verified tonight.
