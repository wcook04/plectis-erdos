# The residue-class invariants of `1 * (-)`: recoverable, and provably useless

Script: `scripts/divisor_transform_recovery.py`
Receipt: `state/formal_math/erdos257_period_noncollapse/divisor_transform_recovery_receipt.json`
Answers: `docs/formal_math/erdos257_computational_exhaustion_map_2026_08_22.md` section AK

## 0. The question this answers

Section AJ of the exhaustion map states the unifying law:

> `tau_A = 1 * 1_A` **preserves** periodicity and boundedness (`sum_{d in A} 1/d < infty`);
> **destroys** complexity entirely.
> A counterexample must have positive density (hence unbounded `tau_A`) and be
> aperiodic, so it has neither preserved property.

Section AK then asks whether there is a **third** invariant of the transform that
no transcendence mechanism has used — "which statistics of `A` are invariants of
`tau_A` beyond density and periodicity".

This note answers that for the most natural candidate. The candidate is real, the
recovery is verified, and **it is not a third invariant, and could not have been
one.**

## 1. A CLOSED lane, recorded first

Rationality of `y = p/q` makes `{2^N y}` purely periodic with period
`ell = ord_q(2)`, which suggested cycle-averaging the carry recursion
`D_N = 2 D_{N-1} + t_N - tau_A(N)` around the residue cycle to collide bounded
`t` against divergent `taubar`. The resulting identity

    Dbar_j (2^ell - 1) = sum_{i=1..ell} 2^(ell-i) (taubar_{j+i} - t_{j+i})

is **a tautology**, not a constraint. With `R_N = sum_k tau_A(N+k) 2^-k`,
splitting `k = i + m*ell` gives

    Rbar_j = sum_{k>=1} 2^-k taubar_{j+k}
           = sum_{i=1..ell} taubar_{j+i} 2^-i * (1 - 2^-ell)^-1
           = (2^ell - 1)^-1 sum_{i=1..ell} 2^(ell-i) taubar_{j+i}

and `theta_j = sum_k t_{j+k} 2^-k` is the matching binary expansion of `{2^j y}`,
so `Dbar_j = Rbar_j - theta_j` reproduces the identity term for term. Both sides
diverge at the same rate. **Do not re-derive this.**

## 2. What IS recoverable [COMPUTED, verified]

Fix any modulus `ell`. The residue-class means of `tau_A` satisfy

    taubar_j := lim (ell/x) sum_{N <= x, N = j mod ell} tau_A(N)
              = sum_{g | ell, g | j} g * H_g(A),    H_g = sum_{a in A, gcd(a,ell)=g} 1/a

so `taubar_j` depends on `j` only through `d = gcd(j, ell)`. Writing `F_d` for that
common value, the system is triangular over the divisor lattice and inverts:

    d * H_d(A) = sum_{g | d} mu(d/g) F_g                              (RECOVERY)

**Verified.** Eight families, `X = 600000`, support cut at `amax = X/500`, worst
relative recovery error `7.97e-03`:

| family | `ell` | max rel. error |
|---|---|---|
| all naturals | 12 | 2.26e-03 |
| evens | 12 | 1.10e-03 |
| coprime to 12 | 12 | 4.06e-03 |
| AP `5 mod 12` (periodic) | 12 | 1.20e-03 |
| squares (summable) | 12 | 5.13e-04 |
| aperiodic density-½ | 12 | 1.10e-03 |
| all naturals | 16 | 3.24e-03 |
| odds | 16 | 7.97e-03 |

The families deliberately span both preserved properties **and neither**, so the
recovery is not an artifact of periodicity or summability.

*Measurement trap, recorded because it fired.* A first run reported
`RECOVERY FAILED` at 2–55%. That was truncation, not mathematics: `taubar_j` over
`N <= X` credits each `a` a count `~ (X/a)(g/ell)`, but `H_g` truncated at `X`
credits every `a <= X` its full `1/a`, and for `a` near `X` the true count is 0 or
1. The tell was that the *summable* family had by far the smallest error. The
support cutoff must be separated from the averaging window (`amax << X`); the
script now enforces this and documents why.

## 3. VERDICT — negative, and structurally so

Two reasons this cannot be the third invariant section AK is looking for.

**(a) It is density, refined.** For `A` of positive density, `H_g / log X` tends to
the relative density of `{a in A : gcd(a, ell) = g}`. So what the transform
preserves here is the *density vector of `A` along a finite partition into
residue classes* — a refinement of a property the law already names, not a new
kind. Consistent with section AI: `tau_A`'s complexity is a function of density
alone, and this says the recoverable refinement is still densities.

**(b) It is finite-dimensional, so it can never obstruct.** For any modulus `ell`
the recovered data is `d(ell)` real numbers. A counterexample support is an
infinite-dimensional object, and finitely many real constraints cannot exclude
it — for any prescribed vector `(H_g)_{g | ell}` one can build `A` realising it.
Choosing `q` so that `ell = ord_q(2)` is highly composite raises the dimension but
keeps it finite, and the adversary chooses `q`.

**Consequence for iteration 10.** The transform's kernel should not be probed for
*finite-dimensional* invariants at all; any such family is excluded by (b) before
it is measured. Only an invariant carrying infinitely many independent
constraints on `A` — one per scale, or one per prime — could obstruct. That is a
sharper target than "beyond density and periodicity", and it rules out the whole
residue-class family in one step.

## 4. Not a claim about Erdos 257

Nothing here is progress on 257. It closes one lane (section 1) and eliminates one
candidate class for section AK (section 3). Both are offered to the exhaustion
map's owner; `ProgrammeSpine.md` and the exhaustion map were not modified.

## 5. CORRECTION to section AK's premise — the transform has NO kernel [COMPUTED]

Section AK proposes that iteration 10 "measures the transform's kernel: how much
of `A` can be reconstructed from `tau_A` truncated to `[1,M]`". That measurement
has an exact answer, available in one line, and it is **all of it**.

`tau_A = 1 * 1_A` is Dirichlet convolution with the unit `1`, whose Dirichlet
inverse is the Mobius function. Hence

    1_A = mu * tau_A,      i.e.   1_A(N) = sum_{d | N} mu(d) tau_A(N/d)

and the reconstruction of `A ∩ [1, M]` from `tau_A|[1,M]` is **exact for every
`a <= M`**. The transform is a bijection on arithmetic functions; its kernel is
trivial.

**Verified**, `M = 200000`, mismatches over all `N` in `[1, M]`:

| support | `|A|` | mismatches |
|---|---|---|
| aperiodic density-½ (random) | 100121 | 0 |
| Sturmian `1/phi` | 123607 | 0 |
| all naturals | 200000 | 0 |
| squares | 447 | 0 |

### What section AI actually measured, then

Section AI is not contradicted — the subword complexity of `tau_A` really is a
function of density alone, and its controls fired. But complexity is a *statistic*,
not information content. The two coexist because the inverse is **nonlocal**:
recovering `1_A(N)` needs `tau_A` at every divisor of `N`, and those range over
all of `[1, N]`. Subword complexity is a bounded-window statistic. So:

> The transform destroys no information. It destroys **locality**.

### The sharpened question

This replaces section AK's question with a strictly better one. Not

  *which functionals of `1_A` survive the transform* — all of them do —

but

  *which functionals of `1_A` are computable from **bounded windows** of `tau_A`.*

That is the real obstruction, and it explains section AJ's law -- in the REVISED
form section AM landed after this note was drafted:

    tau_A preserves:  PERIODICITY -- and nothing else non-trivial
          destroys:   complexity, and boundedness is not an independent
                      invariant (<=> finiteness)

The locality reading **predicts that revision**. Periodicity is the one property
readable from a bounded window, so under the locality account it should be the
sole survivor -- which is what section AM concluded independently, from section
AL (`tau_A` is unbounded for every infinite `A`, so the boundedness bullet was
never an independent lever). Complexity is not locally readable, which is why it
appeared to be "destroyed". Two routes, one single-survivor law.

*Provenance:* sections 0-4 were written against section AJ's original two-property
statement; only this paragraph is written against the revised one. Where they
disagree, section AM governs, and section 3(a)'s phrase "a property the law
already names" should be read as naming density, not boundedness.

Combined with section 3(b) above, iteration 10's search space narrows twice: skip
finite-dimensional invariants (cannot obstruct), and skip kernel measurement
(the kernel is trivial). What is left is the locality question.

## 6. The locality bound, made quantitative [PROVED + VERIFIED]

Section 5 said the transform destroys locality rather than information. That was
qualitative. Here is the sharp form, and it is an indistinguishability bound, so
it constrains every recovery rule rather than just the Mobius formula.

**Proposition.** Let `N` be composite, `p` its least prime factor, and
`m = N/p >= sqrt(N)` its largest proper divisor. Then `1_A(N)` is **not
determined** by `tau_A` restricted to any window `[N-w, N+w]` with `w < m`.

*Proof.* Let `A` contain `m` but not `N`, and let `A'` contain `N` but not `m`,
agreeing with `A` elsewhere. Then

    tau_{A'}(K) - tau_A(K) = [N | K] - [m | K].

Inside the window the only multiple of `N` is `N` itself, and the only multiple
of `m` is also `N` itself, since the neighbouring multiples `N +- m` lie at
distance `m > w`. The two changes therefore cancel at every window position, so
`tau_A = tau_{A'}` on the window while `1_A(N) != 1_{A'}(N)`. QED

For `N` prime the reverse holds: `1_A(N) = tau_A(N) - tau_A(1)`, radius 0 plus a
single global value.

**Verified**, `scripts/tau_locality_lower_bound.py`, receipt
`state/formal_math/erdos257_period_noncollapse/tau_locality_lower_bound_receipt.json`:
14 composite flip pairs (`N` from 12 to 1024, covering prime powers `2^k`, `3^k`,
`p^2`, and squarefree `2*3*5*7`) all give identical `tau` across the full window
of radius `m-1` with the indicator differing; 8 prime controls all recover
correctly at radius 0. `ALL CHECKS PASSED: True`.

### What it eliminates

Because it is an indistinguishability bound, no recovery rule of any kind can
beat it. Hence:

> Any mechanism that reads `tau_A` through **bounded windows** can access `A`
> only at the **primes**.

Subword complexity, local automaticity, `k`-block frequencies, transducer and
finite-automaton models, and sliding-window statistics are all bounded-window
functionals, so the whole class is eliminated at once for everything except
`A ∩ P`.

This *explains* the exhaustion map's revised single-survivor law (section AM,
"`tau_A` preserves PERIODICITY and nothing else non-trivial") rather than
restating it: periodicity is exactly the property a bounded window can read, and
complexity is exactly the one it cannot. Two independent routes, one law.

**Nonclaim.** Not progress on 257. It closes a class of attacks, which is the
only thing claimed.

## 7. T13a FAILS the sign-flip falsifier -- it eliminates mechanisms, it cannot prove 257

`ProgrammeSpine.md` section 16 supplies a mechanical falsifier:

> Any candidate argument that would also prove the `+1` case is wrong.

because for the `+1` family `1/(2^d + 1)` the 257 analogue is FALSE, with explicit
witness `1/7` (section 15). Section 16 then sets the target: "whichever of `Q_n`,
`Psi_n`, `tau_A`, or the lcm ladder `D_n` behaves differently between `a = +1` and
`a = -1` is the only place a proof of 257 can live."

Section 6's bound lives in the `tau_A` coordinate, so it must be audited. **It
fails the audit.**

### The audit

The `+1` family replaces `tau_A = 1 * 1_A` with `sigma_A = lambda * 1_A`, where
`lambda(m) = (-1)^(m-1)`, since `1/(2^d + 1) = sum_j (-1)^(j-1) 2^(-jd)`.

Flipping `1_A` at `N` and at a proper divisor `d > w` changes the window value at
`K = N` by `eps_N * lambda(1) + eps_d * lambda(N/d)`. So cancellation needs

    eps_d = - eps_N * lambda(1) / lambda(N/d)

which is solvable whenever `lambda(N/d) = +- lambda(1)`. For `lambda = 1` the
compensator runs OPPOSITE to `N`; for `lambda(m) = (-1)^(m-1)` it runs opposite
when `N/d` is odd and WITH `N` when `N/d` is even. Either way it exists.

**Measured**, both flip directions, both families, `d = N/p_min`, window radius
`d - 1`:

| N | parity | `-1` opp | `-1` same | `+1` opp | `+1` same | blind in `+1`? |
|---|---|---|---|---|---|---|
| 9, 15, 21, 25, 49, 81 | odd | True | False | True | False | **yes** |
| 12, 16, 30, 64, 100, 128, 256, 1024 | even | True | False | False | True | **yes** |

Both families are locally blind at **every** composite `N`, at the **same** radius
`m = N/p_min`. Only which direction cancels differs, and that is just the sign of
`lambda(p)`.

*Recorded because it fired:* a first pass tested only the opposite-direction flip
and reported `+1 indist = False` at every even `N`, which looked like exactly the
separation section 16 asks for. It was an artifact of testing one direction. The
same error class as the cap on assuming an edit landed -- check the other branch
before claiming a separation.

### Consequence, stated generally

For ANY `+-1`-valued `lambda` with `lambda(1) != 0`, the compensator exists with
`eps_d` chosen by the sign of `lambda(N/d)`. So the blind radius is a property of
the **divisor lattice alone**, not of the coefficient signs, and every locality
statement of this shape is sign-flip-blind by construction.

**Therefore the locality coordinate cannot host a proof of Erdos 257.** Section 6
stands as proved, and its elimination of bounded-window mechanisms stands -- but it
eliminates them for the `+1` family too, so it is a mechanism filter, never a proof
ingredient. Anyone tempted to build on section 6 should stop here.

By elimination, among the four quantities section 16 names, `tau_A`'s locality is
now excluded; the live ones remain `Q_n` positivity (the J-ladder band
`Q_m <= floor(T_m + Psi_m)`, which section 17 notes is the one mechanism using
both positivity AND set-ness), `Psi_n`, and the lcm ladder `D_n`.

## 8. The machine-checked reduction, and the wall it hits [PROVED + VERIFIED]

Recorded in neither programme: `grep -i closeReturn` finds nothing in
`ERDOS257_CROSS_INDEX.md` or anywhere under `erdos257_hole_geometry/notes/`.

### The reduction

`ReciprocalSupportIrrationality.lean:938` (chain verified: `sorry = 0`,
`axiom = 0` across that file, `RationalSupportCarrySkeleton.lean`, and
`CertificateKernel.lean`; the single `admit` grep hit at line 633 is the English
word in a docstring, not the tactic):

    theorem irrational_erdosSupportSeries_two_of_infinite_of_shiftedAtom_closeReturn
        (A : Set N) (hA : A.Infinite)
        (hclose : forall eps > 0, exists N > 0,
            (sum_d shiftedSupportAtom A N d) < (sum_d shiftedSupportAtom A 0 d) + eps) :
        Irrational (erdosSupportSeries 2 A)

Its docstring is explicit: *"no summability-to-return theorem is assumed here"*.
The summable hypothesis is only one PRODUCER of `hclose` (line 957). With
`shiftedMersenneAtom N d = 2^(N mod d)/(2^d - 1)` (line 21) and

    Phi_A(N) := sum_{d in A} 2^(N mod d) / (2^d - 1),        Phi_A(0) = y

Erdos 257 follows, for **every** infinite `A`, from the cofinal return

    inf_{N >= 1} Phi_A(N)  =  Phi_A(0).

So the corpus has a live reduction after all -- section 21's restatement is
closed (cross-index line 62), but this one is not the same statement.

### The wall [PROVED]

**Proposition.** If `A` has gaps bounded by `G`, i.e. `a+(N) - N <= G` for all
large `N` where `a+(N) = min{a in A : a > N}`, then `hclose` FAILS.

*Proof.* Take `d = a+(N) > N`, so `N mod d = N`. That single term contributes
`(2^N)/(2^d - 1)` against `1/(2^d - 1)` at `N = 0`, an excess of

    (2^N - 1)/(2^(a+(N)) - 1)  >=  (2^N - 1)/(2^(N+G) - 1)  ->  2^-G  > 0.

All terms are non-negative, so the total excess is bounded below by this. And
for every `N >= 1` the excess is already strictly positive, since `A` is
infinite and every `d > N` has `d` not dividing `N`. Hence
`inf_{N>=1} (Phi_A(N) - Phi_A(0)) > 0` and no `eps` below it is achievable. QED

**Corollary.** `hclose` implies `A` has unbounded gaps, hence density zero.

**Verified**, `scripts/close_return_criterion_boundary.py`, receipt
`state/formal_math/erdos257_period_noncollapse/close_return_boundary_receipt.json`,
exact rational arithmetic, `cap = 220`, `N <= 120`:

| family | reciprocal sum | gap `G` | `2^-G` | large-`N` min excess |
|---|---|---|---|---|
| all naturals | divergent | 1 | 0.500000 | 1.841626 |
| evens | divergent | 2 | 0.250000 | 0.426800 |
| odds | divergent | 2 | 0.250000 | 1.114403 |
| `d = 1 mod 3` | divergent | 3 | 0.125000 | 0.423630 |
| `d = 0 mod 7` | divergent | 7 | 0.007812 | **0.007936** |
| powers of two | summable | -- | -- | 0.000000 (exactly, at `N = 64 = lcm`) |
| squares | summable | -- | -- | 0.000412 (global min, at `N = 36`) |

Every bounded-gap family sits at or above its `2^-G` floor; `d = 0 mod 7` lands
on it to three significant figures. Summable families reach zero -- powers of two
*exactly*, at `N = lcm`, which is precisely how the summable producer works: the
lcm zeroes the first `k` terms and summability makes the tail negligible.

### Consequence -- the producer hunt is dead

`hclose` is sufficient but **not necessary**: for `A = N` it fails outright
(excess `>= 1/2` at every `N >= 1`), yet `sum_{d>=1} 1/(2^d - 1) = E` is
irrational by Erdos 1948. So the criterion is structurally confined to sparse
supports and is blind to the entire positive-density regime -- which is exactly
the regime where 257 is open.

> **Strengthening the producer cannot extend the Lean route.** No producer can
> establish `hclose` for `A = N`, because `hclose` is FALSE there. Reaching the
> open regime requires a different CRITERION, not a better producer.

That kills the obvious next move before it is spent, and it explains why the
Lean corpus stops exactly at reciprocal-summability: that is not an artifact of
how hard the producer was to prove, it is the criterion's true reach.

### Bookkeeping resolved

Section 17 calls the J-ladder band `Q_m <= floor(T_m + Psi_m)` "the one mechanism
in this corpus that uses both (i) and (ii)" and says "that lane is still
running". Section 21 reports its return: `mechanism_killed`, via `K12` (a DFS
whose pruning predicate is a *necessary* condition reports `deepest_depth = N`
for every `N` below the survival horizon -- measured 24/24) and `K13` (the whole
enumeration-under-sound-constraints family is circular; "the engine cannot be
cheaper than the problem"). **Section 21 supersedes section 17 here**; section
17's "still running" is stale.

## 9. The T14 wall extends to the primes -- the uncovered band is not safe [PROVED]

Section 8 excluded bounded-gap `A`; the sibling Lean theorem excludes summable
`A`. The band left uncovered was **unbounded gaps with divergent reciprocal
sum**, whose canonical member is `A = P`, the primes (gaps ~ log p, sum 1/p
divergent). That band is now closed too.

### The right form of the excess

Write `delta_d(N)` for the distance from `N` up to the next multiple of `d`.
For `d` not dividing `N` we have `N mod d = d - delta_d(N)`, so that term is

    (2^(d - delta) - 1)/(2^d - 1)  <  2^-delta,

and for `d | N` the term is **exactly 0**. Hence

    excess(N) = Phi_A(N) - Phi_A(0)  ~  sum_{d in A, d does not divide N} 2^(-delta_d(N)).

*Recorded because it fired.* My first characterisation said "excess small iff
long runs of integers with no divisor in `A`", i.e. it only counted the
`delta` large route. `A = {2^k}` falsified it immediately: max run 1, yet excess
is **exactly 0** at `N = 64`, because every element up to 64 DIVIDES 64 and the
sole survivor 128 has `delta = 64`. The `d | N` route was missing.

### Proposition (primes)

`hclose` FAILS for `A = P`. For any `N >= 1`, pick any prime `p | N + 1`. Then
`p` does not divide `N`, so `delta_p(N) = 1`, and that single term contributes

    (2^(p-1) - 1)/(2^p - 1)  >=  1/3,     -> 1/2 for large p.

All terms are non-negative, so `excess(N) >= 1/3` for every `N >= 1` and no
`eps < 1/3` is achievable. QED

**Measured**, exact rationals, `cap = 200`, `N <= 150`:

| family | min excess | max run with no divisor in `A` |
|---|---|---|
| primes | **0.516943** | 1 |
| all naturals `>= 2` | 0.606695 | 1 |
| multiples of 30 | `9.313226e-10` = **exactly `2^-30`** | 29 |
| powers of two | `5.42e-20` at `N = 64`, and **`-> 0`** | 1 |
| squares | 0.000412 | 3 |
| `{2^k + 1}` | 0.002190 | 4 |

CORRECTED 2026-08-22. Those two `0.000000` entries were DISPLAY ARTIFACTS at 6 dp and
meant OPPOSITE things. `multiples_of_30` has gaps bounded by 30, so section 8's own
wall applies: its infimum is `2^-30 > 0` and **`hclose` FAILS** for it. It does NOT
"win by long runs" -- the 29-long run is irrelevant, because the term at `d = a+(N)`
never vanishes. The only genuine witness here is `powers_of_two`, which wins by
divisibility at `N = lcm` despite runs of length 1, and whose excess truly tends to
0 (`~ 2^-N`). See CertificateSocketCollapse.md section 23.

### The general wall

> If for every large `N` there is some `d` in `A` with `d` not dividing `N` but
> `d | N + j` for some bounded `j`, then `hclose` fails, with
> `excess >= (2^(d-j) - 1)/(2^d - 1) ~ 2^-j`.

Bounded-gap `A` (section 8) and `A = P` are both instances: for the primes,
`j = 1` works at every `N` because `N + 1` always has a prime factor. So the
criterion is blocked not by density as such but by **`A`'s multiples nearly
covering** the integers just above `N`.

### Consequence

The three exclusions now compose: `hclose` reaches summable supports, and fails
for bounded-gap supports, for the primes, and generally whenever `A`'s multiples
nearly cover. The uncovered band was **NOT** closed by this: see
CertificateSocketCollapse.md section 21, which constructs a harmonically divergent
`A` with unbounded gaps for which `hclose` HOLDS, via the `d | N` route at
`N = lcm`. Divergent reciprocal sum does not imply near-covering.
Whatever criterion reaches the positive-density regime, it is not this one, and
searching for a producer inside the criterion remains dead (T14).

## 10. The sunflower socket is the lane density does NOT block [COMPUTED]

Receipt: `state/formal_math/erdos257_period_noncollapse/sunflower_socket_reach_receipt.json`

The Lean corpus contains 16 machine-checked sufficient criteria for
`Irrational (erdosSupportSeries 2 A)` (indexed in the cross-index). Two are
**support-first** in the sense `ProgrammeSpine.md` section 12 requires, and
neither is discussed in either programme's prose:

    SupportSunflowerDichotomy.lean:381   SunflowerForcedCarrySupply A
    SupportSunflowerDichotomy.lean:540   OrthogonalPetalBouquet A + forced slot-tail selection

With `supportCoeff A n = #{d | n : d in A}` = `tau_A(n)` (`CertificateKernel.lean:9044`),
the first unpacks to: for every `q > 0` there are `N, K <= L, C` with

  1. `2^K | sum_{r=1..K} tau_A(N+r) 2^(K-r)`      -- a forced carry: the block reads as a multiple of 2^K
  2. `sum_{r=K+1..L} tau_A(N+r) 2^(L-r) <= C`
  3. `exists t, tau_A(N+L+1+t) > 0`               -- the support continues
  4. `q (C + N + L + 2) < 2^L`

The file's own comment calls this a **socket** -- a hypothesis to be supplied,
not yet supplied. Nothing in it obviously fails for dense `A`: (2) needs only
`tau_A(N+K+1) <~ 2^(K+1)/q`, satisfiable by enlarging `K`.

### Measured reach, seven families

Witness search, `M = 60000`, `N <= 6000`, `K <= 22`, incremental sliding sum.
Entry = largest `q` for which a witness `(N,K,L,C)` was found.

| family | reciprocal sum | max `q` with witness |
|---|---|---|
| density-1/2 aperiodic | divergent | **1000** |
| evens | divergent | **1000** |
| primes | divergent | **1000** |
| all naturals | divergent | 100 |
| squares | summable | 100 |
| `{2^k + 1}` | summable | 100 |
| powers of two | summable | **10** |

**The profile is the inverse of close-return's.** Sections 8-9: close-return
reaches summable supports (powers of two hit excess exactly 0 at `N = lcm`) and
is provably walled on bounded-gap, near-covering and dense supports. Here the
summable families are the ones that run out first, and the divergent ones --
including the primes and a density-1/2 aperiodic set -- go furthest.

> **[SUPERSEDED BY SECTION 11 -- read that first.]** The measured profile below
> is real, but the reading "a support-first criterion density does not block"
> is WRONG: section 11 shows the socket is equivalent to a statement about
> `y`'s numerical value, and is strictly stronger than the irrationality it
> yields, so it is not a route to 257 at all.

### CAVEAT -- absence here is a search limit, not a wall

Do not read the empty cells as impossibility. Condition (4) contains `N` on the
left, so enlarging `N` makes it *harder*, and the binding constraint is
`K >~ log2(q * tau_A)` while condition (1) holds with probability `~2^-K` per `N`.
Expected hits therefore fall below 1 as `q` grows: at `q = 10^4` roughly one hit
is expected in `2^17` trials. Widening to `N <= 150000` at `q = 10^4` and `10^5`
found nothing for either a density-1/2 set or powers of two, which is exactly
what the estimate predicts and settles nothing. **This section claims a
comparative profile at `q <= 1000`, not a boundary.**

### What would be a one-way result

Proving `SunflowerForcedCarrySupply A` for every infinite `A` would prove Erdos
257 outright, by the machine-checked theorem at line 381. Proving it fails for
some infinite `A` would bound the socket the way sections 8-9 bounded
close-return. Neither is attempted here.

## 11. The sunflower socket is a statement about `y`, and is stronger than 257 [PROVED + VERIFIED]

Section 10 measured the socket's reach and read the result as "a support-first
criterion that density does not block". **That reading is wrong.** Unpacking the
definition algebraically collapses it onto the one class `ProgrammeSpine.md`
section 12 has already killed.

### The collapse

Condition (1) is `2^K | V_K(N)` with `V_K(N) = sum_{r=1..K} tau_A(N+r) 2^(K-r)`.
Since `V_K(N) = 2^K * sum_{r=1..K} tau_A(N+r) 2^-r`,

    cond (1)   <=>   trunc_K(N) := sum_{r=1..K} tau_A(N+r) 2^-r   is an INTEGER.

Condition (4), taking `C = S_2` minimal and `L` large, is `q * 2^-K R(N+K) < 1`
where `R(M) = sum_{j>=1} tau_A(M+j) 2^-j` is the rescaled tail. Since
`R(N) = trunc_K(N) + 2^-K R(N+K)`, the two conditions together say

    R(N) = (an integer) + eps,      0 <= eps < 1/q,

that is `{R(N)} < 1/q`. And `R(N) = 2^N y - (integer)`, so `{R(N)} = {2^N y}`.
Hence

> **SunflowerForcedCarrySupply(A)  <=>  liminf_N {2^N y} = 0.**

**Verified.** Density-1/2 aperiodic support, exact `Fraction` arithmetic:
cond (1) versus "trunc_K is an integer" agree on **7787** `(N,K)` pairs with
**0 mismatches**; and at every cond-(1) hit the remaining tail equals `{R(N)}`
exactly (8/8 rows to the last printed digit, e.g. `N=263, K=7`, both
`0.02415556`).

### Why that kills it as a route

* It is a statement about `y`'s **numerical value**, not about the support --
  exactly the defect section 12 names in all six killed families, notwithstanding
  that the definition is *written* through `tau_A`.
* For non-dyadic rational `y = p/q0`, `{2^N y}` lies in `(1/q0)Z \ {0}`, so
  `{2^N y} >= 1/q0` and the socket fails. That is why the theorem at line 381 is
  true -- but it also means the socket separates rationals from *some* irrationals
  only.
* An irrational `y` can have `liminf_N {2^N y} > 0` (any `y` whose binary
  expansion has no long zero runs). So **socket => irrational, but irrational =/=>
  socket**: the hypothesis is STRICTLY STRONGER than the conclusion it yields.
  Establishing it for a given `A` is therefore harder than proving 257 for that
  `A`, and it cannot be a route to the theorem.

### And it re-explains section 10's measurement

The "inverted profile" (dense supports reaching `q = 1000`, powers of two
stopping at 10) is not a support-structure effect. `liminf {2^N y} = 0` is
generic: a dense support gives a more equidistribution-like binary expansion, so
`{2^N y}` dips below `1/q` more often. That is T10 / K6 genericity again, wearing
a support-first costume.

**Net.** The lane section 10 opened is closed by section 11.  The forced-carry
criterion remains machine-checked and correct, but is not usable as an attack.
The other named sunflower endpoint is now closed independently in Lean:
`OrthogonalPetalBouquet.summable_reciprocalSupportTerm` proves every bouquet
support reciprocal-summable, and
`irrational_erdosSupportSeries_of_orthogonalPetalBouquet_unconditional` invokes
the existing reciprocal-support theorem with no forced-slot selector.  Thus the
bouquet route never enters the reciprocal-divergent or positive-density regime;
its conditional selector endpoint is subsumed rather than a second open mechanism.
