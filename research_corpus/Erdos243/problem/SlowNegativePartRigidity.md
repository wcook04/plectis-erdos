# Erdős #243: slow negative part, common-divisor persistence, and the cap on the coprimality route

Status: proof note. Lean authority for the arithmetic core is
`ErdosProblems/Erdos243/SlowRiseBarrier.lean`; the transfer to the canonical
orbit and the analytic threshold are ordinary proofs written out in full below.
Nothing here settles Erdős #243.

## 0. What is new, in one paragraph

The strongest longitudinal theorem on record for #243 excludes a *bounded*
negative part of the centred error (`boundedNegativePart_eventually_zero`).
Its proof stabilises the tail gcd, which needs bounded negative magnitudes, and
that is exactly where it stops. This note replaces gcd stabilisation by
*persistence*: a common divisor of one tail state `C_n` and denominator state
`D_n` divides every later `C_t`, `D_t`, hence every later centred error
`E_t = D_t − (a_t − 1) C_t`. With a CRT block placed in `[P, 2P)` this gives a
barrier whose rise bound is only needed below `2P`, and a landing locks a whole
block modulus into every later error. The outcome is Theorem 4: under the exact
dynamics and normalised vanishing, a negative part bounded by
`(1 − δ) log₂ log₂ C_n` (any `δ > 0`) already forces `E_n = 0` eventually, hence
the Sylvester recurrence. The bounded case is the special case `δ` arbitrary
with a constant bound. Two side results are unconditional facts about any
counterexample: the overlap `gcd(a_n, D_n)` of every multiplier with the
accumulated denominator divides every later error (Theorem 1), and the
negative part satisfies `limsup (−E_n)_+ / log₂ log₂ C_n ≥ 1` (Corollary 5).
A no-go closes the route: coprimality data alone is satisfiable by walks with
rises `O(log u)`, so no argument using only pairwise-coprime old moduli and
whole-modulus avoidance can exclude negative parts of order `log C_n`
(Proposition 7). The `1/n` threshold recorded as advisory in the packet is
verified with the exact constant `1`, and shown to be exactly the boundary of
the Erdős–Straus method (Theorem 8).

## 1. Setting and dictionary

Koizumi, *Irrationality of the reciprocal sum of doubly exponential sequences*,
arXiv:2504.05933 (INTEGERS 26 (2026), A28). For a rational `r = p/q` with
pseudo-greedy expansion `a_n = ⌊x_n^{-1} + 1⌉`, remainders `x_n = c_n / d_n`
with `d_n = q a_1 ⋯ a_{n−1}`, and gap sequence `ε_n = e_n / c_n`, Lemma 15 gives

    e_n ≡ d_n (mod c_n),  −c_n/2 ≤ e_n < c_n/2,
    a_n = (d_n − e_n)/c_n + 1,  c_{n+1} = c_n − e_n,  d_{n+1} = d_n a_n .

Under `(C_n, D_n, E_n) = (c_n, d_n, e_n)` this is the exact natural orbit of
`ReciprocalTailRigidity.lean`: `C_{n+1} + D_n = a_n C_n`, `D_{n+1} = a_n D_n`,
`E_n = D_n − (a_n − 1) C_n`. Corollary 10 there makes any sequence with
`a_n^2/a_{n+1} → 1` and summable reciprocals the pseudo-greedy expansion of its
own tail after a finite shift, with `ε_n → 0`; Theorem 16 there shows that
`ε_n → 0` is *all* the rate hypothesis contains (Question 5 is equivalent to
Conjecture 6). Hence every theorem below is stated for the state system with

    (NV)  normalised vanishing:  ∀ K ∃ N ∀ n ≥ N,  K |E_n| < C_n ,

which is the division-free form of `ε_n → 0`, and no further analytic input is
available or used. Positive `C_n` and `E_n ≠ 0` eventually (else absorption
gives the Sylvester tail) are used throughout; `C_n → ∞` then follows from (NV)
(`tailState_tendsto_atTop_of_nonzero_normalizedVanishes`).

All identities of this section were checked exactly on orbits of many
rationals, including Koizumi's example `11/29`, by
`formal_math/probes/erdos243_koizumi_state_probe.py`
(receipt `state/formal_math/erdos257_period_noncollapse/erdos243_koizumi_state_probe_receipt.json`,
`all_identity_checks_pass: true`; the survey of all `p/q` with `q ≤ 300`
reproduces Koizumi's termination for all 27 397 orbits).

## 2. Persistence (Lean)

**Theorem 1 (common-divisor persistence).** Let `(a, C, D)` satisfy the exact
dynamics from index `N`. If `d ∣ C_n` and `d ∣ D_n` for some `n ≥ N`, then
`d ∣ C_t` and `d ∣ D_t` for every `t ≥ n`, and therefore `d ∣ E_t` for every
`t ≥ n`. In particular

    gcd(a_n, D_n) ∣ E_t   for every t > n .

*Proof.* `C_{t+1} = a_t C_t − D_t` and `D_{t+1} = a_t D_t` preserve common
divisors. For the overlap, `gcd(a_n, D_n)` divides `a_n C_n − D_n = C_{n+1}` and
`D_{n+1} = a_n D_n`. Finally `E_t = D_t − (a_t − 1) C_t`. ∎

Lean: `commonDivisor_persists`, `multiplierOverlap_persists`,
`dvd_centeredState_of_dvd`, `multiplierOverlap_dvd_laterCenteredState`
(`SlowRiseBarrier.lean`).

**Corollary 1′ (old parts are small on a counterexample).** On the canonical
orbit of any counterexample to #243, `E_t ≠ 0` for all large `t`, so
`gcd(a_n, D_n) ≤ |E_t|` for all `t > n`, and in particular
`gcd(a_n, D_n) ≤ −E_t` at the first negative index `t > n`. The same holds for
the tail gcd `gcd(C_n, D_n)`. This is a new clause of the frontier profile
(Prop. `res:frontier` of the paper): the overlap of each multiplier with the
accumulated denominator is bounded by the depth of the next negative excursion.
Checked exactly on finite orbits in the probe above (identity I3).

## 3. The bounded CRT block and the landing (Lean)

**Lemma 2 (bounded CRT block).** For pairwise-coprime `m_0, …, m_{B−1} ≥ 2`
with product `P` there is `x` with `P ≤ x < 2P` and `m_r ∣ x + r` for all
`r < B`.

*Proof.* Take the CRT solution `y` of `y ≡ −r (mod m_r)`, reduce it modulo `P`
(each `m_r` divides `P`, so the congruences survive) and add `P`. ∎

Lean: `exists_consecutiveMultiples_between`. The existing
`exists_shifted_consecutiveMultiples` only places the block beyond a bound.

**Theorem 3 (slow-rise landing).** Let `(a, C, D)` satisfy the exact dynamics
from index `N`, let `T ≥ N`, and let `m_0, …, m_{B−1} ≥ 2` be pairwise coprime
with each `m_r ∣ D_T` and product `P`. Suppose `C_T < P`, `C_n → ∞`, and

    for every n ≥ T with C_n < 2P:   C_{n+1} ≤ C_n + B .

Then there is `s ≥ T` with `C_{s+1} < 2P + B` and an `r < B` such that
`m_r ∣ C_t` and `m_r ∣ D_t` for every `t ≥ s + 1`; hence `m_r ∣ E_t` for every
`t ≥ s + 1`.

*Proof.* Let `x ∈ [P, 2P)` be the block of Lemma 2 and let `t` be the first
index `> T` with `C_t ≥ x`; put `s = t − 1`, so `C_s < x` (by minimality, or by
`C_T < P ≤ x` if `s = T`). Since `C_s < x < 2P` the rise bound gives
`C_{s+1} ≤ C_s + B < x + B`, so `C_{s+1} = x + r` for some `r < B` and
`m_r ∣ C_{s+1}`. Also `m_r ∣ D_T ∣ D_{s+1}`. Theorem 1 finishes. ∎

Lean: `slowRise_landing`.

**Theorem 3′ (slow-negative contradiction, block form).** In the setting of
Theorem 3, suppose in addition that negative errors occur cofinally and that

    for every t ≥ T with E_t < 0 and C_t < 2P + B:   −E_t < m_r for all r .

Then there is a contradiction.

*Proof.* Land as in Theorem 3 and let `t` be the first negative index
`≥ s + 1`. Between `s + 1` and `t` the errors are nonnegative, so `C` does not
rise and `C_t ≤ C_{s+1} < 2P + B`. Now `m_r ∣ E_t` with `E_t < 0` gives
`m_r ≤ −E_t`, against the hypothesis. ∎

Lean: `no_slowNegative_of_coprimeBlock`, with the descent
`tailState_antitone_of_nonnegative`.

**Theorem 3″ (reduced-tail form).** No reduced exact tail `(a, u, v)` from
index `N` with `a_n > 1`, `u_n → ∞`, can satisfy, for some `B`,
`u_{N+B} < ∏_{i<B} a_{N+i} =: P` and `u_{n+1} ≤ u_n + B` at every `n ≥ N + B`
with `u_n < 2P`.

*Proof.* Multipliers of a reduced tail are pairwise coprime and each divides
`v_{N+B}`; land as in Theorem 3 with `C := u`, `D := v`; the landing modulus
divides both `u_{s+1}` and `v_{s+1}`, which are coprime, so it is `1`. ∎

Lean: `no_slowRise_reducedTail`. This generalises `no_boundedRise_reducedTail`
(uniform rise `B` gives the block hypothesis for that `B` once
`u_{N+B} < 2^B`, which holds for large `N`).

## 4. Slow negative part on the state system (ordinary proof over the Lean core)

Write `LL(x) := log₂ log₂ x` for `x ≥ 2`.

**Theorem 4 (slow negative part).** Let `(a, C, D)` be an exact natural orbit
with `a_n > 1`, `C_n > 0`, `D_0 ≥ 1`, satisfying (NV). Suppose that for some
`δ ∈ (0, 1)` and some `N_1`,

    for every n ≥ N_1 with E_n < 0:   −E_n ≤ (1 − δ) · LL(C_n) .           (S_δ)

Then `E_n = 0` for all large `n`, and consequently `a_{n+1} = a_n^2 − a_n + 1`
for all large `n`.

The bounded-negative theorem is the case of a constant bound (a constant is
eventually below `(1 − δ) LL(C_n)` because `C_n → ∞`). The proof below is
complete modulo the four Lean theorems of Sections 2–3, whose statements are
quoted where used.

*Proof.* If `E_n ≥ 0` for all large `n`, descent (`centeredState_eventually_zero`)
gives `E_n = 0` eventually. Otherwise negative indices are cofinal; assume for
contradiction that `E` is not eventually zero. By absorption
(`centeredState_zero_absorbing`, using strict centring from (NV) with `K = 1`)
there is `N_2` with `E_n ≠ 0` for `n ≥ N_2`, and `C_n → ∞`. We collect
constants; every `N_i` below is finite.

*(G1) Growth of `C`.* By (NV) with `K = 4` there is `N_3 ≥ max(N_1, N_2)` with
`4|E_n| < C_n` for `n ≥ N_3`; hence `C_n ≥ 4` and
`C_{n+1} = C_n − E_n < (3/2) C_n`, so `C_n ≤ C_{N_3} (3/2)^{n − N_3}` and
`LL(C_n) ≤ log₂ n + κ_1` for `n ≥ N_4`, for a constant `κ_1`.

*(G2) Growth of `a`.* For `n ≥ N_3`, `|E_n| < C_n` gives
`D_n/C_n < a_n < D_n/C_n + 2`. As `D_n = D_0 ∏_{k<n} a_k ≥ 2^n` and `C_n` is
at most exponential with base `3/2`, `a_n ≥ c_1 (4/3)^n` for a constant
`c_1 > 0`; so `log₂ a_n ≥ (log₂ (4/3)) n − κ_3`.

*(G3) Size of `D`.* For `n ≥ N_3`, `a_n < D_n/C_n + 2 ≤ 2 D_n`, so
`log₂ D_{n+1} ≤ 2 log₂ D_n + 1` and by induction
`log₂ D_n + 1 ≤ 2^{n − N_3} (log₂ D_{N_3} + 1)`; hence `LL(D_n) ≤ n + κ_0`.

*(P) Old parts are small.* For `n ≥ N_3` let `t > n` be the first negative
index after `n` (cofinality). Between `n + 1` and `t` the errors are
nonnegative, so `C_t ≤ C_{n+1} < (3/2) C_n`, and by (S_δ) and Theorem 1,

    g_n := gcd(a_n, D_n) ≤ −E_t ≤ (1 − δ) LL(C_t) ≤ LL((3/2) C_n) ≤ LL(C_n) + 1 =: φ_n ,

using `C_n ≥ 4`. By (G1), `φ_n ≤ log₂ n + κ_1 + 1` for `n ≥ N_4`.

*(B) Burn primes.* Write `a_n = NEW_n · OLD_n` where `NEW_n` is the largest
divisor of `a_n` coprime to `D_n`. Then `OLD_n = g_n · BURN_n` with

    BURN_n = ∏_{p ∣ D_n,  v_p(a_n) > v_p(D_n)}  p^{v_p(a_n) − v_p(D_n)} ,

and for every prime `p` in this product `p^{v_p(D_n)} ∣ g_n`, so `p ≤ φ_n` and
`v_p(D_n) ≤ log₂ φ_n`. Call such `p` a *burn prime at `n`*. If `p` is a burn
prime at `n` then `v_p(D_m) ≥ v_p(a_n)` for all `m > n`; so `p` can be a burn
prime at some `m > n` only if `v_p(a_n) ≤ v_p(D_m) ≤ log₂ φ_m`.

*(R) Rich indices.* Fix `Θ ≥ 3` (chosen at the end). Call `n` *rich* if
`NEW_n > Θ` and *poor* otherwise. At a poor `n ≥ N_4`,
`BURN_n ≥ a_n/(φ_n Θ)`, and `BURN_n` is a product of at most `φ_n` prime
powers with primes `≤ φ_n`, so some burn prime `p_n` at `n` has

    v_{p_n}(a_n) ≥ log₂ BURN_n / (φ_n log₂ φ_n)
                ≥ (log₂(4/3) n − κ_3 − log₂(φ_n Θ)) / (φ_n log₂ φ_n) .

By (G1) the right side exceeds `√n` for `n ≥ N_5(Θ)`, where `N_5(Θ) = O(log Θ)`.
Now fix `T ≥ max(N_4, N_5(Θ))` and consider the window `W = [T, 2^T]`. For poor
`n < n′` in `W` with `p_n = p_{n′}`, (B) forces
`√n < v_{p_n}(a_n) ≤ log₂ φ_{n′} ≤ log₂(T + κ_1 + 1) ≤ log₂(n + κ_1 + 1)`, false
for `T` large. So `n ↦ p_n` is injective on the poor indices of `W`, with
values among the primes `≤ T + κ_1 + 1`; hence `W` contains at most
`T + κ_1 + 1` poor indices. Taking the first `B` rich indices
`n_1 < ⋯ < n_B` in `W` gives

    n_B ≤ 2T + B + κ_1 + 1                                                  (R1)

provided `2T + B + κ_1 + 1 ≤ 2^T`.

*(M) Moduli.* Put `m_r := NEW_{n_r}` and `T′ := n_B + 1`. Each `m_r > Θ ≥ 3`;
`m_r ∣ a_{n_r} ∣ D_{T′}`; and for `r < r′`, `m_r ∣ D_{n_{r′}}` while `m_{r′}` is
coprime to `D_{n_{r′}}`, so the `m_r` are pairwise coprime. Let
`P := ∏_r m_r ≥ Θ^B ≥ 2^B ≥ B`. Since the `a_{n_r}` are distinct factors of
`D_{T′}/D_0`, `P ≤ D_{T′}`, and by (G3) and (R1)

    LL(2P + B) ≤ LL(4P) ≤ LL(D_{T′}) + 2 ≤ 2T + B + κ_2                      (M1)

for a constant `κ_2`.

*(H) Hypotheses of Theorem 3′.* Start: `C_{T′} ≤ C_{N_3}(3/2)^{T′} < Θ^B ≤ P`
once `B ≥ B_0(T, Θ)`, by (G1) and (R1). Rise: for `n ≥ T′` with `C_n < 2P`,
either `E_n ≥ 0` and `C_{n+1} ≤ C_n`, or by (S_δ) and (M1)
`C_{n+1} − C_n = −E_n ≤ (1 − δ) LL(2P) ≤ (1 − δ)(2T + B + κ_2) ≤ B` once
`B ≥ (1 − δ)(2T + κ_2)/δ`. Slow: for `t ≥ T′` with `E_t < 0` and
`C_t < 2P + B`, `−E_t ≤ (1 − δ)(2T + B + κ_2) < Θ < m_r` once
`Θ > (1 − δ)(2T + B + κ_2)`. Cofinal negativity and `C_n → ∞` hold.

*(Choice of constants.)* `B_0(T, Θ)` and `⌈(1 − δ)(2T + κ_2)/δ⌉` are both
`O(T/δ)` for `Θ ≥ 3`, and `N_5(Θ) = O(log Θ)`. Choose `T_δ` with
`2^T ≥ 2T + c T/δ + κ_1 + 1` for all `T ≥ T_δ`, where `c T/δ` bounds the two
requirements on `B`; this makes the window condition automatic. Then choose
`Θ` so large that `T := max(N_4, N_5(Θ), T_δ)` is `O(log Θ)` and
`Θ > (1 − δ)(2T + cT/δ + κ_2)`, and finally `B := max(B_0(T, Θ), ⌈(1 − δ)(2T + κ_2)/δ⌉)`.
All hypotheses of Theorem 3′ now hold, and it gives a contradiction. Hence
`E_n = 0` eventually, and `sylvesterNext_eventually_of_centered_zero` gives the
recurrence. ∎

**Corollary 5 (frontier profile, quantitative).** For the canonical integer
state of any counterexample to #243, for every `δ > 0` there are infinitely
many `n` with `E_n < 0` and `−E_n > (1 − δ) log₂ log₂ C_n`; that is,

    limsup_{n→∞}  (−E_n)_+ / log₂ log₂ C_n  ≥ 1 .

This strengthens the clause `limsup_{E_n<0} (−E_n) = ∞` of the frontier
profile. Together with Corollary 1′ and `C_n ≤ C_{N}(3/2)^{n−N}`, the
counterexample must have negative excursions of depth at least
`(1 − δ) log₂ log₂ C_n`, where `log₂ log₂ C_n ≤ log₂ n + O(1)`.

**Theorem 6 (original coordinates).** Let `a_{n+1}/a_n^2 → 1` and
`∑ 1/a_n ∈ ℚ`, and write

    Q_n := (a_1 a_2 ⋯ a_{n−1} / a_n) · (a_n^2 / a_{n+1} − 1) ,

the product form of the Erdős–Straus quantity (Erdős–Straus 1964, Theorem 3,
uses the least common multiple in place of the product; Koizumi, Cor. 20(1),
uses the product). Then:

1. (bounded negative part, original form) if `limsup_n Q_n < ∞`, the sequence
   is eventually Sylvester;
2. (slow negative part, original form) there is a constant `λ > 0` depending
   only on the sequence such that, if for some `δ > 0` and all large `n`
   `Q_n ≤ (1 − δ) λ log₂ log₂ (a_1 ⋯ a_{n−1} / a_n)`, the sequence is eventually
   Sylvester.

*Proof.* After Koizumi's finite shift, with `B_n := (1/a_1) ∏_{k ≤ n} (1 + β_k)`
and `β_k = O(1/a_k)` as in the proof of his Corollary 20(1), and using
`∏_{k<n} (1 − ε_k) = c_n / c_1`,

    Q_n = −(B_{n−1}/c_1) e_n + (B_{n−1}/c_1) β_n c_{n+1} ,

and the second term tends to `0` because `c_{n+1} ≤ c_1 (3/2)^n` while `a_n`
is doubly exponential; `B_n → B_∞ ∈ (0, ∞)`. Hence `limsup Q_n < ∞` iff the
negative part of `e_n` is bounded, which is `boundedNegativePart_sylvesterNext_eventually`
composed with Koizumi's bridge. For (2), `a_1 ⋯ a_{n−1}/a_n = B_{n−1} c_n / c_1`,
so `log₂ log₂ c_n = log₂ log₂ (a_1 ⋯ a_{n−1}/a_n) + o(1)`, and the displayed
hypothesis with `λ := B_∞ / c_1` gives (S_{δ′}) for any `δ′ < δ`; Theorem 4
applies. ∎

Part (1) is the cleanest statement of the existing theorem in the language of
the problem: Erdős–Straus require `limsup Q_n ≤ 0`; the Lean-checked theorem
weakens this to `limsup Q_n < ∞`. The Erdős–Straus quantity with the least
common multiple is `Q_n / M_n` with `M_n = q a_1 ⋯ a_{n−1} / lcm(q, a_1, …, a_{n−1})`,
and `M_n ∣ c_n` (checked in the probe, identity I2). Whether `limsup Q_n/M_n < ∞`
suffices is open; the LCM-state persistence fails at cancellation steps
(`γ_n U_{n+1} = U_n − V_n` divides by `γ_n = gcd(L_n, a_n)`), which is why the
product form is the one proved.

## 5. The cap on the coprimality route (no-go)

**Proposition 7.** Let `m_0 < m_1 < ⋯` be pairwise coprime integers `≥ 2` with
`∑_i 1/m_i ≤ 1/2` (for instance `m_i ≥ 2^{2^i}`). For every `x ≥ 1` and every
`L > 2^{k+1}`, where `k := #{i : m_i ≤ x + L}`, the window `[x, x + L)`
contains an integer coprime to every `m_i`. Consequently there is a sequence
`u_n → ∞` with `u_{n+1} − u_n ≤ 2^{k(u_n)+1} + 1` that is coprime to every
`m_i`, where `k(u) = #{i : m_i ≤ 2u + 2}`; for `m_i ≥ 2^{2^i}` this is a rise
of at most `4 log₂ (2u_n + 2) + 3 = O(log u_n)`.

*Proof.* Only the `k` moduli `≤ x + L` can divide an element of the window.
By inclusion–exclusion the number of elements coprime to all of them is at
least `L ∏_{i<k} (1 − 1/m_i) − 2^k ≥ L/2 − 2^k > 0`. Walk greedily. ∎

Every theorem of the coprimality route (Theorem `res:barrier` of the paper,
Theorems 3–3″ here) uses about the multipliers only that they are pairwise
coprime, that they divide later denominator states, and, at a landing, that a
modulus dividing the current numerator is impossible or forces a large later
error. Proposition 7 shows that these data admit walks with rises `O(log u)`,
while the CRT block forces a rise `≥ B` at some height `< 2^{2^{B + O(1)}}`,
that is, rises of order `log₂ log₂ u`. Hence:

* no argument using only pairwise coprimality and whole-modulus avoidance can
  exclude negative parts of order `log C_n`;
* the constant `1` in Corollary 5 is the CRT constant: `B` moduli of size
  `≈ 2^{2^i}` cover a window of length `B` at height `≈ 2^{2^{B}}`, and a
  modulus covers at most one position of a window shorter than itself.

Iwaniec's bound on the Jacobsthal function would sharpen the admissible rise
in Proposition 7 to `O((log log u)^2)`; that bound is reported, not used. The
witness walk is exhibited numerically in
`formal_math/probes/erdos243_crt_block_and_coprime_witness.py` (receipt
`state/formal_math/erdos257_period_noncollapse/erdos243_crt_block_and_coprime_witness_receipt.json`):
against Sylvester's numbers as moduli the greedy avoiding walk needs a maximal
rise of `12` up to height `2·10^6` (`log₂` of the height is `21`), and the
bounded block of Lemma 2 is constructed and its landing property checked for
blocks of Sylvester numbers and of consecutive primes.

The exact remaining obstacle is therefore the regime

    (1 − δ) log₂ log₂ C_n  ≤  −E_n  = o(C_n)   at infinitely many n ,

with divergent normalised negative mass. Any argument entering it must use the
congruence `E_n ≡ D_n (mod C_n)` beyond coprimality, or supply a second
mechanism that forces landings.

## 6. The `1/n` threshold (verified) and the Erdős–Straus boundary

**Theorem 8.** Let `a_{n+1}/a_n^2 → 1` and `∑ 1/a_n ∈ ℚ`. If

    limsup_{n→∞}  n · (a_n^2 / a_{n+1} − 1)_+  < 1 ,

then `a_{n+1} = a_n^2 − a_n + 1` for all large `n`. The constant `1` is exactly
the boundary of the method: the template `e_n ≡ −1`, `c_n = c + n` has
`n(−e_n)/c_n → 1`, satisfies every hypothesis of Erdős–Straus' criterion except
the sign, and is excluded only by the prime-lock theorem
(`no_eventuallyConstantNegative_orbit`).

*Proof.* Pass to Koizumi's canonical state. From `a_n^2/a_{n+1} = (1 − ε_n)(1 + β_n)`
with `β_n = O(1/a_n)`, `(a_n^2/a_{n+1} − 1)_+ ≥ (−e_n)_+ / c_n − 2|β_n|`, and
`n β_n → 0`. So there are `θ < 1` and `N` with `(−e_n)_+ ≤ θ c_n / n` for
`n ≥ N`. Then `c_{n+1} = c_n − e_n ≤ c_n (1 + θ/n)`, so
`c_n ≤ c_N ∏_{N ≤ k < n} (1 + θ/k) ≤ c_N exp(θ ∑_{N≤k<n} 1/k) ≤ c_N (n/(N−1))^θ`,
and `(−e_n)_+ ≤ θ c_N n^{θ−1} (N−1)^{−θ} → 0`. As `e_n` is an integer,
`e_n ≥ 0` for all large `n`, and Koizumi's Proposition 19(2) (Badea) gives
`e_n = 0` eventually; Lemma 12 there gives the recurrence. ∎

This supersedes the advisory packet entry `subcritical_one_over_n_threshold`
and sharpens Koizumi's Remark 21 (rate `o(1/n)`) to the explicit constant. It
is weaker than Theorem 4: its hypothesis already implies a bounded (indeed
vanishing) negative part. It is recorded because it is the one
number-anchored statement about #243 in the language of the original problem.

## 7. What was tried and did not close

* The LCM-state route with the Erdős–Straus prefactor: `M_n ∣ c_n` is exact
  (Section 4), so the LCM quantity is the product quantity divided by `M_n`,
  and the sign condition is the same in both; the persistence of Theorem 1
  does not survive the division by `γ_n = gcd(L_n, a_n)` at cancellation
  steps, so no strengthening of Theorem 6(1) to `limsup Q_n/M_n < ∞` is
  claimed.
* Pushing the barrier past `log₂ log₂`: excluded for the coprimality route by
  Proposition 7. Using the congruence `E_n ≡ D_n (mod C_n)` at the crossing
  step gives only `a_s^2 e_s ≡ −E_{s+1} (mod C_{s+1})`, a constraint with no
  handle on `a_s mod C_{s+1}` beyond the dynamics that already defines it; no
  second landing mechanism was found.
* Removing the negative-part hypothesis entirely (the parent): every
  constraint available from coprimality has positive density (Proposition 7),
  and the rate hypothesis is exhausted by `ε_n → 0` (Koizumi, Thm 16). A proof
  must show that a deterministic doubly exponential orbit cannot keep the
  residue `D_n mod C_n` within `o(C_n)` of `0` forever; nothing in this note
  or in the corpus supplies that.

## 8. Receipts

`tao_pipeline_receipt`

    input_stage: generation (persistence idea) and verification (Lean core)
    output_stage: exposition (this note) with the transfer as an ordinary proof
    artifact: ErdosProblems/Erdos243/SlowRiseBarrier.lean; this note; two probes
    human_understanding_delta: gcd stabilisation is not needed for the CRT
      barrier, persistence of a common divisor into every later error is; the
      barrier's true scale is log2 log2 C_n and the coprimality route is capped
      at O(log C_n); the 1/n threshold has constant exactly 1
    verification_state: Lean for Theorems 1, 2, 3, 3', 3'' (focused
      lean_fast_build receipt on ErdosProblems.Erdos243.SlowRiseBarrier, see the
      packet row); ordinary proof for Theorems 4, 6, 8 and Proposition 7;
      identities exact-checked by probes
    publication_or_review_state: not reviewed; not packaged
    canonicalization_state: Theorem 4 subsumes boundedNegativePart_* as the
      strongest longitudinal claim; Theorem 8 supersedes the advisory 1/n entry
    unresolved_downstream_bottleneck: formalising the burn count (R) and the
      transfer (H) of Theorem 4; the parent
    next_stage_owner: Lean formalisation of Theorem 4 (R) and (H)

`paper_assimilation`

    paper: erdos-243-reciprocal-tail-rigidity.tex (not edited here)
    section: after Theorem res:bounded; Prop. res:frontier; Problem res:variablerise
    canonical_mechanism_family: CRT barrier by common-divisor persistence
    relation: strengthens res:bounded to a log-log negative part; answers
      res:variablerise for the coprimality route (yes at log2 log2, capped at log)
    understanding_delta: as above
    evidence_boundary: Lean core versus ordinary transfer, stated per theorem
    hard_step: the burn count (R) supplying B pairwise-coprime new parts above
      any threshold inside a window of length 2T + B
    meaningful_failed_route: LCM prefactor; congruence at the crossing step
    open_remainder: negative parts between log2 log2 C_n and o(C_n)
