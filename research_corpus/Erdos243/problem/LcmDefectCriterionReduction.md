# Erdős #243: the lcm-weighted defect criterion is the product criterion after primitive reduction

Status: proof note (ordinary mathematics, exact finite checks). Source: wave-4 desk U1 of
the batch `erdos243_20260905_eight_return_stream_01` (2026-09-05), whose full literature
map and receipt are in that batch's `work/wave4_U1_ahmes_literature_attack.md`. Exact
verifier: `scripts/erdos243_lcm_defect_criterion_probe.py --quick`. Nothing here settles
Erdős #243.

## 0. What this note establishes

With `A_{n-1} = lcm(a_1, ..., a_{n-1})`, `Π_{n-1} = a_1 ⋯ a_{n-1}`, the overlap debt
`M_n = qΠ_{n-1}/lcm(q, a_1, ..., a_{n-1})` of `CumulativeLcmTransfer.lean`, the tail gcd
`G_n = gcd(C_n, D_n)`, and `κ_n = qA_{n-1}/v_n`, `κ'_n = lcm(q, A_{n-1})/v_n` (positive
integers): `G_n = κ_n L_{n-1} = κ'_n M_n` and `E_n/M_n = κ'_n e_n`. Consequently the
Erdős–Straus (1964) Theorem 3 quantity, the Tijdeman–Yuan (2002) Theorem 4.1 quantity and
Koizumi's Corollary 20(1) quantity all have the sign of `E_n` at every index, so each of
those criteria decides exactly the half-space `E_n ≥ 0 eventually`, which Koizumi
Proposition 19(2) already closes. The lcm-weighted question left open in
`SlowNegativePartRigidity.md` §4 ("whether `limsup Q_n/M_n < ∞` suffices") is therefore:
at level `≤ 0`, identical to the product criterion; at level `< ∞`, equivalent to
`(-E_n)_+ = O(M_n)`, empty on cancellation-free tails (where `M_n` is eventually
constant), and blind to the clean record jumps that make up the surviving regime. The
classical size-plus-divisibility mechanism is circular in the open branch: it needs
`-e_n < 1/κ_n ≤ 1`, which for an integer `e_n` is the conclusion.

## 2. Literature map

Everything below was read in this pass from the annex sources named in §6,
except where flagged.

**Sylvester 1880 / Kellogg (tail form).** If `Δ_k ≥ 0` for all `k > n` then
`∑_{k>n} 1/a_k ≤ 1/(a_n(a_n−1))`, with equality iff Sylvester from `n` on.
Monotone quantity: the tail itself.

**Erdős–Straus 1964, Theorem 1.** Hypotheses (i) `limsup n_k^2/n_{k+1} ≤ 1` and
(ii) `{N_k/n_{k+1}}` bounded, `N_k = lcm(n_1,…,n_k)`. Conclusion: `∑1/n_k ∈ ℚ`
iff Sylvester eventually. Defect hypothesis: (i) allows `Δ_k ≥ −o(a_k^2)`, so
(i) is implied by our regime and is not the binding condition; (ii) is. The
proof writes `bN_k = c_k n_{k+1} − d_k`, `0 ≤ d_k < n_{k+1}`, proves `d_k ≤ c_k`
and then `c_{k+1} ≤ c_k`; the **monotone quantity is the integer `c_k`**, and
boundedness is what makes "nonincreasing" into "constant".

**Erdős–Straus 1964, Theorem 3.** (i) together with
(ii'') `limsup N_k(n_{k+1}^2/n_{k+2} − 1) ≤ 0`, replacing the boundedness of
(ii). Same conclusion, same monotone quantity `c_k`. FLAG: the annex OCR of the
1964 printed page is degraded at (i) and (ii''); (ii'') is reconstructed from
Tijdeman–Yuan's statement that their Corollary 4.1(v) is an improvement of it,
and (i) is read as `≤ 1` because Koizumi Corollary 20(1) applies it under
`a_n^2/a_{n+1} → 1`.

**Badea.** Tijdeman–Yuan attribute to Badea their Corollary 4.1(i), which with
`b_n ≡ 1` reads `a_{n+1} ≥ a_n^2 + 1`; Koizumi attributes to Badea the weaker
hypothesis `a_{n+1} ≥ a_n^2 − a_n + 1` for `n ≫ 0`, that is `Δ_n ≥ 0`. FLAG:
Badea's own papers are not in the annex corpus and were not read; both citing
sources were. Koizumi's version is the one that matters here, and his proof
(Corollary 20(2)) is: `Δ_n ≥ 0` reformulates as `ε_n a_n^2/(1−ε_n) ≥ ε_{n+1}`,
so `ε_n < 0` forces `ε_n > ε_{n+1}`, and `ε_n → 0` then forces `ε_n ≥ 0`
eventually. Monotone quantity: `ε_n` on the negative branch, then `C_n`.

**Tijdeman–Yuan 2002, Theorem 4.1 (the strongest classical form).** For positive
integer sequences with `S = ∑ b_n/a_n` convergent and
`limsup_n A_{n-1}(b_{n+1}a_n/a_{n+1} − b_n/a_n) ≤ 0`, `S ∈ ℚ` iff
`a_{n+1} = (b_{n+1}/b_n)a_n(a_n−1) + 1` for large `n`. Corollary 4.1 lists five
sufficient forms; (v) is the hypothesis rewritten, (i) is Badea, (iv) is (v)
under a boundedness side condition. The proof bounds
`a_n R^*_n − R^*_{n-1} ≤ ∑_{j≥0}(a_n/a_{n+j}) d_{n+j}` with
`d_m = a_m/a_{m+1} − 1/a_m`, uses `q A_{n-1}(a_nR^*_n − R^*_{n-1}) ∈ ℤ`, and
concludes that this integer is `< 1` hence `≤ 0`. The **monotone quantity is
`a_1⋯a_n R^*_n`**, a positive element of `(1/q)ℤ`, shown nonincreasing.
Defect hypothesis, with `b_n ≡ 1`: `limsup (A_{n-1}/a_n)(a_n^2/a_{n+1} − 1) ≤ 0`,
which is Erdős–Straus Theorem 3's condition divided by `a_n`.

**Hančl–Tijdeman 2004.** Theorem 2.1: for Cantor series with
`b_n = o(a_{n-1}a_n)`, rationality forces all limit points of `b_n/a_n (mod 1)`
to be rational with one common denominator. Theorem 3.1: the series is rational
iff `q b_n = t_n a_n − t_{n+1}` for large `n`, `t_n` the nearest integer to
`q b_n/a_n`. In the Ahmes case `b_n ≡ 1` and `a_n → ∞`, Theorem 2.1 is vacuous
(the only limit point is `0`) and Theorem 3.1 is the exact reformulation
`t_n = q R_n`, which in canonical coordinates is Koizumi Lemma 15(2) itself.
Neither statement carries defect information. Nothing usable here.

**Koizumi arXiv:2504.05933.** Lemma 15 is the corpus's canonical state
(`d_n = qa_1⋯a_{n-1}`, `x_n = c_n/d_n`, `ε_n = e_n/c_n`, `e_n ≡ d_n (mod c_n)`
centred, `c_{n+1} = c_n − e_n`, `d_{n+1} = d_na_n`, `c_n = O(1.5^n)` and
`c_n = O(Π_{n-1}/a_n)`). Theorem 16 is the equivalence with Erdős 243.
Proposition 19: `liminf ε_n∏_{k<n}(1−ε_k) ≥ 0`, or `ε_n ≥ 0` for `n ≫ 0`,
forces `ε_n = 0` eventually; the first reduces to the second by
`e_n = c_1 ε_n ∏_{k<n}(1−ε_k)`, the second is two lines of monotone positive
integers. Corollary 20 transports this to `Π_{n-1}/a_n`-weighted growth
hypotheses. Remark 21: `a_n^2/a_{n+1} = 1 + o(n^{-1})` suffices, because then
`C_n = n^{o(1)}` and `|ε_n| = o(1/n)`, so `|E_n| = o(1)`.

**Kovač–Tao arXiv:2406.17593.** Consulted; it treats irrationality sequences and
Ahmes representations of a prescribed number, not the rationality-side criteria,
and contains nothing bearing on the open branch.

## 3. Result

### 3.1 The canonical reading of the classical mechanism

**Lemma U1-0.** `−E_n/D_n = x_n − a_n x_{n+1} = 1/a_n − (a_n−1)∑_{k>n}1/a_k.`
Hence `E_n ≥ 0` iff `∑_{k>n}1/a_k ≤ 1/(a_n(a_n−1))`, and Tijdeman–Yuan's
monotone quantity satisfies `a_1⋯a_n R^*_n = C_{n+1}/D_1`. Consequences:
`Δ_k ≥ 0` for all `k > n` implies `E_n ≥ 0` (Sylvester's tail bound), and
`E_n ≥ 0` implies `Δ_n ≥ −1`. The classical half-space and the corpus half-space
are the same half-space.

So every criterion above proves the same thing in the same way: the positive
integer `C_n` is eventually nonincreasing, hence constant, hence `E_n = 0`.
Erdős–Straus's `c_k`, Tijdeman–Yuan's `a_1⋯a_nR^*_n` and Koizumi's `c_n` are one
object. This is confirmed exactly, not asymptotically:

**Proposition U1-4.** For all large `k`, Erdős–Straus's integer
`c_k = ⌈qA_k/a_{k+1}⌉` equals `κ_{k+1} u_{k+1}`, where
`κ_n := qA_{n-1}/v_n ∈ ℤ_{≥1}`. Hence Erdős–Straus Theorem 1 condition (ii),
"`{N_k/n_{k+1}}` bounded", is exactly "`κ_n u_n` bounded", and it implies
`u_n = O(1)`. The corpus's first necessary condition on a counterexample,
`C_n → ∞`, is precisely the negation of (ii); equivalently a counterexample has
`lcm(a_1,…,a_{n-1})/a_n → ∞`, whereas the Sylvester sequence has
`A_{n-1} = Π_{n-1} = a_n − 1`. Verified: `c_k = κ_{k+1}u_{k+1}` on 49 frames with
`a_k ≥ 2^{40}`, zero mismatches; `A_{n-1}/a_n = κ_n u_n/q` to relative error
`< 9·10^{-13}` on 86 frames.

### 3.2 The lcm refinement buys exactly the primitive reduction

The literature's strongest form (Tijdeman–Yuan) weights by `A_{n-1}/a_n` where
Koizumi's Corollary 20(1) weights by `Π_{n-1}/a_n`. The ratio is the lcm defect
`L_{n-1} := Π_{n-1}/A_{n-1} ∈ ℤ_{≥1}`, which is unbounded in general (measured
up to 128 on `q ≤ 60`). The corpus records the same object as the overlap debt
`M_n = qΠ_{n-1}/lcm(q, a_1,…,a_{n-1}) = L_{n-1}·gcd(q, A_{n-1})`, proves
`M_n ∣ C_n` and `M_n ∣ E_n` in `CumulativeLcmTransfer.lean`, and states in
`SlowNegativePartRigidity.md` §4 that "whether `limsup Q_n/M_n < ∞` suffices is
open", where `Q_n = (Π_{n-1}/a_n)(a_n^2/a_{n+1} − 1) = −(B_{n-1}/C_1)E_n + o(1)`.

**Theorem U1-1 (exact factorisation of the gcd).**
`G_n = κ_n L_{n-1} = κ'_n M_n` with `κ'_n = lcm(q,A_{n-1})/v_n ∈ ℤ_{≥1}`.
All factors are positive integers, so `L_{n-1} ∣ M_n ∣ G_n ∣ C_n` and
`E_n/M_n = κ'_n e_n ∈ ℤ`. Verified on 4,472 exact frames, zero failures.

**Theorem U1-2 (the lcm criterion at level `≤ 0` is the product criterion).**
`Q_n/M_n = −(B_{n-1}/C_1)·κ'_n e_n + o(1/M_n)`. Since `κ'_n ≥ 1` and `e_n ∈ ℤ`,
`limsup_n Q_n/M_n ≤ 0` holds iff `E_n ≥ 0` for all large `n`. The same holds for
Tijdeman–Yuan's own normalisation `(A_{n-1}/a_n)(a_n^2/a_{n+1}−1) = Q_n/L_{n-1}`
and for Erdős–Straus Theorem 3's `A_{n-1}(a_n^2/a_{n+1}−1) = a_nQ_n/L_{n-1}`.
Therefore Tijdeman–Yuan Theorem 4.1, Erdős–Straus Theorem 3, Badea and Koizumi
Corollary 20 all decide exactly the half-space `{E_n ≥ 0 eventually}`, which
Koizumi Proposition 19(2) closes in two lines. Verified: the exact relation
`Q_{TY} = −Q_{ES}/L_{n-1}` holds with zero failures, `q·Q_{ES} = E_n` and
`q·Q_{TY} = −κ_n e_n` to `10^{-11}`, and the sign of `Q_{ES}` matches the sign of
`E_n` at every frame.

This settles the `≤ 0` half of the corpus's open question negatively: the lcm
weighting gains nothing there, because dividing by `M_n` replaces the integer
`E_n` by the integer `κ'_n e_n`, and "a small integer is `≤ 0`" is invariant
under the primitive reduction the corpus already performs.

**Theorem U1-3 (the `< ∞` half is orthogonal to the surviving regime).**
`limsup_n Q_n/M_n < ∞` holds iff `κ'_n(−e_n)_+` is bounded, iff
`(−E_n)_+ = O(M_n)`. The corpus's Lean-proved product row is `(−E_n)_+ = O(1)`,
so the entire open gap is the factor `M_n`. Now `M_n ∣ G_n = G_1∏_{k<n}h_k`, so:

1. If the tail is cancellation-free (`h_n = 1` for `n ≥ N`) then `G_n` is
   constant, `M_n` is nondecreasing and bounded, hence eventually constant, and
   `limsup Q_n/M_n < ∞` is equivalent to `limsup Q_n < ∞`, which is already
   proved. The lcm refinement is empty on cancellation-free tails.
2. By Proposition S4-B, `∑_{n<N} log h_n ≤ log C_N = o(N)`, so
   `M_n ≤ G_n ≤ C_n = e^{o(n)}`: the maximum possible gain is `e^{o(n)}` and it
   is available only at paid steps `h_n > 1`.
3. Every record of `u` is set by a clean step (wave-1 F), and a clean step has
   `h_n = 1`, so it contributes no factor to `M`. The indices the surviving
   regime is made of, the cofinally many clean primitive record jumps of size
   `≥ 3` of §11.1, are exactly the indices at which `M` does not grow.

So the open lcm-weighted question cannot be answered by anything that acts on
the clean record jumps, and on the corpus's own exact fixtures it is not merely
unproved but vacuous.

### 3.3 The cancellation-free sub-regime

Assume `h_n = 1` for all `n ≥ N`. Then `v_{n+1} = a_nv_n`, `u_{n+1} = a_nu_n − v_n
= u_n − e_n`, `gcd(u_n,v_n) = 1`, and `gcd(a_n, v_n) = 1`, so the multipliers are
pairwise coprime from `N` on and coprime to `v_N`; equivalently
`gcd(A_{n-1}, a_n) = 1`, `L_{n-1}` and `κ_n` are eventually constant, and
`u_m ≡ −v_j∏_{i=j+1}^{m-1}a_i (mod a_j)` for `m > j`, i.e. `a_j^2 ∣ v_m + a_ju_m`.

**Proposition U1-5.** In a cancellation-free tail,
`u_{n+2} = (a_{n+1}+a_n)u_{n+1} − a_n^2 u_n` and
`e_{n+1} = a_n^2 e_n − Δ_n u_{n+1}`.
Verified on 610 clean triples, zero failures. The second identity is the exact
form of the corpus congruence `e_{n+1} ≡ a_n^2 e_n (mod u_{n+1})`: it says the
defect is `Δ_n = (a_n^2e_n − e_{n+1})/u_{n+1}`, so a single negative primitive
error at a clean step costs a defect of size about `a_n^2|e_n|/u_n`, and
`a_{n+1}/a_n^2 → 1` is exactly `|e_n|/u_n → 0`.

The classical size-plus-divisibility argument does not close this case, and the
reason is structural rather than technical. The only integrality resource is
`v_n ∣ qA_{n-1}`, that is `qA_{n-1}x_n = κ_n u_n ∈ ℤ`. The classical step needs
`−E_n/D_n = −e_n/v_n` to be smaller than the spacing `1/(qA_{n-1}) = 1/(κ_n v_n)`
of the lattice it lives on. Those two quantities differ by the factor `κ_n(−e_n)`,
so the required smallness is `−e_n < 1/κ_n ≤ 1`, which for an integer `e_n` is
the conclusion itself. In a cancellation-free tail `κ_n` is constant, so no
amount of later structure changes the comparison. This is the precise sense in
which the classical mechanism is circular in the open branch.

## 4. Where it stops, with the fixture

The failing lemma is **Tijdeman–Yuan Theorem 4.1's hypothesis**, and equivalently
Erdős–Straus Theorem 3's (ii'') and Koizumi Corollary 20(1)'s liminf condition.
In the Ahmes case with `b_n ≡ 1` it is not a growth restriction on `Δ_n`: by
Theorem U1-2 it is the assertion `E_n ≥ 0` for large `n`, dressed as an analytic
condition by the weight `A_{n-1}/a_n`, which is `κ_nu_n/q(1+o(1))` and therefore
tracks the state rather than constraining it.

The finite fixture is the corpus's own S4-R family
(`scripts/erdos243_clean_rise_cost_probe.py`, `s4r_seed`): heights `c_n = c + nm`,
`D_n = (a_n−1)c_n − m`, `a_n = 1 + c_{n+1}k_n`, `k_0 = λ∏_{j=2}^{H+1}c_j`. On
`(c,m,H) = (10,3,6)`, `(13,3,6)` and `(100003,3,5)` the exact orbit has, at every
index of the block,

    E_n = −3,  G_n = 1,  L_{n-1} = 1,  κ_n = 1,  M_n = 1,  Δ_n < 0,
    q·(A_{n-1}/a_n)(a_n^2/a_{n+1} − 1) = 3 = −E_n.

Every classical criterion's hypothesis quantity is positive and equal to `−E_n`
at every index of an arbitrarily long block, and the lcm weight is trivial there
because the block is cancellation-free. The defects are large and negative
(`Δ_0 = −821{,}441{,}431{,}921{,}017{,}600` at `(10,3,6)`, growing doubly
exponentially), yet `Δ_n = o(a_n^2)` throughout, so the regime hypothesis holds
and the classical hypotheses fail by exactly `m` units. The recovery family
`(11, 11(33 + 79833600k) − 1)` behaves the same way with `G_n = 4`, `L = 1`,
`κ_n = 4`, `E_n = −4`, `e_n = −1`, and `q·Q_{TY} = 4 = κ_n·|e_n|`, which is the
`κ' > 1` case of Theorem U1-2 in action.

What the corpus's verified necessary conditions do not repair. `C_n → ∞` kills
Erdős–Straus Theorem 1 rather than being repaired by it (Proposition U1-4).
Divergent `B`-shifted excess mass, record increments above `ℓ(C_n)`, roughness of
the multipliers and aperiodicity of the primitive error are all statements about
the negative branch; none of them bounds `κ'_n(−e_n)_+`, which is what the lcm
criterion needs, and the one place where a bound would come cheaply (the growth
of `M_n`) is confined to paid steps by Theorem U1-3(3). Koizumi Remark 21 is the
sharpest sufficient condition in the literature and it asks for `|E_n| = o(1)`,
instantiated by `ε_n = o(1/n)`; the corpus's necessary condition is only
`log C_n = o(n)`, and the gap between the two is the whole problem.

## 5. What this leaves open

The two doors named in §9 of the conductor notes are untouched by the classical
toolkit and remain the doors. To them this desk adds one sharpened target: the
corpus's own open question `limsup Q_n/M_n < ∞ ⟹ Sylvester` is now known to be
equivalent to `(−E_n)_+ = O(M_n) ⟹ Sylvester`, to be empty on cancellation-free
tails, and to be blind to clean record jumps. If it is to be worth a desk, the
statement to aim at is `(−e_n)_+ ≤ B ⟹ Sylvester` for `B ≥ 3` with arbitrary
cancellation, which is the primitive form of r08 Corollary 6 and is already
proved for `B ≤ 2` by `primitive_record_two_unit_rigidity`.
