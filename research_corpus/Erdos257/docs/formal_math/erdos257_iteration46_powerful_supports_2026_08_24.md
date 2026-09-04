# Erdős 257 — iteration 46: irrationality for prime-power-rich powerful supports

**Disjoint path.** Prior: `…iteration44_parity_certificate_2026_08_24` (§EV–§FB2, the certificate
machinery), `…iteration45_positive_density_point_2026_08_24` (§FG–§FJ), `…session_summary_2026_08_23`.

Iteration 44 built a finite certificate criterion and noted it is *equivalent* to the conjecture, so
it cannot be closed by a softer argument. Iteration 45 put one point in the open region by a
Diophantine split and said in §FJ that the real advance would be a support whose irrationality is
forced by **the arithmetic of `τ_A` itself**.

This iteration does that for a broad, explicitly delimited class rather than one point:

> **THEOREM.** Let `A` be an infinite set of **powerful** integers (`p ∣ d ⟹ p² ∣ d` for every
> `d ∈ A`), and suppose there is a fixed `t ≥ 2` such that for infinitely many primes `q`,
> `q^t ∈ A` and `q^v ∉ A` for `1 ≤ v < t`. Then for **every** integer `b ≥ 2`,
> `Σ_{d∈A} 1/(b^d − 1)` is irrational.

The hypothesis is on the *support*, not on growth: `A` need not be lacunary, pairwise coprime,
periodic, or a monomial image. Every infinite subset of the powerful numbers meeting the stated
fixed-height prime-power condition is covered. This is a uniform theorem for
**prime-power-rich powerful supports**; it is not a theorem for every powerful support (see §FQ).

Everything in §FK–§FN is proved. §FO records verification. §FP is the honest priority boundary:
**the `A = {k^s}` case is prior art (Duverney–Tachiya 2019); the prime-power-rich powerful-support
statement was not located in the bounded search recorded there. No novelty or priority claim is made
without specialist review.**

---

## FK. Setup and the certificate lemma [PROVED]

Fix an integer `b ≥ 2`. For infinite `A ⊆ ℕ_{>0}` put `τ_A(m) = #{d ∈ A : d ∣ m}` and

    y := Σ_{d∈A} 1/(b^d − 1) = Σ_{m≥1} τ_A(m) b^{−m},        R_M := Σ_{j≥1} τ_A(M+j) b^{−j}.

Both converge, since `τ_A(m) ≤ d(m) ≤ 2√m`. From `b^M y = Σ_{m≤M} τ_A(m)b^{M−m} + R_M` we get
`R_M = b^M y − n_M` with `n_M ∈ ℤ`.

**Lemma 1 (integrality under rationality).** Suppose `y = P/Q ∈ ℚ`. Write `Q = Q_b Q'` with every
prime factor of `Q_b` dividing `b` and `gcd(Q', b) = 1`; let `r := ord_{Q'}(b)` (`r = 1` if `Q' = 1`)
and let `s` be least with `Q_b ∣ b^s`. If `R` is a multiple of `r` and `M − R ≥ s`, then

    R_M − R_{M−R} ∈ ℤ.

*Proof.* `R_M − R_{M−R} = b^{M−R}(b^R − 1)y − (n_M − n_{M−R})`. Now `Q_b ∣ b^s ∣ b^{M−R}` and
`Q' ∣ b^r − 1 ∣ b^R − 1`, so `Q ∣ b^{M−R}(b^R−1)` and the first term is an integer. ∎

**Lemma 2 (certificate).** Let `R ≥ 1`, `L ≥ 0`, `n > R`, and set `c_m := τ_A(m) − τ_A(m−R)`. Suppose

  (C1) `c_{n+i} = 0` for `i = 1, …, L`;
  (C2) `b ∤ c_n`;
  (C3) `σ := b^{−(L+1)}(R_{n+L} + R_{n+L−R}) < 1/b`.

Then `R_{n−1} − R_{n−1−R} ∉ ℤ`.

*Proof.* `w := R_{n−1} − R_{n−1−R} = Σ_{j≥1} c_{n−1+j} b^{−j}`. By (C1) the terms `j = 2,…,L+1`
vanish, so `w = c_n/b + E` with

    |E| ≤ Σ_{i≥1} |c_{n+L+i}| b^{−(L+1+i)}
        ≤ b^{−(L+1)} Σ_{i≥1} (τ_A(n+L+i) + τ_A(n+L+i−R)) b^{−i} = σ.

Write `c_n = κb + τ` with `0 < τ < b`, possible by (C2). Then `dist(c_n/b, ℤ) = min(τ, b−τ)/b ≥ 1/b`,
so `dist(w, ℤ) ≥ 1/b − σ > 0`. ∎

**Proposition 3 (criterion).** If for every `r ≥ 1` and every `T ≥ 1` there exist a multiple `R` of
`r` and an `n > R + T` satisfying (C1)–(C3), then `y` is irrational.

*Proof.* Otherwise take `r, s` from Lemma 1 and apply the hypothesis with `T = s + 1`; then
`n − 1 − R ≥ s`, so Lemma 1 forces `R_{n−1} − R_{n−1−R} ∈ ℤ`, contradicting Lemma 2. ∎

Note what (C1)–(C3) are: a **finite, purely combinatorial** statement about `τ_A`, with no evaluation
of `y` and no unknown constants. This is iteration 44's §EW machinery restated at base `b`, with the
parity condition replaced by the weaker and base-correct `b ∤ c_n`.

## FL. Two reductions that make the certificate constructible [PROVED]

Fix `R` and put `A^R := {d ∈ A : d ∣ R}` and `A_R := A ∖ A^R`.

**Lemma 4 (only `A_R` matters).** For every `m`,
`c_m = Σ_{d ∈ A_R} ( [d ∣ m] − [d ∣ m−R] )`.

*Proof.* If `d ∣ R` then `d ∣ m ⟺ d ∣ m−R`, so those terms cancel. ∎

So (C1) and (C2) are statements about `A_R` alone, and `Σ_{d ∈ A_R} 1/d` can be made as small as we
like by taking `R` divisible by `lcm(A ∩ [1,K])` for large `K` — *provided* `Σ_{d∈A} 1/d < ∞`. For
powerful `A` that is automatic:

    Σ_{n powerful} 1/n = ζ(2)ζ(3)/ζ(6) = 1.9436…  < 2.                                    (†)

**Lemma 5 (rigidity of powerful supports).** Let `A` consist of powerful numbers, let `d₀ ∈ A`, and
let `u` be **squarefree with `gcd(u, d₀) = 1`**. Then every `d ∈ A` with `d ∣ d₀u` satisfies `d ∣ d₀`.

*Proof.* Suppose `v_p(d) > v_p(d₀)` for some prime `p`. From `d ∣ d₀u`,
`v_p(d) ≤ v_p(d₀) + v_p(u)`. If `v_p(d₀) > 0` then `p ∤ u`, so `v_p(d) ≤ v_p(d₀)` — contradiction.
Hence `v_p(d₀) = 0`, so `v_p(d) ≤ v_p(u) ≤ 1` because `u` is squarefree. But `d` is powerful, so
`v_p(d) ≥ 2`. Contradiction. Therefore `v_p(d) ≤ v_p(d₀)` for every `p`. ∎

Lemma 5 is the load-bearing step and it is where *powerful* is used: it turns "which elements of `A`
divide `n`" from a sieve problem into a **deterministic** one. No union bound is spent at the defect
position.

## FM. The construction [PROVED]

Let `A` be as in the Theorem, and fix `r ≥ 1`, `T ≥ 1`.

**Step 1 — the window length `L`, chosen first and independent of everything else.**
For a prime `q` with `d₀ = q^t` and any integer `a`, the mean of `τ_A(d₀u + a)` over `u ≤ U` tends to
`Σ_{d∈A} [gcd(d,d₀) ∣ a] · gcd(d,d₀)/d ≤ Σ_{v=0}^{t} q^v Σ_{d∈A,\, q^v ∣ d} 1/d`. For `v = 0` this is
`< 2` by (†); for `v ≥ 1` every `d ∈ A` with `q^v ∣ d` is powerful, hence of the form `q^w m` with
`w ≥ max(v,2)` and `m` powerful and coprime to `q`, so
`Σ_{d∈A, q^v∣d} 1/d ≤ 2·(Σ_{w≥max(v,2)} q^{−w}) < 4q^{−v}`, and the term is `< 4`. Hence

    mean_u R_{d₀u + a} ≤ (b−1)^{−1} (2 + 4t) =: μ,     independent of q, K and R.

Here the passage from finite congruence counts to the infinite sum is legitimate, rather than a
formal interchange: truncate to `d ≤ d₀U+|a|`, count each soluble congruence with
`U·gcd(d,d₀)/d + O(1)` representatives, and use
`#{d ≤ X : d powerful} = O(√X)`. For fixed `d₀` the accumulated `O(1)` error is therefore `o(U)`;
the displayed convergent reciprocal majorant then controls the truncation tail.

Fix `L := ⌈ log_b (16μ) ⌉ + 1`, so that `b^{−(L+1)}·16μ < 1/b`.

**Step 2 — `K` and `R`.** By (†) and `Σ_{d∈A}1/d < ∞`, choose `K` with
`E(K) := Σ_{d∈A,\,d>K} 1/d < 1/(100(L+1))`, and put `R₀ := r · lcm(A ∩ [1,K])`.

**Step 3 — `d₀`.** Choose a prime `q` with `q^t ∈ A`, `q^v ∉ A` for `1 ≤ v < t`, and
`q > max(K, L+2, r, T, 128)`; infinitely many such `q` exist by hypothesis. Put `d₀ := q^t`. Since every
prime factor of `lcm(A∩[1,K])` is `≤ K < q` and `q ∤ r`, we have `gcd(R₀, d₀) = 1`.

**Step 4 — `R`.** Choose `c` with `cR₀ ≡ −1 (mod d₀)` and set `R := cR₀`. Then `r ∣ R`,
`gcd(R, d₀) = 1` (so `d₀ ∈ A_R`), and `R ≡ −1 (mod q^v)` for every `1 ≤ v ≤ t`. Also
`A_R ⊆ {d ∈ A : d > K} ∪ {d ∈ A : q ∣ d}` — every `d ∈ A` with `d ≤ K` and `q ∤ d` divides `R₀ ∣ R`.

**Step 5 — `n`.** Let `n := d₀ u` with `u` squarefree and `gcd(u,q) = 1`. Write
`𝒜 := {0, −R} ∪ {i, i−R : 1 ≤ i ≤ L}`, the shift set.

**Claim A (defect, deterministic).** `{d ∈ A_R : d ∣ n} = {d₀}`.
*Proof.* By Lemma 5, `d ∣ n ⟹ d ∣ d₀ = q^t`, so `d = q^v` with `0 ≤ v ≤ t`. `d = 1` divides `R`, so
`1 ∉ A_R`. For `1 ≤ v ≤ t`, `q^v ∈ A` only for `v = t` by the choice of `q`. And `q^t ∤ R`. ∎

**Claim B (`d₀` misses every other shift).** For `a ∈ 𝒜 ∖ {0}`, `d₀ ∤ n + a`.
*Proof.* `d₀ ∣ n`, so `d₀ ∣ n+a ⟺ d₀ ∣ a`. `a = −R`: `gcd(R,d₀)=1` and `d₀>1`. `a = i`:
`0 < i ≤ L < d₀`. `a = i−R ≡ i+1 (mod d₀)` and `0 < i+1 ≤ L+1 < d₀`. ∎

**Claim C (no `d ∈ A_R` divisible by `q` hits any nonzero shift).** If `q ∣ d` and `d ∣ n+a` with
`a ∈ 𝒜∖{0}`, then with `v := min(v_q(d), t) ≥ 1` we need `q^v ∣ a`. But `q ∤ R`; `q ∤ i` since
`0 < i ≤ L < q`; and `i − R ≡ i+1 (mod q^v)` with `0 < i+1 ≤ L+1 < q ≤ q^v`. So no such `d` exists. ∎

**Claim D (union bound for the rest).** The remaining `d ∈ A_R∖{d₀}` have `q ∤ d`, hence
`gcd(d,d₀) = 1`, so `d ∣ d₀u + a` puts `u` in a single class mod `d`, of density `1/d`. Summing over
the `2L+1` nonzero shifts,

    density of bad u  ≤  (2L+1) Σ_{d∈A_R} 1/d  ≤  (2L+1) E(K)  <  1/40.

Here `Σ_{d ∈ A_R} 1/d ≤ E(K)` because every `d ∈ A_R` with `q ∤ d` exceeds `K` (Step 4).
Precisely, for `u ≤ U` only `d ≤ d₀U+O(1)` can occur. The union count is bounded by
`UΣ_d 1/d + O(#{d ≤ d₀U+O(1): d powerful})`; after division by `U`, the second term is `o(1)` by
the `O(√X)` powerful-number count. Thus the displayed inequality is an upper-density bound, not an
unqualified countable-union assertion.

**Claim E (tail bound).** By Step 1 and Markov, the set of `u` with `R_{n+L} > 8μ` has density `< 1/8`,
and likewise for `R_{n+L−R}`; so both are `≤ 8μ` outside a set of density `< 1/4`.

**Putting it together.** Squarefree `u` coprime to `q` have exact density
`(6/π²)q/(q+1) ≥ 6/π² − 1/q > 0.6`, by the explicit choice `q > 128`. Removing
Claims D and E costs `< 1/40 + 1/4 < 0.28`, so a set of `u` of density `> 0.32` remains; in
particular there are arbitrarily large such `u`, hence `n > R + T`. For such an `n`:

* (C1): by Lemma 4, `c_{n+i} = Σ_{d∈A_R}([d∣n+i] − [d∣n+i−R])`, and Claims B, C, D say no `d ∈ A_R`
  divides `n+i` or `n+i−R`. So `c_{n+i} = 0` for `1 ≤ i ≤ L`.
* (C2): by Lemma 4, Claim A and Claims B–D (applied at `a = −R`), `c_n = 1 − 0 = 1`, and `b ∤ 1`.
* (C3): `σ = b^{−(L+1)}(R_{n+L} + R_{n+L−R}) ≤ b^{−(L+1)}·16μ < 1/b` by Claim E and Step 1.

Proposition 3 now gives the Theorem. ∎

## FN. What the hypotheses buy, and corollaries [PROVED]

Both hypotheses are used exactly once and neither can be dropped from this proof:

* **powerful** is used only in Lemma 5, to make the defect deterministic;
* **`q^t ∈ A` with `q^v ∉ A` for `v < t`** is used only to make `gcd(R, d₀) = 1` (Steps 3–4) and to
  make the count in Claim A equal to `1` rather than merely nonzero.

**Remark (a second admissible hypothesis).** The prime-power condition is used only to force
`gcd(R, d₀) = 1` and to make Claim A a singleton. Both also follow if instead

> `A` contains infinitely many elements `d₀` that are **coprime to every smaller element of `A`**,

since then Lemma 5 gives `{d ∈ A : d ∣ n} ⊆ {1, d₀}` directly, and `d₀` is automatically coprime to
`lcm(A ∩ [1,K])` for `K < d₀`. (At most `ω(r)` such `d₀` can share a factor with `r`, because any two
of them are coprime, so infinitely many survive.) One bookkeeping change is required: `μ` in Step 1
then depends on `d₀`, so the parameter order becomes `d₀ → μ → L → K` with `K < d₀`, which closes
because `μ(d₀) ≤ ∏_{p ∣ d₀}(1 − p^{−1/2})^{−1} = d₀^{o(1)}` while `E(K) ≪ K^{−1/2}`. The two
hypotheses are incomparable, and neither covers e.g. `A = {36k²}`; see §FQ.

**Corollary 1.** `Σ_{n powerful} 1/(b^n − 1)` is irrational for every integer `b ≥ 2`.
(`t = 2`: `q² ` is powerful and `q` is not.)

**Corollary 2.** For every `s ≥ 2`, `Σ_{n \ s-full} 1/(b^n − 1)` is irrational, where `n` is `s`-full
iff `p ∣ n ⟹ p^s ∣ n`. (`t = s`.)

**Corollary 3.** For every `s ≥ 2` and **every** set `S ⊆ ℕ` containing infinitely many primes,
`Σ_{k ∈ S} 1/(b^{k^s} − 1)` is irrational. (`A = {k^s : k ∈ S}`, `t = s`.) No structure on `S` beyond
"infinitely many primes" is needed — in particular `S` may be arbitrarily irregular.

**Corollary 4.** `Σ_{n powerful,\, n ≡ a (mod m)} 1/(b^n − 1)` is irrational whenever `q² ≡ a (mod m)`
is solvable with `gcd(q,m)=1` (Dirichlet supplies infinitely many such primes `q`).

Corollary 3 with `S = ℕ` recovers `Σ_{k≥1} 1/(b^{k^s}−1)`, which is **not** new (see §FP).
Corollaries 1, 2, 4 and Corollary 3 for general `S` are not located in the literature.

## FO. Verification [COMPUTED]

All computations in `scratchpad/e257/` (`pf.py`, `pf2.py`, `pf3.py`, `pf4.py`), reproduced in-repo as
`docs/formal_math/erdos257_powerful_support/verify.py`.

* **The classical route provably fails on these supports.** For `A = {k²}` the truncation denominator
  is `lcm{b^d−1 : d ∈ A, d ≤ K} = ∏_{e ∈ Div} Φ_e(2)`, of bit-size `Σ_{e∈Div} φ(e)`. Measured:
  `48, 312, 2376, 7776` bits at `m = 5, 10, 20, 30`, against a tail worth only `(m+1)² = 36, 121,
  441, 961` bits. The gap is cubic-against-quadratic and widening — the Padé/denominator argument
  cannot reach any of these supports.
* **The construction fires as designed.** For `A =` powerful numbers, `t = 2`, and every
  `r ∈ [1,120]`, Steps 1–5 produce certificates at bases `b = 2, 3, 10`: `c_n = ±1`, `c_{n+i} = 0` for
  `i ≤ L`, `σ < 1/b`, and `r ∣ R` in every case. Example (`b=2`, `r=7`): `R = 3024`, `d₀ = 25`,
  `4028` certificates with the least at `n = 3050`.
* **The hypotheses are sharp for the construction, not decorative.** Running the same search with
  `d₀` chosen as `min A_R` *without* the coprimality of Step 3 yields **zero** certificates exactly in
  the rows where `gcd(d₀, R) > 1` (e.g. `d₀ = 8`, `R = 4`), and hundreds as soon as `gcd(d₀,R) = 1`
  (e.g. `d₀ = 9`). The failure mode predicted by Steps 3–4 is the failure mode observed.
* **Cross-check on (†).** `Σ_{n powerful, n ≤ 6·10⁵} 1/n = 1.9409` against
  `ζ(2)ζ(3)/ζ(6) = 1.9436`.

## FP. Priority — checked, and one case is prior art [ASSESSMENT + VERIFIED]

The `A = {k^s}` case is **not new**. Duverney–Tachiya, *Refinement of the Chowla–Erdős method and
linear independence of certain Lambert series*, Forum Math. **31** (2019) 1557–1566, Corollary 1.2
(author preprint p. 4) states: for `E ∈ ℰ` and `F_s(E)` the set of products of members of `E` with
exponents `< s`, and `|q|^L ≤ s` with `L = lcm(1,…,ℓ)`, the numbers `1` and
`Σ_{n∈F_s} (q^{jn^i} − 1)^{−1}` (`i ≤ ℓ`, `j ≤ h`) are linearly independent over `ℚ`; and
*"in particular, if `s := ∞`, then the numbers (1.12) are linearly independent over `ℚ` for any
integer `q` (`|q|>1`)"*. Taking `E = P`, `s = ∞` (so `F_∞ = ℕ`), `i = s`, `j = 1` gives exactly
`Σ_{k≥1} 1/(b^{k^s}−1)`. **This was verified against the paper text, not inferred.** The repo's own
survey (`…/paper_257.md` line 274) reads the `i ≥ 2` exclusion as attached to the `s = 2` row; at
`s = ∞` the constraint `|q|^L ≤ s` is vacuous and higher `i` are admitted. That reading of the survey
is corrected here.

What is **not** covered by that theorem: its supports are always `{n^i : n ∈ F_s(E)}` — the `i`-th
power image of a full multiplicative semigroup generated by a pairwise coprime sequence. An arbitrary
infinite set of powerful numbers is not of that shape, and neither is the set of all powerful numbers,
the set of `s`-full numbers, or `{k^s : k ∈ S}` for irregular `S`.

Against the other known mechanisms:

| mechanism | why it does not cover an arbitrary powerful support |
|---|---|
| Erdős 1948 (full support), dilates, eventually periodic | powerful supports have density `0` and are not periodic |
| Erdős 1968 (pairwise coprime, `Σ1/a < ∞`) | powerful numbers are not pairwise coprime (`4, 8, 16, …`) |
| classical denominator-gap (factorials, `{2^k}`) | fails by §FO's measured cubic-vs-quadratic gap |
| Duverney–Tachiya `F_s(E)` and monomial images | supports must be a monomial image of a semigroup |
| Tao–Teräväinen 2025 (primes, base 2) | disjoint support class |
| Mahler / Nishioka (`§CG/§CL`) | `Y_A` Mahler ⟺ `k`-free part finite; not applicable |

**Erdős's own unproved extension.** Immediately after the p. 222 theorem of *On the irrationality of
certain series*, Math. Student **36** (1968), 222–226, Erdős says pairwise coprimality can be removed
by a more complicated argument, and does not give that argument (p. 226 repeats the boundary). The
Theorem here is a proved instance of that removal on a natural sub-universe: powerful supports have
`Σ 1/d < ∞` and are as far from pairwise coprime as a support can be.

**Novelty status: candidate scoped result; no priority claim.** Searches run this pass: the
erdosproblems.com #257 reference list as recorded in the repo survey, Duverney–Tachiya (full text
read), plus web searches on Lambert-series irrationality and on "powerful numbers". The
erdosproblems.com page itself returned `403` to automated fetch and was **not** read this pass; the
repo survey's transcription of it is `reported_prior`, not `verified_current`. Treat the priority of
Corollaries 1, 2 and 4, and of the general prime-power-rich theorem, as open until specialist review.

## FQ. Honest boundary [ASSESSMENT]

**This does not solve Erdős 257.** The problem asks for every infinite `A ⊆ ℕ`; this settles the
prime-power-rich part of the powerful sub-universe. The two live obstructions are unchanged:

* **Positive density is untouched by this method.** Lemma 4's reduction needs `Σ_{d ∈ A_R} 1/d`
  small, which needs `Σ_{d∈A} 1/d < ∞`. Every positive-density support — Beatty, Thue–Morse, and
  `A = ℕ` itself — has divergent reciprocal sum, so Step 2 cannot even start. §CJ's open region is
  still open, and iteration 45's point in it is still the only point.
* **Not every powerful support is covered.** `A = {36k²}` is powerful, is not lacunary, contains no
  prime power, and has no element coprime to a smaller one — so it satisfies neither hypothesis. The
  construction still appears to work there (`d₀ = 36p²` for `p` the least prime power above
  `√(K/36)` gives `d₀/gcd(d₀,R₀) = p² → ∞`, which is what the gcd bookkeeping actually needs), but the
  general statement "every infinite powerful support" is **not proved here**. The clean question left
  open is whether `d₀/gcd(d₀, R₀) → ∞` can fail for a powerful `A` outside the classical lacunary
  class.
* **The certificate criterion remains equivalent to the conjecture** (§FA). What changed is not the
  criterion but that a nontrivial class of supports now has a *constructible* certificate: Lemma 5
  turns the defect from a sieve question into an identity.

**What this does add to the map.** It is the first mechanism in this session that proves irrationality
for an infinite family of supports, unconditionally, at every base, by `τ_A` arithmetic alone — no
Diophantine split, no growth hypothesis, no coprimality, no Mahler theory. The `A = {k^s}` corollary
gives an elementary two-page proof of a case that previously required the Chowla–Erdős refinement.

*Status: §FK–§FN proved and self-contained modulo `Σ_{n powerful}1/n = ζ(2)ζ(3)/ζ(6)`. §FO computed
and reproducible. §FP verified against the Duverney–Tachiya text; erdosproblems.com not read this
pass. §FQ assessment.*
