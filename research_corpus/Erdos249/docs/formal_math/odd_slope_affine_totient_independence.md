# The totient k-kernel: exact rank for every base, and a corrected provenance

Status 2026-08-12, **revised** after the all-base arithmetic and spanning layer
landed in the public Lean corpus. The earlier version of this file classified the
affine independence theorem as "novelty unassessed"; that was wrong. A later
version also described the whole all-base theorem as unformalised; that is now too
coarse. Three claims live here with **different** evidence classes; never merge
them.

| Claim | Evidence | Provenance |
|---|---|---|
| **A. Affine totient independence** (odd slopes) | Lean-checked, sorry-free, axioms `[propext, Classical.choice, Quot.sound]` | **Subsumed by Martin 2006, Theorem 1.** Our contribution is a Lean formalisation and an alternative finite-determinant proof of a corollary of Martin — *not* an original theorem. |
| **B. Totient k-kernel rank `k^e + 1` for every integer `k ≥ 2`** | Paper proof plus a Lean-checked unconditional arithmetic/spanning layer and a Lean-checked exact-rank conclusion **conditional on `LinearIndependent`**. The unconditional all-base independence theorem, `Basis`, and complete relation normal form are not in Lean. | Rank formula, explicit basis and complete relation normal form: no source located. Novelty unassessed pending specialist review. |
| **C. Erdős #249** | — | Untouched. Open. Nothing here bears on it. |

---

## 0. The provenance correction

**Greg Martin, "Simultaneous inequalities among values of the Euler phi-function",
arXiv:math/0603053, submitted 2 March 2006.** Annexed at
`annexes/martin-2006-simultaneous-phi-inequalities/` (arXiv LaTeX source, not a
summary). Theorem 1, verbatim from that source:

> Let `k ≥ 2` be an integer, let `a_1,…,a_k` be positive integers, and let
> `b_1,…,b_k` be integers. Assume that `a_i b_j ≠ a_j b_i` for every
> `1 ≤ i < j ≤ k`. Then for any positive constant `C`, the set of positive
> integers `n` for which
> `φ(a_1 n+b_1)/φ(a_2 n+b_2) > C, …, φ(a_{k-1} n+b_{k-1})/φ(a_k n+b_k) > C`
> has positive lower density.

Martin also remarks that the hypotheses are symmetric in the polynomials, so any
of the `k!` prescribed orderings occurs on a positive-lower-density set.

### Dominance corollary (immediate from Martin)

Let `L_1,…,L_m` satisfy Martin's hypotheses. Then `{n ↦ φ(L_i(n))}` is linearly
independent **over ℝ**, hence over every characteristic-zero subfield.

*Proof.* Suppose `S(n) = Σ c_i φ(L_i(n)) ≡ 0` with `c_t ≠ 0`. By the symmetry
remark, reorder so `L_t` is first. Take `C > (Σ_{i≠t}|c_i|)/|c_t|`. Chaining the
ratio gaps gives `φ(L_t(n)) > C·φ(L_i(n))` for every `i ≠ t` on a set of positive
lower density, so `|c_t|φ(L_t(n)) > Σ_{i≠t}|c_i|φ(L_i(n))` and `S(n) ≠ 0` there.
Contradiction. ∎

**Consequences for our theorem A.** Three of its four hypotheses are unnecessary:
slopes need not be odd, forms need not be primitive, and `b_i < a_i` is a
normal-form convenience. Martin needs only positive slopes and
`a_i b_j ≠ a_j b_i`. He also gets a strictly stronger conclusion (positive
density of simultaneous dominance) than bare non-vanishing.

**Correct classification of the Lean module:**

> A Lean formalisation, by an independent finite-determinant proof, of an
> immediate corollary of Martin's Theorem 1.

It is **not** a formalisation of Martin's theorem — Martin proves positive-density
simultaneous dominance by an analytic argument; the Lean module proves only linear
independence, via CRT + Dirichlet + a 2-adic determinant. Martin's own proof uses
a biased progression and disjoint prime sets with CRT, but has no evaluation
determinant and no 2-adic diagonalisation.

Also relevant: Martin's **Corollary 4** states that Theorem 1 and Corollaries 2–3
hold with `φ` replaced by `σ` throughout. So σ is already covered, in stronger
form. Do not present a σ analogue as new.

Provenance phrasing note: exact-title, DOI and venue searches did not locate a
separate journal publication. Say **"a corollary of Martin's 2006 arXiv
preprint"**, not "a published theorem".

---

## 1. Theorem A as checked

`formal_math/odd_slope_affine_totient/OddSlopeAffineTotient.lean`

```lean
theorem Erdos249257.OddSlopeAffineFamily.linearIndependent_family
    {ι : Type u_1} [Fintype ι] [DecidableEq ι] (F : OddSlopeAffineFamily ι) :
    LinearIndependent ℚ F.family
```

`#print axioms` → `[propext, Classical.choice, Quot.sound]`; `sorry` count 0.

Five of six ingredients were already generic in
`Erdos249257/TotientMahlerDefect.lean` and are reused unchanged
(`exists_large_distinct_primes_modEq_one`, `exists_affine_root_mod_prime`,
`affine_target_coprime_of_cross`, `paritySeparatedMatrix_det_ne_zero`,
`linearIndependent_of_separatedMinorCertificate`). The one new ingredient is
`exists_base_residue`: odd slopes are invertible mod 8, so every channel can be
steered to `3 mod 8` and the dyadic column-depth machinery collapses to depth 1.

That engineering value survives the provenance correction intact. What does not
survive is any claim of mathematical originality.

---

## 2. Theorem B — every integer base `k ≥ 2`

This is the real result, and it is strictly stronger than the odd-prime statement
the #249 note poses as `prob:oddprime`. It also strictly generalises the repo's
existing dyadic theorem (`k = 2`).

Write `F^{(k)}_{j,r}(n) = φ(k^j n + r)` and
`V_{k,e} = span_Q{F^{(k)}_{j,r} : 0 ≤ j ≤ e, 0 ≤ r < k^j}`.

> **Theorem.** For every integer `k ≥ 2` and every `e ≥ 1`,
> `dim_Q V_{k,e} = k^e + 1`, with basis
> `B_{k,e} = {F_{0,0}, F_{1,0}} ∪ {F_{j,r} : 1 ≤ j ≤ e, 1 ≤ r < k^j, k ∤ r}`.

**The basis condition is `k ∤ r`, not `gcd(k,r) = 1`.** For composite `k` a residue
may share prime factors with `k` and still be a basis residue. This is not a
detail: at `k = 4, e = 2` the `gcd`-version yields 12 elements where 17 are
needed; at `k = 12, e = 2`, 54 where 145 are needed.

### 2.1 Zero-residue relation

For `j ≥ 1`: `F_{j,0} = k^{j-1} F_{1,0}`.

Multiplying the argument by `k^{j-1}` raises `v_p` by exactly `(j-1)v_p(k)` for
every `p | k`, so prime-power evaluation gives `φ(k^j n) = k^{j-1} φ(k n)`.

### 2.2 Composite-base reduction

Let `r > 0` with `k | r`. Put `t = max{s : k^s | r}` and `r = k^t u` with `k ∤ u`;
since `r < k^j`, `t ≤ j-1`. Then

```
F_{j,r} = C_k(t,u) · F_{j-t,u},     C_k(t,u) = k^t · ∏_{p | k, p ∤ u} (1 - 1/p)
```

*Why it is independent of `n`.* Set `m = k^{j-t}n + u`. For `p | k` we have
`p | m ⟺ p | u`. Writing `p^α ∥ k`, the local factor of `φ(k^t m)/φ(m)` is
`p^{αt}` when `p | u` (independently of the exact `v_p(m) ≥ 1`), and
`p^{αt-1}(p-1) = p^{αt}(1 - 1/p)` when `p ∤ u`. Primes not dividing `k` are
untouched. ∎

This is the composite replacement for the prime-base coefficient
`ℓ^{t-1}(ℓ-1)`, which it recovers at `k = ℓ`, `u` coprime to `ℓ`.

### 2.3 Spanning and count

Zero residues reduce to `F_{1,0}`; positive residues divisible by `k` reduce to a
strictly lower level with `k ∤ u`. At level `j` exactly `k^{j-1}` of the `k^j`
residues are divisible by `k`, so
`|B_{k,e}| = 2 + Σ_{j=1..e}(k^j − k^{j-1}) = 2 + (k^e − 1) = k^e + 1`.

### 2.3a What the public Lean source now checks

At public source commit `9e231ce4371fcda607f81c4520d29b16dcb4482e`, the
all-base module checks the following layers separately:

* `totientKernelReductionScalar_ne_zero` and
  `allBaseTotientKernelSeq_mul_residue_step` establish the nonzero composite-base
  reduction scalar and the exact residue-reduction identity;
* `allBaseTotientKernelSeq_mem_span_canonical_of_le` and
  `span_allBaseTotientKernelThroughLevelFamily_eq_canonical` establish
  unconditional canonical spanning and span equality;
* `finrank_canonicalAllBaseTotientKernel_eq_of_linearIndependent` and
  `finrank_allBaseTotientKernelThroughLevelFamily_eq_of_linearIndependent`
  establish dimension `k^e+1` under the explicit hypothesis that the canonical
  family is linearly independent.

Thus the arithmetic, indexing and spanning parts of Theorem B are kernel-checked.
Lean does not discharge the `LinearIndependent` hypothesis. The paper discharges
it using Martin's theorem, and the complete basis and relation-normal-form
presentation remain paper mathematics rather than assumption-free Lean
declarations.

### 2.4 Independence

Restrict to `n = km + 1`. Then `F_{0,0}(km+1) = φ(km+1)`, and since
`gcd(k, km+1) = 1`, `F_{1,0}(km+1) = φ(k)·φ(km+1)` — the two base channels are
proportional on this progression, so they are handled separately. The remaining
channels become `F_{j,r}(km+1) = φ(k^{j+1}m + (k^j + r))`, i.e. affine forms

```
L_0(m) = k m + 1,        L_{j,r}(m) = k^{j+1} m + (k^j + r),   k ∤ r.
```

All slopes positive. Pairwise non-proportional:

* `L_0` vs `L_{j,r}`: cross-difference `k(k^j + r) − k^{j+1} = k r ≠ 0`.
* `L_{j,r}` vs `L_{j',r'}`: equality forces `k^{j+1} r' = k^{j'+1} r`; for `j < j'`
  that gives `r' = k^{j'-j} r`, so `k | r'`, excluded.

Martin's hypotheses are exactly these two, so the dominance corollary gives
independence of `φ(L_0)` together with all `φ(L_{j,r})`. Hence `c_{j,r} = 0` for
every basis residue and `c_{0,0} + φ(k) c_{1,0} = 0`.

The relation has collapsed to `c_{0,0}φ(n) + c_{1,0}φ(kn) = 0`. Evaluate at
`n = k`, using `φ(k²) = k φ(k)`: `c_{0,0} + k c_{1,0} = 0`. Subtracting,
`(k − φ(k)) c_{1,0} = 0`, and `φ(k) < k` for `k ≥ 2`, so `c_{1,0} = c_{0,0} = 0`. ∎

Note this endgame is the composite-correct one: at a prime `ℓ` it reduces to the
earlier `(ℓ−1)` versus `ℓ` pair.

### 2.4a Second provenance correction: infinite-dimensionality is Coons

Found while checking a claim in an unsent draft, and it cuts against us.

> **Lemma.** Let `M ⊆ Z^N` be a subgroup of integer-valued sequences whose
> `Q`-span has finite dimension `d`. Then `M` is a finitely generated `Z`-module.
>
> *Proof.* If `d = 0`, `M = 0`. Otherwise pick `m_1,…,m_d ∈ M` that are
> `Q`-independent. Linearly independent functions admit evaluation points
> `n_1,…,n_d` with `D := det[m_i(n_j)] ≠ 0`, and `D` is a nonzero **integer**.
> For `x ∈ M` write `x = Σ a_i m_i` with `a_i ∈ Q`; evaluating at `n_1,…,n_d`
> gives an integer linear system, so Cramer's rule puts every `a_i` in
> `(1/D)Z`. Hence `M ⊆ (1/D)(Z m_1 + … + Z m_d)`, a free `Z`-module of rank `d`,
> and over the PID `Z` every submodule of a finitely generated module is
> finitely generated. ∎

So for integer-valued sequences, **finitely generated ⟺ finite `Q`-dimension**.
The obvious would-be counterexample (`Z[1/2]` has rank 1 and is not finitely
generated) cannot be realised here: an integer sequence bounds its own
denominators through its values at small indices.

Consequently `k`-regularity of `φ` is *equivalent* to finite-dimensionality of
the `Q`-span of its `k`-kernel, and **Coons's Theorem 3.2 already gives
infinite-dimensionality**. Our
`not_finiteDimensional_span_fullTotientKernel` is therefore a formalisation of a
consequence of Coons, not an independent result, and must be reclassified
accordingly. It was previously carried as "locally proved result; novelty
unassessed" in the same contribution family as the exact rank; the two must be
separated.

What survives untouched is the **exact finite-level rank** `k^e + 1`, the
explicit basis and the relation normal form. Those do not follow from Coons —
non-finite-generation says nothing about the dimension at each level. Read in
the other direction, the rank theorem gives an independent, quantitative proof
of Coons's non-regularity.

### 2.5 Full kernel

`B_k = {F_{0,0}, F_{1,0}} ∪ {F_{j,r} : j ≥ 1, 1 ≤ r < k^j, k ∤ r}` is a basis of
the rational span of the full `k`-kernel; every finite subset sits inside some
`B_{k,e}`. In particular the span is infinite-dimensional, with the exact growth
law `rank_Q K_e(φ) = k^e + 1`.

This is quantitatively sharper than Coons's Theorem 3.2 (`φ` is not `k`-regular
for any `k ≥ 2`), which is proved by analytic continuation of `ζ(s−1)/ζ(s)` and
gives no finite-level rank, basis, or relations. It would supply an independent
structural proof of non-regularity.

---

## 3. Falsification receipts

Two probes, exact integer arithmetic, ranks mod `1 000 003` (a modular rank is a
**lower** bound for the rational rank, so agreement on the full family *and* the
proposed basis simultaneously confirms both independence and that the reductions
lose nothing).

* `verify_oddprime.py` / `verify_oddprime_receipt.txt` — odd primes `ℓ ∈ {3,5,7,11,13}`.
* `verify_allbase_kernel.py` / `verify_allbase_kernel_receipt.txt` — **all bases**,
  `k ∈ {2,3,4,5,6,8,9,10,12,15,16}`, including the composite coefficient
  `C_k(t,u)` checked exactly, and the `k ∤ r` versus `gcd(k,r)=1` discrimination.

Every case matched `k^e + 1`. These are falsification evidence, not proof; the
proof above does not depend on them.

---

## 4. What is left

* **Discharge all-base independence in Lean.** Composite reduction, canonical
  spanning and the dimension conclusion conditional on independence are now
  checked. The remaining formal step is an assumption-free proof that the
  canonical all-base family is linearly independent. This could route through a
  formalisation of the required corollary of Martin, or through a separate
  determinant argument strong enough for the general composite-base family.
  Only after that step is checked should Lean expose an unconditional basis or
  complete relation normal form.
* **Prior art on the rank formula.** A targeted search found no source giving an
  exact finite-level rank, explicit basis, or relation normal form for the
  `k`-kernel of `φ`. That is a dated negative search result, not a novelty
  theorem. Specialist review still required before any priority claim.
* **Do not** extract a grand all-slope framework merely because it is elegant.
  Build it only if it genuinely shrinks both the odd and dyadic row producers and
  shortens theorem B.

## 5. Do-not-claim

* That theorem A is original — it is a corollary of Martin's Theorem 1.
* That Martin's positive-density theorem has been formalised.
* That the determinant proof is Martin's proof.
* That theorem B is wholly Lean-checked: only its arithmetic and spanning layers,
  and its rank conclusion conditional on `LinearIndependent`, are checked.
* That the unconditional all-base basis or complete relation normal form is a
  Lean declaration.
* That the rank formula is new, before specialist prior-art review.
* That the modular ranks are proof.
* That a σ analogue would be new — Martin's Corollary 4 already covers σ.
* That any of this bears on the irrationality of `Σ φ(n)/2^n`, or on Erdős #249.
* That any of this has had human mathematical peer review.
