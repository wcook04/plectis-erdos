# Sufficient target: a signed Land inequality

Type B file 05, Proposition A. **Do not register as a theorem.** The boxed
inequality is unproved. Sufficiency for irrationality of
`Π = Σ_{n≥0} p_n 2^{-(n+1)}` is an ordinary argument, independently checked
below. The contribution is a smaller interface to Land's Sections 2–5, not a
logical weakening with a proved separation.

## The interface

Retain Land's `k, H, H_0, B_k, U, V` with `ℓ = log log X`. For large `X` put

```
R = ⌊ℓ³ / (log ℓ)²⌋,
A_X = {t ∈ [X, 2X] ∩ ℤ : t + B_k ⊂ primes},
Y(t) = #{h ∈ V : t+h prime},
Z(t) = #{u ∈ U : t+u prime}.
```

**Target (A), unproved.** There is a fixed `C_0 > 0` and an unbounded sequence
of scales `X` for which

```
Σ_{t ∈ A_X} [ Y(t)(1 − Z(t)) − R ]  ≥  X exp(−C_0 (log log X)²).
```

## Why sufficiency survives

1. The sign `Y(1−Z)` extracts unspoiled occurrences: if `Z ≥ 1` the summand is
   nonpositive; if `Z = 0` and `Y ≤ R` it is at most `R`. Hence
   `W − R|A| ≤ H|T|` and (A) supplies `|T| ≥ (X/H) exp(−C_0 ℓ²)`.
2. For `t ∈ T`, `t = p_i` and `Z(t) = 0` force the quadratic consecutive block
   `p_{i+j} = t + 2j²`, gaps `4j−2`, and an open gap after the block strictly
   larger than `4k+6` in the weighted tail, so `G_i > 6`.
3. `Y(t) > R` supplies `R` later primes inside span `H`. Splitting the tail
   and averaging the global mass `Σ G_j ≪ X` (PNT-scale, not avoided) against
   `|T|` makes some occurrence have both error terms `H/2^k` and
   `H exp(C_0 ℓ²)/2^{k+R}` tending to zero.
4. Rationality `Π = a/b` puts every `G_i` in `b^{-1}ℤ`. Then `G_i − 6` is a
   positive lattice element smaller than `1/b` for large `X`, which is
   impossible. (`6` is always in `b^{-1}ℤ`.)

The missing assertion is a lower bound on the signed triple-count
`Σ_h C_X(B_k ∪ {h}) − Σ_{h,u} C_X(B_k ∪ {h,u}) − R C_X(B_k)`.
Kuperberg's Theorem 4.1 supplies uniform *upper* sieve bounds, not matching
positive lower bounds. Land obtains the estimates from his uniform prime-tuples
hypothesis. Reversing an upper bound does not produce (A).

## What this is not

- Not a theorem of this corpus.
- Not a claim that `O(log X)` span follows from Land's estimates: those
  estimates need `R ≫ ℓ²` later primes, hence span larger than
  `log X · ℓ² log ℓ` in this sufficient regime.
- Not a replacement for the cofinal adjacent-small-mismatch producer; it is a
  named analytic interface to one conditional route.
