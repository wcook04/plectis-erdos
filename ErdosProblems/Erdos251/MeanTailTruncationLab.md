# Average omitted-tail bound (ordinary)

Type B r3 file 05, Theorem 3.1 and Corollaries 3.2--3.3. **Ordinary proof,
not Lean.** Collision-checked against the live packet: no existing exact
result states a first-moment bound on `|D_h - W_{h,L}|` averaged over a
dyadic index window. The parent irrationality is not proved. The lower bound
on the signed truncated count is not proved.

Throughout, `X` is a prime-index scale. Write
`D_h(N) = T_{N+h} - T_N` and
`W_{h,L}(N) = ∑_{j=1}^L 2^{-j}(g_{N+h+j} - g_{N+j})`.

## Elementary mean tail bound

There is an absolute `C` with `p_n ≤ C(n+1) log(n+2)`. The binomial
`binom(2m,m) ≥ 4^m/(2m+1)` and Legendre's formula give an elementary
`π(y) ≫ y/log y`, hence the displayed growth after inverting. This is the
logarithmic refinement of the corpus polynomial bound, not a prime-number
theorem.

Positivity and Tonelli then yield, uniformly in `0 ≤ a ≤ 3X`,
`∑_{X ≤ N < 2X} T_{N+a} ≤ C_T X log X`. The inner gap sum telescopes to
`p_{2X+a+j} - p_{X+a+j} ≤ p_{5X+j}`. The exact identity
`∑_{N=A}^{B-1} T_N = p_{B+1} - p_{A+1} - T_A + T_B` shows that omitting
the endpoint `T_B` would be unjustified.

## Average truncation

The exact split `D_h(N) - W_{h,L}(N) = 2^{-L} D_h(N+L)` and the mean bound
give, for `X ≥ 2` and `1 ≤ h,L ≤ X`,

```
∑_{X ≤ N < 2X} |D_h(N) - W_{h,L}(N)| ≤ 2 C_T X log X · 2^{-L}.
```

Markov: the number of indices with error `≥ η` is
`O(X log X / (η 2^L))`.

## Sufficient depth, not a count

If a signed truncated count `V_{h,η}(X,L)` of the `Δ = ±2` half-window
events (with margin `η`) exceeds that error budget, one genuine adjacent
small mismatch occurs in the window. If this holds on unbounded scales for
every fixed `h`, then `Π` is irrational. At candidate density
`X/(log X)^α` the depth `(α+1+ε) log_2 log X` is a sufficient budget. This
does not prove the candidate count.

The signed two-window identity supplies the adjacent shift: one truncated
coordinate is enough. No independence of digit and tail is used.

## Evidence class

Ordinary. Not registered as a Lean theorem. Does not replace
`cofinal_adjacent_small_mismatch`. The needed lower bound remains an
analytic task on prime-index scales; prime heights are of order
`X log X` and must not be silently substituted.
