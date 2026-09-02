# Erdős #1049: derivation of the `0.40568302138…` contour

Verdict: **derived**. The constant is `θ* = C_0/C_1 = 1/μ_Zudilin`, where
`μ_Zudilin = C_1/C_0 = 2.46497868…` is the irrationality-exponent bound of
Theorem 1 in W. Zudilin, *Heine's basic transform and a permutation group for
q-harmonic series*, Acta Arith. 111.2 (2004) 153–164 (annex
`annexes/zudilin-2004-heine-q-harmonic-series/`). The derivation is the one in
the Type B return `~/.codex/attachments/8a7ad785-1578-4ce4-ba0d-ac7d66aeacd2/pasted-text.txt`
(packet attachment role "Zudilin hypergeometric rational homogenisation …";
copy in this directory as `typeb_return_8a7ad785.txt`). It was not on the
repo's disk, but it exists; below it is re-derived from the paper with every
step checked and the finite part reconstructed exactly for `n = 1, 2, 3`.

## 1. The equation for the constant

Zudilin, Section 5, direction `(α0, α1, α2; β) = (14, 12, 14; 27)`,
`a_j = α_j n + 1`, `b = βn + 2`, six-tuple
`c = (c00, c01, c11, c21, c12, c22) = (13, 14, 12, 14, 15, 13)`, `m = max c = 15`:

```
C_1 = (α0+α1+α2)β − (α1² + α2² + β²)/2                       = 1091/2 = 545.5        (paper (25))
C_0 = α1²/2 + α0α1 + (β−α2)(α2−α1) − (3/π²)·( m² − J )      = 266 − (3/π²)(225 − J)  (paper (26))
J   = ∫_0^1 ω(x) d(−ψ'(x)) = Σ_{[u,v): ω=1} ( ψ_1(u) − ψ_1(v) )                      (paper Lemma 2)
ω(x)= max{0, ⌊14x⌋+⌊13x⌋−⌊12x⌋−⌊15x⌋, 2⌊14x⌋−⌊13x⌋−⌊15x⌋}
θ*  = C_0 / C_1
```

`ω = 1` exactly on the thirteen intervals the paper prints:
`[1/14,1/12) [1/7,1/6) [3/14,1/4) [2/7,1/3) [5/14,2/5) [3/7,7/15) [1/2,8/15) [4/7,3/5) [9/14,2/3) [5/7,11/15) [11/14,4/5) [6/7,13/15) [13/14,14/15)`
(recomputed from ω, not transcribed; `c0_c1_check.py`).

mpmath, 40 digits (`c0_c1_check.py`):

```
J   = 77.94318447500909592258957
C_0 = 221.3000881650050251240427     (paper: 221.30008816…)
C_1/C_0 = 2.464978683574975037454     (paper Theorem 1: 2.46497868…)
θ*  = C_0/C_1 = 0.4056830213840605410  (packet: 0.40568302138…)   ✓ 12+ digits
```

Same pattern for the published rational-base criterion: Bundschuh–Väänänen
Theorem 2 (α = −1 case) requires `λ = log a / log(a/b) < (1/2 + 1/π²)^{-1}`,
i.e. `log b/log a < 1/2 − 1/π² = 0.39867881636 = 1/μ_BV` with
`μ_BV = 2π²/(π² − 2) = 2.50828476` (the exponent Zudilin quotes as (3)).
So both thresholds are `1/(integer-base irrationality exponent)`; the packet's
contour is Zudilin's forms placed in BV's height framework. Rejected
candidates: BV's `1/2 − 1/π²` (0.3987, wrong by 0.007); the packet's
rank-budget formula `(r−1−κ)/r` with `κ = 2/π²` (that reproduces BV, not this).

## 2. Statement

**Theorem (authored; conditional on Zudilin 2004 Lemma 7 and Lemma 2).**
Let `a > b ≥ 1` be coprime integers with `log b / log a < C_0/C_1 = 0.405683…`.
Then `h_{a/b}(1) = Σ_{m≥1} 1/((a/b)^m − 1) ∉ Q`. In particular
`F((31/4)^r)` is irrational for every `r ≥ 1`, since
`log 4/log 31 = 0.40370 < 81/200 < θ*` (`4^200 < 31^81`, Lean-checked in
`ZudilinHeightRegion.lean`).

## 3. Proof, with the authority class of each step

Write `p = a/b > 1`, `q = 1/p`, and for each `n` the Zudilin parameters
`a0 = 14n+1, a1 = 12n+1, a2 = 14n+1, b = 27n+2` (paper's `b`, not the
denominator; below the denominator is written `b_den` when both occur).
`N = 15n`, `D_N(p) = Π_{l≤N} Φ_l(p)`, `Ω_n(p) = Π_{2≤l≤N} Φ_l(p)^{ν_l}`,
`ν_l = ω(n/l) ∈ {0,1}`, `M_n = 266n² + 34n + 1` (paper (16)).

**Step 1 (identity in Q(p), analytic in p).** For real `p > 1`,
`F_n(p) := Σ_{t≥0} R(q^t) = A_n(p) h_p(1) − B_{1,n}(p) − B_{2,n}(p)` with the
paper's (8)–(11). This is the partial-fraction summation identity; it holds for
every complex `q` with `|q| < 1`. *Elementary; paper Section 3.*

**Step 2 (polynomial integrality — Zudilin Lemma 7).**
`Λ_n(p) := p^{−M_n} D_N(p) Ω_n(p)^{−1} F_n(p) = U_n(p) h_p(1) − V_n(p)` with
`U_n, V_n ∈ Z[p]`. Lemma 7 is a statement in the ring `Z[p]` (Gaussian
binomials, cyclotomic lcm clearing, Heine-transform stability, Gauss's lemma
for division by the monic `Ω`); the paper's standing hypothesis `p ∈ Z` is used
only afterwards, in (24), to pass from `Z[p]` to `Z`. Uniqueness of `(U_n, V_n)`
holds because `h_p(1)` is not in `Q(p)` (poles at all roots of unity).
*Published, p-independent.* Checked exactly here for `n = 1,2,3`: `Ω_n` divides
both `D_N A_n` and `D_N (B_1 + B_2)` with zero remainder, and `p^{M_n}` divides
both quotients (`exact_forms.py`).

**Step 3 (degrees, elementary).** The `k`-th summand of `A_n` has `p`-degree
`d_{n,k} = a0 k + E_{n,k} + (a1−1)(k−a1) + (b−k−1)(k−a2)` and
`d_{n,k+1} − d_{n,k} = a0 + a1 + a2 − k − 2 = 40n + 1 − k > 0` for `k ≤ b−2`,
so `deg A_n = d_{n,b−1} =: K_n = (1091n² + 81n + 2)/2`, leading coefficient
`±1`, and `K_n/n² → 545.5 = C_1` (this makes the paper's lim sup in (25) an
exact degree count). Hence
`W_n := deg U_n = K_n − M_n + Σ_{l≤N} φ(l) − Σ_{l≤N} ν_l φ(l)`,
and `deg V_n = W_n − 1` (as `p → ∞`: `U_n h_p ~ p^{W_n−1}` while
`Λ_n ~ p^{W_n − K_n}`). Verified: `W_1, W_2, W_3 = 333, 1315, 2944`,
`deg V_n = W_n − 1`, leading coefficients `±1`, `ord_0 U_n = 2n²`, `V_n(0) = 1`.

**Step 4 (homogenisation, trivial).** `Û_n := b_den^{W_n} U_n(a/b_den)` and
`V̂_n := b_den^{W_n} V_n(a/b_den)` are integers, and
`Λ̂_n := b_den^{W_n} Λ_n(a/b_den) = Û_n h_{a/b_den}(1) − V̂_n`. Verified
(`exact_forms.py`): integers at `31/4, 3/2, 7/2`; `b_den^{W_n−1} U_n` is not an
integer, so the degree is exactly `W_n`.

**Step 5 (positivity = nonvanishing, elementary).** For real `p > 1` every
factor of `R(q^t)` is positive, so `F_n(p) > 0`; `Φ_l(p) > 0` for `p > 1`; hence
`Λ_n(p) > 0` and `Λ̂_n > 0`. No determinant or Nesterenko-type criterion is
needed.

**Step 6 (size, elementary + Lemma 1/2).**
`log Λ̂_n = W_n log b_den − M_n log p + log D_N(p) − log Ω_n(p) + log F_n(p)`.
* `(q;q)_∞² ≤ F_n(p) ≤ (q;q)_∞^{−2} (1 − q^{a0})^{−1}`, so `log F_n = O_p(1)`
  (each `q`-Pochhammer factor of `R(q^t)` lies in `[(q;q)_∞, 1]`). This replaces
  the paper's `|F| = |p|^{O(b)}` and is valid for every real `p > 1`.
* `log Φ_l(p) = φ(l) log p + log Π_{d|l}(1 − p^{−d})^{μ(l/d)}`, and the
  correction summed over `l ≤ N` is `O_p(N) = o(n²)`.
* Therefore `log Λ̂_n = K_n log b_den − (K_n − W_n) log a + o(n²)`, and
  `(K_n − W_n)/n² = M_n/n² − (Σφ(l) − Σν_lφ(l))/n² → 266 − (3/π²)(225 − J) = C_0`
  by Lemma 1 (`Σ_{l≤N} φ(l) ~ 3N²/π²`, classical) and Lemma 2 (the
  `{n/l}`-equidistribution of `φ(l)`, weight `ψ_1(u) − ψ_1(v)`; published,
  `p`-independent, only intervals with `u ≥ 1/14` occur so `l > 15n` never
  contributes).
  Hence `log Λ̂_n / n² → C_1 log b_den − C_0 log a`.

**Step 7 (conclusion).** If `h_{a/b}(1) = P/Q` then `Q Λ̂_n = P Û_n − Q V̂_n` is a
positive integer, but it tends to `0` whenever `C_1 log b_den < C_0 log a`,
i.e. `log b_den / log a < C_0/C_1`. ∎

External inputs actually consumed: Zudilin 2004 **Lemma 7** (integrality with
the cyclotomic divisor `Ω`) and **Lemma 2** (trigamma equidistribution, from
[Zu1, Lemma 1]). *Not* consumed: the paper's Archimedean estimate (17)/(25) for
`|A_n|` and the `p ∈ Z` hypothesis. The paper's own remark that Theorem 1 "is
uniform in p" is the shadow of the same fact.

## 4. Numerical receipts (`exact_forms.py`, output `exact_forms_n3.log`)

Exact `U_n, V_n ∈ Z[p]` built from cyclotomic products (no rational-function
arithmetic), then the identity `U_n(p) h_p(1) − V_n(p) = p^{−M_n}(D_N/Ω_n)(p) F_n(p)`
evaluated at `mp.dps ≈ K_n log₁₀ p + 300`:

| n | base | rel. diff of identity | Λ̂_n > 0 | log Λ̂_n | K log b − (K−W) log a | residual (= log F_n + cyclotomic tail) |
|---|---|---|---|---|---|---|
| 1 | 31/4 | 1.3e-25 | yes | −58.735 | −58.478 | −0.257 |
| 2 | 31/4 | 1.2e-49 | yes | −120.043 | −120.283 | +0.241 |
| 3 | 31/4 | 1.2e-73 | yes | −194.215 | −194.332 | +0.117 |
| 1 | 3/2 | 1.2e-5 | yes | +126.220 | +127.830 | −1.610 |
| 2 | 3/2 | 2.1e-10 | yes | +527.504 | +526.702 | +0.802 |
| 3 | 3/2 | 3.6e-15 | yes | +1193.975 | +1194.014 | −0.039 |
| 1 | 7/2 | 5.8e-16 | yes | −87.949 | −87.384 | −0.565 |
| 2 | 7/2 | 1.2e-30 | yes | −276.899 | −277.384 | +0.484 |
| 3 | 7/2 | 2.4e-45 | yes | −574.939 | −575.144 | +0.205 |

(The 3/2 rows at low precision are limited by the 1e-5 relative accuracy of
the `mpf` conversion at n=1, not by the identity.) Exact main term at 31/4 for
larger n (only `Σφ`, `Σν_lφ` needed):

```
 n   (K−W)/n²   K/n²     main term      /n²
 1    254.00   587.00     −58.478    −58.478
 10   224.85   549.56   −1028.009    −10.280
 100  221.63   545.91  −42973.205     −4.297
 400  221.38   545.60 −618056.339     −3.863   → C_1 log4 − C_0 log31 = −3.718
```

The return's exact rational sub-bound is reproduced: truncating each
`ψ_1(u) − ψ_1(v) = Σ_k (v−u)(2k+u+v)/((k+u)²(k+v)²)` at `k < 10` gives
`J > 77.93981814 > 389699/5000`; with `π > 157/50`, `C_0 > 221.2537 > 88371/400`,
and `88371/400 = (81/200)·(1091/2)`, so `θ* > 81/200` by finite rational
arithmetic. (Lean-bindable: only `ψ_1` lower bounds by finite sums are needed.)

## 5. What the packet gets slightly wrong or leaves vague

* "consumes an external asymptotic theorem": the consumed items are Lemma 7
  and Lemma 2 of Zudilin 2004, both used as `p`-independent identities; no
  rational-base asymptotic theorem of Zudilin exists or is needed. The
  Archimedean part is elementary (Step 6).
* `longitudinal_truth §4`: "no derivation anywhere on disk … may be false.
  Demote to hypothesis" — the derivation exists in the Type B attachment
  (outside the repo) and is now re-derived and machine-checked at `n ≤ 3`.
  Evidence class: authored theorem conditional on two published lemmas, not a
  hypothesis. It is *not* kernel-checked and *not* a published theorem.
* Convergence of `(K_n − W_n)/n²` to `C_0` is slow (`O(1/n)`, from `34n` in
  `M_n` and the `N log N` term of `Σφ`), so at the razor-thin base 31/4 the
  per-`n²` rate is `−58, −10, −4.3, −3.9` for `n = 1, 10, 100, 400`; the sign is
  negative from `n = 1` and the limit is `−3.718`. Irrationality only needs the
  limit.
* Priority: no source found that states a rational-base threshold above
  BV's for `h_{a/b}(1)`. Checked: Zudilin 2004 (integer p), Tachiya 2004
  (integer q in Q or imaginary quadratic), Bézivin 1988, Borwein 1991/92,
  Van Assche 2001, Amdeberhan–Zeilberger 1998, Postelmans–Van Assche 2006,
  Zudilin 2016 (generalized q-log) — all integer base. BV 1994 Theorem 2 is the
  only rational-base criterion and its framework (number-field height `λ`)
  is exactly the homogenisation used here. A formal priority search remains a
  Type B obligation; do not word this as new without it.

## 6. Packet rows that must change (controller edits `research_packet.json`)

1. `zudilin_rational_homogenisation_height_region` (line ~396): keep status
   `authored_mathematics_external_asymptotic_dependency` but replace the bare
   statement with: constant = `C_0/C_1 = 1/μ_Zudilin` with the explicit formula
   (Section 1), derivation locator (this note + attachment id 8a7ad785),
   external inputs = Zudilin 2004 Lemma 7 + Lemma 2 only, Archimedean part
   elementary, positivity supplies nonvanishing, exact finite reconstruction
   `n ≤ 3` receipt, and a claim boundary: not kernel-checked, no priority claim,
   same pattern as BV (`1/μ_BV`).
2. `thirtyone_four_power_family` and `claim_ceiling_addendum_2026_08_11 (1)`:
   change "still consumes an external asymptotic theorem" to "consumes Zudilin
   2004 Lemma 7 (Z[p]-integrality with Ω) and Lemma 2 (trigamma
   equidistribution); the Archimedean estimate is elementary"; add
   "`0.40568302138… = C_0/C_1 = 1/2.46497868…`".
3. `public_projection.minimum_release`: "cite and verify the primary Zudilin
   height theorem separately" → there is no Zudilin height theorem; replace with
   "cite Zudilin 2004 Lemmas 7 and 2 and BV 1994 Theorem 2's height framework;
   the rational-base theorem is authored and awaits a priority search".
4. `docs/formal_math/palomar/longitudinal_truth_2026_09_01.md` §4 bullet:
   replace "no derivation anywhere on disk … may be false. Demote to
   hypothesis" with "derivation reconstructed and checked
   (scratch note); authored theorem conditional on two published lemmas;
   `F((31/4)^r)` irrational for all r at that evidence class; priority open".
5. Optional Lean follow-on (not done here): define `zudilinC1 = 1091/2`,
   `zudilinC0 = 266 − (3/π²)(225 − J)` with `J` as the 13-interval trigamma sum,
   and prove `81/200 < zudilinC0/zudilinC1` from finite `ψ_1` lower sums and
   `π > 157/50`; then `ZudilinHeightRegion` becomes a sub-region of the
   authored contour rather than a free-standing 81/200.

Files: `c0_c1_check.py`, `exact_forms.py`, `exact_forms_n3.log`,
`typeb_return_8a7ad785.txt` (all in this directory).
