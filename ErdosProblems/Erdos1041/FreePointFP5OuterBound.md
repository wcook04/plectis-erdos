# Erdős 1041: FP_5 is CLOSED — the outer bound via the halving lemma, a modulus-only deficit, and a 32-second replayable box certificate

Date: 2026-08-30.  Origin: wave-2 opus outer-bound agent (four proved
lemmas + an 8.74M-configuration battery, zero violations beyond
roundoff), main-loop replay of the box certificate (bit-identical
counts).  Certificate: `scripts/certify_erdos1041_fp5_outer_bnb.py`
(self-contained; `... 0.05` re-certifies in ~30 s: 34 rounds, 154,968
boxes excluded, 262,167 verified, empty live set; `... 0.10` also
certifies, 37 rounds).  Checker:
`scripts/check_erdos1041_fp5_outer_bound.py` (replays the symbolic
lemma bank, the per-step battery on fresh configs, AND the full box
certificate).  Consumes `FreePointFP5StructureLab.md` (ROWCERT+, whose
failure set this note covers) and `FreePointTorusPshReduction.md` (the
bridge `FP_{n-1} ==> (S)_n`).

## 1. The theorem chain

Objects as in the lab note: `c in closed-disk^5`, `rho_j = |c_j|`,
`d_jk = |1 - conj(c_j) c_k|`, `t_jk = rho_j rho_k`, rows `e^{h_j}`,
`S = sum_j e^{h_j}`; `H_j` the one-sided modulus ceiling,
`T_j = e^{H_j}`; `L_j = -log(1 - rho_j^2)`, `Lbar` their mean;
`f_jk = t_jk/(1+t_jk)^2`, `F^(n)` the zero-diagonal matrix of
`f_jk^n`, `Sigma_n = sum_{j != k} f_jk^n`;

```text
D(rho) = max_{1 <= N <= 12} (1/10) sum_{n <= N} (1/n) [ C(2n,n) Sigma_n
          + (4^n - C(2n,n)) * 5 lambda_min(F^(n)) ],
OUT(rho) = sum_j T_j - (1 - e^{-D(rho)/2}) (T_(1) + T_(2)),
```

`T_(1) <= T_(2)` the two smallest.

> **Theorem (OUTER).**  `S <= OUT(rho)` for every `c`.
>
> **Localization Lemma.**  With `Hsharp = (1/5) log(3125/729)` and
> `LAMBDA = 1/Phi(Hsharp) = 1.8107280533`: the ROWCERT+ quantity
> satisfies `A <= Phi(Hsharp) Lbar`, so certificate failure (`A >= 1`)
> forces `Lbar >= LAMBDA`, i.e. `prod_j (1 - rho_j^2) <= e^{-9.0536}`.
>
> **MOD (box certificate).**  For every `rho in [0,1]^5`:
> `Lbar >= LAMBDA ==> OUT(rho) <= 4.95` (and even `<= 4.90`).
>
> **Corollary (FP_5).**  `S_5 <= 5` for all `c` in the closed polydisk,
> with equality only at `c = 0`.  Hence, by the landed bridge,
> **(S) holds at degree 6** — (S) is now proved for `n = 2..6`.

Proof of OUTER, in four lemmas (checker-replayed):

1. **Row ceiling** (from the lab note): `h_j <= H_j`; write the row
   deficit `s_j = H_j - h_j = (1/5) sum_{k != j} delta_jk` with
   `delta_jk = log((1+t_jk)/d_jk) >= 0` SYMMETRIC.
2. **Halving Lemma (the crux).**  `Delta := sum_j s_j =
   (2/5) sum_{j<k} delta_jk`, hence EVERY row has
   `s_j <= Delta/2` — each pair's deficit is delivered to two rows, so
   no single row can absorb more than half the total.  (Without this,
   the certificate maxes at 5.12 on the failure set; with it, 4.77.)
3. **Deficit Lemma.**  `Delta >= D(rho)`.  From
   `d_jk^2 = (1+t_jk)^2 - 2 t_jk g_jk`, `g_jk = 1 + cos(phase)`:
   `delta_jk = -(1/2) log(1 - 2 f_jk g_jk)`, expand to order `N` (all
   terms nonnegative; `2 f g <= 1`), write
   `g^n = 2^{-n}[C(2n,n) + 2 sum_r C(2n,n-r) cos(r phase)]`, and bound
   each Fourier mode by Rayleigh:
   `sum_{j != k} w_jk cos(r phase_jk) >= 5 lambda_min(W)` at unit
   vectors `v_j = e^{i r alpha_j}`.  The truncation must be a MAX over
   `N`, not the full series: the `n`-th modal term goes negative for
   `n >= 8` at `m = 5` (`5 C(2n,n) < 4^n` once `sqrt(pi n) > 5`).
4. **Transfer Lemma.**  `S = sum_j T_j e^{-s_j}` is bounded by its max
   over the polytope `{sigma >= 0, sum sigma = Delta,
   sigma_j <= Delta/2}`; convexity puts the max at extreme points,
   which have EXACTLY TWO coordinates at `Delta/2`; monotonicity in
   `Delta` then substitutes `D(rho)`.

Equality bookkeeping: if ROWCERT+ holds (`A < 1`), `S < 5` unless the
Fourier energy `E = 0`, which forces every power sum to vanish, i.e.
`c = 0` (Newton); if it fails, MOD gives `S <= 4.95 < 5`.  No residual
equality case.

## 2. Verification

- 8,740,000 configurations (uniform, boundary-concentrated,
  near-equal-large; angle families incl. the `1+2+2` mirror extremal
  and the 5-star at `rho_*`), of which 4,696,722 fail ROWCERT+: every
  step at roundoff (worst genuine slack `s_j <= Delta/2` margin
  `1.5e-13`; final `S <= 5` attained exactly at `c = 0`).
- Extremals of the certificate: max `OUT` on `{Lbar >= LAMBDA}` is
  `4.8154` (margin `0.185`) at the `1+1+3` profile
  `(0.9967, 0.8640, 0.7679 x3)` ON the boundary `Lbar = LAMBDA` — NOT
  at the true extremal family (the 5-star has 0.39 of certificate
  slack; the lab's 0.115 headroom describes the truth, not this
  certificate's binding constraint).
- Localization sharpness: bites at `rho = 0.91458` on the all-equal ray
  vs the true `rho_* = 0.92445` (loss 0.0099).
- Symbolic bank (sympy): the `(1-x)(1+x)^5` max at `x = 2/3` with value
  `3125/729`; `Phi` increasing via `Phi(h) = int_0^1 (1-s) e^{sh} ds`;
  the `d^2` identity; the modal expansion and `C(2n,n) + 2 sum_r
  C(2n,n-r) = 4^n`; the transfer polytope's extreme-point structure.

## 3. Evidence class and the m-uniform remnant

Lemmas 1–4, the localization lemma, and the equality bookkeeping are
ordinary proved mathematics.  MOD is a machine certificate at
IEEE-DOUBLE evidence class (one-sided elementary bounds per box —
exact 1-D concavity maxima, Weyl for `lambda_min`, upper bounds only on
`T` — but floating arithmetic without directed rounding; accumulated
error `~1e-12` against margin `0.05`).  A directed-rounding or rational
re-run is the upgrade path to exact class; the certificate is
deterministic and replays bit-identically in ~30 s (the checker does).

m-uniformity: the row ceiling, halving, deficit, transfer, and
localization lemmas are verbatim `m`-uniform (`LAMBDA_m` explicit,
decreasing to `1/Phi(log 2) = 1.565`).  The single non-uniform step is
MOD — one `m`-dimensional modulus-only box inequality per degree.  The
honest all-`m` remnant is exactly that family of box certificates, and
the lab's shrinking sphere margins (`2.2e-2 -> 5.1e-3` over
`m = 5..8`) warn that the margin may not survive `m -> infty` in this
form.

## Claim boundary

FP_5 is closed at the stated composite evidence class (proved lemmas +
an IEEE-double deterministic box certificate); (S)_6 follows by the
landed bridge.  Nothing here touches the parent problem ((S) does not
imply it), FP_m for `m >= 6`, or the exact-arithmetic upgrade of MOD.
The 8.74M battery is supporting measurement, not part of the proof.
