# Erdős 1041: the Form A-cut hub is not free — near Fekete it is the adjacent good pair

Status: one near-field expansion with checked error orders, one closed-half-plane
count, one leading-order sufficiency proof for an explicit selector when
`E_1 != 0`, one refuted selector, and a measured agreement with the free
optimum. Corrected 2026-08-25.
**Erdős #1041 remains open** and nothing below claims otherwise.

## 0. The gap this addresses

[TruncatedSpokeReduction.md](TruncatedSpokeReduction.md) proves the reduction
that carries **no length obligation at all**:

> **Form A-cut.** If for every monic `f` with roots in the open unit disk there
> are distinct roots `a, b` and radii `s_a, s_b` with `|f| < 1` on `[s_a â, a]`,
> on `[s_b b̂, b]` and on `[s_a â, s_b b̂]`, then Erdős #1041 holds.

Its §6 records adversarial hill-climbing that "cannot move `V` off one by more
than about `5e-7` at any degree 3 through 9", and its §7 leaves the *selection*
open: which pair, which radius. `form_a_cut_cusp_exponent_at_the_regular_gon`
identifies the near-field model `W(zeta) = Re(e^{i psi} zeta) - Re(zeta^n)` and
the half-plane count, and records that the cusp constant `c_n` **is not proved
positive**.

This note supplies the selector, proves it sufficient at leading order for
`n >= 4`, and refutes the selector one would guess first.

## 1. The near field, with error orders

Normalise so the roots are `a_k = omega^k (1 + e_k)`, `omega = e^{2 pi i/n}`,
`eta = max_k |e_k|`, all `|a_k| <= 1`. Put

```text
E_0 = sum_k e_k ,        E_1 = sum_k e_k omega^{-k} ,      |E_m| = O(n eta) .
```

`near_fekete_origin_spoke_balance_and_kernel` gives
`log|f(z)| = log|1 - z^n| + Re Lambda(z) + O(eta^2)` with
`Lambda(z) = sum_k e_k/(1 - z omega^{-k})`. Expanding both parts at `|z| = sigma`,

```text
log|f(z)|  =  Re E_0  +  Re(E_1 z)  -  Re(z^n)  +  R ,
|R|  <=  C(n) ( eta sigma^2  +  eta^2  +  sigma^{2n} ) .                (N)
```

**The orders close.** With `sigma ~ eta^{1/(n-1)}` the two leading terms are both
`~ eta^{n/(n-1)}`, while `eta sigma^2 ~ eta^{(n+1)/(n-1)}`,
`sigma^{2n} ~ eta^{2n/(n-1)}` and `eta^2` are all of strictly higher order for
`n >= 3` (`n/(n-1) <= 2`). So (N) is an asymptotically exact model, not a formal
expansion — and it stays exact down to `sigma ~ eta^{1/2}`, since `eta^2 << eta
sigma` there.

Two facts sit inside (N) and are used throughout:

* `Re E_0 = sum_k (|a_k| - 1) + O(eta^2) <= 0` because the roots are in the
  closed unit disk; it is **strictly** negative unless every `|a_k| = 1`.
* on a root ray, `Re(z^n) = u^n Re(â_j^n) ~ +u^n`, so `-Re(z^n) < 0` there.

## 2. Good rays are a closed half plane

> **Definition.** The root `a_j` carries a **good ray** if
> `p_j := Re(E_1 â_j) <= 0`.

> **Lemma 1.** If `a_j` carries a good ray then, at leading order, the whole
> truncated arm `[s â_j, a_j]` lies in `{|f| < 1}` for **every** `s in (0,|a_j|]`
> — the entry radius is zero.

*Proof.* Near field: `log|f(u â_j)| = Re E_0 + u p_j - u^n Re(â_j^n) + R`, all
three leading terms `<= 0`. Far field: `log|f(t â_j)| = log(1-t^n) + P_j(t) +
O(eta^2)` with `P_j = O(n log n * eta)` bounded on `[0,1]`
(`g_m(1) = cot(pi m/n)/2`), so `P_j(t) <= -log(1-t^n)` as soon as `t^n >> eta`.
The two ranges overlap. ∎

> **Lemma 2.** `{j : p_j <= 0}` is the set of root directions in a **closed half
> plane**, hence a contiguous arc of at least `floor(n/2)` indices. It contains
> two **adjacent** indices exactly when `n >= 4`.

*Proof.* `p_j = |E_1| cos(arg E_1 + arg â_j)`, so the condition is a closed half
plane through `0`. The `n` directions are within `O(eta)` of the `n`-th roots of
unity; a closed half plane contains at least `floor(n/2)` of them, and they are
consecutive. `floor(n/2) >= 2` iff `n >= 4`. ∎

The recorded identity `P_j'(0) = p_j` is the same statement twice: from
`g_m(t) ~ t sin(2 pi m/n)`,
`P_j'(0) = sum_{m>0} sin(2 pi m/n)(theta_{j+m} - theta_{j-m}) = Re(E_1 omega^j)`.

## 3. The chord criterion, and why *adjacent* is the right pair

Take a common radius: the chord is `z(tau) = sigma w(tau)`,
`w(tau) = (1-tau) â_i + tau â_j`. By (N),

```text
log|f(z(tau))| / 1  =  Re E_0  +  sigma [ (1-tau) p_i + tau p_j ]
                        -  sigma^n Re( w(tau)^n )  +  R .
```

The bracket is a linear interpolation of `p_i, p_j <= 0`, hence `<= 0`; the only
positive contribution is `-sigma^n Re(w^n)` where `Re(w^n) < 0`.

> **Criterion.** The pair `(i,j)` works for all sufficiently small `sigma` iff
>
> ```text
> Re( w(tau)^n ) < 0   =>   (1-tau) p_i + tau p_j < 0        (tau in [0,1]) ,
> ```
>
> and then any `sigma` with
> `sigma^{n-1} < min { -[(1-tau)p_i + tau p_j] / [-Re(w(tau)^n)] }` suffices.

> **Lemma 3.** If `E_1 != 0`, every **adjacent** good pair satisfies the
> criterion, for `n >= 3`.

*Proof.* Along the chord between two adjacent directions the argument of `w` is
monotone and increases by `2 pi/n`, so `arg(w^n)` increases by exactly `2 pi`
from `arg(â_i^n) ~ 0` to `arg(â_j^n) ~ 0`: `Re(w^n) < 0` only on a subinterval of
the **open** interval `(0,1)`. There the interpolant `(1-tau)p_i + tau p_j` is
strictly negative unless `p_i = p_j = 0`, which would put both directions on the
line `Re(E_1 zeta) = 0`, i.e. make them antipodal — impossible for adjacent
directions when `n >= 3`. Here `E_1 != 0` is essential: if `E_1 = 0`, then
every `p_j` vanishes and the strict implication in the criterion is not
available. ∎

Combining Lemmas 1–3:

> **Proposition (leading-order selector, nondegenerate first mode).** For
> `n >= 4`, `E_1 != 0`, and every sufficiently small perturbation of the
> regular `n`-gon, Form A-cut holds with
>
> * the pair = **two adjacent roots whose directions both satisfy
>   `Re(E_1 â_j) <= 0`** (such a pair exists by Lemma 2), and
> * the common radius `sigma` any small enough positive number.
>
> The two-dimensional free hub search is not needed.

`n = 3` is excluded and is settled independently by
[CubicCriticalHub.md](CubicCriticalHub.md); it is also exactly the degree at
which Lemma 2 gives only one good ray, matching
`form_a_cut_cusp_exponent_at_the_regular_gon`'s "degree three is the ONLY such
degree".

The omitted `E_1 = 0` case is not covered by declaring every ray "good": the
strict chord criterion used above then has zero on its left side.  The correct
replacement is to pass to the first nonzero Fourier mode.  The exact
homogeneous-model theorem, including the arithmetic reason that degree three is
the only deficient degree, is proved in
[FormACutFirstNonzeroMode.md](FormACutFirstNonzeroMode.md).  Carrying either
selector through the uniform polynomial remainder remains the same open
near-Fekete stability step.

## 4. The selector one would guess first is FALSE

The chord's positive term `-sigma^n Re(w^n)` is largest where the chord is
farthest from the origin, so the obvious rule is *take the two good rays that
are most nearly antipodal*, making the chord dip close to `0`. That rule is
**false**, and the reason is visible in Lemma 3's proof: the extreme rays of the
good arc are the ones closest to the line `Re(E_1 zeta) = 0`, i.e. the ones with
`p_j` closest to zero, so the negative linear term they contribute is the
weakest available.

Measured with **exact** segment maxima, radius scanned on a logarithmic grid:
the most-antipodal-good-pair selector returns `V > 1` at

| `n` | `eta` | perturbation | selector `V` |
|---|---|---|---|
| 8 | `1e-2` | angular | `1.0003866137` |
| 10 | `1e-1` | angular | `1.0287764761` |
| 10 | `1e-5` | angular | `1.0000002022` |

`45 / 48` for that rule (arm `ANTI`). The free optimum is below `1` at every one
of those rows, so Form A-cut itself is untouched — only the selector fails. Note
the `n = 10`, `eta = 1e-5` row: the rule fails by `2e-7` *arbitrarily close to
the regular polygon*, so this is not a large-perturbation artefact.

## 5. Measurement of the corrected selector, and where it stops

Segment maxima **exact** throughout (real roots of `d|f|^2/dt`, never sampled).

**Seed stream A**, `70` configurations over `n = 4,5,6,7,8,10,12` and
`eta = 1e-1, 1e-2, 1e-3, 1e-5, 1e-7`, angular and mixed (angular + inward
radial): the adjacent-good-pair selector succeeds at **`70/70`**, and at `57` of
the `70` rows it reproduces the free two-dimensional optimum **to nine printed
digits** — e.g. `n = 7`, `eta = 1e-3`, angular: `0.999769236` on both sides;
`n = 10`, `eta = 1e-7`, mixed: `0.999999421` on both. Where it is strictly worse
the gap is `~1e-2` at `eta = 1e-1` and below `1e-6` at `eta <= 1e-5`.

**But it is genuinely a near-Fekete statement, and a second seed stream shows
where it stops.** At `n = 12`, angular, the selector crosses `1`:

| `eta` | `0.10` | `0.07` | `0.05` | `0.03` | `0.02` | `0.01` |
|---|---|---|---|---|---|---|
| adjacent selector `V` | `1.011157` | `1.012253` | `1.008483` | `1.002637` | `0.999793` | `0.997914` |
| free optimum `V` | `0.161933` | `0.388202` | `0.594164` | `0.791934` | `0.876771` | `0.951298` |

The free optimum is **far** below `1` at every one of those rows, so Form A-cut
itself is untouched: what fails past `eta ~ 0.02` is the *selector*, exactly as
the Proposition's "sufficiently small perturbation" says it should. The receipt
asserts the selector only for `eta <= 1e-2` and asserts separately that the free
optimum stays below `1` across the scan.

**A sampled instrument hides this.** A `3001`-point grid on the same rows
reported `70/70` for the selector *and* missed the crossing above, because a
sampled maximum can only under-report. That is `negative_results` entry 34's
class again, at a fifth location, and it is why every number here is exact.

The number of good rays tracks Lemma 2: `2` at `n = 4`, `3` at `n = 5,6`,
`3–4` at `n = 7,8`, `5–7` at `n = 10,12`.

## 6. Claim boundary

**Proved, and elementary:** the error orders in (N); Lemma 1's near-field half
(the far-field half uses the recorded bound on `P_j`); Lemma 2 including the
half-plane count and its `n >= 4` threshold; Lemma 3 under its necessary
`E_1 != 0` hypothesis; the identity
`P_j'(0) = Re(E_1 omega^j)`.

**Leading order only.** The Proposition is a statement about the model (N), and
its selector in this file assumes `E_1 != 0`. To
become a theorem it needs (a) the remainder `R` handled uniformly over the whole
arm `[sigma, |a_j|]` rather than in two overlapping ranges, (b) an explicit
threshold `eta_0(n)` below which it applies, and (c) the modulus part of the
perturbation carried through Lemma 1's far-field half, which is currently stated
for the angular family the recorded kernel identity covers. **None of these is
done here.** In particular this does **not** prove
`form_a_cut_cusp_exponent_at_the_regular_gon`'s constant `c_n > 0`; it identifies
what a proof of it would have to select, and shows that the selection is forced
rather than searched.

**Measured, not proved:** every number in §4 and §5. Segment maxima are exact
(real roots of `d|f|^2/dt`), so a `V <= 1` row **is** a certificate that Form
A-cut holds at that configuration with that pair, and a `V > 1` row is a sound
refutation of that *selector*. The sampled `3001`-point instrument used in a
first pass reported `70/70` for the antipodal rule as well and missed the `n=12`
crossing of §5; both are corrected above.

**Erdős #1041 remains open**, and Form A-cut is a *sufficient* family, so its
success proves the target while its failure would prove nothing.

## Replay

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_form_a_cut_selector.py --part all
```

| arm | what fails it |
|---|---|
| `HALFPLANE` | the good set is not a contiguous arc, or has fewer than `floor(n/2)` members, or `floor(n/2) >= 2` does not first hold at `n = 4` |
| `DERIV` | `P_j'(0) != Re(E_1 omega^j)` |
| `CHORD` | an adjacent pair fails the criterion of §3, or `Re(w^n) < 0` reaches an endpoint |
| `ADJ` | the adjacent-good-pair selector returns `V > 1` at any `eta <= 1e-2` configuration, the free optimum reaches `1` anywhere in the `n = 12` scan, or that scan fails to exhibit the selector's crossing |
| `ANTI` | the most-antipodal-good-pair selector does **not** exceed `1` at the three recorded rows |
