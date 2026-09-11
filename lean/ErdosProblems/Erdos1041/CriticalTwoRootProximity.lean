import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Erdős #1041: the constant `2` from the critical-point balance alone

`CassiniTreeBudget` falsifies the coarea/tree-length metric estimate: the
Cassini family makes the proposed tree budget numerically smaller than the
distance between two roots.  That kills the route, not the conjecture — the
Cassini segment itself has length `2a < 2`.

This module recovers the sharp metric scale `2` by a completely different
mechanism, with no coarea, no tree, and no perimeter tail.  It uses only the
**logarithmic balance at a critical point** together with the geometric mean of
the root distances.

It also checks the decisive algebraic core of the stronger global disk theorem:
for roots in the closed unit disk, the two nearest roots to **every** critical
point have total distance at most `2`, with no boundary-annulus exception
(`two_add_le_two_of_disk_inverse_balance`).

## The theorem

Let `c` be a point at which the logarithmic derivative vanishes,

```
  ∑_k (c - z_k)⁻¹ = 0,
```

and let `r` be the geometric mean of the distances, `r^n = ∏_k ‖c - z_k‖`.
Then two distinct roots satisfy

```
  ‖c - z_i‖ + ‖c - z_j‖ ≤ 2r.
```

(`exists_two_roots_dist_sum_le_two_mul_geomMean`.)

Combined with any bound placing some critical value inside the unit lemniscate
— for roots in the open unit disc the discriminant/Hadamard bound
`|Disc| < n^n` supplies one — this produces a critical point `c` and two roots
whose **broken line through `c` has total length `< 2`**, which is exactly the
Erdős–Herzog–Piranian scale.

## Why this is not yet the Erdős path

The two straight spokes can leave the lemniscate.  The degree-five example

```
  F(z) = (z-r)(z-ir)(z+ir)(z-rω)(z-rω̄),   ω = e^{2πi/3},   r = 999/1000
```

has `F'(0) = 0` and `|F(0)| = r^5 < 1`, yet at `z = r/10` on the spoke towards
the real root, `|F(r/10)| = r^5 · 100899/100000 > 1` — the exact integer
comparison `999^5 · 100899 = 100395512981514394101 > 10^20`
(`spoke_escapes_lemniscate_exact`).  The two spokes towards `±ir` are safe, so
this is **not** a counterexample to #1041; it shows the remaining statement is a
*selection* theorem for the two descending branches, not blanket
star-shapedness.

## The mechanism

The proof is two inequalities and one Bernoulli estimate.  Writing `d_k` for
the distances sorted so that `d_i` is smallest and `d_j` next:

* the balance gives `1/d_i ≤ ∑_{k≠i} 1/d_k ≤ (n-1)/d_j`, hence `d_j ≤ (n-1)d_i`;
* the geometric mean gives `r^n = ∏_k d_k ≥ d_i · d_j^{n-1}`.

`two_add_le_two_of_bernoulli` then shows those two constraints alone force
`d_i + d_j ≤ 2r`.  The constant `2` is not tuned: it is the exact output of the
Bernoulli inequality `(1-u)(1+u)^m ≥ (1-u)(1+mu) > 1`.

## Claim ceiling

**Erdős #1041 remains open.**  The ordinary proof in
`GlobalCriticalTwoNearestBudget.md`, together with the algebraic consumer here,
closes the global Euclidean critical-point budget.  It does not prove
containment; nothing here shows that the selected roots admit a path of that
length inside `{|f| < 1}`.
-/

namespace ErdosProblems.Erdos1041

/-! ## The real core -/

/-- **The sharp constant `2`.**  The two normalised distances at a critical
point satisfy `b ≤ m·a` and `a·b^m ≤ 1`; those two constraints alone force
`a + b ≤ 2`.  The bound is the exact output of Bernoulli's inequality. -/
theorem two_add_le_two_of_bernoulli {m : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbm : b ≤ (m : ℝ) * a) (hprod : a * b ^ m ≤ 1) :
    a + b ≤ 2 := by
  by_contra hcon
  push Not at hcon
  -- `b > 1`, else `a + b ≤ 2b ≤ 2`.
  have hb1 : 1 < b := by
    by_contra hb
    push Not at hb
    linarith
  have hbpos : 0 < b := lt_trans zero_lt_one hb1
  -- `a < 1`, else `a * b ^ m ≥ b ^ m > 1`.
  have ha1 : a < 1 := by
    by_contra hA
    push Not at hA
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exfalso
        subst h
        simp at hbm
        linarith
      · exact h
    have hbm1 : 1 < b ^ m := one_lt_pow₀ hb1 (by omega)
    nlinarith
  -- `a > 2/(m+1)` from `2 < a + b ≤ (m+1)a`.
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hagt : 2 < ((m : ℝ) + 1) * a := by nlinarith
  set u : ℝ := 1 - a with hu
  have hupos : 0 < u := by simp only [hu]; linarith
  -- `u < (m-1)/(m+1)`, which already forces `m ≥ 2`.
  have hukey : ((m : ℝ) + 1) * u < (m : ℝ) - 1 := by
    simp only [hu]
    nlinarith
  -- `m·u < m - 1` follows from `(m+1)u < m-1` and `u > 0`.
  have hmu : (m : ℝ) * u < (m : ℝ) - 1 := by nlinarith [hukey, hupos]
  -- Bernoulli.
  have hbern : 1 + (m : ℝ) * u ≤ (1 + u) ^ m := by
    have := one_add_mul_le_pow (a := u) (by linarith) m
    linarith [this]
  have hbgt : 1 + u < b := by simp only [hu]; linarith
  have hpow : (1 + u) ^ m ≤ b ^ m :=
    pow_le_pow_left₀ (by linarith) (le_of_lt hbgt) m
  have h1 : (1 : ℝ) + (m : ℝ) * u ≤ b ^ m := le_trans hbern hpow
  have hstep1 : a * (1 + (m : ℝ) * u) ≤ a * b ^ m :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt ha)
  have haeq : a = 1 - u := by simp only [hu]; ring
  have hstep2 : 1 < a * (1 + (m : ℝ) * u) := by
    rw [haeq]
    nlinarith [mul_pos hupos (show (0 : ℝ) < (m : ℝ) - 1 - (m : ℝ) * u by linarith)]
  linarith

/-- **Global disk/inverse-balance budget.**  This is the algebraic core of the
global two-nearest-root theorem.  Here `t` is the modulus of the critical
point, `δ ≤ e` are its two smallest root distances, and `N` is the degree.

The hypotheses record exactly the four geometric inputs:

* `δ ≤ 1` (nearest-root bound in the unit disk),
* `e ≤ 1 + t` (the diameter bound),
* `e ≤ (N-1)δ` (reciprocal balance at the critical point), and
* the inverse-square disk estimate.

Together they force the sharp conclusion `δ + e ≤ 2`, with no restriction
such as `t ≤ 1 - 2/N`. -/
theorem two_add_le_two_of_disk_inverse_balance
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e ≤ 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have he1 : 1 < e := by
    by_contra he
    push Not at he
    linarith
  have hepos : 0 < e := lt_trans zero_lt_one he1
  -- A violating pair must straddle the radial gap: `1 - t < δ`.
  have hgap : 1 - t < δ := by linarith
  have hgap0 : 0 ≤ 1 - δ := by linarith
  have htgap : 1 - δ < t := by linarith
  have htsum : 0 < t + (1 - δ) := by nlinarith
  have hsquares : (1 - δ) ^ 2 < t ^ 2 := by
    have hfac : 0 < (t - (1 - δ)) * (t + (1 - δ)) :=
      mul_pos (sub_pos.mpr htgap) htsum
    nlinarith
  -- Hence the disk scale is strictly smaller than `δ(2-δ)`, and the
  -- putative violation makes that in turn strictly smaller than `δe`.
  have hscale : 1 - t ^ 2 < δ * (2 - δ) := by nlinarith [hsquares]
  have htwodelta : 2 - δ < e := by linarith
  have hscale' : 1 - t ^ 2 < δ * e :=
    lt_trans hscale (mul_lt_mul_of_pos_left htwodelta hδ)
  have hApos : 0 < 1 / δ ^ 2 + (N - 1) / e ^ 2 := by
    have hleft : 0 < 1 / δ ^ 2 := one_div_pos.mpr (sq_pos_of_pos hδ)
    have hright : 0 ≤ (N - 1) / e ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg e)
    linarith
  have hstrict :
      N < δ * e * (1 / δ ^ 2 + (N - 1) / e ^ 2) := by
    have hmul := mul_lt_mul_of_pos_right hscale' hApos
    exact lt_of_le_of_lt hstar hmul
  -- After cancelling the positive distances this is
  -- `N < x + (N-1)/x`, where `x = e/δ`.
  set x : ℝ := e / δ with hx
  have hxpos : 0 < x := by simp only [hx]; positivity
  have hx1 : 1 ≤ x := by
    simp only [hx]
    exact (le_div_iff₀ hδ).2 (by simpa using hδe)
  have hxN : x ≤ N - 1 := by
    simp only [hx]
    exact (div_le_iff₀ hδ).2 hbal
  have hquad : (x - 1) * (x - (N - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx1) (sub_nonpos.mpr hxN)
  have hpoly : x ^ 2 + (N - 1) ≤ N * x := by nlinarith [hquad]
  have hratio : x + (N - 1) / x ≤ N := by
    have hid : x + (N - 1) / x = (x ^ 2 + (N - 1)) / x := by
      field_simp
    rw [hid]
    exact (div_le_iff₀ hxpos).2 hpoly
  have hcancel :
      δ * e * (1 / δ ^ 2 + (N - 1) / e ^ 2) = x + (N - 1) / x := by
    simp only [hx]
    field_simp
  rw [hcancel] at hstrict
  linarith

/-- A strict diameter margin makes the global two-nearest-root budget strict. -/
theorem two_add_lt_two_of_disk_inverse_balance_of_strict_diameter
    {N t δ e : ℝ}
    (hN : 2 ≤ N) (ht1 : t < 1)
    (hδ : 0 < δ) (hδe : δ ≤ e) (hδ1 : δ ≤ 1)
    (hemax : e < 1 + t) (hbal : e ≤ (N - 1) * δ)
    (hstar : N ≤ (1 - t ^ 2) * (1 / δ ^ 2 + (N - 1) / e ^ 2)) :
    δ + e < 2 := by
  have hupper := two_add_le_two_of_disk_inverse_balance hN ht1 hδ hδe hδ1
    (le_of_lt hemax) hbal hstar
  by_contra hnot
  have hge : 2 ≤ δ + e := le_of_not_gt hnot
  have hsum : δ + e = 2 := le_antisymm hupper hge
  have hgap : 1 - t < δ := by linarith
  have hgap0 : 0 ≤ 1 - δ := by linarith
  have htgap : 1 - δ < t := by linarith
  have htsum : 0 < t + (1 - δ) := by nlinarith
  have hsquares : (1 - δ) ^ 2 < t ^ 2 := by
    have hfac : 0 < (t - (1 - δ)) * (t + (1 - δ)) :=
      mul_pos (sub_pos.mpr htgap) htsum
    nlinarith
  have hscale : 1 - t ^ 2 < δ * (2 - δ) := by nlinarith [hsquares]
  have hepos : 0 < e := by nlinarith [hsum, hδ1]
  have htwodelta : 2 - δ = e := by linarith
  have hscale' : 1 - t ^ 2 < δ * e := by
    calc
      1 - t ^ 2 < δ * (2 - δ) := hscale
      _ = δ * e := by rw [htwodelta]
  have hApos : 0 < 1 / δ ^ 2 + (N - 1) / e ^ 2 := by
    have hleft : 0 < 1 / δ ^ 2 := one_div_pos.mpr (sq_pos_of_pos hδ)
    have hright : 0 ≤ (N - 1) / e ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg e)
    linarith
  have hstrict :
      N < δ * e * (1 / δ ^ 2 + (N - 1) / e ^ 2) := by
    have hmul := mul_lt_mul_of_pos_right hscale' hApos
    exact lt_of_le_of_lt hstar hmul
  set x : ℝ := e / δ with hx
  have hxpos : 0 < x := by simp only [hx]; positivity
  have hx1 : 1 ≤ x := by
    simp only [hx]
    exact (le_div_iff₀ hδ).2 (by simpa using hδe)
  have hxN : x ≤ N - 1 := by
    simp only [hx]
    exact (div_le_iff₀ hδ).2 hbal
  have hquad : (x - 1) * (x - (N - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx1) (sub_nonpos.mpr hxN)
  have hpoly : x ^ 2 + (N - 1) ≤ N * x := by nlinarith [hquad]
  have hratio : x + (N - 1) / x ≤ N := by
    have hid : x + (N - 1) / x = (x ^ 2 + (N - 1)) / x := by
      field_simp
    rw [hid]
    exact (div_le_iff₀ hxpos).2 hpoly
  have hcancel :
      δ * e * (1 / δ ^ 2 + (N - 1) / e ^ 2) = x + (N - 1) / x := by
    simp only [hx]
    field_simp
  rw [hcancel] at hstrict
  linarith

/-! ## The critical two-root proximity theorem -/

open Finset in
/-- **Critical geometric-mean proximity.**  If the logarithmic derivative
vanishes at `c`, then two distinct roots lie within total distance `2r` of `c`,
where `r` is the geometric mean of all the root distances. -/
theorem exists_two_roots_dist_sum_le_two_mul_geomMean
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ)
    (hne : ∀ k, c - z k ≠ 0)
    (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    {r : ℝ} (hr : 0 < r) (hrn : r ^ n = ∏ k, ‖c - z k‖) :
    ∃ i j : Fin n, i ≠ j ∧ ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r := by
  classical
  set d : Fin n → ℝ := fun k => ‖c - z k‖ with hd
  have hdpos : ∀ k, 0 < d k := fun k => norm_pos_iff.mpr (hne k)
  have huniv : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  obtain ⟨i, -, hi⟩ := exists_min_image (univ : Finset (Fin n)) d huniv
  have herase : (univ.erase i).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hjmem, hj⟩ := exists_min_image (univ.erase i) d herase
  have hij : i ≠ j := fun h => (mem_erase.mp hjmem).1 h.symm
  refine ⟨i, j, hij, ?_⟩
  have hdi := hdpos i
  have hdj := hdpos j
  have hdij : d i ≤ d j := hi j (mem_univ j)
  have hcard : (univ.erase i).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have hn1R : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- (a)  the logarithmic balance:  d j ≤ (n-1) * d i
  have hbal : d j ≤ ((n : ℝ) - 1) * d i := by
    have hsum := Finset.add_sum_erase univ (fun k => (c - z k)⁻¹) (mem_univ i)
    rw [hcrit] at hsum
    have hsplit : (c - z i)⁻¹ = -∑ k ∈ univ.erase i, (c - z k)⁻¹ := by
      linear_combination hsum
    have hnorm : (d i)⁻¹ ≤ ∑ k ∈ univ.erase i, (d k)⁻¹ := by
      calc (d i)⁻¹ = ‖(c - z i)⁻¹‖ := by rw [norm_inv]
        _ = ‖∑ k ∈ univ.erase i, (c - z k)⁻¹‖ := by rw [hsplit, norm_neg]
        _ ≤ ∑ k ∈ univ.erase i, ‖(c - z k)⁻¹‖ := norm_sum_le _ _
        _ = ∑ k ∈ univ.erase i, (d k)⁻¹ := by
            exact Finset.sum_congr rfl fun k _ => by rw [norm_inv]
    have hbound : ∑ k ∈ univ.erase i, (d k)⁻¹ ≤ ((n : ℝ) - 1) * (d j)⁻¹ := by
      calc ∑ k ∈ univ.erase i, (d k)⁻¹
          ≤ ∑ _k ∈ univ.erase i, (d j)⁻¹ := by
            refine Finset.sum_le_sum fun k hk => ?_
            exact inv_anti₀ hdj (hj k hk)
        _ = ((univ.erase i).card : ℝ) * (d j)⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((n : ℝ) - 1) * (d j)⁻¹ := by rw [hcard, hn1R]
    have hchain : (d i)⁻¹ ≤ ((n : ℝ) - 1) * (d j)⁻¹ := le_trans hnorm hbound
    have hmul := mul_le_mul_of_nonneg_right hchain
      (by positivity : (0 : ℝ) ≤ d i * d j)
    have hL : (d i)⁻¹ * (d i * d j) = d j := by field_simp
    have hR : (((n : ℝ) - 1) * (d j)⁻¹) * (d i * d j) = ((n : ℝ) - 1) * d i := by
      field_simp
    rwa [hL, hR] at hmul
  -- (b)  the geometric mean:  d i * d j ^ (n-1) ≤ r ^ n
  have hgeom : d i * d j ^ (n - 1) ≤ r ^ n := by
    have hsub : d j ^ (n - 1) ≤ ∏ k ∈ univ.erase i, d k := by
      calc d j ^ (n - 1) = ∏ _k ∈ univ.erase i, d j := by
            rw [Finset.prod_const, hcard]
        _ ≤ ∏ k ∈ univ.erase i, d k :=
            Finset.prod_le_prod (fun _ _ => le_of_lt hdj) (fun k hk => hj k hk)
    have hfac : ∏ k, d k = d i * ∏ k ∈ univ.erase i, d k :=
      (Finset.mul_prod_erase univ d (mem_univ i)).symm
    rw [hrn, hfac]
    exact mul_le_mul_of_nonneg_left hsub (le_of_lt hdi)
  -- Normalise and apply the real core.
  have hrn1 : r ^ n = r * r ^ (n - 1) := by
    conv_lhs => rw [show n = 1 + (n - 1) by omega]
    rw [pow_add, pow_one]
  have hapos : 0 < d i / r := div_pos hdi hr
  have hab : d i / r ≤ d j / r := by gcongr
  have hbm : d j / r ≤ ((n - 1 : ℕ) : ℝ) * (d i / r) := by
    rw [hn1R]
    rw [div_le_iff₀ hr]
    have hexp : ((n : ℝ) - 1) * (d i / r) * r = ((n : ℝ) - 1) * d i := by
      field_simp
    rw [hexp]
    exact hbal
  have hprod : (d i / r) * (d j / r) ^ (n - 1) ≤ 1 := by
    rw [div_pow, div_mul_div_comm, div_le_one (by positivity)]
    calc d i * d j ^ (n - 1) ≤ r ^ n := hgeom
      _ = r * r ^ (n - 1) := hrn1
  have hcore := two_add_le_two_of_bernoulli hapos hab hbm hprod
  have hfin := mul_le_mul_of_nonneg_right hcore (le_of_lt hr)
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hr), div_mul_cancel₀ _ (ne_of_gt hr)] at hfin
  linarith

/-! ## The degree-five falsifier to the naive spoke completion -/

/-- The exact integer comparison behind the degree-five falsifier: on the spoke
from the critical point `0` to the real root, the quintic exceeds modulus one.
`|F(r/10)| = r^5 · 100899/100000` with `r = 999/1000`, and
`999^5 · 100899 > 10^20`. -/
theorem spoke_escapes_lemniscate_exact :
    (10 : ℕ) ^ 20 < 999 ^ 5 * 100899 := by norm_num

/-! ## A unique-nearest-root obstruction to the straight-spoke completion

The preceding example has five roots at the same radius, so a selection rule
could avoid its unsafe real spoke by resolving the distance tie differently.
The exact configuration below removes that loophole.  Put

`p = 999/1000`, `a = (901/902)p`, and
`u± = (-451 ± 780i)/901`.

The five roots are `a`, `±ip`, and `p u±`.  Since
`451² + 780² = 901²`, the last four roots have modulus `p`, whereas the real
root has the strictly smaller modulus `a`.  Their reciprocal sum is zero.  At
one tenth of the unique nearest spoke, the factored polynomial has modulus
strictly larger than one.  Thus the two-nearest-roots theorem above cannot be
completed by joining its selected roots to the critical point with straight
segments.
-/

private noncomputable def nearestSpokeP : ℂ := (999 : ℂ) / 1000

private noncomputable def nearestSpokeA : ℂ := ((901 : ℂ) / 902) * nearestSpokeP

private noncomputable def nearestSpokeUPlus : ℂ := ((-451 : ℂ) + 780 * Complex.I) / 901

private noncomputable def nearestSpokeUMinus : ℂ := ((-451 : ℂ) - 780 * Complex.I) / 901

private noncomputable def nearestSpokeRoot : Fin 5 → ℂ
  | 0 => nearestSpokeA
  | 1 => Complex.I * nearestSpokeP
  | 2 => -Complex.I * nearestSpokeP
  | 3 => nearestSpokeP * nearestSpokeUPlus
  | 4 => nearestSpokeP * nearestSpokeUMinus

/-- The five explicit roots have critical-point balance at the origin. -/
theorem nearestSpoke_reciprocal_balance :
    ∑ k, (nearestSpokeRoot k)⁻¹ = 0 := by
  simp [Fin.sum_univ_succ, nearestSpokeRoot, nearestSpokeA, nearestSpokeP,
    nearestSpokeUPlus, nearestSpokeUMinus]
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]

/-- The real root is the unique nearest root to the critical point.  Squared
norms avoid any square-root normalization in this exact certificate. -/
theorem nearestSpoke_unique_nearest_normSq :
    (∀ k : Fin 5, k ≠ 0 →
      Complex.normSq (nearestSpokeRoot 0) < Complex.normSq (nearestSpokeRoot k)) := by
  intro k hk
  fin_cases k <;> norm_num [nearestSpokeRoot, nearestSpokeA, nearestSpokeP,
    nearestSpokeUPlus, nearestSpokeUMinus, Complex.normSq_apply] at *

/-- Exact evaluation on one tenth of the unique nearest straight spoke.  The
four positive factors are the absolute values of
`(z-a)`, `(z²+p²)`, and `(z-pu+)(z-pu-)` at `z=a/10`. -/
theorem nearestSpoke_unique_nearest_spoke_escapes :
    (1 : ℝ) <
      (900099 / 902000 : ℝ) * (1 - 1 / 10) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 + (999 / 1000) ^ 2) *
        (((1 / 10 : ℝ) * (900099 / 902000)) ^ 2 +
          (1 / 10) * (999 / 1000) ^ 2 + (999 / 1000) ^ 2) := by
  norm_num

/-! ## Every straight root-pair segment can fail

The preceding quintic rules out a particular two-spoke selection through a
critical point.  The cubic below is stronger in a different direction: no
straight segment between any two of its roots stays in the unit lemniscate.
The midpoint of every pair is enough to witness failure.
-/

private noncomputable def allStraightRadius : ℂ := (99 : ℂ) / 100

private noncomputable def allStraightOmega : ℂ :=
  (-1 : ℂ) / 2 + ((Real.sqrt 3 : ℂ) / 2) * Complex.I

private noncomputable def allStraightRoot : Fin 3 → ℂ
  | 0 => allStraightRadius
  | 1 => allStraightRadius * allStraightOmega
  | 2 => allStraightRadius * allStraightOmega ^ 2

private noncomputable def allStraightCubic (z : ℂ) : ℂ :=
  z ^ 3 - allStraightRadius ^ 3

private theorem allStraightOmega_quadratic :
    allStraightOmega ^ 2 + allStraightOmega + 1 = 0 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    norm_num [allStraightOmega, pow_two, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im] <;> nlinarith

private theorem allStraightOmega_cube : allStraightOmega ^ 3 = 1 := by
  apply sub_eq_zero.mp
  calc allStraightOmega ^ 3 - 1 =
        (allStraightOmega - 1) *
          (allStraightOmega ^ 2 + allStraightOmega + 1) := by ring
    _ = 0 := by rw [allStraightOmega_quadratic, mul_zero]

private theorem allStraightOmega_normSq :
    Complex.normSq allStraightOmega = 1 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  simp [allStraightOmega, Complex.normSq_apply]
  ring_nf
  nlinarith

/-- All three explicit cubic roots lie strictly inside the unit disk. -/
theorem allStraightCubic_roots_in_unitDisk :
    ∀ k : Fin 3, ‖allStraightRoot k‖ < 1 := by
  intro k
  have homega : ‖allStraightOmega‖ = 1 := by
    rw [Complex.norm_def, allStraightOmega_normSq]
    norm_num
  fin_cases k <;>
    simp [allStraightRoot, allStraightRadius, homega, norm_pow] <;> norm_num

/-- The displayed points are roots of `z³-r³`. -/
theorem allStraightCubic_roots :
    ∀ k : Fin 3, allStraightCubic (allStraightRoot k) = 0 := by
  intro k
  fin_cases k
  · simp [allStraightCubic, allStraightRoot]
  · simp [allStraightCubic, allStraightRoot, mul_pow, allStraightOmega_cube]
  · simp [allStraightCubic, allStraightRoot, mul_pow, allStraightOmega_cube]
    rw [show (allStraightOmega ^ 2) ^ 3 =
      (allStraightOmega ^ 3) ^ 2 by ring]
    rw [allStraightOmega_cube]
    ring

private theorem allStraight_midpoint_value_of_unit
    (u : ℂ) (hu : u ^ 3 = 1) :
    allStraightCubic (-(allStraightRadius * u) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  unfold allStraightCubic
  rw [div_pow, neg_pow, mul_pow, hu]
  ring

private theorem allStraight_pair_zero_one :
    allStraightCubic ((allStraightRoot 0 + allStraightRoot 1) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  rw [show (allStraightRoot 0 + allStraightRoot 1) / 2 =
      -(allStraightRadius * allStraightOmega ^ 2) / 2 by
        simp only [allStraightRoot]
        linear_combination (allStraightRadius / 2) * allStraightOmega_quadratic]
  apply allStraight_midpoint_value_of_unit
  rw [show (allStraightOmega ^ 2) ^ 3 =
    (allStraightOmega ^ 3) ^ 2 by ring]
  rw [allStraightOmega_cube]
  norm_num

private theorem allStraight_pair_zero_two :
    allStraightCubic ((allStraightRoot 0 + allStraightRoot 2) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  rw [show (allStraightRoot 0 + allStraightRoot 2) / 2 =
      -(allStraightRadius * allStraightOmega) / 2 by
        simp only [allStraightRoot]
        linear_combination (allStraightRadius / 2) * allStraightOmega_quadratic]
  exact allStraight_midpoint_value_of_unit allStraightOmega allStraightOmega_cube

private theorem allStraight_pair_one_two :
    allStraightCubic ((allStraightRoot 1 + allStraightRoot 2) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  rw [show (allStraightRoot 1 + allStraightRoot 2) / 2 =
      -(allStraightRadius * 1) / 2 by
        simp only [allStraightRoot]
        linear_combination (allStraightRadius / 2) * allStraightOmega_quadratic]
  exact allStraight_midpoint_value_of_unit 1 (by norm_num)

private theorem allStraight_pair_midpoint_value
    (i j : Fin 3) (hij : i ≠ j) :
    allStraightCubic ((allStraightRoot i + allStraightRoot j) / 2) =
      -(9 / 8 : ℂ) * allStraightRadius ^ 3 := by
  fin_cases i <;> fin_cases j <;> simp_all
  · simpa only [neg_mul] using allStraight_pair_zero_one
  · simpa only [neg_mul] using allStraight_pair_zero_two
  · convert allStraight_pair_zero_one using 1 <;> ring
  · simpa only [neg_mul] using allStraight_pair_one_two
  · convert allStraight_pair_zero_two using 1 <;> ring
  · convert allStraight_pair_one_two using 1 <;> ring

/-- **All-straight-segments no-go.**  For this monic cubic with all roots in
the open unit disk, every pair of distinct roots has a midpoint outside the
strict unit lemniscate.  Hence no straight root-pair segment can prove
Erdős #1041 in general; a genuinely curved or topological mechanism is
necessary. -/
theorem allStraightCubic_every_pair_midpoint_escapes :
    ∀ i j : Fin 3, i ≠ j →
      1 < ‖allStraightCubic ((allStraightRoot i + allStraightRoot j) / 2)‖ := by
  intro i j hij
  rw [allStraight_pair_midpoint_value i j hij, norm_mul, norm_neg]
  norm_num [allStraightRadius, norm_pow]

end ErdosProblems.Erdos1041
