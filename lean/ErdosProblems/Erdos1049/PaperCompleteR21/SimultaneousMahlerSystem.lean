import Mathlib

/-!
# Erdős #1049: no finite simultaneous `2`/`3`-system

Lean form of `long1049:res:nomahler`
(`paper/reasoning-parts/erdos1049/core.tex`, line 3569):

> Let `ℒ(z) = ∑_{n ≥ 1} zⁿ/(1 - zⁿ)`.  There is no finite-dimensional
> `ℚ(z)`-vector space that contains `ℒ` and is stable under both `z ↦ z²` and
> `z ↦ z³`.

The ambient space is the field `ℚ((z))` of formal Laurent series, a vector space
over `ℚ(z)`, exactly as the paragraph above the proposition states; in Mathlib
this is `ℚ⸨X⸩ = HahnSeries ℤ ℚ`, a module over `RatFunc ℚ`.  Stability means that
substituting `z^k` for `z` sends the subspace into itself; that substitution is
the ring homomorphism `subs k` below, and it is not `ℚ(z)`-linear.

`ℒ` is the divisor generating series.  The paper introduces it in this very
subsection as `𝓛(z) = ∑_{n ≥ 1} τ(n) zⁿ` and then displays it in the Lambert
form; the two are the same series.  `divisorLambert` is that series, and
`divisorReal_partial_lower` records the Lambert relation in the direction the
boundary estimate uses: for real `0 < s < 1` and every `N`,
`∑_{d ≤ N} s^d/(1 - s^d) ≤ ∑ₙ τ(n) sⁿ`.

## What is proved and what is assumed

Everything in the paper's proof is proved here except one cited external
theorem.  `AdamczewskiBell` is the hypothesis form of

  B. Adamczewski and J. P. Bell, *A problem about Mahler functions*,
  Thm. 1.1, p. 6 (cited as `[adamczewskibell2013]` in the paper):

a Laurent series that is both `k`-Mahler and `l`-Mahler, for multiplicatively
independent `k, l ≥ 2`, is a rational function.  It is absent from Mathlib and
from this tree, and the paper states the proposition unconditionally, so the
main theorem takes it as one explicit named hypothesis.

Everything else is proved here:

* `mahler_of_stable`: a finite-dimensional `ℚ(z)`-subspace stable under
  `z ↦ z^k` forces a genuine `k`-Mahler equation, one with a nonzero
  coefficient of the unshifted function, for some `z ↦ z^{k^j}` substitute of
  its member.  This is the paper's linear-dependence step together with the
  step that produces a nonzero unshifted coefficient.
* `isMahler_subs`: a `k`-Mahler function stays `k`-Mahler after `z ↦ z^m`.
  With the previous item this brings the two bases to one common function,
  which is what the Adamczewski–Bell theorem is applied to.
* `divisorLambert_subs_not_rational`: no `z ↦ z^M` substitute of `ℒ` is a
  rational function.  This is the paper's own functional nonrationality
  (`long1049:sec:source-forms`): `(x-1)F(x) → ∞` and `(x-1)²F(x) → 0` as
  `x ↓ 1`, which no rational function does.  It is proved here in the
  equivalent variable `ℒ(z) = F(1/z)`, in the elementary form
  `(1-r)·ℒ(r) → ∞` and `(1-r)²·ℒ(r) → 0` as `r ↑ 1`
  (`tendsto_one_sub_mul_divisorReal`, `tendsto_one_sub_sq_mul_divisorReal`).
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21

open scoped LaurentSeries PowerSeries Polynomial RatFunc
open Filter Topology

noncomputable section NoMahlerSystem

/-! ## The substitution `z ↦ z ^ k` on `ℚ((z))` -/

/-- `max k 1`, as an integer.  Using `max k 1` keeps the substitution below a
total function of `k`; every statement about it carries `1 ≤ k`, where it is
`k`. -/
private def kpos (k : ℕ) : ℤ := ((max k 1 : ℕ) : ℤ)

private lemma kpos_pos (k : ℕ) : 0 < kpos k := by
  have h : 1 ≤ max k 1 := le_max_right k 1
  have h' : (1 : ℤ) ≤ ((max k 1 : ℕ) : ℤ) := by exact_mod_cast h
  exact lt_of_lt_of_le zero_lt_one h'

private lemma kpos_eq {k : ℕ} (hk : 1 ≤ k) : kpos k = (k : ℤ) := by
  simp [kpos, max_eq_left hk]

/-- `n ↦ k * n` as an order embedding of `ℤ`. -/
private def subsEmb (k : ℕ) : ℤ ↪o ℤ :=
  ⟨⟨fun n => kpos k * n, fun _ _ h => mul_left_cancel₀ (kpos_pos k).ne' h⟩,
    ⟨fun h => le_of_mul_le_mul_left h (kpos_pos k),
      fun h => mul_le_mul_of_nonneg_left h (kpos_pos k).le⟩⟩

/-- The substitution `z ↦ z ^ k` on `ℚ((z))`, as a ring homomorphism. -/
def subs (k : ℕ) : ℚ⸨X⸩ →+* ℚ⸨X⸩ :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (kpos k))
    (fun _ _ h => mul_left_cancel₀ (kpos_pos k).ne' h)
    (fun _ _ => ⟨fun h => le_of_mul_le_mul_left h (kpos_pos k),
      fun h => mul_le_mul_of_nonneg_left h (kpos_pos k).le⟩)

private lemma subs_eq_embDomain (k : ℕ) (f : ℚ⸨X⸩) :
    subs k f = HahnSeries.embDomain (subsEmb k) f := rfl

private lemma subs_coeff_kpos (k : ℕ) (f : ℚ⸨X⸩) (m : ℤ) :
    (subs k f).coeff (kpos k * m) = f.coeff m := by
  rw [subs_eq_embDomain]
  exact HahnSeries.embDomain_coeff (f := subsEmb k) (x := f) (a := m)

lemma subs_coeff_natMul {k : ℕ} (hk : 1 ≤ k) (f : ℚ⸨X⸩) (m : ℤ) :
    (subs k f).coeff ((k : ℤ) * m) = f.coeff m := by
  rw [← kpos_eq hk]; exact subs_coeff_kpos k f m

lemma subs_coeff_zero_of_not_dvd {k : ℕ} (hk : 1 ≤ k) (f : ℚ⸨X⸩) {n : ℤ}
    (hn : ¬ (k : ℤ) ∣ n) : (subs k f).coeff n = 0 := by
  rw [subs_eq_embDomain]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, hm⟩
  have h2 : kpos k * m = n := hm
  rw [kpos_eq hk] at h2
  exact hn ⟨m, h2.symm⟩

lemma subs_coeff {k : ℕ} (hk : 1 ≤ k) (f : ℚ⸨X⸩) (n : ℤ) :
    (subs k f).coeff n = if (k : ℤ) ∣ n then f.coeff (n / (k : ℤ)) else 0 := by
  have hk0 : (k : ℤ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  by_cases h : (k : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [if_pos ⟨m, rfl⟩, subs_coeff_natMul hk, Int.mul_ediv_cancel_left _ hk0]
  · rw [if_neg h, subs_coeff_zero_of_not_dvd hk f h]

lemma subs_one (f : ℚ⸨X⸩) : subs 1 f = f := by
  ext n
  rw [subs_coeff le_rfl]
  simp

lemma subs_comp {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (f : ℚ⸨X⸩) :
    subs k (subs l f) = subs (k * l) f := by
  have hkl : 1 ≤ k * l := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  ext n
  by_cases h : ((k * l : ℕ) : ℤ) ∣ n
  · obtain ⟨t, rfl⟩ := h
    have e : ((k * l : ℕ) : ℤ) * t = (k : ℤ) * ((l : ℤ) * t) := by push_cast; ring
    rw [subs_coeff_natMul hkl, e, subs_coeff_natMul hk, subs_coeff_natMul hl]
  · rw [subs_coeff_zero_of_not_dvd hkl f h]
    by_cases h2 : (k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := h2
      rw [subs_coeff_natMul hk]
      refine subs_coeff_zero_of_not_dvd hl f ?_
      rintro ⟨t, rfl⟩
      exact h ⟨t, by push_cast; ring⟩
    · exact subs_coeff_zero_of_not_dvd hk _ h2

/-! ## The substitution on polynomials -/

private lemma coeff_algebraMap_poly (P : ℚ[X]) (n : ℤ) :
    (algebraMap ℚ[X] ℚ⸨X⸩ P).coeff n = if n < 0 then 0 else P.coeff n.natAbs := by
  have h1 : algebraMap ℚ[X] ℚ⸨X⸩ P = ((P : ℚ⟦X⟧) : ℚ⸨X⸩) := rfl
  rw [h1, PowerSeries.coeff_coe]
  by_cases hn : n < 0
  · simp [hn]
  · simp [hn, Polynomial.coeff_coe]

/-- Substituting `z ↦ z^m` in a polynomial is `Polynomial.expand`. -/
lemma subs_algebraMap_poly {m : ℕ} (hm : 1 ≤ m) (P : ℚ[X]) :
    subs m (algebraMap ℚ[X] ℚ⸨X⸩ P)
      = algebraMap ℚ[X] ℚ⸨X⸩ (Polynomial.expand ℚ m P) := by
  have hm0 : 0 < m := hm
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm0
  ext n
  rw [subs_coeff hm, coeff_algebraMap_poly (Polynomial.expand ℚ m P) n]
  by_cases hn : n < 0
  · rw [if_pos hn]
    by_cases hd : (m : ℤ) ∣ n
    · rw [if_pos hd, coeff_algebraMap_poly, if_pos (Int.ediv_neg_of_neg_of_pos hn hmZ)]
    · rw [if_neg hd]
  · rw [if_neg hn]
    push_neg at hn
    lift n to ℕ using hn with j
    by_cases hd : (m : ℤ) ∣ (j : ℤ)
    · have hdn : m ∣ j := by exact_mod_cast hd
      obtain ⟨t, rfl⟩ := hdn
      have hmz : (m : ℤ) ≠ 0 := by
        have : m ≠ 0 := by omega
        exact_mod_cast this
      have hq : ((m * t : ℕ) : ℤ) / (m : ℤ) = (t : ℤ) := by
        push_cast
        rw [Int.mul_ediv_cancel_left _ hmz]
      rw [if_pos hd, hq, coeff_algebraMap_poly,
        if_neg (not_lt.mpr (Int.natCast_nonneg t)),
        Polynomial.coeff_expand hm0, if_pos ⟨t, rfl⟩]
      simp [Int.natAbs_mul, Nat.mul_div_cancel_left t (show 0 < m by omega)]
    · have hdn : ¬ m ∣ j := fun hc => hd (by exact_mod_cast hc)
      rw [if_neg hd, Polynomial.coeff_expand hm0, if_neg]
      simpa using hdn

/-! ## Mahler equations -/

/-- `f` satisfies a `k`-Mahler functional equation: there are polynomials
`p 0, …, p d` over `ℚ` with `p 0 ≠ 0` and `∑_{i ≤ d} pᵢ(z) · f(z^{k^i}) = 0`.
The nonvanishing of the coefficient of the *unshifted* function is part of the
definition, as in Adamczewski–Bell; the paper's proof is written exactly to
produce it. -/
def IsMahler (k : ℕ) (f : ℚ⸨X⸩) : Prop :=
  ∃ (d : ℕ) (p : ℕ → ℚ[X]), p 0 ≠ 0 ∧
    ∑ i ∈ Finset.range (d + 1), algebraMap ℚ[X] ℚ⸨X⸩ (p i) * subs (k ^ i) f = 0

/-- A `k`-Mahler function stays `k`-Mahler after the substitution `z ↦ z^m`:
apply `z ↦ z^m` to the equation, which replaces each polynomial coefficient by
its `m`-fold expansion and commutes with the `k`-powers. -/
lemma isMahler_subs {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) {f : ℚ⸨X⸩}
    (hf : IsMahler k f) : IsMahler k (subs m f) := by
  obtain ⟨d, p, hp0, hsum⟩ := hf
  refine ⟨d, fun i => Polynomial.expand ℚ m (p i), ?_, ?_⟩
  · simpa [Polynomial.expand_eq_zero (show 0 < m from hm)] using hp0
  · have hmap := congrArg (subs m) hsum
    rw [map_sum, map_zero] at hmap
    rw [← hmap]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hki : 1 ≤ k ^ i := Nat.one_le_pow _ _ (by omega)
    rw [map_mul, subs_algebraMap_poly hm, subs_comp hm hki, subs_comp hki hm,
      mul_comm m (k ^ i)]

/-! ## A finite-dimensional stable space forces a Mahler equation -/

/-- The paper's first two steps.  If a finite-dimensional `ℚ(z)`-subspace `V`
contains `f` and is stable under `z ↦ z^k`, then some `z ↦ z^{k^j}` substitute
of `f` satisfies a genuine `k`-Mahler equation.

`f(z), f(z^k), …, f(z^{k^d})` all lie in `V`, so they are linearly dependent
over `ℚ(z)`; clearing denominators gives polynomials `P₀, …, P_d`, not all zero,
with `∑ Pᵢ(z) f(z^{k^i}) = 0`.  Taking `j` least with `P_j ≠ 0` and writing
`f(z^{k^i}) = (f ∘ z^{k^j})(z^{k^{i-j}})` for `i ≥ j` leaves an equation whose
unshifted coefficient `P_j` is nonzero. -/
theorem mahler_of_stable {k : ℕ} (hk : 1 ≤ k) (V : Submodule (RatFunc ℚ) ℚ⸨X⸩)
    [Module.Finite (RatFunc ℚ) V] {f : ℚ⸨X⸩} (hf : f ∈ V)
    (hstab : ∀ g ∈ V, subs k g ∈ V) :
    ∃ j : ℕ, IsMahler k (subs (k ^ j) f) := by
  classical
  have hmem : ∀ i : ℕ, subs (k ^ i) f ∈ V := by
    intro i
    induction i with
    | zero => simpa [subs_one] using hf
    | succ i ih =>
        have hki : 1 ≤ k ^ i := Nat.one_le_pow _ _ (by omega)
        have hstep : subs k (subs (k ^ i) f) = subs (k ^ (i + 1)) f := by
          rw [subs_comp hk hki, ← pow_succ']
        rw [← hstep]
        exact hstab _ ih
  set d : ℕ := Module.finrank (RatFunc ℚ) V with hd
  have hnotli : ¬ LinearIndependent (RatFunc ℚ)
      (fun i : Fin (d + 1) => (⟨subs (k ^ (i : ℕ)) f, hmem i⟩ : V)) := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, ← hd] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hnotli
  obtain ⟨c, hc, i₀, hi₀⟩ := hnotli
  have hamb : ∑ i : Fin (d + 1), c i • subs (k ^ (i : ℕ)) f = 0 := by
    have h := congrArg (fun x : V => (x : ℚ⸨X⸩)) hc
    simpa using h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℚ[X])
    (Finset.univ : Finset (Fin (d + 1))) c
  have hball : ∀ i : Fin (d + 1), ∃ Q : ℚ[X],
      algebraMap ℚ[X] (RatFunc ℚ) Q = (b : ℚ[X]) • c i := by
    intro i
    obtain ⟨Q, hQ⟩ := hb i (Finset.mem_univ i)
    exact ⟨Q, hQ⟩
  choose Pf hPf using hball
  have hbne : (b : ℚ[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hb0 : algebraMap ℚ[X] (RatFunc ℚ) (b : ℚ[X]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).2 hbne
  set p : ℕ → ℚ[X] := fun n => if h : n < d + 1 then Pf ⟨n, h⟩ else 0 with hpdef
  have hpval : ∀ i : Fin (d + 1), p (i : ℕ) = Pf i := by
    intro i
    simp only [hpdef]
    rw [dif_pos i.isLt]
  have hpbig : ∀ n, d + 1 ≤ n → p n = 0 := by
    intro n hn
    simp only [hpdef]
    rw [dif_neg (by omega : ¬ n < d + 1)]
  have hpi₀ : p (i₀ : ℕ) ≠ 0 := by
    rw [hpval]
    intro hzero
    have h := hPf i₀
    rw [hzero, map_zero, Algebra.smul_def] at h
    rcases mul_eq_zero.1 h.symm with h1 | h1
    · exact hb0 h1
    · exact hi₀ h1
  have hrel : ∑ i ∈ Finset.range (d + 1),
      algebraMap ℚ[X] ℚ⸨X⸩ (p i) * subs (k ^ i) f = 0 := by
    have hstep : ∀ i : Fin (d + 1),
        algebraMap ℚ[X] ℚ⸨X⸩ (p (i : ℕ)) * subs (k ^ (i : ℕ)) f
          = algebraMap ℚ[X] (RatFunc ℚ) (b : ℚ[X]) •
              (c i • subs (k ^ (i : ℕ)) f) := by
      intro i
      rw [hpval, smul_smul]
      have h1 : algebraMap ℚ[X] ℚ⸨X⸩ (Pf i)
          = algebraMap (RatFunc ℚ) ℚ⸨X⸩ (algebraMap ℚ[X] (RatFunc ℚ) (Pf i)) :=
        IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) ℚ⸨X⸩ (Pf i)
      rw [h1, hPf i, Algebra.smul_def, Algebra.smul_def, map_mul]
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => algebraMap ℚ[X] ℚ⸨X⸩ (p i) * subs (k ^ i) f) (d + 1)]
    simp_rw [hstep]
    rw [← Finset.smul_sum, hamb, smul_zero]
  have hex : ∃ n, p n ≠ 0 := ⟨(i₀ : ℕ), hpi₀⟩
  have hjne : p (Nat.find hex) ≠ 0 := Nat.find_spec hex
  set j : ℕ := Nat.find hex with hj
  have hjlt : ∀ i, i < j → p i = 0 := by
    intro i hi
    have hlt : i < Nat.find hex := by rw [← hj]; exact hi
    exact not_not.mp (Nat.find_min hex hlt)
  have hjle : j ≤ d := by
    by_contra hcon
    push_neg at hcon
    exact hjne (hpbig j (by omega))
  refine ⟨j, d - j, fun t => p (j + t), by simpa using hjne, ?_⟩
  have hsub : Finset.Ico j (d + 1) ⊆ Finset.range (d + 1) := by
    intro x hx
    simp only [Finset.mem_Ico] at hx
    simp only [Finset.mem_range]
    exact hx.2
  have hzero : ∀ x ∈ Finset.range (d + 1), x ∉ Finset.Ico j (d + 1) →
      algebraMap ℚ[X] ℚ⸨X⸩ (p x) * subs (k ^ x) f = 0 := by
    intro x hx hxn
    simp only [Finset.mem_range] at hx
    have hxj : x < j := by
      rcases Nat.lt_or_ge x j with h | h
      · exact h
      · exact absurd (Finset.mem_Ico.mpr ⟨h, hx⟩) hxn
    rw [hjlt x hxj, map_zero, zero_mul]
  have hIco : ∑ i ∈ Finset.Ico j (d + 1),
      algebraMap ℚ[X] ℚ⸨X⸩ (p i) * subs (k ^ i) f = 0 := by
    rw [Finset.sum_subset hsub hzero]; exact hrel
  rw [Finset.sum_Ico_eq_sum_range, show d + 1 - j = (d - j) + 1 by omega] at hIco
  rw [← hIco]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hki : 1 ≤ k ^ i := Nat.one_le_pow _ _ (by omega)
  have hkj : 1 ≤ k ^ j := Nat.one_le_pow _ _ (by omega)
  rw [subs_comp hki hkj, ← pow_add, Nat.add_comm i j]

/-! ## The divisor generating series -/

/-- `ℒ(z) = ∑_{n ≥ 1} zⁿ/(1 - zⁿ) = ∑_{n ≥ 1} τ(n) zⁿ`, the divisor generating
series, as a formal Laurent series over `ℚ`. -/
def divisorLambert : ℚ⸨X⸩ :=
  HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk fun n => (n.divisors.card : ℚ))

/-- The same series read as a real function: `ℒ(s) = ∑ₙ τ(n) sⁿ`. -/
def divisorReal (s : ℝ) : ℝ := ∑' n : ℕ, (n.divisors.card : ℝ) * s ^ n

private lemma tau_le_self (n : ℕ) : (n.divisors.card : ℝ) ≤ (n : ℝ) := by
  have hsub : n.divisors ⊆ Finset.Ico 1 (n + 1) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hd.2 (Nat.eq_zero_of_zero_dvd hd.1)
    rw [Finset.mem_Ico]
    exact ⟨Nat.one_le_iff_ne_zero.mpr hd0,
      Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1)⟩
  have hcard : n.divisors.card ≤ n := by
    have h := Finset.card_le_card hsub
    simpa using h
  exact_mod_cast hcard

lemma divisorReal_summable {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable fun n : ℕ => (n.divisors.card : ℝ) * s ^ n := by
  have hnorm : ‖s‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hs0]
  have hgeo : Summable fun n : ℕ => (n : ℝ) * s ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  exact mul_le_mul_of_nonneg_right (tau_le_self n) (by positivity)

lemma divisorReal_nonneg {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ divisorReal s :=
  tsum_nonneg fun n => by positivity

/-! ### The elementary inequality `1 - s^d ≤ d (1 - s)` -/

private lemma one_sub_pow_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (d : ℕ) :
    1 - s ^ d ≤ (d : ℝ) * (1 - s) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hpow : s ^ d ≤ 1 := pow_le_one₀ hs0 hs1
      have hmul : s * (1 - s ^ d) ≤ 1 * (1 - s ^ d) :=
        mul_le_mul_of_nonneg_right hs1 (by linarith)
      have hsplit : 1 - s ^ (d + 1) = (1 - s) + s * (1 - s ^ d) := by ring
      push_cast
      rw [hsplit]
      nlinarith [ih, hmul]

/-! ### The Lambert lower bound -/

private lemma geom_block {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {d : ℕ} (hd : 1 ≤ d) :
    ∑' n : ℕ, (if d ∣ n ∧ 1 ≤ n then s ^ n else 0) = s ^ d / (1 - s ^ d) := by
  have hsd1 : s ^ d < 1 := pow_lt_one₀ hs0.le hs1 (by omega)
  have hsd0 : (0 : ℝ) ≤ s ^ d := by positivity
  have hinj : Function.Injective (fun k : ℕ => d * (k + 1)) := by
    intro a b hab
    have h := Nat.eq_of_mul_eq_mul_left (show 0 < d by omega) hab
    omega
  have hsupp : Function.support (fun n : ℕ => (if d ∣ n ∧ 1 ≤ n then s ^ n else 0))
      ⊆ Set.range (fun k : ℕ => d * (k + 1)) := by
    intro n hn
    by_cases hcase : d ∣ n ∧ 1 ≤ n
    · obtain ⟨⟨m, rfl⟩, hn1⟩ := hcase
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hn1
        · exact h
      refine ⟨m - 1, ?_⟩
      show d * (m - 1 + 1) = d * m
      rw [Nat.sub_add_cancel hm]
    · exact absurd (if_neg hcase) hn
  rw [← hinj.tsum_eq hsupp]
  have hsimp : ∀ k : ℕ,
      (if d ∣ d * (k + 1) ∧ 1 ≤ d * (k + 1) then s ^ (d * (k + 1)) else 0)
        = s ^ d * (s ^ d) ^ k := by
    intro k
    rw [if_pos ⟨Dvd.intro _ rfl,
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))⟩,
      ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [tsum_congr hsimp, tsum_mul_left, tsum_geometric_of_lt_one hsd0 hsd1,
    div_eq_mul_inv]

/-- The Lambert relation in the direction the boundary estimate uses: the
partial Lambert sums `∑_{d ≤ N} s^d/(1 - s^d)` are below `ℒ(s) = ∑ₙ τ(n) sⁿ`. -/
theorem divisorReal_partial_lower {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, s ^ (i + 1) / (1 - s ^ (i + 1)) ≤ divisorReal s := by
  classical
  set g : ℕ → ℕ → ℝ := fun d n => (if d ∣ n ∧ 1 ≤ n then s ^ n else 0) with hgdef
  have hgnn : ∀ d n, 0 ≤ g d n := by
    intro d n
    simp only [hgdef]
    by_cases h : d ∣ n ∧ 1 ≤ n
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  have hgle : ∀ d n, g d n ≤ s ^ n := by
    intro d n
    simp only [hgdef]
    by_cases h : d ∣ n ∧ 1 ≤ n
    · rw [if_pos h]
    · rw [if_neg h]; positivity
  have hgsummable : ∀ d ∈ Finset.range N, Summable (g (d + 1)) := by
    intro d _
    exact Summable.of_nonneg_of_le (fun n => hgnn _ n) (fun n => hgle _ n)
      (summable_geometric_of_lt_one hs0.le hs1)
  have hterm : ∀ n : ℕ, (∑ d ∈ Finset.range N, g (d + 1) n)
      ≤ (n.divisors.card : ℝ) * s ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz : ∀ d : ℕ, g d 0 = 0 := by
        intro d
        simp only [hgdef]
        rw [if_neg (by simp)]
      simp [hz]
    · have hfil : (∑ d ∈ Finset.range N, g (d + 1) n)
          = ∑ _d ∈ (Finset.range N).filter (fun d => (d + 1) ∣ n ∧ 1 ≤ n), s ^ n := by
        rw [Finset.sum_filter]
      rw [hfil, Finset.sum_const, nsmul_eq_mul]
      have hsub : ((Finset.range N).filter (fun d => (d + 1) ∣ n ∧ 1 ≤ n)).card
          ≤ n.divisors.card := by
        refine Finset.card_le_card_of_injOn (fun d => d + 1) ?_ ?_
        · intro d hd
          have hd' : d ∈ (Finset.range N).filter (fun d => (d + 1) ∣ n ∧ 1 ≤ n) := hd
          rw [Finset.mem_filter] at hd'
          have hmem : (d + 1) ∈ n.divisors :=
            Nat.mem_divisors.mpr ⟨hd'.2.1, by omega⟩
          exact hmem
        · intro a _ b _ hab
          have h' : a + 1 = b + 1 := hab
          omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) (by positivity)
  have hsumF : Summable (fun n : ℕ => ∑ d ∈ Finset.range N, g (d + 1) n) :=
    Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun d _ => hgnn _ n) hterm
      (divisorReal_summable hs0.le hs1)
  have hswap : ∑' n : ℕ, (∑ d ∈ Finset.range N, g (d + 1) n)
      = ∑ d ∈ Finset.range N, ∑' n : ℕ, g (d + 1) n :=
    Summable.tsum_finsetSum hgsummable
  have hblock : ∑ d ∈ Finset.range N, ∑' n : ℕ, g (d + 1) n
      = ∑ i ∈ Finset.range N, s ^ (i + 1) / (1 - s ^ (i + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro d _
    exact geom_block hs0 hs1 (by omega)
  calc ∑ i ∈ Finset.range N, s ^ (i + 1) / (1 - s ^ (i + 1))
      = ∑' n : ℕ, (∑ d ∈ Finset.range N, g (d + 1) n) := by rw [hswap, hblock]
    _ ≤ divisorReal s :=
        Summable.tsum_le_tsum hterm hsumF (divisorReal_summable hs0.le hs1)

/-- The Lambert form displayed in the paper: for real `0 < s < 1` the partial
sums `∑_{d ≤ N} s^d/(1 - s^d)` converge to `ℒ(s) = ∑ₙ τ(n) sⁿ`.  This is the
identity behind the paper's display `ℒ(z) = ∑_{n ≥ 1} zⁿ/(1 - zⁿ)`, and it is
why `divisorLambert` is the paper's `ℒ`. -/
theorem tendsto_lambert_partial {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, s ^ (i + 1) / (1 - s ^ (i + 1)))
      atTop (𝓝 (divisorReal s)) := by
  classical
  have hsum := divisorReal_summable hs0.le hs1
  have hlower : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), (n.divisors.card : ℝ) * s ^ n
      ≤ ∑ i ∈ Finset.range N, s ^ (i + 1) / (1 - s ^ (i + 1)) := by
    intro N
    set g : ℕ → ℕ → ℝ := fun d n => (if d ∣ n ∧ 1 ≤ n then s ^ n else 0) with hgdef
    have hgnn : ∀ d n, 0 ≤ g d n := by
      intro d n
      simp only [hgdef]
      by_cases h : d ∣ n ∧ 1 ≤ n
      · rw [if_pos h]; positivity
      · rw [if_neg h]
    have hgle : ∀ d n, g d n ≤ s ^ n := by
      intro d n
      simp only [hgdef]
      by_cases h : d ∣ n ∧ 1 ≤ n
      · rw [if_pos h]
      · rw [if_neg h]; positivity
    have hgsummable : ∀ d ∈ Finset.range N, Summable (g (d + 1)) := fun d _ =>
      Summable.of_nonneg_of_le (fun n => hgnn _ n) (fun n => hgle _ n)
        (summable_geometric_of_lt_one hs0.le hs1)
    have hzero : ∑ d ∈ Finset.range N, g (d + 1) 0 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro d _
      simp only [hgdef]
      rw [if_neg (by simp)]
    have hterm : ∀ n : ℕ, (∑ d ∈ Finset.range N, g (d + 1) n)
        ≤ (n.divisors.card : ℝ) * s ^ n := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hzero]; simp
      · have hfil : (∑ d ∈ Finset.range N, g (d + 1) n)
            = ∑ _d ∈ (Finset.range N).filter (fun d => (d + 1) ∣ n ∧ 1 ≤ n), s ^ n := by
          rw [Finset.sum_filter]
        rw [hfil, Finset.sum_const, nsmul_eq_mul]
        have hsub : ((Finset.range N).filter (fun d => (d + 1) ∣ n ∧ 1 ≤ n)).card
            ≤ n.divisors.card := by
          refine Finset.card_le_card_of_injOn (fun d => d + 1) ?_ ?_
          · intro d hd
            have hd' : d ∈ (Finset.range N).filter (fun d => (d + 1) ∣ n ∧ 1 ≤ n) := hd
            rw [Finset.mem_filter] at hd'
            have hmem : (d + 1) ∈ n.divisors := Nat.mem_divisors.mpr ⟨hd'.2.1, by omega⟩
            exact hmem
          · intro a _ b _ hab
            have h' : a + 1 = b + 1 := hab
            omega
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsub) (by positivity)
    have hFsummable : Summable (fun n : ℕ => ∑ d ∈ Finset.range N, g (d + 1) n) :=
      Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun d _ => hgnn _ n) hterm hsum
    have heq : ∀ n ∈ Finset.range (N + 1),
        (n.divisors.card : ℝ) * s ^ n = ∑ d ∈ Finset.range N, g (d + 1) n := by
      intro n hnr
      rw [Finset.mem_range] at hnr
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hzero]; simp
      · have hfil : (∑ d ∈ Finset.range N, g (d + 1) n)
            = ∑ _d ∈ (Finset.range N).filter (fun d => (d + 1) ∣ n ∧ 1 ≤ n), s ^ n := by
          rw [Finset.sum_filter]
        rw [hfil, Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.range N).filter (fun d => (d + 1) ∣ n ∧ 1 ≤ n)).card
            = n.divisors.card := by
          refine Finset.card_bij (fun d _ => d + 1) ?_ ?_ ?_
          · intro a ha
            rw [Finset.mem_filter] at ha
            exact Nat.mem_divisors.mpr ⟨ha.2.1, by omega⟩
          · intro a _ b _ hab
            have h' : a + 1 = b + 1 := hab
            omega
          · intro e he
            rw [Nat.mem_divisors] at he
            have he1 : 1 ≤ e := by
              rcases Nat.eq_zero_or_pos e with rfl | h
              · exact absurd (Nat.eq_zero_of_zero_dvd he.1) he.2
              · exact h
            have hen : e ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero he.2) he.1
            have hmemf : e - 1 ∈ (Finset.range N).filter (fun d => (d + 1) ∣ n ∧ 1 ≤ n) := by
              rw [Finset.mem_filter, Finset.mem_range]
              refine ⟨by omega, ?_, hn⟩
              rw [Nat.sub_add_cancel he1]
              exact he.1
            refine ⟨e - 1, hmemf, ?_⟩
            show e - 1 + 1 = e
            omega
        rw [hcard]
    calc ∑ n ∈ Finset.range (N + 1), (n.divisors.card : ℝ) * s ^ n
        = ∑ n ∈ Finset.range (N + 1), (∑ d ∈ Finset.range N, g (d + 1) n) :=
          Finset.sum_congr rfl heq
      _ ≤ ∑' n : ℕ, (∑ d ∈ Finset.range N, g (d + 1) n) :=
          hFsummable.sum_le_tsum _ (fun n _ => Finset.sum_nonneg fun d _ => hgnn _ n)
      _ = ∑ d ∈ Finset.range N, ∑' n : ℕ, g (d + 1) n :=
          Summable.tsum_finsetSum hgsummable
      _ = ∑ i ∈ Finset.range N, s ^ (i + 1) / (1 - s ^ (i + 1)) :=
          Finset.sum_congr rfl fun d _ => geom_block hs0 hs1 (by omega)
  have hps : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (n.divisors.card : ℝ) * s ^ n)
      atTop (𝓝 (divisorReal s)) := hsum.hasSum.tendsto_sum_nat
  have hps' : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (n.divisors.card : ℝ) * s ^ n)
      atTop (𝓝 (divisorReal s)) := hps.comp (tendsto_add_atTop_nat 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hps' tendsto_const_nhds hlower
    (fun N => divisorReal_partial_lower hs0 hs1 N)

/-- The lower bound behind `(x-1)F(x) → ∞`: for every `N`,
`(1-s)·ℒ(s) ≥ s^N · (1 + 1/2 + ⋯ + 1/N)`. -/
lemma divisorReal_lower {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ) :
    s ^ N * (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1)) ≤ (1 - s) * divisorReal s := by
  have hone : (0 : ℝ) < 1 - s := by linarith
  have hstep : ∀ i ∈ Finset.range N,
      s ^ N / ((i : ℝ) + 1) ≤ (1 - s) * (s ^ (i + 1) / (1 - s ^ (i + 1))) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hd1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hpowlt : s ^ (i + 1) < 1 := pow_lt_one₀ hs0.le hs1 (by omega)
    have hden : (0 : ℝ) < 1 - s ^ (i + 1) := by linarith
    have h1 : s ^ N ≤ s ^ (i + 1) := pow_le_pow_of_le_one hs0.le hs1.le (by omega)
    have h2 : 1 - s ^ (i + 1) ≤ ((i : ℝ) + 1) * (1 - s) := by
      have h := one_sub_pow_le hs0.le hs1.le (i + 1)
      push_cast at h
      linarith
    have hA : s ^ N * (1 - s ^ (i + 1)) ≤ s ^ (i + 1) * (((i : ℝ) + 1) * (1 - s)) :=
      mul_le_mul h1 h2 (by linarith) (by positivity)
    rw [mul_div_assoc', div_le_div_iff₀ hd1 hden]
    nlinarith [hA]
  calc s ^ N * (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1))
      = ∑ i ∈ Finset.range N, s ^ N / ((i : ℝ) + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range N, (1 - s) * (s ^ (i + 1) / (1 - s ^ (i + 1))) :=
        Finset.sum_le_sum hstep
    _ = (1 - s) * ∑ i ∈ Finset.range N, s ^ (i + 1) / (1 - s ^ (i + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ (1 - s) * divisorReal s :=
        mul_le_mul_of_nonneg_left (divisorReal_partial_lower hs0 hs1 N) hone.le

/-! ### The upper bound -/

private lemma tau_le_split (n A : ℕ) (hA : 1 ≤ A) :
    (n.divisors.card : ℝ) ≤ (A : ℝ) + (n : ℝ) / (A : ℝ) := by
  classical
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : (Nat.divisors 0).card = 0 := by simp
    rw [hz]
    push_cast
    positivity
  have hsplit : n.divisors.card
      = (n.divisors.filter (fun d => d ≤ A)).card
        + (n.divisors.filter (fun d => ¬ d ≤ A)).card :=
    (Finset.filter_card_add_filter_neg_card_eq_card _).symm
  have h1 : (n.divisors.filter (fun d => d ≤ A)).card ≤ A := by
    have hsub : n.divisors.filter (fun d => d ≤ A) ⊆ Finset.Icc 1 A := by
      intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hd.1.2 (Nat.eq_zero_of_zero_dvd hd.1.1)
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd0, hd.2⟩
    simpa using Finset.card_le_card hsub
  have h2 : (n.divisors.filter (fun d => ¬ d ≤ A)).card ≤ n / (A + 1) := by
    have hmaps : ∀ d ∈ n.divisors.filter (fun d => ¬ d ≤ A),
        n / d ∈ Finset.Icc 1 (n / (A + 1)) := by
      intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors, not_le] at hd
      obtain ⟨⟨hdvd, hn0⟩, hdA⟩ := hd
      have hd0 : 0 < d := by omega
      refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
      · exact (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd)
      · exact Nat.div_le_div_left hdA (by omega)
    have hinj : Set.InjOn (fun d => n / d)
        (n.divisors.filter (fun d => ¬ d ≤ A) : Finset ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Nat.mem_divisors] at ha hb
      have ea := Nat.div_div_self ha.1.1 ha.1.2
      have eb := Nat.div_div_self hb.1.1 hb.1.2
      simp only at hab
      rw [← ea, ← eb, hab]
    have hle := Finset.card_le_card_of_injOn _ hmaps hinj
    simpa using hle
  have hnat : n.divisors.card ≤ A + n / (A + 1) := by omega
  have hcast : (n.divisors.card : ℝ) ≤ (A : ℝ) + ((n / (A + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hdiv : ((n / (A + 1) : ℕ) : ℝ) ≤ (n : ℝ) / (A : ℝ) := by
    refine le_trans (Nat.cast_div_le (α := ℝ)) ?_
    push_cast
    rw [div_le_div_iff₀ (by positivity) hA0]
    nlinarith [Nat.cast_nonneg (α := ℝ) n, hA0]
  linarith

/-- The upper bound behind `(x-1)²F(x) → 0`: for every `A ≥ 1`,
`(1-s)²·ℒ(s) ≤ 1/A + A(1-s)`. -/
lemma divisorReal_upper {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (A : ℕ) (hA : 1 ≤ A) :
    (1 - s) ^ 2 * divisorReal s ≤ 1 / (A : ℝ) + (A : ℝ) * (1 - s) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hone : (0 : ℝ) < 1 - s := by linarith
  have hnorm : ‖s‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hs0]
  have hgeo : Summable fun n : ℕ => s ^ n := summable_geometric_of_lt_one hs0 hs1
  have hng : Summable fun n : ℕ => (n : ℝ) * s ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have hval : ∑' n : ℕ, ((A : ℝ) * s ^ n + (1 / (A : ℝ)) * ((n : ℝ) * s ^ n))
      = (A : ℝ) * (1 - s)⁻¹ + (1 / (A : ℝ)) * (s / (1 - s) ^ 2) := by
    rw [Summable.tsum_add (hgeo.mul_left _) (hng.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_lt_one hs0 hs1, tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  have hbound : divisorReal s
      ≤ (A : ℝ) * (1 - s)⁻¹ + (1 / (A : ℝ)) * (s / (1 - s) ^ 2) := by
    rw [← hval]
    refine Summable.tsum_le_tsum (fun n => ?_) (divisorReal_summable hs0 hs1)
      ((hgeo.mul_left _).add (hng.mul_left _))
    have h1 := tau_le_split n A hA
    have h2 : (A : ℝ) * s ^ n + (1 / (A : ℝ)) * ((n : ℝ) * s ^ n)
        = ((A : ℝ) + (n : ℝ) / (A : ℝ)) * s ^ n := by
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hstep : (1 - s) ^ 2 * divisorReal s
      ≤ (1 - s) ^ 2 * ((A : ℝ) * (1 - s)⁻¹ + (1 / (A : ℝ)) * (s / (1 - s) ^ 2)) :=
    mul_le_mul_of_nonneg_left hbound (by positivity)
  have hcalc : (1 - s) ^ 2 * ((A : ℝ) * (1 - s)⁻¹ + (1 / (A : ℝ)) * (s / (1 - s) ^ 2))
      = (A : ℝ) * (1 - s) + s / (A : ℝ) := by
    field_simp
  have hsA : s / (A : ℝ) ≤ 1 / (A : ℝ) := by
    rw [div_le_div_iff₀ hA0 hA0]
    nlinarith [hA0]
  rw [hcalc] at hstep
  linarith

/-! ### The two boundary limits -/

private lemma eventually_pos_lt : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 := by
  have h1 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr using hr
  have h2 : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h1, h2] with r hr1 hr2 using ⟨hr2, hr1⟩

/-- `(1-r)·ℒ(r^M) → ∞` as `r ↑ 1`: the paper's `(x-1)F(x) → ∞`. -/
theorem tendsto_one_sub_mul_divisorReal {M : ℕ} (hM : 1 ≤ M) :
    Tendsto (fun r : ℝ => (1 - r) * divisorReal (r ^ M)) (𝓝[<] (1 : ℝ)) atTop := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  refine tendsto_atTop.mpr fun K => ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      2 * (M : ℝ) * (|K| + 1) ≤ ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) := by
    obtain ⟨N, hN⟩ :=
      (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_ge_atTop
        (2 * (M : ℝ) * (|K| + 1))).exists
    exact ⟨N, hN⟩
  have hcont : Tendsto (fun r : ℝ => r ^ (M * N)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have h : Tendsto (fun r : ℝ => r ^ (M * N)) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) ^ (M * N))) :=
      (continuous_pow (M * N)).tendsto 1
    simpa using h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), (1 / 2 : ℝ) < r ^ (M * N) :=
    hcont (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [eventually_pos_lt, hev] with r hr hrN
  obtain ⟨hr0, hr1⟩ := hr
  set s : ℝ := r ^ M with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s < 1 := by rw [hs]; exact pow_lt_one₀ hr0.le hr1 (by omega)
  have hsN : s ^ N = r ^ (M * N) := by rw [hs, ← pow_mul]
  have hrN' : (1 / 2 : ℝ) < s ^ N := by rw [hsN]; exact hrN
  have hLnn : 0 ≤ divisorReal s := divisorReal_nonneg hs0.le
  have hkey : s ^ N * (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1))
      ≤ (1 - s) * divisorReal s := divisorReal_lower hs0 hs1 N
  have hMs : 1 - s ≤ (M : ℝ) * (1 - r) := by
    rw [hs]; exact one_sub_pow_le hr0.le hr1.le M
  have hA : (1 / 2 : ℝ) * (2 * (M : ℝ) * (|K| + 1))
      ≤ s ^ N * (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1)) :=
    mul_le_mul hrN'.le hN (by positivity) (by positivity)
  have hB : (M : ℝ) * (|K| + 1) ≤ (1 - s) * divisorReal s := by
    have h := le_trans hA hkey
    linarith [h]
  have hC : (1 - s) * divisorReal s ≤ (M : ℝ) * (1 - r) * divisorReal s := by
    have h := mul_le_mul_of_nonneg_right hMs hLnn
    linarith [h]
  have hD : (M : ℝ) * (|K| + 1) ≤ (M : ℝ) * ((1 - r) * divisorReal s) := by
    have h := le_trans hB hC
    rw [mul_assoc] at h
    exact h
  have hE : |K| + 1 ≤ (1 - r) * divisorReal s := le_of_mul_le_mul_left hD hM0
  linarith [le_abs_self K, hE]

/-- `(1-r)²·ℒ(r^M) → 0` as `r ↑ 1`: the paper's `(x-1)²F(x) → 0`. -/
theorem tendsto_one_sub_sq_mul_divisorReal {M : ℕ} (hM : 1 ≤ M) :
    Tendsto (fun r : ℝ => (1 - r) ^ 2 * divisorReal (r ^ M)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨A, hA⟩ := exists_nat_gt (max (2 / ε) 1)
  have hA1 : (1 : ℝ) < (A : ℝ) := lt_of_le_of_lt (le_max_right _ _) hA
  have hA1' : 1 ≤ A := by exact_mod_cast hA1.le
  have hA0 : (0 : ℝ) < (A : ℝ) := by linarith
  have hAe : 1 / (A : ℝ) < ε / 2 := by
    have h2 : 2 / ε < (A : ℝ) := lt_of_le_of_lt (le_max_left _ _) hA
    rw [div_lt_iff₀ hε] at h2
    rw [div_lt_div_iff₀ hA0 (by norm_num : (0 : ℝ) < 2)]
    linarith [h2, mul_comm (A : ℝ) ε]
  have htend : Tendsto (fun r : ℝ => (A : ℝ) * (M : ℝ) * (1 - r)) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => (A : ℝ) * (M : ℝ) * (1 - r)) (𝓝 (1 : ℝ))
        (𝓝 ((A : ℝ) * (M : ℝ) * (1 - 1))) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).tendsto 1
    simpa using h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), (A : ℝ) * (M : ℝ) * (1 - r) < ε / 2 :=
    htend (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  filter_upwards [eventually_pos_lt, hev] with r hr hrA
  obtain ⟨hr0, hr1⟩ := hr
  set s : ℝ := r ^ M with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s < 1 := by rw [hs]; exact pow_lt_one₀ hr0.le hr1 (by omega)
  have hsr : s ≤ r := by
    rw [hs]
    calc r ^ M ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le hM
      _ = r := pow_one r
  have hLnn : 0 ≤ divisorReal s := divisorReal_nonneg hs0.le
  have hup : (1 - s) ^ 2 * divisorReal s ≤ 1 / (A : ℝ) + (A : ℝ) * (1 - s) :=
    divisorReal_upper hs0.le hs1 A hA1'
  have hsq : (1 - r) ^ 2 ≤ (1 - s) ^ 2 := by nlinarith [hsr, hr1, hs1]
  have hMs : 1 - s ≤ (M : ℝ) * (1 - r) := by
    rw [hs]; exact one_sub_pow_le hr0.le hr1.le M
  have h1 : (1 - r) ^ 2 * divisorReal s ≤ (1 - s) ^ 2 * divisorReal s :=
    mul_le_mul_of_nonneg_right hsq hLnn
  have h2 : (A : ℝ) * (1 - s) ≤ (A : ℝ) * ((M : ℝ) * (1 - r)) :=
    mul_le_mul_of_nonneg_left hMs hA0.le
  have hchain : (1 - r) ^ 2 * divisorReal s
      ≤ 1 / (A : ℝ) + (A : ℝ) * (M : ℝ) * (1 - r) := by
    have hassoc : (A : ℝ) * ((M : ℝ) * (1 - r)) = (A : ℝ) * (M : ℝ) * (1 - r) := by ring
    linarith [h1, h2, hup, hassoc]
  have hnn : 0 ≤ (1 - r) ^ 2 * divisorReal s := mul_nonneg (sq_nonneg _) hLnn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-! ## Nonrationality -/

private lemma divisorLambert_coeff (n : ℤ) :
    divisorLambert.coeff n = if n < 0 then 0 else ((n.natAbs.divisors.card : ℚ)) := by
  have h1 : divisorLambert
      = (((PowerSeries.mk fun m => (m.divisors.card : ℚ)) : ℚ⟦X⟧) : ℚ⸨X⸩) := rfl
  rw [h1, PowerSeries.coeff_coe]
  by_cases h : n < 0 <;> simp [h]

/-- The coefficients of `z ↦ z^M` applied to `ℒ`, as real numbers. -/
private def csubs (M n : ℕ) : ℝ := if M ∣ n then (((n / M).divisors.card : ℝ)) else 0

private lemma csubs_nonneg (M n : ℕ) : 0 ≤ csubs M n := by
  simp only [csubs]
  by_cases h : M ∣ n
  · rw [if_pos h]; positivity
  · rw [if_neg h]

private lemma csubs_le (M n : ℕ) : csubs M n ≤ (n : ℝ) := by
  simp only [csubs]
  by_cases h : M ∣ n
  · simp only [if_pos h]
    refine le_trans (tau_le_self (n / M)) ?_
    exact_mod_cast Nat.div_le_self n M
  · simp only [if_neg h]
    positivity

private lemma subs_divisorLambert_coeff {M : ℕ} (hM : 1 ≤ M) (n : ℕ) :
    (((subs M divisorLambert).coeff (n : ℤ) : ℚ) : ℝ) = csubs M n := by
  rw [subs_coeff hM]
  simp only [csubs]
  by_cases h : M ∣ n
  · obtain ⟨t, rfl⟩ := h
    have hmz : (M : ℤ) ≠ 0 := by
      have : M ≠ 0 := by omega
      exact_mod_cast this
    have hZ : (M : ℤ) ∣ ((M * t : ℕ) : ℤ) := ⟨(t : ℤ), by push_cast; ring⟩
    have hq : ((M * t : ℕ) : ℤ) / (M : ℤ) = (t : ℤ) := by
      push_cast
      rw [Int.mul_ediv_cancel_left _ hmz]
    rw [if_pos hZ, if_pos ⟨t, rfl⟩, hq, divisorLambert_coeff,
      if_neg (not_lt.mpr (Int.natCast_nonneg t))]
    simp [Nat.mul_div_cancel_left t (show 0 < M by omega)]
  · have hZ : ¬ (M : ℤ) ∣ (n : ℤ) := fun hc => h (by exact_mod_cast hc)
    rw [if_neg hZ, if_neg h]
    simp

private lemma subs_divisorLambert_coeff_neg {M : ℕ} (hM : 1 ≤ M) {i : ℤ} (hi : i < 0) :
    (subs M divisorLambert).coeff i = 0 := by
  have hMZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
  rw [subs_coeff hM]
  by_cases h : (M : ℤ) ∣ i
  · rw [if_pos h, divisorLambert_coeff, if_pos (Int.ediv_neg_of_neg_of_pos hi hMZ)]
  · rw [if_neg h]

private lemma csubs_summable {M : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => csubs M n * r ^ n := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hgeo : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (csubs_nonneg M n) (by positivity)) (fun n => ?_) hgeo
  exact mul_le_mul_of_nonneg_right (csubs_le M n) (by positivity)

private lemma csubs_tsum {M : ℕ} (hM : 1 ≤ M) (r : ℝ) :
    ∑' n : ℕ, csubs M n * r ^ n = divisorReal (r ^ M) := by
  have hinj : Function.Injective (fun m : ℕ => M * m) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by omega) hab
  have hsupp : Function.support (fun n : ℕ => csubs M n * r ^ n)
      ⊆ Set.range (fun m : ℕ => M * m) := by
    intro n hn
    by_cases h : M ∣ n
    · obtain ⟨m, rfl⟩ := h
      exact ⟨m, rfl⟩
    · refine absurd ?_ hn
      simp only [Function.mem_support, not_not, csubs, if_neg h, zero_mul]
  rw [← hinj.tsum_eq hsupp]
  simp only [divisorReal]
  refine tsum_congr fun m => ?_
  simp only [csubs, if_pos (Dvd.intro m rfl),
    Nat.mul_div_cancel_left m (show 0 < M by omega)]
  rw [← pow_mul]

/-- The paper's functional nonrationality, in the variable `ℒ(z) = F(1/z)`: no
`z ↦ z^M` substitute of the divisor generating series is a rational function,
because `(1-r)ℒ(r^M) → ∞` and `(1-r)²ℒ(r^M) → 0`, which no rational function
does. -/
theorem divisorLambert_subs_not_rational {M : ℕ} (hM : 1 ≤ M) :
    subs M divisorLambert ∉ Set.range (algebraMap (RatFunc ℚ) ℚ⸨X⸩) := by
  haveI : (𝓝[<] (1 : ℝ)).NeBot := nhdsWithin_Iio_neBot le_rfl
  rintro ⟨R, hR⟩
  obtain ⟨P, Q, hQ0, hcop, hRQ⟩ :
      ∃ P Q : ℚ[X], Q ≠ 0 ∧ IsCoprime P Q ∧
        R * algebraMap ℚ[X] (RatFunc ℚ) Q = algebraMap ℚ[X] (RatFunc ℚ) P := by
    refine ⟨R.num, R.denom, R.denom_ne_zero, R.isCoprime_num_denom, ?_⟩
    have hden0 : algebraMap ℚ[X] (RatFunc ℚ) R.denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).2 R.denom_ne_zero
    rw [eq_comm, ← div_eq_iff hden0, eq_comm]
    exact (RatFunc.num_div_denom R).symm
  have hLaurent : subs M divisorLambert * algebraMap ℚ[X] ℚ⸨X⸩ Q
      = algebraMap ℚ[X] ℚ⸨X⸩ P := by
    have h := congrArg (algebraMap (RatFunc ℚ) ℚ⸨X⸩) hRQ
    rw [map_mul, hR, ← IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) ℚ⸨X⸩,
      ← IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) ℚ⸨X⸩] at h
    exact h
  set cq : ℕ → ℚ := fun n => (subs M divisorLambert).coeff (n : ℤ) with hcq
  have hps0 : subs M divisorLambert
      = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk cq) := by
    ext i
    have hco : (HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk cq)).coeff i
        = if i < 0 then 0 else cq i.natAbs := by
      have h1 : HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.mk cq)
          = (((PowerSeries.mk cq) : ℚ⟦X⟧) : ℚ⸨X⸩) := rfl
      rw [h1, PowerSeries.coeff_coe]
      by_cases h : i < 0 <;> simp [h]
    rw [hco]
    by_cases hi : i < 0
    · rw [if_pos hi, subs_divisorLambert_coeff_neg hM hi]
    · rw [if_neg hi]
      push_neg at hi
      lift i to ℕ using hi with jj
      simp [hcq]
  have hpsQ : (PowerSeries.mk cq) * (Q : ℚ⟦X⟧) = (P : ℚ⟦X⟧) := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
    rw [map_mul]
    have hQc : HahnSeries.ofPowerSeries ℤ ℚ (Q : ℚ⟦X⟧) = algebraMap ℚ[X] ℚ⸨X⸩ Q := rfl
    have hPc : HahnSeries.ofPowerSeries ℤ ℚ (P : ℚ⟦X⟧) = algebraMap ℚ[X] ℚ⸨X⸩ P := rfl
    rw [hQc, hPc, ← hps0]
    exact hLaurent
  have hconv : ∀ n : ℕ,
      ∑ ij ∈ Finset.antidiagonal n, cq ij.1 * Q.coeff ij.2 = P.coeff n := by
    intro n
    have h := congrArg (fun φ : ℚ⟦X⟧ => PowerSeries.coeff n φ) hpsQ
    simpa [PowerSeries.coeff_mul, Polynomial.coeff_coe] using h
  set Pr : ℝ[X] := P.map (algebraMap ℚ ℝ) with hPr
  set Qr : ℝ[X] := Q.map (algebraMap ℚ ℝ) with hQr
  have hQr0 : Qr ≠ 0 := by
    rw [hQr, Ne, Polynomial.map_eq_zero_iff (algebraMap ℚ ℝ).injective]
    exact hQ0
  have hcopr : IsCoprime Pr Qr := by
    have h := hcop.map (Polynomial.mapRingHom (algebraMap ℚ ℝ))
    simpa [hPr, hQr] using h
  have hPrc : ∀ n : ℕ, Pr.coeff n = ((P.coeff n : ℚ) : ℝ) := by
    intro n; rw [hPr, Polynomial.coeff_map]; rfl
  have hQrc : ∀ n : ℕ, Qr.coeff n = ((Q.coeff n : ℚ) : ℝ) := by
    intro n; rw [hQr, Polynomial.coeff_map]; rfl
  have hpolyeval : ∀ (S : ℝ[X]) (r : ℝ), ∑' n : ℕ, S.coeff n * r ^ n = S.eval r := by
    intro S r
    rw [tsum_eq_sum (s := Finset.range (S.natDegree + 1)) ?_, ← Polynomial.eval_eq_sum_range]
    intro bb hbb
    simp only [Finset.mem_range, not_lt] at hbb
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  have hpolysummable : ∀ (S : ℝ[X]) (r : ℝ), Summable fun n : ℕ => ‖S.coeff n * r ^ n‖ := by
    intro S r
    refine summable_of_ne_finset_zero (s := Finset.range (S.natDegree + 1)) ?_
    intro bb hbb
    simp only [Finset.mem_range, not_lt] at hbb
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, norm_zero]
  have hident : ∀ r : ℝ, 0 ≤ r → r < 1 → Qr.eval r * divisorReal (r ^ M) = Pr.eval r := by
    intro r hr0 hr1
    have hc : ∀ n : ℕ, ((cq n : ℚ) : ℝ) = csubs M n := fun n =>
      subs_divisorLambert_coeff hM n
    have hfnorm : Summable fun n : ℕ => ‖csubs M n * r ^ n‖ := by
      refine (csubs_summable (M := M) hr0 hr1).congr (fun n => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (csubs_nonneg M n) (by positivity))]
    have hcauchy := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (f := fun n : ℕ => csubs M n * r ^ n) (g := fun n : ℕ => Qr.coeff n * r ^ n)
      hfnorm (hpolysummable Qr r)
    rw [csubs_tsum hM r, hpolyeval Qr r] at hcauchy
    have hterm : ∀ n : ℕ,
        (∑ ij ∈ Finset.antidiagonal n,
          (csubs M ij.1 * r ^ ij.1) * (Qr.coeff ij.2 * r ^ ij.2))
          = Pr.coeff n * r ^ n := by
      intro n
      have hrw : ∀ ij ∈ Finset.antidiagonal n,
          (csubs M ij.1 * r ^ ij.1) * (Qr.coeff ij.2 * r ^ ij.2)
            = (csubs M ij.1 * Qr.coeff ij.2) * r ^ n := by
        intro ij hij
        rw [Finset.mem_antidiagonal] at hij
        rw [← hij, pow_add]
        ring
      rw [Finset.sum_congr rfl hrw, ← Finset.sum_mul]
      congr 1
      have hcast : ∑ ij ∈ Finset.antidiagonal n, csubs M ij.1 * Qr.coeff ij.2
          = ((∑ ij ∈ Finset.antidiagonal n, cq ij.1 * Q.coeff ij.2 : ℚ) : ℝ) := by
        push_cast
        exact Finset.sum_congr rfl fun ij _ => by rw [← hc, hQrc]
      rw [hcast, hconv n, ← hPrc]
    have hrhs : ∑' n : ℕ, (∑ ij ∈ Finset.antidiagonal n,
        (csubs M ij.1 * r ^ ij.1) * (Qr.coeff ij.2 * r ^ ij.2)) = Pr.eval r := by
      rw [tsum_congr hterm]
      exact hpolyeval Pr r
    rw [hrhs] at hcauchy
    rw [mul_comm]
    exact hcauchy
  have hL1 := tendsto_one_sub_mul_divisorReal hM
  have hL2 := tendsto_one_sub_sq_mul_divisorReal hM
  have hLtop : Tendsto (fun r : ℝ => divisorReal (r ^ M)) (𝓝[<] (1 : ℝ)) atTop := by
    refine tendsto_atTop_mono' _ ?_ hL1
    filter_upwards [eventually_pos_lt] with r hr
    obtain ⟨hr0, hr1⟩ := hr
    have hnn : 0 ≤ divisorReal (r ^ M) := divisorReal_nonneg (pow_nonneg hr0.le M)
    nlinarith [hnn, hr0, hr1]
  have hcontPoly : ∀ S : ℝ[X], Continuous fun r : ℝ => S.eval r := by
    intro S; fun_prop
  have hPtend : Tendsto (fun r : ℝ => Pr.eval r) (𝓝[<] (1 : ℝ)) (𝓝 (Pr.eval 1)) :=
    ((hcontPoly Pr).tendsto 1).mono_left nhdsWithin_le_nhds
  have hidev : (fun r : ℝ => Qr.eval r * divisorReal (r ^ M)) =ᶠ[𝓝[<] (1 : ℝ)]
      fun r : ℝ => Pr.eval r := by
    filter_upwards [eventually_pos_lt] with r hr
    exact hident r hr.1.le hr.2
  set b : ℕ := Qr.rootMultiplicity 1 with hbdef
  set Q1 : ℝ[X] := Qr /ₘ (Polynomial.X - Polynomial.C (1 : ℝ)) ^ b with hQ1def
  have hfac : (Polynomial.X - Polynomial.C (1 : ℝ)) ^ b * Q1 = Qr :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq Qr 1
  have hQ1ne : Q1.eval 1 ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 1 hQr0
  rcases Nat.lt_or_ge b 1 with hb0 | hb1
  · have hb0' : b = 0 := by omega
    have hQrQ1 : Qr = Q1 := by rw [← hfac, hb0']; simp
    have hQr1 : Qr.eval 1 ≠ 0 := by rw [hQrQ1]; exact hQ1ne
    have hQabs : (0 : ℝ) < |Qr.eval 1| := abs_pos.mpr hQr1
    have habsQ : Tendsto (fun r : ℝ => |Qr.eval r|) (𝓝[<] (1 : ℝ)) (𝓝 |Qr.eval 1|) :=
      (((hcontPoly Qr).tendsto 1).mono_left nhdsWithin_le_nhds).abs
    have hQhalf : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), |Qr.eval 1| / 2 < |Qr.eval r| :=
      habsQ (lt_mem_nhds (by linarith))
    have hbig : Tendsto (fun r : ℝ => |Pr.eval r|) (𝓝[<] (1 : ℝ)) atTop := by
      refine tendsto_atTop_mono' _ ?_
        (Tendsto.const_mul_atTop (show (0 : ℝ) < |Qr.eval 1| / 2 by linarith) hLtop)
      filter_upwards [eventually_pos_lt, hQhalf, hidev] with r hr hQ2 hid
      have hnn : 0 ≤ divisorReal (r ^ M) := divisorReal_nonneg (pow_nonneg hr.1.le M)
      calc |Qr.eval 1| / 2 * divisorReal (r ^ M)
          ≤ |Qr.eval r| * divisorReal (r ^ M) := mul_le_mul_of_nonneg_right hQ2.le hnn
        _ = |Qr.eval r * divisorReal (r ^ M)| := by rw [abs_mul, abs_of_nonneg hnn]
        _ = |Pr.eval r| := by rw [hid]
    exact not_tendsto_nhds_of_tendsto_atTop hbig _ hPtend.abs
  · have hdvd1 : (Polynomial.X - Polynomial.C (1 : ℝ)) ∣ Qr := by
      rw [← hfac]
      exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    have hPr1 : Pr.eval 1 ≠ 0 := by
      intro hzero
      have hdP : (Polynomial.X - Polynomial.C (1 : ℝ)) ∣ Pr :=
        Polynomial.dvd_iff_isRoot.mpr hzero
      exact Polynomial.not_isUnit_X_sub_C (1 : ℝ) (hcopr.isUnit_of_dvd' hdP hdvd1)
    rcases Nat.lt_or_ge b 2 with hb1' | hb2
    · have hbe : b = 1 := by omega
      have hQfac : Qr = (Polynomial.X - Polynomial.C (1 : ℝ)) * Q1 := by
        rw [← hfac, hbe, pow_one]
      have hQ1abs : (0 : ℝ) < |Q1.eval 1| := abs_pos.mpr hQ1ne
      have habs1 : Tendsto (fun r : ℝ => |Q1.eval r|) (𝓝[<] (1 : ℝ)) (𝓝 |Q1.eval 1|) :=
        (((hcontPoly Q1).tendsto 1).mono_left nhdsWithin_le_nhds).abs
      have hhalf : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), |Q1.eval 1| / 2 < |Q1.eval r| :=
        habs1 (lt_mem_nhds (by linarith))
      have hbig : Tendsto (fun r : ℝ => |Pr.eval r|) (𝓝[<] (1 : ℝ)) atTop := by
        refine tendsto_atTop_mono' _ ?_
          (Tendsto.const_mul_atTop (show (0 : ℝ) < |Q1.eval 1| / 2 by linarith) hL1)
        filter_upwards [eventually_pos_lt, hhalf, hidev] with r hr hQ2 hid
        obtain ⟨hr0, hr1⟩ := hr
        have hnn : 0 ≤ divisorReal (r ^ M) := divisorReal_nonneg (pow_nonneg hr0.le M)
        have hprod : 0 ≤ (1 - r) * divisorReal (r ^ M) := by nlinarith [hnn, hr1]
        calc |Q1.eval 1| / 2 * ((1 - r) * divisorReal (r ^ M))
            ≤ |Q1.eval r| * ((1 - r) * divisorReal (r ^ M)) :=
              mul_le_mul_of_nonneg_right hQ2.le hprod
          _ = |Pr.eval r| := by
              rw [← hid, hQfac]
              simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
                Polynomial.eval_C]
              rw [abs_mul, abs_mul, abs_of_nonneg hnn,
                abs_of_nonpos (by linarith : r - 1 ≤ 0)]
              ring
      exact not_tendsto_nhds_of_tendsto_atTop hbig _ hPtend.abs
    · obtain ⟨S, hS⟩ : (Polynomial.X - Polynomial.C (1 : ℝ)) ^ 2 ∣ Qr := by
        rw [← hfac]
        exact Dvd.dvd.mul_right (pow_dvd_pow _ hb2) _
      have hStend : Tendsto (fun r : ℝ => S.eval r) (𝓝[<] (1 : ℝ)) (𝓝 (S.eval 1)) :=
        ((hcontPoly S).tendsto 1).mono_left nhdsWithin_le_nhds
      have hzero : Tendsto (fun r : ℝ => Pr.eval r) (𝓝[<] (1 : ℝ)) (𝓝 (0 * S.eval 1)) := by
        refine Tendsto.congr' ?_ (hL2.mul hStend)
        filter_upwards [eventually_pos_lt, hidev] with r hr hid
        rw [← hid, hS]
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        ring
      rw [zero_mul] at hzero
      exact hPr1 (tendsto_nhds_unique hPtend hzero)

/-! ## The external theorem, and the proposition -/

private lemma two_three_indep : ∀ a b : ℕ, 2 ^ a = 3 ^ b → a = 0 ∧ b = 0 := by
  intro a b h
  have ha : a = 0 := by
    by_contra ha
    have hdvd : (2 : ℕ) ∣ 3 ^ b := by
      rw [← h]
      exact dvd_pow_self 2 ha
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
    omega
  subst ha
  refine ⟨rfl, ?_⟩
  simp only [pow_zero] at h
  exact (Nat.pow_eq_one.mp h.symm).resolve_left (by norm_num)

/-- The theorem of Adamczewski and Bell [Thm. 1.1, p. 6], as a hypothesis: for
multiplicatively independent `k, l ≥ 2`, a Laurent series over `ℚ` that is both
`k`-Mahler and `l`-Mahler is a rational function.  This is the only external
input; it is proved neither here nor in Mathlib. -/
def AdamczewskiBell : Prop :=
  ∀ k l : ℕ, 2 ≤ k → 2 ≤ l → (∀ a b : ℕ, k ^ a = l ^ b → a = 0 ∧ b = 0) →
    ∀ f : ℚ⸨X⸩, IsMahler k f → IsMahler l f →
      f ∈ Set.range (algebraMap (RatFunc ℚ) ℚ⸨X⸩)

/-- `long1049:res:nomahler`.  There is no finite-dimensional `ℚ(z)`-subspace of
`ℚ((z))` containing the divisor generating series `ℒ(z) = ∑_{n ≥ 1} zⁿ/(1 - zⁿ)`
and stable under both `z ↦ z²` and `z ↦ z³`.

Conditional on the cited theorem of Adamczewski and Bell, exactly as in the
paper's proof. -/
theorem no_finite_simultaneous_two_three_system (hAB : AdamczewskiBell) :
    ¬ ∃ V : Submodule (RatFunc ℚ) ℚ⸨X⸩,
        Module.Finite (RatFunc ℚ) V ∧
        divisorLambert ∈ V ∧
        (∀ f ∈ V, subs 2 f ∈ V) ∧ (∀ f ∈ V, subs 3 f ∈ V) := by
  rintro ⟨V, hVfin, hL, h2, h3⟩
  haveI := hVfin
  obtain ⟨j2, hj2⟩ := mahler_of_stable (k := 2) (by norm_num) V hL h2
  obtain ⟨j3, hj3⟩ := mahler_of_stable (k := 3) (by norm_num) V hL h3
  have hp2 : 1 ≤ 2 ^ j2 := Nat.one_le_pow _ _ (by norm_num)
  have hp3 : 1 ≤ 3 ^ j3 := Nat.one_le_pow _ _ (by norm_num)
  have hA : IsMahler 2 (subs (3 ^ j3) (subs (2 ^ j2) divisorLambert)) :=
    isMahler_subs (by norm_num) hp3 hj2
  have hB : IsMahler 3 (subs (2 ^ j2) (subs (3 ^ j3) divisorLambert)) :=
    isMahler_subs (by norm_num) hp2 hj3
  have heq : subs (3 ^ j3) (subs (2 ^ j2) divisorLambert)
      = subs (2 ^ j2) (subs (3 ^ j3) divisorLambert) := by
    rw [subs_comp hp3 hp2, subs_comp hp2 hp3, Nat.mul_comm]
  rw [heq] at hA
  have hrat := hAB 2 3 (by norm_num) (by norm_num) two_three_indep _ hA hB
  rw [subs_comp hp2 hp3] at hrat
  exact divisorLambert_subs_not_rational
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) hrat

end NoMahlerSystem

end ErdosProblems.Erdos1049.PaperCompleteR21

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.subs_comp
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.subs_algebraMap_poly
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.isMahler_subs
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.mahler_of_stable
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.divisorReal_partial_lower
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.tendsto_lambert_partial
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.divisorReal_lower
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.divisorReal_upper
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.tendsto_one_sub_mul_divisorReal
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.tendsto_one_sub_sq_mul_divisorReal
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.divisorLambert_subs_not_rational
#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.no_finite_simultaneous_two_three_system
