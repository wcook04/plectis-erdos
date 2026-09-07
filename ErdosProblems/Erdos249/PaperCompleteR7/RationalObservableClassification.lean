import ErdosProblems.Erdos249.ResidueClassTotientSeries
import Mathlib

/-!
# Rational-valued dyadic observables: the missing paper assembly

Targets: short-note `res:residueseries`; long-record
`thm:dyadic-classification`, and the sharpness clause of
`thm:residueobservable`.

`positiveValue` subtracts the n=0 contribution explicitly.  The integer
observable in the imported library includes n=0 and assumes f(0)=0;
confusing these conventions would give the wrong rational-value formula.

The proof clears finitely many rational denominators, invokes the existing
integer-observable theorem, and evaluates the eventually constant tail.
No new CRT, Dirichlet, or isolated-pulse hypothesis is assumed.
Build status: NOT RUN; all declarations below are complete proof candidates.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables

open scoped BigOperators

/-- Full n>=0 series minus its n=0 coefficient: the paper's n>=1 sum. -/
noncomputable def positiveValue (f : ℕ → ℚ) (m : ℕ) : ℝ :=
  (∑' n : ℕ, (f (Nat.totient n % m) : ℝ) / 2 ^ n) - (f 0 : ℝ)

/-- Finite rational data have a single positive natural multiplier making all
values integral. The real-cast formulation is used directly by the series proof. -/
theorem finite_common_denominator (f : ℕ → ℚ) (m : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, i < m → ∃ z : ℤ,
      (D : ℝ) * (f i : ℝ) = (z : ℝ) := by
  induction m with
  | zero =>
      exact ⟨1, by omega, fun i hi => by omega⟩
  | succ m ih =>
      obtain ⟨D, hD, hclear⟩ := ih
      let d := (f m).den
      have hd : 0 < d := (f m).den_pos
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have hnum : (d : ℝ) * (f m : ℝ) = ((f m).num : ℝ) := by
        rw [Rat.cast_def]
        change (d : ℝ) * (((f m).num : ℝ) / (d : ℝ)) = ((f m).num : ℝ)
        field_simp [hdR]
      refine ⟨D * d, Nat.mul_pos hD hd, ?_⟩
      intro i hi
      by_cases him : i = m
      · subst i
        refine ⟨(D : ℤ) * (f m).num, ?_⟩
        push_cast
        rw [mul_assoc, hnum]
      · have hil : i < m := by omega
        obtain ⟨z, hz⟩ := hclear i hil
        refine ⟨(d : ℤ) * z, ?_⟩
        push_cast
        calc
          (D : ℝ) * (d : ℝ) * (f i : ℝ)
              = (d : ℝ) * ((D : ℝ) * (f i : ℝ)) := by ring
          _ = (d : ℝ) * (z : ℝ) := by rw [hz]

/-- Every residue observable is bounded, hence its full binary series converges. -/
theorem summable_terms (f : ℕ → ℚ) {m : ℕ} (hm : 0 < m) :
    Summable (fun n : ℕ => (f (Nat.totient n % m) : ℝ) / 2 ^ n) := by
  let C : ℝ := ∑ i ∈ Finset.range m, |(f i : ℝ)|
  have hbound (n : ℕ) : |(f (Nat.totient n % m) : ℝ)| ≤ C := by
    exact Finset.single_le_sum (fun i _ => abs_nonneg (f i : ℝ))
      (Finset.mem_range.mpr (Nat.mod_lt _ hm))
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => C / 2 ^ n) (summable_const_div_two_pow C)
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
  exact div_le_div_of_nonneg_right (hbound n) (by positivity)

theorem positiveValue_eq_tsum_succ (f : ℕ → ℚ) {m : ℕ} (hm : 0 < m) :
    positiveValue f m =
      ∑' n : ℕ, (f (Nat.totient (n + 1) % m) : ℝ) / 2 ^ (n + 1) := by
  have h := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (f (Nat.totient n % m) : ℝ) / 2 ^ n) 1
    (summable_terms f hm)
  simp only [Finset.sum_range_one, Nat.totient_zero, Nat.zero_mod,
    pow_zero, div_one] at h
  unfold positiveValue
  linarith

/-- Affine scaling identity, with its n=0 and constant-series corrections. -/
theorem centred_integer_value_eq
    (f : ℕ → ℚ) {m D : ℕ} (hm : 0 < m) (g : ℕ → ℤ)
    (hg : ∀ r, r < m → (g r : ℝ) = (D : ℝ) * ((f r : ℝ) - (f 0 : ℝ))) :
    totientObservableValue g m =
      (D : ℝ) * (positiveValue f m - (f 0 : ℝ)) := by
  have hs := summable_terms f hm
  have hc := summable_const_div_two_pow (f 0 : ℝ)
  have hcval : (∑' n : ℕ, (f 0 : ℝ) / 2 ^ n) = 2 * (f 0 : ℝ) := by
    calc
      (∑' n : ℕ, (f 0 : ℝ) / 2 ^ n)
          = ∑' n : ℕ, (2 * (f 0 : ℝ)) / 2 / 2 ^ n :=
              tsum_congr (fun n => by ring)
      _ = 2 * (f 0 : ℝ) := tsum_geometric_two' _
  unfold totientObservableValue positiveValue
  calc
    (∑' n : ℕ, (g (Nat.totient n % m) : ℝ) / 2 ^ n)
        = ∑' n : ℕ, (D : ℝ) *
            ((f (Nat.totient n % m) : ℝ) / 2 ^ n - (f 0 : ℝ) / 2 ^ n) := by
              apply tsum_congr
              intro n
              rw [hg _ (Nat.mod_lt _ hm)]
              ring
    _ = (D : ℝ) * (∑' n : ℕ,
          ((f (Nat.totient n % m) : ℝ) / 2 ^ n - (f 0 : ℝ) / 2 ^ n)) :=
            tsum_mul_left
    _ = (D : ℝ) * ((∑' n : ℕ,
          (f (Nat.totient n % m) : ℝ) / 2 ^ n) - 2 * (f 0 : ℝ)) := by
            rw [hs.tsum_sub hc, hcval]
    _ = _ := by ring

/-- Rational coefficients and a nonzero constant offset introduce no extra
hypothesis into the unit-residue irrationality theorem. -/
theorem irrational_positiveValue_of_unit
    {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℚ)
    {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m)
    (hfr : f r ≠ f 0) : Irrational (positiveValue f m) := by
  classical
  obtain ⟨D, hD, hclear⟩ := finite_common_denominator (fun i => f i - f 0) m
  let g : ℕ → ℤ := fun i =>
    if hi : i < m then Classical.choose (hclear i hi) else 0
  have hg (i : ℕ) (hi : i < m) :
      (g i : ℝ) = (D : ℝ) * ((f i : ℝ) - (f 0 : ℝ)) := by
    dsimp [g]
    rw [dif_pos hi]
    simpa only [Rat.cast_sub] using (Classical.choose_spec (hclear i hi)).symm
  have hg0 : g 0 = 0 := by
    apply Int.cast_injective (α := ℝ)
    simpa only [sub_self, mul_zero, Int.cast_zero] using hg 0 (by omega)
  have hgr : g r ≠ 0 := by
    intro hzero
    have hz := hg r hr
    rw [hzero, Int.cast_zero] at hz
    have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have heq : (f r : ℝ) = (f 0 : ℝ) := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz.symm).resolve_left hDR)
    exact hfr (Rat.cast_injective heq)
  have hirr := irrational_totientObservable hm g hg0 hr hcop hgr
  have hvalue := centred_integer_value_eq f (by omega : 0 < m) g hg
  intro hrational
  obtain ⟨q, hq⟩ := hrational
  apply hirr
  refine ⟨(D : ℚ) * (q - f 0), ?_⟩
  rw [hvalue, ← hq]
  push_cast <;> rfl

theorem two_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- The unit condition is automatic for an even dyadic residue. -/
theorem irrational_positiveValue_of_even
    {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℚ)
    {r : ℕ} (hr : r < 2 ^ k) (heven : r % 2 = 0)
    (hfr : f r ≠ f 0) : Irrational (positiveValue f (2 ^ k)) := by
  have h2 : Nat.Coprime 2 (r + 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  exact irrational_positiveValue_of_unit (two_le_two_pow hk) f hr
    (Nat.Coprime.pow_right k h2.symm) hfr

/-- All n>=3 have an even totient residue at a positive dyadic resolution. -/
theorem totient_mod_two_pow_even {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 3 ≤ n) :
    (Nat.totient n % 2 ^ k) % 2 = 0 := by
  have hd : 2 ∣ 2 ^ k := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj, pow_succ]
    exact dvd_mul_left 2 (2 ^ j)
  rw [Nat.mod_mod_of_dvd _ hd]
  exact Nat.mod_eq_zero_of_dvd ((even_iff_two_dvd).mp (Nat.totient_even (by omega)))

/-- The rational-value formula, including both exceptional indices 1 and 2. -/
theorem positiveValue_eq_of_even_constant
    {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℚ) (c : ℚ)
    (hc : ∀ r, r < 2 ^ k → r % 2 = 0 → f r = c) :
    positiveValue f (2 ^ k) = ((3 * f 1 / 4 + c / 4 : ℚ) : ℝ) := by
  have hm : 0 < 2 ^ k := by positivity
  have hm2 := two_le_two_pow hk
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (f (Nat.totient n % 2 ^ k) : ℝ) / 2 ^ n) 3
    (summable_terms f hm)
  have htail : (∑' n : ℕ,
      (f (Nat.totient (n + 3) % 2 ^ k) : ℝ) / 2 ^ (n + 3)) = (c : ℝ) / 4 := by
    calc
      (∑' n : ℕ, (f (Nat.totient (n + 3) % 2 ^ k) : ℝ) / 2 ^ (n + 3))
          = ∑' n : ℕ, ((c : ℝ) / 4) / 2 ^ (n + 1) := by
              apply tsum_congr
              intro n
              rw [hc _ (Nat.mod_lt _ hm) (totient_mod_two_pow_even hk (by omega))]
              rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
              norm_num <;> ring
      _ = (c : ℝ) / 4 := tsum_const_div_two_pow_succ _
  have hprefix : (∑ n ∈ Finset.range 3,
      (f (Nat.totient n % 2 ^ k) : ℝ) / 2 ^ n) =
      (f 0 : ℝ) + (f 1 : ℝ) / 2 + (f 1 : ℝ) / 4 := by
    norm_num [Finset.sum_range_succ, show Nat.totient 2 = 1 by decide,
      Nat.mod_eq_of_lt (show 1 < 2 ^ k by omega)]
  rw [htail, hprefix] at hsplit
  unfold positiveValue
  push_cast
  linarith

/-- COMPLETE dyadic classification, in finite-residue representative coordinates.
The constant may equivalently be written f(0). -/
theorem rational_dyadic_observable_iff
    {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℚ) :
    (∃ q : ℚ, positiveValue f (2 ^ k) = (q : ℝ)) ↔
      ∀ r, r < 2 ^ k → r % 2 = 0 → f r = f 0 := by
  constructor
  · rintro ⟨q, hq⟩ r hr heven
    by_contra hne
    exact (irrational_positiveValue_of_even hk f hr heven hne).ne_rat q hq
  · intro hc
    exact ⟨3 * f 1 / 4 + f 0 / 4,
      positiveValue_eq_of_even_constant hk f (f 0) hc⟩

/-- Exact ZMod-domain formulation of the displayed paper theorem. -/
theorem rational_zmod_observable_iff
    {k : ℕ} (hk : 1 ≤ k) (f : ZMod (2 ^ k) → ℚ) :
    (∃ q : ℚ,
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        2 ^ (n + 1)) = (q : ℝ)) ↔
      ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0 := by
  have h := rational_dyadic_observable_iff hk
    (fun r : ℕ => f (r : ZMod (2 ^ k)))
  have heq := positiveValue_eq_tsum_succ
    (fun r : ℕ => f (r : ZMod (2 ^ k))) (by positivity : 0 < 2 ^ k)
  rw [heq] at h
  simpa only [ZMod.natCast_mod, Nat.cast_zero] using h

/-- The value formula in the same literal ZMod coordinates. -/
theorem zmod_observable_value
    {k : ℕ} (hk : 1 ≤ k) (f : ZMod (2 ^ k) → ℚ) (c : ℚ)
    (hc : ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = c) :
    (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
      2 ^ (n + 1)) = ((3 * f 1 / 4 + c / 4 : ℚ) : ℝ) := by
  have h := positiveValue_eq_of_even_constant hk
    (fun r : ℕ => f (r : ZMod (2 ^ k))) c hc
  rw [positiveValue_eq_tsum_succ _ (by positivity : 0 < 2 ^ k)] at h
  simpa only [ZMod.natCast_mod, Nat.cast_one] using h

/-- Bridge to the original least-residue value (whose n=0 summand is zero). -/
theorem positiveValue_natCast (m : ℕ) :
    positiveValue (fun r : ℕ => (r : ℚ)) m = totientResidueValue m := by
  unfold positiveValue totientResidueValue
  simp only [Nat.cast_zero, Rat.cast_zero, sub_zero, Rat.cast_natCast]

@[simp] theorem totientResidueValue_one : totientResidueValue 1 = 0 := by
  have h : ∀ n : ℕ, ((Nat.totient n % 1 : ℕ) : ℝ) / 2 ^ n = 0 := by
    intro n
    rw [Nat.mod_one, Nat.cast_zero, zero_div]
  unfold totientResidueValue
  exact (tsum_congr h).trans tsum_zero

@[simp] theorem totientResidueValue_two : totientResidueValue 2 = 3 / 4 := by
  have h := positiveValue_eq_of_even_constant (k := 1) (by omega)
    (fun r : ℕ => (r : ℚ)) 0 (by
      intro r hr heven
      have : r = 0 := by norm_num at hr; omega
      simp [this])
  norm_num [positiveValue_natCast] at h
  exact h

/-- The entire numerical sharpness part of long-record thm:residueobservable. -/
theorem residue_series_sharp_range :
    (∀ m : ℕ, 3 ≤ m → Irrational (totientResidueValue m)) ∧
    totientResidueValue 1 = 0 ∧ totientResidueValue 2 = 3 / 4 := by
  exact ⟨fun _ hm => residue_series_irrational hm,
    totientResidueValue_one, totientResidueValue_two⟩

/-- One end-to-end assembly for short-note res:residueseries. -/
theorem short_note_residue_theorem :
    (∀ m : ℕ, 3 ≤ m → Irrational (totientResidueValue m)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : ZMod (2 ^ k) → ℚ,
      ((∃ q : ℚ,
        (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
          2 ^ (n + 1)) = (q : ℝ)) ↔
        ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : ZMod (2 ^ k) → ℚ, ∀ c : ℚ,
      (∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = c) →
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        2 ^ (n + 1)) = ((3 * f 1 / 4 + c / 4 : ℚ) : ℝ)) := by
  exact ⟨fun _ hm => residue_series_irrational hm,
    fun _ hk f => rational_zmod_observable_iff hk f,
    fun _ hk f c hc => zmod_observable_value hk f c hc⟩

end ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables
