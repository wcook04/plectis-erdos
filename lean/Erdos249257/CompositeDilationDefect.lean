import Erdos249257.SupportDilationDifferences
import Erdos249257.SupportSunflowerDichotomy
import Mathlib.Tactic

/-!
# Composite dilation defects

For a support coefficient `f_A(n) = #{d ∈ A : d ∣ n}`, dilation by a
composite support element can create divisors other than the distinguished
element itself.  This file isolates that exact finite defect.  It does not
assert a correlation estimate or any bounded-`Ω` irrationality theorem.
-/

namespace Erdos249257.CompositeDilationDefect

open Erdos249257.SupportSunflowerDichotomy
open Erdos249257.SupportSunflowerDichotomy.OrthogonalPetalBouquet

/-- Support divisors created by multiplication by `a`, excluding the
distinguished divisor `a` itself. -/
noncomputable def compositeDilationDefect (A : Set ℕ) (a x : ℕ) : ℕ :=
  by
    classical
    exact ((a * x).divisors.filter fun d =>
      d ∈ A ∧ ¬ d ∣ x ∧ d ≠ a).card

/-- Exact composite replacement for the prime-dilation identity.  The new
support divisors split into the distinguished member `a` (when it was not
already present at `x`) and the composite dilation defect. -/
theorem supportCoeff_mul_eq_add_defect
    (A : Set ℕ) {a x : ℕ} (ha : a ∈ A) (ha0 : 0 < a) (hx0 : 0 < x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x := by
  classical
  let all := (a * x).divisors.filter fun d => d ∈ A
  let old := all.filter fun d => d ∣ x
  let new := all.filter fun d => ¬ d ∣ x
  have hmul0 : a * x ≠ 0 := Nat.mul_ne_zero ha0.ne' hx0.ne'
  have hold : old = x.divisors.filter fun d => d ∈ A := by
    ext d
    simp only [old, all, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hdax, -⟩, hdA⟩, hdx⟩
      exact ⟨⟨hdx, hx0.ne'⟩, hdA⟩
    · rintro ⟨⟨hdx, -⟩, hdA⟩
      exact ⟨⟨⟨hdx.trans (dvd_mul_left x a), hmul0⟩, hdA⟩, hdx⟩
  have hall : all.card = old.card + new.card := by
    simpa [old, new] using
      (Finset.card_filter_add_card_filter_not
        (s := all) (fun d : ℕ => d ∣ x)).symm
  have hnew : new.card = (if a ∣ x then 0 else 1) +
      compositeDilationDefect A a x := by
    have hsplit :=
      Finset.card_filter_add_card_filter_not
        (s := new) (fun d : ℕ => d = a)
    have ha_mem_all : a ∈ all := by
      simp [all, Nat.mem_divisors, ha, hmul0]
    have hdistinguished :
        (new.filter fun d => d = a).card = if a ∣ x then 0 else 1 := by
      by_cases hax : a ∣ x
      · rw [if_pos hax, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff]
        intro d hdnew hda
        have hndx : ¬ d ∣ x := (Finset.mem_filter.mp hdnew).2
        exact hndx (hda ▸ hax)
      · rw [if_neg hax]
        have heq : new.filter (fun d => d = a) = {a} := by
          ext d
          constructor
          · intro hd
            have hda : d = a := (Finset.mem_filter.mp hd).2
            simp [hda]
          · intro hd
            have hda : d = a := by simpa using hd
            subst d
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_filter.mpr ⟨ha_mem_all, hax⟩, rfl⟩
        rw [heq]
        simp
    have hrest :
        (new.filter fun d => ¬ d = a).card =
          compositeDilationDefect A a x := by
      have heq : new.filter (fun d => ¬ d = a) =
          (a * x).divisors.filter (fun d =>
            d ∈ A ∧ ¬ d ∣ x ∧ d ≠ a) := by
        ext d
        simp only [new, all, Finset.mem_filter]
        tauto
      rw [heq]
      rfl
    rw [hdistinguished, hrest] at hsplit
    omega
  rw [supportCoeff_eq_card_filter A (a * x),
    supportCoeff_eq_card_filter A x]
  change all.card = _
  rw [hall, hold, hnew]
  omega

/-- On a support consisting only of primes, no composite dilation defect can
survive.  Thus the composite identity specializes exactly to the familiar
prime-support formula. -/
theorem compositeDilationDefect_eq_zero_of_prime_support
    (A : Set ℕ) {p x : ℕ} (hp : p.Prime)
    (hAprime : ∀ d ∈ A, d.Prime) :
    compositeDilationDefect A p x = 0 := by
  classical
  rw [compositeDilationDefect, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro d hd hbad
  rcases hbad with ⟨hdA, hndx, hdne⟩
  have hdp := hAprime d hdA
  have hdpx : d ∣ p * x := Nat.dvd_of_mem_divisors hd
  rcases hdp.dvd_mul.mp hdpx with hdp' | hdx
  · exact hdne ((Nat.prime_dvd_prime_iff_eq hdp hp).mp hdp')
  · exact hndx hdx

/-- Prime-support specialization of `supportCoeff_mul_eq_add_defect`. -/
theorem supportCoeff_mul_prime_support
    (A : Set ℕ) {p x : ℕ} (hp : p.Prime) (hpA : p ∈ A)
    (hx0 : 0 < x) (hAprime : ∀ d ∈ A, d.Prime) :
    supportCoeff A (p * x) =
      supportCoeff A x + (if p ∣ x then 0 else 1) := by
  rw [supportCoeff_mul_eq_add_defect A hpA hp.pos hx0,
    compositeDilationDefect_eq_zero_of_prime_support A hp hAprime,
    Nat.add_zero]

/-- Every individual bouquet defect is a local signed cost.  It is either an
exceptional finite-core channel, or it comes from a unique foreign ray whose
petal already divides the undilated argument.  This is the pointwise engine
behind the bound by `exceptional.card + supportCoeff (Set.range petal) x`;
it makes no appeal to lower-rank irrationality. -/
theorem mem_compositeDilationDefect_bouquet_imp_exceptional_or_petal_dvd
    {A : Set ℕ} (hB : OrthogonalPetalBouquet A) (i x d : ℕ)
    (hdiv : d ∣ hB.ray i * x) (hdA : d ∈ A) (hdne : d ≠ hB.ray i) :
    d ∈ hB.exceptional ∨
      ∃ j : ℕ, j ≠ i ∧ d = hB.ray j ∧ hB.petal j ∣ x := by
  rw [hB.support_eq] at hdA
  rcases hdA with hdE | ⟨j, hj⟩
  · exact Or.inl (by simpa using hdE)
  · subst d
    have hji : j ≠ i := by
      intro hji
      subst j
      exact hdne rfl
    exact Or.inr ⟨j, hji, rfl, hB.petal_dvd_of_ray_dvd hji hdiv⟩

/-- Cardinal form of the local bouquet defect budget.  Exceptional channels
cost at most the finite frame cardinality.  Every remaining defect injects,
via its unique ray index, into a petal divisor of `x`. -/
theorem compositeDilationDefect_le_exceptional_add_petalCoeff
    {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (i x : ℕ) (hx : 0 < x) :
    compositeDilationDefect A (hB.ray i) x ≤
      hB.exceptional.card + supportCoeff (Set.range hB.petal) x := by
  classical
  rw [compositeDilationDefect,
    supportCoeff_eq_card_filter (Set.range hB.petal) x]
  let D := ((hB.ray i * x).divisors.filter fun d =>
    d ∈ A ∧ ¬ d ∣ x ∧ d ≠ hB.ray i)
  let P := x.divisors.filter fun p => p ∈ Set.range hB.petal
  change D.card ≤ hB.exceptional.card + P.card
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := D) (fun d : ℕ => d ∈ hB.exceptional)
  rw [← hsplit]
  apply Nat.add_le_add
  · apply Finset.card_le_card
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  · let f : ℕ → ℕ := fun d => hB.petal (hB.rayIndex d)
    have hrange : ∀ d ∈ D.filter (fun d => ¬ d ∈ hB.exceptional),
        d ∈ Set.range hB.ray := by
      intro d hd
      have hdD : d ∈ ((hB.ray i * x).divisors.filter fun e =>
          e ∈ A ∧ ¬ e ∣ x ∧ e ≠ hB.ray i) := by
        simpa [D] using (Finset.mem_filter.mp hd).1
      have hdnot : d ∉ hB.exceptional := (Finset.mem_filter.mp hd).2
      have hdparts := Finset.mem_filter.mp hdD
      rcases mem_compositeDilationDefect_bouquet_imp_exceptional_or_petal_dvd
          hB i x d (Nat.dvd_of_mem_divisors hdparts.1) hdparts.2.1
            hdparts.2.2.2 with hdE | ⟨j, _hji, hdj, _⟩
      · exact False.elim (hdnot hdE)
      · exact ⟨j, hdj.symm⟩
    have hmaps : ∀ d ∈ D.filter (fun d => ¬ d ∈ hB.exceptional),
        f d ∈ P := by
      intro d hd
      have hdD : d ∈ ((hB.ray i * x).divisors.filter fun e =>
          e ∈ A ∧ ¬ e ∣ x ∧ e ≠ hB.ray i) := by
        simpa [D] using (Finset.mem_filter.mp hd).1
      have hddiv : d ∣ hB.ray i * x :=
        Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdD).1
      have hri : hB.ray (hB.rayIndex d) = d :=
        hB.ray_rayIndex_eq (hrange d hd)
      have hidx : hB.rayIndex d ≠ i := by
        intro hidx
        rw [hidx] at hri
        exact (Finset.mem_filter.mp hdD).2.2.2 hri.symm
      have hpdiv : hB.petal (hB.rayIndex d) ∣ x :=
        hB.petal_dvd_of_ray_dvd hidx (by rw [hri]; exact hddiv)
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hpdiv, hx.ne'⟩,
          ⟨hB.rayIndex d, rfl⟩⟩
    have hinj : Set.InjOn f ↑(D.filter fun d => ¬ d ∈ hB.exceptional) := by
      intro d₁ hd₁ d₂ hd₂ heq
      have hd₁' := Finset.mem_coe.mp hd₁
      have hd₂' := Finset.mem_coe.mp hd₂
      have hidx : hB.rayIndex d₁ = hB.rayIndex d₂ :=
        hB.petal_injective heq
      calc
        d₁ = hB.ray (hB.rayIndex d₁) :=
          (hB.ray_rayIndex_eq (hrange d₁ hd₁')).symm
        _ = hB.ray (hB.rayIndex d₂) := by rw [hidx]
        _ = d₂ := hB.ray_rayIndex_eq (hrange d₂ hd₂')
    exact Finset.card_le_card_of_injOn f hmaps hinj

/-- The smallest composite-defect witness: multiplying by `6` creates both
the distinguished support member `6` and the lower-rank support divisor `2`.-/
theorem compositeDilationDefect_two_six_fixture :
    compositeDilationDefect ({2, 6} : Set ℕ) 6 1 = 1 := by
  norm_num [compositeDilationDefect]
  decide

/-- The exact identity on the same fixture records the extra defect term. -/
theorem supportCoeff_mul_eq_add_defect_two_six_fixture :
    supportCoeff ({2, 6} : Set ℕ) (6 * 1) =
      supportCoeff ({2, 6} : Set ℕ) 1 + 1 +
        compositeDilationDefect ({2, 6} : Set ℕ) 6 1 := by
  apply supportCoeff_mul_eq_add_defect
  · simp
  · norm_num
  · norm_num

#print axioms supportCoeff_mul_eq_add_defect
#print axioms compositeDilationDefect_eq_zero_of_prime_support
#print axioms supportCoeff_mul_prime_support
#print axioms mem_compositeDilationDefect_bouquet_imp_exceptional_or_petal_dvd
#print axioms compositeDilationDefect_le_exceptional_add_petalCoeff
#print axioms compositeDilationDefect_two_six_fixture
#print axioms supportCoeff_mul_eq_add_defect_two_six_fixture

end Erdos249257.CompositeDilationDefect
