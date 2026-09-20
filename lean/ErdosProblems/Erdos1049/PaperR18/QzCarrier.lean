import Mathlib
import ErdosProblems.Erdos1049.PaperR16.MahlerBoundary

/-!
# A literal Q(z)-module and nontrivial denominator clearing

NEW CANDIDATE: UNRUN. No elaboration or axiom receipt is asserted.

`Carrier` is the localization, by the nonzero rational polynomials, of the
ring of all complex-valued functions on the open unit disc. Equality is the
actual localization equivalence, not an assumed Mahler equation. The functions
in the Lambert orbit are the literal functions in PaperR16.

This deliberately larger carrier allows a particularly direct transport:
a zero localization class supplies a nonzero polynomial annihilator. Retaining
that annihilator in every coefficient gives an identity at EVERY disc point,
including denominator zeros. No cancellation at a pole and no hidden analytic
continuation premise occur in this Lean route. Its injection on holomorphic
functions, and the separate all-meromorphic-germs theorem, are proved in the
ordinary mathematical report; they are not additional Lean claims here.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ErdosProblems.Erdos1049.PaperR18

open PaperR16

abbrev QPoly := Polynomial ℚ
abbrev Qz := FractionRing QPoly
abbrev Denominators := nonZeroDivisors QPoly
abbrev Disc := {z : ℂ // ‖z‖ < 1}
abbrev DiscFunction := Disc → ℂ

/-- Evaluation is pointwise, using the canonical rational-to-complex map. -/
def polyAction : QPoly →+* DiscFunction where
  toFun p z := Polynomial.aeval z.1 p
  map_one' := by funext z; simp
  map_mul' p q := by funext z; simp
  map_zero' := by funext z; simp
  map_add' p q := by funext z; simp

instance discFunctionAlgebra : Algebra QPoly DiscFunction := polyAction.toAlgebra

@[simp] theorem polynomial_smul_apply (p : QPoly) (f : DiscFunction) (z : Disc) :
    (p • f) z = Polynomial.aeval z.1 p * f z := rfl

/-- The scalar field is genuinely Frac(Q[X]), i.e. Q(z). -/
abbrev Carrier := LocalizedModule Denominators DiscFunction

local instance (priority := 2000) carrierQzModule : Module Qz Carrier :=
  LocalizedModule.moduleOfIsLocalization

/-- The literal function-to-localization map; not asserted injective on ALL functions. -/
abbrev embed : DiscFunction →ₗ[QPoly] Carrier :=
  LocalizedModule.mkLinearMap Denominators DiscFunction

@[simp] theorem embed_as_fraction (f : DiscFunction) :
    embed f = LocalizedModule.mk f (1 : Denominators) := rfl

theorem denominator_ne_zero (s : Denominators) : (s : QPoly) ≠ 0 :=
  mem_nonZeroDivisors_iff_ne_zero.mp s.2

theorem denominator_cast_ne_zero (s : Denominators) :
    algebraMap QPoly Qz (s : QPoly) ≠ 0 := by
  intro h
  apply denominator_ne_zero s
  exact IsFractionRing.injective QPoly Qz (by simpa using h)

/-- A cast rational-polynomial scalar agrees with the original module action. -/
theorem cast_smul_embed (p : QPoly) (f : DiscFunction) :
    (algebraMap QPoly Qz p) • embed f = embed (p • f) := by
  simpa only [embed_as_fraction, Localization.mk_eq_mk', IsLocalization.mk'_one,
    one_mul] using (LocalizedModule.mk_smul_mk p f
      (1 : Denominators) (1 : Denominators))

/-- The quotient's defining equality. This records exactly what zero means. -/
theorem embed_eq_zero_iff (f : DiscFunction) :
    embed f = 0 ↔ ∃ s : Denominators, (s : QPoly) • f = 0 := by
  constructor
  · intro h
    have h' : LocalizedModule.mk f (1 : Denominators) =
        LocalizedModule.mk (0 : DiscFunction) (1 : Denominators) := by
      simpa only [embed_as_fraction, LocalizedModule.zero_mk] using h
    obtain ⟨s, hs⟩ := LocalizedModule.mk_eq.mp h'
    exact ⟨s, by simpa only [one_smul, smul_zero, Submonoid.smul_def] using hs⟩
  · rintro ⟨s, hs⟩
    have h' : LocalizedModule.mk f (1 : Denominators) =
        LocalizedModule.mk (0 : DiscFunction) (1 : Denominators) := by
      apply LocalizedModule.mk_eq.mpr
      exact ⟨s, by simpa only [one_smul, smul_zero, Submonoid.smul_def] using hs⟩
    simpa only [embed_as_fraction, LocalizedModule.zero_mk] using h'

/-- Clearing a finite scalar family. Nontriviality is checked in the field,
not by evaluating the common denominator at a possibly singular point. -/
theorem finite_scalar_denominators {ι : Type*} [Fintype ι] (a : ι → Qz) :
    ∃ s : Denominators, ∃ p : ι → QPoly,
      (∀ i, algebraMap QPoly Qz (p i) =
        algebraMap QPoly Qz (s : QPoly) * a i) ∧
      (∀ i, a i ≠ 0 → p i ≠ 0) := by
  classical
  choose r hr using (fun i : ι => IsLocalization.surj Denominators (a i))
  let q : ι → Denominators := fun i => (r i).2
  let s : Denominators := ∏ i, q i
  let o : ι → QPoly := fun i => ∏ j ∈ (Finset.univ : Finset ι).erase i, (q j : QPoly)
  let p : ι → QPoly := fun i => o i * (r i).1
  have hprod (i : ι) : o i * (q i : QPoly) = (s : QPoly) := by
    have hp := Finset.mul_prod_erase (Finset.univ : Finset ι)
      (fun j => (q j : QPoly)) (Finset.mem_univ i)
    simpa [o, s, mul_comm] using hp
  have hc (i : ι) : algebraMap QPoly Qz (p i) =
      algebraMap QPoly Qz (s : QPoly) * a i := by
    have hi : a i * algebraMap QPoly Qz (q i : QPoly) =
        algebraMap QPoly Qz (r i).1 := hr i
    calc
      algebraMap QPoly Qz (p i) =
          algebraMap QPoly Qz (o i) * algebraMap QPoly Qz (r i).1 := by
        exact map_mul _ _ _
      _ = algebraMap QPoly Qz (o i) *
          (a i * algebraMap QPoly Qz (q i : QPoly)) := by rw [hi]
      _ = (algebraMap QPoly Qz (o i) *
          algebraMap QPoly Qz (q i : QPoly)) * a i := by ring
      _ = algebraMap QPoly Qz (s : QPoly) * a i := by
        rw [← map_mul, hprod]
  refine ⟨s, p, hc, ?_⟩
  intro i hai hpi
  have hz : algebraMap QPoly Qz (s : QPoly) * a i = 0 := by
    rw [← hc i, hpi, map_zero]
  exact (mul_ne_zero (denominator_cast_ne_zero s) hai) hz

/-- The substantive transport lemma: a nonzero Q(z) relation in the concrete
carrier produces nonzero Q[X] coefficients and a pointwise identity on the
ENTIRE open disc. The extra polynomial annihilator is part of the output. -/
theorem localized_relation_to_pointwise {ι : Type*} [Fintype ι]
    (f : ι → DiscFunction) (a : ι → Qz)
    (hrel : ∑ i, a i • embed (f i) = 0) (hne : ∃ i, a i ≠ 0) :
    ∃ p : ι → QPoly, (∃ i, p i ≠ 0) ∧
      ∀ z : Disc, ∑ i, Polynomial.aeval z.1 (p i) * f i z = 0 := by
  classical
  obtain ⟨s, p, hp, hpne⟩ := finite_scalar_denominators a
  have hcleared : embed (∑ i, p i • f i) = 0 := by
    calc
      embed (∑ i, p i • f i) = ∑ i, embed (p i • f i) := map_sum _ _ _
      _ = ∑ i, (algebraMap QPoly Qz (p i)) • embed (f i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (cast_smul_embed (p i) (f i)).symm
      _ = (algebraMap QPoly Qz (s : QPoly)) •
          (∑ i, a i • embed (f i)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hp i, mul_smul]
      _ = 0 := by rw [hrel, smul_zero]
  obtain ⟨t, ht⟩ := (embed_eq_zero_iff _).mp hcleared
  refine ⟨fun i => (t : QPoly) * p i, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hne
    exact ⟨i, mul_ne_zero (denominator_ne_zero t) (hpne i hi)⟩
  · intro z
    have hz := congrFun ht z
    simpa only [Finset.smul_sum, ← mul_smul, Finset.sum_apply,
      polynomial_smul_apply, Pi.zero_apply, map_mul, Finset.mul_sum, mul_assoc] using hz

/-- Rational polynomials are transported injectively to the G07 coefficient field. -/
def complexify (p : QPoly) : ℂ[X] := p.map (algebraMap ℚ ℂ)

theorem complexify_injective : Function.Injective complexify :=
  Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective

@[simp] theorem complexify_eval (p : QPoly) (z : ℂ) :
    (complexify p).eval z = Polynomial.aeval z p := by
  simp only [complexify, Polynomial.eval_map, Polynomial.aeval_def]

theorem complexify_ne_zero {p : QPoly} (hp : p ≠ 0) : complexify p ≠ 0 := by
  intro h
  apply hp
  apply complexify_injective
  simpa only [complexify, Polynomial.map_zero] using h

/-- The exact Lambert source, with PaperR16's harmless zero summand convention. -/
def lambertFunction : DiscFunction := fun z => lambert z.1

def iterateFunction (k i : ℕ) : DiscFunction :=
  fun z => lambert (z.1 ^ (k ^ i))

def lambertVector : Carrier := embed lambertFunction

def orbit (k i : ℕ) : Carrier := embed (iterateFunction k i)

@[simp] theorem orbit_zero (k : ℕ) : orbit k 0 = lambertVector := by
  apply congrArg embed
  funext z
  simp [iterateFunction, lambertFunction]

end ErdosProblems.Erdos1049.PaperR18
