import ErdosProblems.Erdos68.PaperCompleteExisting
import ErdosProblems.Erdos68.DivisorChannelBasis

/-!
# The p=2 support mismatch in long-record res:translator

The long record fixes coefficient support n≥2 before stating the translator
for every prime p. At p=2 its prescribed coefficient c_(p-1)=p is c_1=2.
The identities on the auxiliary domain are valid; admissibility is not.
This is the ONE labelled correction returned: require p≥3 in res:translator,
or explicitly change the coefficient domain for that theorem.

These proof scripts are uncompiled in this return. No claim of a compiled
no-go is made; the exact arithmetic contradiction is independently transparent.
-/
namespace ErdosProblems.Erdos68.PaperComplete

/-- No supported coefficient vector can carry the prescribed p=2 coefficient. -/
theorem translator_two_support_no_go :
    ¬ ∃ c : ℕ →₀ ℤ,
      (∀ n ∈ c.support, 2 ≤ n) ∧ c ((2 : ℕ) - 1) = (2 : ℤ) := by
  rintro ⟨c, hsupp, hc⟩
  have hc1 : c 1 = 2 := by simpa using hc
  have hmem : 1 ∈ c.support := Finsupp.mem_support_iff.mpr (by omega)
  have := hsupp 1 hmem
  omega

/-- This is an actual prime counterexample to the omitted support hypothesis. -/
theorem translator_two_is_prime_counterexample :
    Nat.Prime 2 ∧
    ¬ (∀ j : Fin 2, 2 ≤ _root_.Erdos68.primeTranslatorIndex 2 j) := by
  constructor
  · norm_num
  · intro h
    have := h 0
    norm_num [_root_.Erdos68.primeTranslatorIndex] at this

/-- Corrected support statement, with the sufficient hypothesis p≥3 exposed. -/
theorem prime_translator_admissible {p : ℕ} (hp : 3 ≤ p) :
    ∀ j : Fin 2, 2 ≤ _root_.Erdos68.primeTranslatorIndex p j := by
  intro j
  fin_cases j <;> simp [_root_.Erdos68.primeTranslatorIndex] <;> omega

/-- Corrected complete translator environment. -/
theorem admissible_prime_channel_corrector {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∀ j : Fin 2, 2 ≤ _root_.Erdos68.primeTranslatorIndex p j) ∧
    _root_.Erdos68.factorialMoment (_root_.Erdos68.primeTranslatorCoeff p)
      (_root_.Erdos68.primeTranslatorIndex p) = 0 ∧
    _root_.Erdos68.channelNumerator (_root_.Erdos68.primeTranslatorCoeff p)
      (_root_.Erdos68.primeTranslatorIndex p) p = (p.factorial : ℤ) - 1 ∧
    (∀ d : ℕ, 2 ≤ d → d ≠ p →
      _root_.Erdos68.channelNumerator (_root_.Erdos68.primeTranslatorCoeff p)
        (_root_.Erdos68.primeTranslatorIndex p) d = 0) :=
  ⟨prime_translator_admissible hp3, prime_channel_corrector hp⟩

end ErdosProblems.Erdos68.PaperComplete
