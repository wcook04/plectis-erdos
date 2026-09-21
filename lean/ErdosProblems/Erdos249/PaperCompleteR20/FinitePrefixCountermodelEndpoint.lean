import ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel
import ErdosProblems.Erdos249.PaperCompleteR20.DyadicMersenneDenominator

namespace ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel
open Erdos249257
open scoped BigOperators

def dyadicBase (B : ℕ) : ℚ :=
  2 - ∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℚ) / 2 ^ n

def value (B P : ℕ) : ℚ := dyadicBase B - 1 / ((2 ^ P - 1 : ℕ) : ℚ)

theorem dyadicBase_den (B : ℕ) : (dyadicBase B).den ∣ 2 ^ B := by
  have hs : (∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℚ) / 2 ^ n).den ∣ 2 ^ B := by
    apply Finset.sum_induction (fun n : ℕ => ((n - Nat.totient n : ℕ) : ℚ) / 2 ^ n)
      (fun q : ℚ => q.den ∣ 2 ^ B)
    · intro a b ha hb
      exact (Rat.add_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)
    · simp
    · intro n hn
      have hnB : n ≤ B := by simpa using hn
      have hdiv : (((n - Nat.totient n : ℕ) : ℚ) / 2 ^ n).den ∣ 2 ^ n := by
        have hh := Rat.den_dvd ((n - Nat.totient n : ℕ) : ℤ) ((2 : ℤ) ^ n)
        rw [Rat.divInt_eq_div] at hh
        simp only [Int.cast_natCast, Int.cast_pow, Int.cast_ofNat] at hh
        apply Int.natCast_dvd_natCast.mp
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh
      exact hdiv.trans (pow_dvd_pow 2 hnB)
  exact (Rat.sub_den_dvd_lcm 2 _).trans (Nat.lcm_dvd (by simp) hs)

theorem value_cast (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = (value B P : ℝ) := by
  have hpow : 1 ≤ (2 : ℕ) ^ P := Nat.one_le_pow _ _ (by norm_num)
  simp only [value, dyadicBase, Rat.cast_sub, Rat.cast_ofNat, Rat.cast_sum,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Nat.cast_sub hpow, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one]
  simpa using exact_series B P hBP

theorem exact_denominator (B P : ℕ) (hBP : B < P) :
    ∃ e ≤ B, (value B P).den = 2 ^ e * (2 ^ P - 1) := by
  have hP : 0 < P := by omega
  have hm : 0 < 2 ^ P - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hP.ne')
  have hcop : Nat.Coprime (2 ^ P - 1) 2 := by
    apply Nat.coprime_two_right.mpr
    have he : 2 ^ P = 2 ^ (P - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hp : 1 ≤ (2 : ℕ) ^ (P - 1) := Nat.one_le_pow _ _ (by norm_num)
    refine ⟨2 ^ (P - 1) - 1, ?_⟩
    omega
  exact dyadic_sub_reciprocal_denominator (dyadicBase B) B (2 ^ P - 1) hm hcop (dyadicBase_den B)

theorem no_certificate_after_prefix (B P : ℕ) (hBP : B < P) :
    ∀ N : ℕ, B ≤ N → ∀ L : ℕ, ¬ GenericTailCertificates.certificate (gamma B P) P N L := by
  obtain ⟨e, he, hden⟩ := exact_denominator B P hBP
  intro N hN L hcert
  have hP : 0 < P := by omega
  have hm : 0 < 2 ^ P - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hP.ne')
  have hv : binaryCoeffSeries (gamma B P) =
      ((value B P).num : ℝ) / ((2 : ℝ) ^ e * ((2 ^ P - 1 : ℕ) : ℝ)) := by
    rw [value_cast B P hBP, Rat.cast_def, hden]
    push_cast
    rfl
  have ht := GenericTailCertificates.generic_tail_period (gamma B P) (gamma_le B P)
    (value B P).num e (2 ^ P - 1) P N hm (by omega) (dvd_refl _) hv
  exact GenericTailCertificates.certificate_sound (gamma B P) (gamma_le B P) P N L hcert ht

def separation (c : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, GenericTailCertificates.certificate c h N L

theorem gamma_not_separation (B P : ℕ) (hBP : B < P) : ¬ separation (gamma B P) := by
  intro hs
  obtain ⟨N, hN, L, hL⟩ := hs P (by omega) B
  exact no_certificate_after_prefix B P hBP N hN L hL

theorem no_uniform_prefix_rule (B : ℕ) :
    ¬ (∀ c : ℕ → ℕ, (∀ n, c n ≤ n) → (∀ n, n ≤ B → c n = Nat.totient n) → separation c) := by
  intro hrule
  exact gamma_not_separation B (B + 1) (by omega)
    (hrule (gamma B (B + 1)) (gamma_le B (B + 1)) (gamma_prefix B (B + 1)))

end ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.dyadicBase_den
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.value_cast
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_denominator
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_certificate_after_prefix
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_not_separation
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_uniform_prefix_rule
