import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace ErdosProblems.Erdos249.PaperCompleteR20

/-- Subtracting the reciprocal of a coprime odd denominator preserves that
entire denominator; only the dyadic part can cancel. -/
theorem dyadic_sub_reciprocal_denominator (q : ℚ) (B M : ℕ)
    (hm : 0 < M) (hcop : Nat.Coprime M 2) (hq : q.den ∣ 2 ^ B) :
    ∃ e ≤ B, (q - 1 / (M : ℚ)).den = 2 ^ e * M := by
  have hrec : (1 / (M : ℚ)).den = M := by simp [hm.ne']
  have hupper : (q - 1 / (M : ℚ)).den ∣ 2 ^ B * M := by
    have hh := Rat.sub_den_dvd q (1 / (M : ℚ))
    rw [hrec] at hh
    exact hh.trans (Nat.mul_dvd_mul_right hq M)
  have hback := Rat.sub_den_dvd q (q - 1 / (M : ℚ))
  rw [sub_sub_cancel, hrec] at hback
  have hMd : M ∣ (q - 1 / (M : ℚ)).den :=
    ((hcop.pow_right B).dvd_mul_left).mp
      (hback.trans (Nat.mul_dvd_mul_right hq _))
  obtain ⟨d, hd⟩ := hMd
  have hddiv : d ∣ 2 ^ B := by
    obtain ⟨k, hk⟩ := hupper
    refine ⟨k, Nat.eq_of_mul_eq_mul_left hm ?_⟩
    rw [hd] at hk
    nlinarith [hk]
  obtain ⟨e, he, hde⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hddiv
  exact ⟨e, he, by rw [hd, hde, mul_comm]⟩

end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.dyadic_sub_reciprocal_denominator
