import Erdos249257.GreedyAchievementSet
import Erdos249257.MersenneLambertLadder

/-!
# The Möbius-sign support does not hit one half

The signed Lambert identity

`sum mu(d) / (2^d - 1) = 1/2`

is an exact baseline for Erdős #257, but discarding its negative signs is not
a Boolean solution.  If `N` is the set of indices `d >= 2` with `mu(d) = -1`
and `P` the set with `mu(d) = 1`, then absolute convergence permits sign
separation and gives

`sum_{d in N} 1/(2^d-1) = 1/2 + sum_{d in P} 1/(2^d-1)`.

In particular the negative-Möbius support overshoots by at least the first
positive tail term, at `d = 6`, namely `1/63`.  This is a route-sufficiency
no-go only: it does not decide whether some other infinite Boolean support
sums to `1/2`.
-/

namespace Erdos249257
namespace MobiusSignSupportNoGo

open ArithmeticFunction

/-- The positive Möbius tail, with the exceptional `d = 1` term removed. -/
noncomputable def positiveMobiusTailTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = 1 ∧ (d : ℕ) ≠ 1 then mersenneWeight (d : ℕ) else 0

/-- The Boolean support term selected by the negative Möbius sign. -/
noncomputable def negativeMobiusTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = -1 then mersenneWeight (d : ℕ) else 0

/-- The single `d = 1` term in the signed Möbius Lambert series. -/
noncomputable def mobiusOneTerm (d : ℕ+) : ℝ :=
  if (d : ℕ) = 1 then mersenneWeight (d : ℕ) else 0

private theorem summable_mersenneWeight_pnat :
    Summable (fun d : ℕ+ => mersenneWeight (d : ℕ)) := by
  rw [summable_pnat_iff_summable_succ]
  simpa using summable_mersenneWeight

theorem summable_positiveMobiusTailTerm :
    Summable positiveMobiusTailTerm := by
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    summable_mersenneWeight_pnat
  · simp only [positiveMobiusTailTerm]
    split_ifs
    · exact (mersenneWeight_pos d.pos).le
    · exact le_rfl
  · simp only [positiveMobiusTailTerm]
    split_ifs
    · exact le_rfl
    · exact (mersenneWeight_pos d.pos).le

theorem summable_negativeMobiusTerm :
    Summable negativeMobiusTerm := by
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    summable_mersenneWeight_pnat
  · simp only [negativeMobiusTerm]
    split_ifs
    · exact (mersenneWeight_pos d.pos).le
    · exact le_rfl
  · simp only [negativeMobiusTerm]
    split_ifs
    · exact le_rfl
    · exact (mersenneWeight_pos d.pos).le

theorem summable_mobiusOneTerm : Summable mobiusOneTerm := by
  refine summable_of_ne_finset_zero (s := {(1 : ℕ+)}) (fun d hd => ?_)
  have hd1 : (d : ℕ) ≠ 1 := by
    intro hcoe
    apply hd
    simp only [Finset.mem_singleton]
    exact PNat.coe_injective hcoe
  simp [mobiusOneTerm, hd1]

/-- Pointwise sign separation of the signed Möbius term. -/
theorem mobius_mersenne_term_eq (d : ℕ+) :
    ((moebius (d : ℕ) : ℤ) : ℝ) * mersenneWeight (d : ℕ) =
      mobiusOneTerm d + positiveMobiusTailTerm d - negativeMobiusTerm d := by
  rcases moebius_eq_or (d : ℕ) with hzero | hone | hneg
  · have hd1 : (d : ℕ) ≠ 1 := by
      intro hd
      rw [hd, moebius_apply_one] at hzero
      omega
    simp [mobiusOneTerm, positiveMobiusTailTerm, negativeMobiusTerm, hzero, hd1]
  · by_cases hd1 : (d : ℕ) = 1
    · simp [mobiusOneTerm, positiveMobiusTailTerm, negativeMobiusTerm, hd1]
    · simp [mobiusOneTerm, positiveMobiusTailTerm, negativeMobiusTerm, hone, hd1]
  · have hd1 : (d : ℕ) ≠ 1 := by
      intro hd
      rw [hd, moebius_apply_one] at hneg
      omega
    simp [mobiusOneTerm, positiveMobiusTailTerm, negativeMobiusTerm, hneg, hd1]

theorem tsum_mobiusOneTerm : ∑' d : ℕ+, mobiusOneTerm d = 1 := by
  rw [tsum_eq_single (1 : ℕ+) (fun d hd => ?_)]
  · norm_num [mobiusOneTerm, mersenneWeight]
  · have hd1 : (d : ℕ) ≠ 1 := by
      intro hcoe
      apply hd
      exact PNat.coe_injective hcoe
    simp [mobiusOneTerm, hd1]

/-- Exact sign-separation identity.  The negative-Möbius Boolean support
overshoots `1/2` by the complete positive-Möbius tail. -/
theorem tsum_negativeMobius_eq_half_add_positiveMobiusTail :
    (∑' d : ℕ+, negativeMobiusTerm d) =
      1 / 2 + ∑' d : ℕ+, positiveMobiusTailTerm d := by
  have hLambert := MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half
  have hSigned :
      (∑' d : ℕ+,
        ((moebius (d : ℕ) : ℤ) : ℝ) * mersenneWeight (d : ℕ)) = 1 / 2 := by
    simpa [mersenneWeight, mul_one_div] using hLambert
  have hSep :
      (∑' d : ℕ+,
        ((moebius (d : ℕ) : ℤ) : ℝ) * mersenneWeight (d : ℕ)) =
        (∑' d : ℕ+, mobiusOneTerm d) +
          (∑' d : ℕ+, positiveMobiusTailTerm d) -
            ∑' d : ℕ+, negativeMobiusTerm d := by
    calc
      (∑' d : ℕ+,
          ((moebius (d : ℕ) : ℤ) : ℝ) * mersenneWeight (d : ℕ)) =
          (∑' d : ℕ+,
            ((mobiusOneTerm d + positiveMobiusTailTerm d) - negativeMobiusTerm d)) :=
        tsum_congr mobius_mersenne_term_eq
      _ = (∑' d : ℕ+, (mobiusOneTerm d + positiveMobiusTailTerm d)) -
            (∑' d : ℕ+, negativeMobiusTerm d) :=
        (summable_mobiusOneTerm.add summable_positiveMobiusTailTerm).tsum_sub
          summable_negativeMobiusTerm
      _ = (∑' d : ℕ+, mobiusOneTerm d) +
            (∑' d : ℕ+, positiveMobiusTailTerm d) -
              ∑' d : ℕ+, negativeMobiusTerm d := by
        rw [summable_mobiusOneTerm.tsum_add summable_positiveMobiusTailTerm]
  rw [hSigned, tsum_mobiusOneTerm] at hSep
  linarith

private theorem moebius_six : moebius 6 = 1 := by
  calc
    moebius 6 = moebius 2 * moebius 3 := by
      simpa using isMultiplicative_moebius.map_mul_of_coprime (by norm_num : Nat.Coprime 2 3)
    _ = 1 := by rw [moebius_apply_prime (by norm_num), moebius_apply_prime (by norm_num)]
                norm_num

/-- Quantitative no-go: sign truncation overshoots by at least `1/63`. -/
theorem half_add_one_div_sixty_three_le_tsum_negativeMobius :
    (1 : ℝ) / 2 + 1 / 63 ≤ ∑' d : ℕ+, negativeMobiusTerm d := by
  rw [tsum_negativeMobius_eq_half_add_positiveMobiusTail]
  gcongr
  have hterm : positiveMobiusTailTerm (⟨6, by norm_num⟩ : ℕ+) = (1 : ℝ) / 63 := by
    norm_num [positiveMobiusTailTerm, moebius_six, mersenneWeight]
  rw [← hterm]
  exact summable_positiveMobiusTailTerm.le_tsum (⟨6, by norm_num⟩)
    (fun d _ => by
      simp only [positiveMobiusTailTerm]
      split_ifs
      · exact (mersenneWeight_pos d.pos).le
      · exact le_rfl)

theorem half_lt_tsum_negativeMobius :
    (1 : ℝ) / 2 < ∑' d : ℕ+, negativeMobiusTerm d := by
  have h := half_add_one_div_sixty_three_le_tsum_negativeMobius
  norm_num at h ⊢
  linarith

-- This module records a no-go for one sign-truncation route only.
#print axioms tsum_negativeMobius_eq_half_add_positiveMobiusTail
#print axioms half_add_one_div_sixty_three_le_tsum_negativeMobius
#print axioms half_lt_tsum_negativeMobius

end MobiusSignSupportNoGo
end Erdos249257
