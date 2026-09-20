import Erdos249257.TotientFixedRankLcmAsymptotic
import Erdos249257.TotientTailCarryPeriod

/-! Paper-form restatements of three long-paper environments:

* `prop:FR-01` — a strictly extremal middle totient value forces the
  three-rank second difference to be nonzero, with the sign determined;
* `prop:CP-06` — a directed (non-strict, asymmetric) certificate depth exists
  if and only if the tail difference is not an integer, with the `H₃ = 6`,
  `L = 6` example where the directed test fires and the symmetric one does not
  until depth `7`;
* `prop:CP-07` — cofinal mod-four pulse primes with a finite survivor kill on
  the `2 mod 4` candidate class imply irrationality.

Here `R_N = totientTail N`, `D(h,N,L) = windowDiscrepancy h N L`,
`H(t) = periodLcm t` and `c_{h,N,z} = carryOrbit h N z`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.TotientFixedRankLcmAsymptotic

/-! ### `prop:FR-01` — a sufficient extremal-order condition -/

/-- **If `φ(2H+j) < min{φ(H+j), φ(3H+j)}` then
`φ(3H+j) - 2φ(2H+j) + φ(H+j) > 0`.** -/
theorem extremal_order_curvature_pos {H j : ℕ} (hH : 1 ≤ H)
    (hmin : Nat.totient (2 * H + j) < min (Nat.totient (H + j)) (Nat.totient (3 * H + j))) :
    0 < (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) := by
  obtain ⟨hleft, hright⟩ := lt_min_iff.mp hmin
  simpa [fixedRankSecondDifference] using
    fixedRankSecondDifference_pos_of_middle_strict_min hleft hright

/-- **If the middle value is strictly larger than both outer values, the
second difference is negative.** -/
theorem extremal_order_curvature_neg {H j : ℕ} (hH : 1 ≤ H)
    (hleft : Nat.totient (H + j) < Nat.totient (2 * H + j))
    (hright : Nat.totient (3 * H + j) < Nat.totient (2 * H + j)) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) < 0 := by
  simpa [fixedRankSecondDifference] using
    fixedRankSecondDifference_neg_of_middle_strict_max hleft hright

/-- The same statement in the tree's `MiddleRankTotientExtremal` form: either
strict ordering gives a nonvanishing second difference. -/
theorem extremal_order_curvature_ne_zero {H j : ℕ} (hH : 1 ≤ H)
    (hextremal : MiddleRankTotientExtremal H j) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) ≠ 0 := by
  rcases hextremal with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · have := extremal_order_curvature_pos (H := H) (j := j) hH (lt_min_iff.mpr ⟨hl, hr⟩)
    omega
  · have := extremal_order_curvature_neg (H := H) (j := j) hH hl hr
    omega

/-! ### `prop:CP-06` — a directed certificate condition -/

/-- **A depth `L` with
`N+L+2 ≤ D(h,N,L) mod 2^L ≤ 2^L - (N+h+L+2)` exists if and only if
`R_{N+h} - R_N ∉ ℤ`.**  The endpoint inequalities are non-strict. -/
theorem directed_certificate_iff (h N : ℕ) :
    (∃ L : ℕ,
        ((N : ℤ) + L + 2) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
          windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
            (2 : ℤ) ^ L - ((N : ℤ) + h + L + 2)) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) :=
  exists_directedCertifiedKill_iff_tail_diff_notMem_int h N

/-- The worked example at `H₃ = 6`, `L = 6`: `D(6,6,6) = 270` has residue `14`
modulo `64`, the directed interval `[14,44]` succeeds at its lower endpoint,
the symmetric interval `(20,44)` fails, and the symmetric test first fires at
depth `7`. -/
theorem directed_certificate_example :
    periodLcm 3 = 6 ∧
      windowDiscrepancy 6 6 6 = 270 ∧
      windowDiscrepancy 6 6 6 % (2 : ℤ) ^ 6 = 14 ∧
      directedCertifiedKill 6 6 6 ∧
      (∀ L : ℕ, L ≤ 6 → ¬ certifiedKill 6 6 L) ∧
      certifiedKill 6 6 7 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, by decide⟩
  intro L hL
  interval_cases L <;> decide

/-! ### `prop:CP-07` — a sufficient condition at the prescribed mod-four pulses -/

/-- **A sufficient condition at the prescribed mod-four pulses.**  If for
every `h ≥ 1` and every `B` there are a prime `p > B` and `K` with
`φ(p+4h) - φ(p) ≡ 2 (mod 4)` and every integer `z` with `|z| ≤ p+4h+1` and
`z ≡ 2 (mod 4)` having an index `i ≤ K` with
`|c_{4h,p,z}(i)| ≥ p+i+4h+2`, then `S ∉ ℚ`. -/
theorem irrational_of_modFour_pulse_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] ∧
      ∃ K : ℕ, ∀ z : ℤ, |z| ≤ ((p + 4 * h + 1 : ℕ) : ℤ) → z ≡ (2 : ℤ) [ZMOD 4] →
        ∃ i : ℕ, i ≤ K ∧
          ((p + i + 4 * h + 2 : ℕ) : ℤ) ≤ |carryOrbit (4 * h) p z i|) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totientSeries_of_cofinal_modFourPulseSurvivorKill ?_
  intro h hh B
  obtain ⟨p, hpB, hp, hpulse, K, hkill⟩ := hsupply h hh B
  refine ⟨p, hpB, hp, ?_, K, ?_⟩
  · simpa [deltaTotient] using hpulse
  · intro j hj hjmod
    have hjlt : j < 2 * (p + 4 * h + 1) + 1 := Finset.mem_range.mp hj
    have hzabs :
        |(j : ℤ) - ((p : ℤ) + ((4 * h : ℕ) : ℤ) + 1)| ≤ ((p + 4 * h + 1 : ℕ) : ℤ) := by
      rw [abs_le]
      constructor <;> push_cast <;> omega
    obtain ⟨i, hiK, hi⟩ := hkill _ hzabs hjmod
    refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
    rcases le_abs.mp hi with hge | hle
    · right
      push_cast at hge ⊢
      linarith
    · left
      push_cast at hle ⊢
      linarith

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_pos
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_neg
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_ne_zero
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_iff
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_example
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_modFour_pulse_supply
