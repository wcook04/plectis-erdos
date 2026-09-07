import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState
import ErdosProblems.Erdos243.CumulativeLcmTransfer
import ErdosProblems.Erdos243.LcmCriticalBoundary
import ErdosProblems.Erdos243.LcmRecordCrossing
import ErdosProblems.Erdos243.CoefficientDivisorFence
import ErdosProblems.Erdos243.PrimitiveRecordBarrier

/-!
# Global boundedness and stationarity of the actual LCM state

Uncompiled candidates.  Unlike the existing finite CRT consumers, the
principal theorem constructs its old fresh multipliers from the unbounded
orbit.  No old-prime supply, global avoidance hypothesis, or preconstructed
cover is a premise.  Strict increase of the given denominators supplies
multipliers larger than the fixed bound.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators

/-- A bounded negative LCM digit bounds LCM height.  Only after this
arithmetic theorem is normalised vanishing used to obtain stationarity. -/
theorem bounded_lcm_height
    (q : ℕ) (a U : ℕ → ℕ) (V : ℕ → ℤ)
    (hq : 0 < q) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (hUpos : ∀ n, 0 < U n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * (U (n + 1) : ℤ) = (U n : ℤ) - V n)
    (hcenter : ∀ n, V n = (cumulativeDigitLcm q a n : ℤ) -
      ((a n : ℤ) - 1) * (U n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ V n) :
    ∃ H : ℕ, ∀ n, U n ≤ H := by
  classical
  by_contra hbounded
  have hunbounded : ∀ H : ℕ, ∃ n, H < U n := by
    intro H
    by_contra hnone
    apply hbounded
    refine ⟨H, fun n ↦ ?_⟩
    by_contra hn
    exact hnone ⟨n, by omega⟩
  obtain ⟨Nb, B0, hB0⟩ := hbound
  let B := B0 + 1
  have hBpos : 0 < B := by dsimp [B]; omega
  have hB : ∀ n, Nb ≤ n → -(B : ℤ) ≤ V n := by
    intro n hn
    have hh := hB0 n hn
    dsimp [B]
    omega
  have hcap : ∀ n, Nb ≤ n → lcmOverlap q a n * U (n + 1) ≤ U n + B := by
    intro n hn
    have heq := hstep n
    have hb := hB n hn
    exact_mod_cast (show (lcmOverlap q a n : ℤ) * (U (n + 1) : ℤ) ≤
      (U n : ℤ) + (B : ℤ) by omega)
  have hfresh : ∀ T : ℕ, ∃ n, T ≤ n ∧ lcmOverlap q a n = 1 := by
    intro T
    let S := max T Nb
    let h := runningMax U S + 2 * B + 2
    obtain ⟨K, hK⟩ := hunbounded h
    have hzero : U 0 < h := by
      have hh := le_runningMax U (Nat.zero_le S)
      dsimp [h]
      omega
    obtain ⟨n, hn, _⟩ := LcmRecordCrossing.exists_unique_firstCrossing U h K hzero
      ⟨K, le_rfl, hK.le⟩
    have hfirst := hn.2
    have hSn : S ≤ n := by
      by_contra hlt
      have hs := le_runningMax U (show n + 1 ≤ S by omega)
      have hh := hfirst.2
      dsimp [h] at hh
      omega
    have hcapn := hcap n ((Nat.le_max_right T Nb).trans hSn)
    have hUhigh := hfirst.2
    have hUn := hfirst.1 n le_rfl
    have hρpos := lcmOverlap_pos hq hapos n
    have hρone : lcmOverlap q a n = 1 := by
      by_contra hne
      have htwo : 2 ≤ lcmOverlap q a n := by omega
      have hmul := Nat.mul_le_mul_right (U (n + 1)) htwo
      dsimp [h] at hUn hUhigh
      omega
    exact ⟨n, (Nat.le_max_left T Nb).trans hSn, hρone⟩
  let g : ℕ → ℕ := fun T ↦ Classical.choose (hfresh T)
  have hg : ∀ T, T ≤ g T ∧ lcmOverlap q a (g T) = 1 :=
    fun T ↦ Classical.choose_spec (hfresh T)
  let f : ℕ → ℕ := Nat.rec (g (max Nb (B + 1))) (fun _ prev ↦ g (prev + 1))
  have hfzero : f 0 = g (max Nb (B + 1)) := rfl
  have hfsucc : ∀ i, f (i + 1) = g (f i + 1) := fun _ ↦ rfl
  have hfmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hfsucc]
    have hh := (hg (f i + 1)).1
    omega
  have hffresh : ∀ i, lcmOverlap q a (f i) = 1 := by
    intro i
    cases i with
    | zero => exact (hg (max Nb (B + 1))).2
    | succ i => exact (hg (f i + 1)).2
  have hflow : ∀ i, max Nb (B + 1) ≤ f i := by
    intro i
    exact (hg (max Nb (B + 1))).1.trans (hfmono.monotone (Nat.zero_le i))
  have hanat : ∀ n, n < a n := by
    intro n
    induction n with
    | zero => exact hapos 0
    | succ n ih =>
        have hh : a n < a (n + 1) := ha (Nat.lt_succ_self n)
        omega
  let m : Fin B → ℕ := fun i ↦ a (f i.1)
  have hm : ∀ i, B < m i := by
    intro i
    have hh := hflow i.1
    have hlarge := hanat (f i.1)
    dsimp [m]
    omega
  have hm1 : ∀ i, 1 < m i := by
    intro i
    have hh := hm i
    omega
  have hpair : ∀ i j : Fin B, i ≠ j → Nat.Coprime (m i) (m j) := by
    intro i j hij
    apply lcmFresh_coprime_of_ne q a _ (hffresh i.1) (hffresh j.1)
    intro heq
    apply hij
    exact Fin.ext (hfmono.injective heq)
  let T := f B + 1
  have hTb : Nb ≤ T := by have hh := hflow B; dsimp [T]; omega
  have hmOld : ∀ (i : Fin B) n, T ≤ n → m i ∣ cumulativeDigitLcm q a n := by
    intro i n hn
    have hi := hfmono i.isLt
    exact digit_dvd_cumulativeDigitLcm_of_lt q a (by dsimp [T] at hn; omega)
  obtain ⟨x, hx, hxDiv⟩ := exists_shifted_consecutiveMultiples m hm1 hpair
    (max (runningMax U T) B)
  have hxB : B < x := lt_of_le_of_lt (Nat.le_max_right _ _) hx
  have hxR : runningMax U T < x := lt_of_le_of_lt (Nat.le_max_left _ _) hx
  have hcover : ∀ n, T ≤ n → ∀ z : ℤ, (x : ℤ) ≤ z → z < (x : ℤ) + B →
      ∃ d : ℤ, (B : ℤ) < d ∧ d ∣ z ∧ d ∣ (cumulativeDigitLcm q a n : ℤ) := by
    intro n hn z hzlo hzhi
    have hznonneg : 0 ≤ z - (x : ℤ) := by omega
    let i : Fin B := ⟨(z - (x : ℤ)).toNat, by omega⟩
    have hzi : z = ((x + i.1 : ℕ) : ℤ) := by
      have hi : (i.1 : ℤ) = z - (x : ℤ) := Int.toNat_of_nonneg hznonneg
      push_cast
      omega
    refine ⟨m i, by exact_mod_cast hm i, ?_, ?_⟩
    · rw [hzi]
      exact_mod_cast hxDiv i
    · exact_mod_cast hmOld i n hn
  have hboundedTail : ∀ k, (U (T + k) : ℤ) < (x : ℤ) + B := by
    apply CoefficientDivisorFence.stays_below_fence
      (fun k ↦ (a (T + k) : ℤ)) (fun _ ↦ 1)
      (fun k ↦ (cumulativeDigitLcm q a (T + k) : ℤ))
      (fun k ↦ (U (T + k) : ℤ))
      (fun k ↦ (lcmOverlap q a (T + k) : ℤ)) (B : ℤ) (x : ℤ)
    · intro k; exact_mod_cast hUpos (T + k)
    · intro k; exact_mod_cast lcmOverlap_pos hq hapos (T + k)
    · exact_mod_cast Nat.zero_le B
    · exact_mod_cast hxB
    · intro k
      have hh := hcap (T + k) (by omega)
      exact_mod_cast (show lcmOverlap q a (T + k) * U (T + (k + 1)) ≤
        U (T + k) + B by simpa only [Nat.add_assoc] using hh)
    · intro k
      have hs := hstep (T + k)
      rw [hcenter (T + k)] at hs
      simp only [one_mul]
      simpa only [Nat.add_assoc] using (show
        (lcmOverlap q a (T + k) : ℤ) * (U (T + k + 1) : ℤ) =
          (a (T + k) : ℤ) * (U (T + k) : ℤ) -
            (cumulativeDigitLcm q a (T + k) : ℤ) by nlinarith [hs])
    · have huT := le_runningMax U (le_rfl : T ≤ T)
      have hnat : U T < x + B := by omega
      exact_mod_cast hnat
    · intro k z hlo hhi
      exact hcover (T + k) (by omega) z hlo hhi
  obtain ⟨n, hn⟩ := hunbounded (x + B)
  by_cases hnt : n ≤ T
  · have hh := le_runningMax U hnt
    omega
  · have hTn : T ≤ n := by omega
    have hh := hboundedTail (n - T)
    rw [Nat.add_sub_of_le hTn] at hh
    have hnZ : ((x + B : ℕ) : ℤ) < (U n : ℤ) := by exact_mod_cast hn
    push_cast at hnZ
    omega

/-- Integer boundedness and normalised vanishing force zero LCM digit.
The denominator recurrence is not needed in this final discreteness step. -/
theorem zero_digit_of_bounded_height
    (U : ℕ → ℕ) (V : ℕ → ℤ)
    (hbound : ∃ H, ∀ n, U n ≤ H)
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (V n) < U n) :
    ∃ N, ∀ n, N ≤ n → V n = 0 := by
  obtain ⟨H, hH⟩ := hbound
  exact eventually_zero_of_bounded_lcmState U V H hH hvanish

end ErdosProblems.Erdos243.PaperCompleteR7
