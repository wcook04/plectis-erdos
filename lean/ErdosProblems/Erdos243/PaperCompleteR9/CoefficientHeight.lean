import ErdosProblems.Erdos243.PaperCompleteR7.LcmStationarity

/-!
# Coefficient-uniform height from a bound only at records

Neither strict increase of the multipliers, centring, normalised vanishing,
nor a supply of old moduli is assumed. The supply is constructed below. The
integral coefficients may have either sign.
-/
namespace ErdosProblems.Erdos243.PaperCompleteR9

open scoped BigOperators

/-- A record is attached to its source index. -/
def IsStrictRecord (U : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j, j ≤ n → U j < U (n + 1)

noncomputable def firstDigitIndex (a : ℕ → ℕ) (k : ℕ) : ℕ := by
  classical
  exact if h : ∃ n, a n = k then Nat.find h else 0

noncomputable def smallDigitCutoff (a : ℕ → ℕ) (B : ℕ) : ℕ :=
  1 + ∑ k ∈ Finset.range (B + 1), firstDigitIndex a k

/-- A finite prefix contains an occurrence of every small digit that ever
occurs. This replaces an unnecessary monotonicity assumption on a. -/
theorem small_digit_dvd_old_lcm (q : ℕ) (a : ℕ → ℕ) (B n : ℕ)
    (hn : smallDigitCutoff a B ≤ n) (ha : a n ≤ B) :
    a n ∣ cumulativeDigitLcm q a n := by
  classical
  have hex : ∃ j, a j = a n := ⟨n, rfl⟩
  have hspec : a (firstDigitIndex a (a n)) = a n := by
    unfold firstDigitIndex
    rw [dif_pos hex]
    exact Nat.find_spec hex
  have hsum : firstDigitIndex a (a n) ≤
      ∑ k ∈ Finset.range (B + 1), firstDigitIndex a k :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  have hi : firstDigitIndex a (a n) < n := by
    unfold smallDigitCutoff at hn
    omega
  have hd := digit_dvd_cumulativeDigitLcm_of_lt q a hi
  rwa [hspec] at hd

/-- Late fresh digits exceed any fixed bound without any growth assumption. -/
theorem late_fresh_digit_large (q : ℕ) (a : ℕ → ℕ) (B n : ℕ)
    (ha : ∀ j, 2 ≤ a j) (hn : smallDigitCutoff a B ≤ n)
    (hf : lcmOverlap q a n = 1) : B < a n := by
  by_contra hnot
  have hd := small_digit_dvd_old_lcm q a B n hn (by omega)
  have hdiv : a n ∣ lcmOverlap q a n := Nat.dvd_gcd hd (dvd_refl _)
  rw [hf] at hdiv
  have hle := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hdiv
  have hh := ha n
  omega

/-- Full bounded height, assuming a negative-error bound only at late records.
Old moduli, their size, and the CRT covering are constructed, not assumed. -/
theorem coefficient_height_bounded_at_records
    (q : ℕ) (a U : ℕ → ℕ) (b V : ℕ → ℤ)
    (hq : 0 < q) (ha : ∀ n, 2 ≤ a n) (hU : ∀ n, 0 < U n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * (U (n + 1) : ℤ) =
      (U n : ℤ) - V n)
    (herror : ∀ n, V n = b n * (cumulativeDigitLcm q a n : ℤ) -
      ((a n : ℤ) - 1) * (U n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → IsStrictRecord U n →
      -(B : ℤ) ≤ V n) :
    ∃ H : ℕ, ∀ n, U n ≤ H := by
  classical
  by_contra hbounded
  have hunbounded : ∀ H : ℕ, ∃ n, H < U n := by
    intro H
    by_contra hn
    apply hbounded
    refine ⟨H, fun n ↦ ?_⟩
    by_contra hle
    exact hn ⟨n, by omega⟩
  have hapos : ∀ n, 0 < a n := fun n ↦ lt_of_lt_of_le (by decide) (ha n)
  obtain ⟨Nb, B0, hB0⟩ := hbound
  let B := B0 + 1
  have hBpos : 0 < B := by dsimp [B]; omega
  have hB : ∀ n, Nb ≤ n → IsStrictRecord U n → -(B : ℤ) ≤ V n := by
    intro n hn hr
    have hh := hB0 n hn hr
    dsimp [B]
    omega
  have hcap : ∀ n, Nb ≤ n → IsStrictRecord U n →
      lcmOverlap q a n * U (n + 1) ≤ U n + B := by
    intro n hn hr
    have hs := hstep n
    have hb := hB n hn hr
    exact_mod_cast (show (lcmOverlap q a n : ℤ) * (U (n + 1) : ℤ) ≤
      (U n : ℤ) + (B : ℤ) by omega)
  have hfresh : ∀ T : ℕ, ∃ n, T ≤ n ∧ lcmOverlap q a n = 1 := by
    intro T
    let S := max T Nb
    let H := runningMax U S + 2 * B + 2
    obtain ⟨K, hK⟩ := hunbounded H
    have hzero : U 0 < H := by
      have hh := le_runningMax U (Nat.zero_le S)
      dsimp [H]
      omega
    obtain ⟨n, hn, _⟩ := LcmRecordCrossing.exists_unique_firstCrossing U H K hzero
      ⟨K, le_rfl, hK.le⟩
    have hfirst := hn.2
    have hSn : S ≤ n := by
      by_contra hnot
      have hm := le_runningMax U (show n + 1 ≤ S by omega)
      have hh := hfirst.2
      dsimp [H] at hh
      omega
    have hr : IsStrictRecord U n := hfirst.is_record
    have hc := hcap n ((Nat.le_max_right T Nb).trans hSn) hr
    have hlow := hfirst.1 n le_rfl
    have hhigh := hfirst.2
    have hp := lcmOverlap_pos hq hapos n
    have hone : lcmOverlap q a n = 1 := by
      by_contra hnot
      have htwo : 2 ≤ lcmOverlap q a n := by omega
      have hmul := Nat.mul_le_mul_right (U (n + 1)) htwo
      dsimp [H] at hlow hhigh
      omega
    exact ⟨n, (Nat.le_max_left T Nb).trans hSn, hone⟩
  have hbigfresh : ∀ T : ℕ, ∃ n, T ≤ n ∧ lcmOverlap q a n = 1 ∧ B < a n := by
    intro T
    obtain ⟨n, hn, hf⟩ := hfresh (max T (smallDigitCutoff a B))
    exact ⟨n, (Nat.le_max_left _ _).trans hn, hf,
      late_fresh_digit_large q a B n ha ((Nat.le_max_right _ _).trans hn) hf⟩
  let g : ℕ → ℕ := fun T ↦ Classical.choose (hbigfresh T)
  have hg : ∀ T, T ≤ g T ∧ lcmOverlap q a (g T) = 1 ∧ B < a (g T) :=
    fun T ↦ Classical.choose_spec (hbigfresh T)
  let f : ℕ → ℕ := Nat.rec (g Nb) (fun _ prev ↦ g (prev + 1))
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
    | zero => exact (hg Nb).2.1
    | succ i => exact (hg (f i + 1)).2.1
  have hfbig : ∀ i, B < a (f i) := by
    intro i
    cases i with
    | zero => exact (hg Nb).2.2
    | succ i => exact (hg (f i + 1)).2.2
  have hflow : ∀ i, Nb ≤ f i := by
    intro i
    exact (hg Nb).1.trans (hfmono.monotone (Nat.zero_le i))
  let m : Fin B → ℕ := fun i ↦ a (f i.1)
  have hm : ∀ i, B < m i := fun i ↦ hfbig i.1
  have hm1 : ∀ i, 1 < m i := by
    intro i
    have hh := hm i
    omega
  have hpair : ∀ i j : Fin B, i ≠ j → Nat.Coprime (m i) (m j) := by
    intro i j hij
    apply lcmFresh_coprime_of_ne q a _ (hffresh i.1) (hffresh j.1)
    intro heq
    exact hij (Fin.ext (hfmono.injective heq))
  let T := f B + 1
  have hTb : Nb ≤ T := by
    have hh := hflow B
    dsimp [T]
    omega
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
  obtain ⟨K, hK⟩ := hunbounded (x + B)
  have hzero : U 0 < x + B := by
    have hh := le_runningMax U (Nat.zero_le T)
    omega
  obtain ⟨n, hn, _⟩ := LcmRecordCrossing.exists_unique_firstCrossing U (x + B) K hzero
    ⟨K, le_rfl, hK.le⟩
  have hfirst := hn.2
  have hTn : T ≤ n := by
    by_contra hnot
    have hm := le_runningMax U (show n + 1 ≤ T by omega)
    have hh := hfirst.2
    omega
  have hr : IsStrictRecord U n := hfirst.is_record
  have hcapZ : (lcmOverlap q a n : ℤ) * (U (n + 1) : ℤ) ≤
      (U n : ℤ) + (B : ℤ) := by exact_mod_cast hcap n (hTb.trans hTn) hr
  have hstepZ : (lcmOverlap q a n : ℤ) * (U (n + 1) : ℤ) =
      (a n : ℤ) * (U n : ℤ) - b n * (cumulativeDigitLcm q a n : ℤ) := by
    have hh := hstep n
    rw [herror n] at hh
    nlinarith [hh]
  have hfence := CoefficientDivisorFence.no_jump_through_fence
    (a n : ℤ) (b n) (cumulativeDigitLcm q a n : ℤ)
    (U n : ℤ) (U (n + 1) : ℤ) (lcmOverlap q a n : ℤ) (B : ℤ) (x : ℤ)
    (by exact_mod_cast hU (n + 1))
    (by exact_mod_cast (Nat.succ_le_of_lt (lcmOverlap_pos hq hapos n)))
    (by exact_mod_cast Nat.zero_le B) hcapZ hstepZ
    (by exact_mod_cast hxB)
    (by exact_mod_cast hfirst.1 n le_rfl) (hcover n hTn)
  have hh : (x : ℤ) + (B : ℤ) ≤ (U (n + 1) : ℤ) := by
    exact_mod_cast hfirst.2
  omega

/-- Normalised vanishing is needed only after boundedness, for discreteness. -/
theorem coefficient_zero_of_record_bound
    (q : ℕ) (a U : ℕ → ℕ) (b V : ℕ → ℤ)
    (hq : 0 < q) (ha : ∀ n, 2 ≤ a n) (hU : ∀ n, 0 < U n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * (U (n + 1) : ℤ) = (U n : ℤ) - V n)
    (herror : ∀ n, V n = b n * (cumulativeDigitLcm q a n : ℤ) -
      ((a n : ℤ) - 1) * (U n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → IsStrictRecord U n → -(B : ℤ) ≤ V n)
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * (V n).natAbs < U n) :
    ∃ N, ∀ n, N ≤ n → V n = 0 := by
  exact PaperCompleteR7.zero_digit_of_bounded_height U V
    (coefficient_height_bounded_at_records q a U b V hq ha hU hstep herror hbound)
    hvanish

end ErdosProblems.Erdos243.PaperCompleteR9
