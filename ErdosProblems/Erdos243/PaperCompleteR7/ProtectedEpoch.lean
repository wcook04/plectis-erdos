import ErdosProblems.Erdos243.ProtectedEpochEnergy
import ErdosProblems.Erdos243.LcmRecordCrossing

/-!
# The actual first-crossing set in the protected-epoch inequality

Uncompiled candidate for long-record `res:epochenergy`.
The existing theorem returns SOME clean charged finite set.  The printed
statement names the set of ALL first crossings of the barrier family.
This module retains first-crossing data in the selection, identifies that
specified set, and reuses the existing barrier count and spacing lemmas.
The lower-level crossing argument follows the supplied source proof;
no energy upper bound or cofinal protected-epoch producer is claimed.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open scoped BigOperators

/-- The existing finite interval is the complete index set for the
odd multiples in the window, not just a numerical lower bound. -/
theorem barrierIdx_exact {Q k : ℕ} (hQ : 16 ≤ Q) :
    k ∈ barrierIdx Q ↔ Q < 4 * (2 * k + 1) ∧ 2 * (2 * k + 1) ≤ Q := by
  simp only [barrierIdx, Finset.mem_Icc]
  omega

noncomputable def epochCrossings (u : ℕ → ℕ) (p l s τ : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico s τ).filter (fun n ↦ ∃ k ∈ barrierIdx (p ^ l),
    LcmRecordCrossing.FirstCrossing u ((2 * k + 1) * p) n)

theorem protected_epoch_energy_all_crossings
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ) :
    let J := epochCrossings u p l s τ
    (∀ n ∈ J, s ≤ n ∧ n < τ ∧ runningMax u n < u (n + 1) ∧
          u n + 3 ≤ u (n + 1) ∧ hc n = 1) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  classical
  -- Basic arithmetic on the protected modulus.
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    obtain ⟨j, hj⟩ := hpodd
    omega
  have hppos : 0 < p := by omega
  have hQodd : Odd (p ^ l) := hpodd.pow
  have hpQodd : Odd (p * p ^ l) := hpodd.mul hQodd
  have hbig : 3 * 16 ≤ p * p ^ l := Nat.mul_le_mul hp3 hQ
  have hpow : p ^ (l + 1) = p * p ^ l := by rw [pow_succ]; ring
  obtain ⟨M, hM⟩ := hpQodd
  -- Split off the crossing index.
  obtain ⟨t, rfl⟩ : ∃ t, τ = t + 1 := ⟨τ - 1, by omega⟩
  have hts : s ≤ t := by omega
  -- Every barrier is first crossed at a clean record step with jump ≥ 3.
  have key : ∀ k ∈ barrierIdx (p ^ l), ∃ n,
      s ≤ n ∧ n ≤ t ∧ u n < (2 * k + 1) * p ∧ (2 * k + 1) * p ≤ u (n + 1) ∧
        runningMax u n < u (n + 1) ∧ u n + 3 ≤ u (n + 1) ∧ hc n = 1 ∧
        LcmRecordCrossing.FirstCrossing u ((2 * k + 1) * p) n := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := barrierIdx_spec hQ hk
    -- The barrier sits strictly inside the window `(p * Q / 4, p * Q / 2]`.
    have hb1 : p * p ^ l < 4 * ((2 * k + 1) * p) := by
      calc p * p ^ l = p ^ l * p := by ring
        _ < (4 * (2 * k + 1)) * p := mul_lt_mul_of_pos_right hk1 hppos
        _ = 4 * ((2 * k + 1) * p) := by ring
    have hb2 : 2 * ((2 * k + 1) * p) ≤ p * p ^ l := by
      calc 2 * ((2 * k + 1) * p) = (2 * (2 * k + 1)) * p := by ring
        _ ≤ p ^ l * p := Nat.mul_le_mul hk2 (le_refl p)
        _ = p * p ^ l := by ring
    have hbu : (2 * k + 1) * p ≤ u (t + 1) := by omega
    have hexists : ∃ n, n ∈ {m | s ≤ m ∧ (2 * k + 1) * p ≤ u (m + 1)} := ⟨t, hts, hbu⟩
    -- First crossing of this barrier, as a plain natural number.
    obtain ⟨n, hns, hnb, hnt, hnmin⟩ :
        ∃ n, s ≤ n ∧ (2 * k + 1) * p ≤ u (n + 1) ∧ n ≤ t ∧
          ∀ i, i < n → s ≤ i → u (i + 1) < (2 * k + 1) * p := by
      refine ⟨sInf {m | s ≤ m ∧ (2 * k + 1) * p ≤ u (m + 1)},
        (Nat.sInf_mem hexists).1, (Nat.sInf_mem hexists).2, Nat.sInf_le ⟨hts, hbu⟩, ?_⟩
      intro i hi his
      by_contra hcon
      have hle : sInf {m | s ≤ m ∧ (2 * k + 1) * p ≤ u (m + 1)} ≤ i :=
        Nat.sInf_le ⟨his, by omega⟩
      omega
    -- Nothing in the window has reached the barrier yet.
    have hbefore : ∀ j, s ≤ j → j ≤ n → u j < (2 * k + 1) * p := by
      intro j hj hjn
      rcases Nat.lt_or_ge s j with hlt | hge
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        exact hnmin i (by omega) (by omega)
      · have h1 : u j ≤ runningMax u s := le_runningMax u hge
        omega
    have hun : u n < (2 * k + 1) * p := hbefore n hns (le_refl n)
    have hrun : runningMax u n < (2 * k + 1) * p := by
      refine runningMax_lt u (fun j hj => ?_)
      rcases Nat.lt_or_ge j s with hjs | hjs
      · have h1 : u j ≤ runningMax u s := le_runningMax u (le_of_lt hjs)
        omega
      · exact hbefore j hjs hj
    -- The protected prime power survives to the crossing.
    have hprotn : p ^ l ∣ v (n + 1) := by
      refine protectedPrimePower_persists a u v w hc p l s (M + 1) hp hred hvpos hw hwpos
        hnum hden hslow ?_ hprot (n + 1) (by omega) ?_
      · rw [hpow]; omega
      · intro j hj hjn1
        have hjb := hbefore j hj (by omega)
        omega
    have hpv : p ∣ v (n + 1) := dvd_trans (dvd_pow_self p (by omega)) hprotn
    -- Landing exactly on the barrier is impossible.
    have hne : u (n + 1) ≠ (2 * k + 1) * p := by
      intro hEq
      have hpu : p ∣ u (n + 1) := ⟨2 * k + 1, by rw [hEq]; ring⟩
      have hg : p ∣ Nat.gcd (u (n + 1)) (v (n + 1)) := Nat.dvd_gcd hpu hpv
      rw [(hred (n + 1) (by omega)).gcd_eq_one] at hg
      have := Nat.le_of_dvd Nat.one_pos hg
      omega
    -- Adjacent reduced numerators are coprime.
    have hcopnum : Nat.Coprime (u n) (u (n + 1)) := by
      have h1 : Nat.Coprime (u n) (w n) :=
        rawNext_coprime_currentNumerator (hred n hns) (hw n hns)
      exact h1.coprime_dvd_right ⟨hc n, by rw [hnum n hns]; ring⟩
    -- A jump of at most two would force `(b - 1, b + 1)`, both even.
    have hjump : u n + 3 ≤ u (n + 1) := by
      by_contra hcon
      have hB1 : (2 * k + 1) * p = u n + 1 := by omega
      have hodd1 : Odd (2 * k + 1) := ⟨k, by ring⟩
      have hBodd : Odd ((2 * k + 1) * p) := hodd1.mul hpodd
      obtain ⟨j, hj⟩ := hBodd
      have h2 : 2 ∣ Nat.gcd (u n) (u (n + 1)) :=
        Nat.dvd_gcd ⟨j, by omega⟩ ⟨j + 1, by omega⟩
      rw [hcopnum.gcd_eq_one] at h2
      omega
    -- A strict rise under the centring bound is cancellation-free.
    have hhcpos : 0 < hc n := by
      rcases Nat.eq_zero_or_pos (hc n) with h0 | hpos
      · exfalso
        have h1 := hnum n hns
        rw [h0, Nat.zero_mul] at h1
        have := hwpos n hns
        omega
      · exact hpos
    have hhclt : hc n < 2 := by
      by_contra hcon
      have hcon2 : 2 ≤ hc n := by omega
      have hmul : 2 * u (n + 1) ≤ hc n * u (n + 1) :=
        Nat.mul_le_mul hcon2 (le_refl (u (n + 1)))
      have h1 := hnum n hns
      have h2 := hslow n hns
      omega
    exact ⟨n, hns, hnt, hun, hnb, by omega, hjump, by omega,
      ⟨fun j hj ↦ (le_runningMax u hj).trans_lt hrun, hnb⟩⟩
  choose! f hf using key
  let J := epochCrossings u p l s (t + 1)
  have hmemJ : ∀ k ∈ barrierIdx (p ^ l), f k ∈ J := by
    intro k hk
    obtain ⟨hfs, hft, _, _, _, _, _, hfirst⟩ := hf k hk
    change f k ∈ (Finset.Ico s (t + 1)).filter
      (fun n ↦ ∃ j ∈ barrierIdx (p ^ l),
        LcmRecordCrossing.FirstCrossing u ((2 * j + 1) * p) n)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hfs, by omega⟩, k, hk, hfirst⟩
  have hJmem : ∀ n ∈ J, ∃ k ∈ barrierIdx (p ^ l), f k = n := by
    intro n hn
    obtain ⟨hnwin, k, hk, hfirstn⟩ := Finset.mem_filter.mp hn
    refine ⟨k, hk, ?_⟩
    have hfirstf := (hf k hk).2.2.2.2.2.2.2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlo := hfirstn.1 (f k + 1) (by omega)
      have hhi := hfirstf.2
      omega
    · have hlo := hfirstf.1 (n + 1) (by omega)
      have hhi := hfirstn.2
      omega
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, hk, rfl⟩ := hJmem n hn
    obtain ⟨h1, h2, _, _, h5, h6, h7, _⟩ := hf k hk
    exact ⟨h1, by omega, h5, h6, h7⟩
  · -- Count the barriers fibrewise over their first-crossing steps.
    have hfib : (barrierIdx (p ^ l)).card
        = ∑ n ∈ J, ((barrierIdx (p ^ l)).filter (fun k => f k = n)).card :=
      Finset.card_eq_sum_card_fiberwise hmemJ
    have hspace : ∀ n ∈ J,
        2 * p * ((barrierIdx (p ^ l)).filter (fun k => f k = n)).card
          ≤ 2 * p + (u (n + 1) - u n) := by
      intro n _
      refine fibre_card_le_spacing _ (fun k hk => ?_)
      rw [Finset.mem_filter] at hk
      obtain ⟨hkS, hkf⟩ := hk
      obtain ⟨_, _, h3, h4, _, _, _, _⟩ := hf k hkS
      rw [hkf] at h3 h4
      exact ⟨h3, h4⟩
    have hsum1 : 2 * p * (barrierIdx (p ^ l)).card
        ≤ ∑ n ∈ J, (2 * p + (u (n + 1) - u n)) := by
      rw [hfib, Finset.mul_sum]
      exact Finset.sum_le_sum hspace
    have hd : ∀ n ∈ J, 2 * p + (u (n + 1) - u n)
        = (2 * p + 2) + (u (n + 1) - u n - 2) := by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := hJmem n hn
      obtain ⟨_, _, _, _, _, h6, _, _⟩ := hf k hk
      omega
    have hsum2 : ∑ n ∈ J, (2 * p + (u (n + 1) - u n))
        = (2 * p + 2) * J.card + ∑ n ∈ J, (u (n + 1) - u n - 2) := by
      calc ∑ n ∈ J, (2 * p + (u (n + 1) - u n))
          = ∑ n ∈ J, ((2 * p + 2) + (u (n + 1) - u n - 2)) := Finset.sum_congr rfl hd
        _ = (∑ _n ∈ J, (2 * p + 2)) + ∑ n ∈ J, (u (n + 1) - u n - 2) :=
            Finset.sum_add_distrib
        _ = (2 * p + 2) * J.card + ∑ n ∈ J, (u (n + 1) - u n - 2) := by
            rw [Finset.sum_const, smul_eq_mul]; ring
    have hA : p ^ l ≤ 8 * (barrierIdx (p ^ l)).card + 8 := barrierIdx_card_lower hQ
    have hBd : 2 * p * (barrierIdx (p ^ l)).card
        ≤ (2 * p + 2) * J.card + ∑ n ∈ J, (u (n + 1) - u n - 2) := by
      rw [← hsum2]; exact hsum1
    calc p * p ^ l ≤ p * (8 * (barrierIdx (p ^ l)).card + 8) :=
          Nat.mul_le_mul (le_refl p) hA
      _ = 4 * (2 * p * (barrierIdx (p ^ l)).card) + 8 * p := by ring
      _ ≤ 4 * ((2 * p + 2) * J.card + ∑ n ∈ J, (u (n + 1) - u n - 2)) + 8 * p :=
          Nat.add_le_add_right (Nat.mul_le_mul (le_refl 4) hBd) _
      _ = (8 * p + 8) * J.card + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by ring


/-- The exact signed centring bound in the paper implies the weaker
raw-numerator bound used by the existing protected-prime theorem. -/
theorem centred_implies_epoch_bound (u w : ℕ) (e : ℤ)
    (hraw : (w : ℤ) = (u : ℤ) - e)
    (hsmall : 2 * Int.natAbs e < u) : 2 * w ≤ 3 * u := by
  have habs : -(Int.natAbs e : ℤ) ≤ e := by
    by_cases he : 0 ≤ e
    · rw [Int.natAbs_of_nonneg he]
      omega
    · have hh : (Int.natAbs e : ℤ) = -e := Int.ofNat_natAbs_of_nonpos (by omega)
      rw [hh]
      omega
  have hsmallZ : (2 : ℤ) * Int.natAbs e < (u : ℤ) := by exact_mod_cast hsmall
  have hboundZ : (2 : ℤ) * (w : ℤ) ≤ 3 * (u : ℤ) := by omega
  exact_mod_cast hboundZ

/-- The displayed protected epoch, on its signed primitive-cocycle
hypotheses, with its SPECIFIED first-crossing set.  The natural expressions
4R_s<pQ and pQ≤2u_τ are exactly R_s<L/2 and u_τ≥L for L=pQ/2.
Firstness of τ is unnecessary and is not added as a stronger premise. -/
theorem protected_epoch_paper
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (p l s τ : ℕ)
    (hp : p.Prime) (hp3 : 3 ≤ p)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (herror : ∀ n, s ≤ n → (w n : ℤ) = (u n : ℤ) - e n)
    (hsmall : ∀ n, s ≤ n → 2 * Int.natAbs (e n) < u n)
    (hprot : p ^ l ∣ v s) (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hτ : p * p ^ l ≤ 2 * u τ) :
    let J := epochCrossings u p l s τ
    (∀ n ∈ J, s ≤ n ∧ n < τ ∧ runningMax u n < u (n + 1) ∧
      u n + 3 ≤ u (n + 1) ∧ hc n = 1) ∧
    p * p ^ l ≤ (8 * p + 8) * J.card +
      4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hl : 1 ≤ l := by
    by_contra h
    have hz : l = 0 := by omega
    simp [hz] at hQ
  have hsτ : s < τ := by
    by_contra h
    have hh := le_runningMax u (show τ ≤ s by omega)
    omega
  apply protected_epoch_energy_all_crossings a u v w hc p l s τ
    hp hpodd hl hred hvpos hw hwpos hnum hden _ hprot hQ hRs hsτ hτ
  intro n hn
  exact centred_implies_epoch_bound (u n) (w n) (e n) (herror n hn) (hsmall n hn)

end ErdosProblems.Erdos243.PaperCompleteR7
