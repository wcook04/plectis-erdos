import ErdosProblems.Erdos243.ProtectedEpochEnergy

/-!
# Erdős 243: counting crossings before a prime power is lost, in paper form

Paper-form restatement of `long243:res:epochenergy` of the long note
`paper/reasoning-parts/erdos243/core.tex`.

`ProtectedEpochEnergy.protected_epoch_energy_integer` proves the same
inequality but only for *some* finite set of charged steps, produced by the
proof.  The paper names the set: `J` is *the* set of steps in `[s, τ)` that
first cross at least one odd multiple of `p` in `(L/2, L]`, and asserts that
every element of that named set is a record step with `h n = 1` and `d n ≥ 3`.
That is strictly more than an existential, so the argument is re-run here
against the named set.

Doubled form of the paper's window.  With `Q = p ^ l` and `L = p * Q / 2`, the
products `p * Q` and `L` are odd, so each inequality is carried without
division: `R s < L / 2` is `4 * runningMax u s < p * Q`, `u τ ≥ L` is
`p * Q ≤ 2 * u τ`, and an odd multiple `b` of `p` lies in `(L/2, L]` exactly
when `p * Q < 4 * b` and `2 * b ≤ p * Q`.

The centring hypothesis is the paper's `2 * |ẽ n| < u n` from the index `s`,
with `ẽ n = u n - w n` in the reduced coordinates of that section.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

open ErdosProblems.Erdos243

/-- `barrierIdx Q` is exactly the index set of the odd multiples `(2 * k + 1)`
of the window condition: the barrier `(2 * k + 1) * p` lies in
`(p * Q / 4, p * Q / 2]` precisely for `k ∈ barrierIdx Q`. -/
theorem mem_barrierIdx_iff {Q : ℕ} (hQ : 16 ≤ Q) (k : ℕ) :
    k ∈ barrierIdx Q ↔ Q < 4 * (2 * k + 1) ∧ 2 * (2 * k + 1) ≤ Q := by
  simp only [barrierIdx, Finset.mem_Icc]
  omega

/-- One barrier.  If `b` is an odd multiple of `p` in the protected window and
`n` is the first index at or after `s` whose successor numerator reaches `b`,
then the step `n` is a global record step, is cancellation-free, and jumps by
at least three. -/
private theorem barrier_first_crossing_step
    (a u v w hc : ℕ → ℕ) (p l s n b : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ m, s ≤ m → Nat.Coprime (u m) (v m))
    (hvpos : ∀ m, s ≤ m → 0 < v m)
    (hw : ∀ m, s ≤ m → w m + v m = a m * u m)
    (hwpos : ∀ m, s ≤ m → 0 < w m)
    (hnum : ∀ m, s ≤ m → w m = hc m * u (m + 1))
    (hden : ∀ m, s ≤ m → a m * v m = hc m * v (m + 1))
    (hslow : ∀ m, s ≤ m → 2 * w m ≤ 3 * u m)
    (hprot : p ^ l ∣ v s)
    (hbodd : Odd b)
    (hbp : p ∣ b)
    (hwin1 : p * p ^ l < 4 * b)
    (hwin2 : 2 * b ≤ p * p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hns : s ≤ n)
    (hcross : b ≤ u (n + 1))
    (hfirst : ∀ j, s ≤ j → j < n → u (j + 1) < b) :
    runningMax u n < u (n + 1) ∧ hc n = 1 ∧ u n + 3 ≤ u (n + 1) := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    obtain ⟨j, hj⟩ := hpodd
    omega
  have hbpos : 0 < b := by
    have := Nat.le_of_dvd (by omega) hbp
    omega
  -- Nothing at or before the crossing index has reached the barrier.
  have hbefore : ∀ j, s ≤ j → j ≤ n → u j < b := by
    intro j hj hjn
    rcases Nat.lt_or_ge s j with hlt | hge
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact hfirst i (by omega) (by omega)
    · have h1 : u j ≤ runningMax u s := le_runningMax u hge
      omega
  have hun : u n < b := hbefore n hns (le_refl n)
  have hrun : runningMax u n < b := by
    refine runningMax_lt u (fun j hj => ?_)
    rcases Nat.lt_or_ge j s with hjs | hjs
    · have h1 : u j ≤ runningMax u s := le_runningMax u (le_of_lt hjs)
      omega
    · exact hbefore j hjs hj
  -- The protected prime power survives the crossing.
  have hheight : 3 * b < 2 * p ^ (l + 1) := by
    have hpow : p ^ (l + 1) = p * p ^ l := by rw [pow_succ]; ring
    omega
  have hprotn : p ^ l ∣ v (n + 1) := by
    refine protectedPrimePower_persists a u v w hc p l s b hp hred hvpos hw hwpos
      hnum hden hslow hheight hprot (n + 1) (by omega) ?_
    intro j hj hjn1
    exact hbefore j hj (by omega)
  have hpv : p ∣ v (n + 1) := dvd_trans (dvd_pow_self p (by omega)) hprotn
  -- The crossing cannot land exactly on the barrier.
  have hne : u (n + 1) ≠ b := by
    intro hEq
    have hpu : p ∣ u (n + 1) := by rw [hEq]; exact hbp
    have hg : p ∣ Nat.gcd (u (n + 1)) (v (n + 1)) := Nat.dvd_gcd hpu hpv
    rw [(hred (n + 1) (by omega)).gcd_eq_one] at hg
    have := Nat.le_of_dvd Nat.one_pos hg
    omega
  -- Adjacent reduced numerators are coprime.
  have hcopnum : Nat.Coprime (u n) (u (n + 1)) := by
    have h1 : Nat.Coprime (u n) (w n) :=
      rawNext_coprime_currentNumerator (hred n hns) (hw n hns)
    exact h1.coprime_dvd_right ⟨hc n, by rw [hnum n hns]; ring⟩
  -- A jump of at most two would straddle the odd barrier with two even ends.
  have hjump : u n + 3 ≤ u (n + 1) := by
    by_contra hcon
    have hB1 : b = u n + 1 := by omega
    obtain ⟨j, hj⟩ := hbodd
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
  exact ⟨by omega, by omega, hjump⟩

/-- **Counting crossings before a prime power is lost
(`long243:res:epochenergy`).**

Let the orbit satisfy the reduced recurrences of the section with
`2 * |ẽ n| < u n` from an index `s`, where `ẽ n = u n - w n`.  Let `p ≥ 3` be
prime, let `Q = p ^ l` divide `v s` with `Q ≥ 16`, put `L = p * Q / 2` and
assume `R s < L / 2`.  Assume `u t ≥ L` for some `t > s` and let `τ` be the
first such index.  Let `J` be the set of steps in `[s, τ)` that first cross at
least one odd multiple of `p` in `(L/2, L]`, and put
`X = ∑_{n ∈ J} (d n - 2)`.  Then every `n ∈ J` is a record step with
`h n = 1` and `d n ≥ 3`, and `p * Q ≤ (8p+8) * |J| + 4 * X + 8p`. -/
theorem epoch_energy_named_crossing_set
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ) (J : Finset ℕ)
    (hp : p.Prime)
    (hp3 : 3 ≤ p)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hcentre : ∀ n, s ≤ n → 2 * ((u n : ℤ) - (w n : ℤ)).natAbs < u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ)
    (hτfirst : ∀ n, s < n → n < τ → 2 * u n < p * p ^ l)
    (hJ : ∀ n, n ∈ J ↔ (s ≤ n ∧ n < τ ∧ ∃ b : ℕ, Odd b ∧ p ∣ b ∧
      p * p ^ l < 4 * b ∧ 2 * b ≤ p * p ^ l ∧
      b ≤ u (n + 1) ∧ ∀ j, s ≤ j → j < n → u (j + 1) < b)) :
    (∀ n ∈ J, runningMax u n < u (n + 1) ∧ hc n = 1 ∧ u n + 3 ≤ u (n + 1)) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  classical
  -- The paper's centring bound gives the module's slow-rise bound.
  have hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n := by
    intro n hn
    have h := hcentre n hn
    set k := ((u n : ℤ) - (w n : ℤ)).natAbs with hk
    rcases Int.natAbs_eq ((u n : ℤ) - (w n : ℤ)) with heq | heq <;> omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hl : 1 ≤ l := by
    by_contra hcon
    have hl0 : l = 0 := by omega
    rw [hl0, pow_zero] at hQ
    omega
  have hppos : 0 < p := by omega
  -- Every element of the named set is a clean record step with jump ≥ 3.
  have hstep : ∀ n ∈ J,
      runningMax u n < u (n + 1) ∧ hc n = 1 ∧ u n + 3 ≤ u (n + 1) := by
    intro n hn
    obtain ⟨hns, _hnτ, b, hbodd, hbp, hwin1, hwin2, hcross, hfirst⟩ := (hJ n).mp hn
    exact barrier_first_crossing_step a u v w hc p l s n b hp hpodd hl hred hvpos
      hw hwpos hnum hden hslow hprot hbodd hbp hwin1 hwin2 hRs hns hcross hfirst
  refine ⟨hstep, ?_⟩
  -- Each barrier supplies its own first-crossing step, which lies in `J`.
  obtain ⟨t, rfl⟩ : ∃ t, τ = t + 1 := ⟨τ - 1, by omega⟩
  have hts : s ≤ t := by omega
  have key : ∀ k ∈ barrierIdx (p ^ l), ∃ n, n ∈ J ∧
      u n < (2 * k + 1) * p ∧ (2 * k + 1) * p ≤ u (n + 1) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (mem_barrierIdx_iff hQ k).mp hk
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
    obtain ⟨n, hns, hnb, hnt, hnmin⟩ :
        ∃ n, s ≤ n ∧ (2 * k + 1) * p ≤ u (n + 1) ∧ n ≤ t ∧
          ∀ i, s ≤ i → i < n → u (i + 1) < (2 * k + 1) * p := by
      refine ⟨sInf {m | s ≤ m ∧ (2 * k + 1) * p ≤ u (m + 1)},
        (Nat.sInf_mem hexists).1, (Nat.sInf_mem hexists).2, Nat.sInf_le ⟨hts, hbu⟩, ?_⟩
      intro i his hi
      by_contra hcon
      have hle : sInf {m | s ≤ m ∧ (2 * k + 1) * p ≤ u (m + 1)} ≤ i :=
        Nat.sInf_le ⟨his, by omega⟩
      omega
    have hoddk : Odd (2 * k + 1) := ⟨k, by ring⟩
    have hodd : Odd ((2 * k + 1) * p) := hoddk.mul hpodd
    have hmem : n ∈ J := by
      refine (hJ n).mpr ⟨hns, by omega, (2 * k + 1) * p, hodd, ⟨2 * k + 1, by ring⟩,
        hb1, hb2, hnb, hnmin⟩
    have hbelow : u n < (2 * k + 1) * p := by
      rcases Nat.lt_or_ge s n with hlt | hge
      · obtain ⟨i, hi⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
        rw [hi]
        exact hnmin i (by omega) (by omega)
      · have h1 : u n ≤ runningMax u s := le_runningMax u hge
        omega
    exact ⟨n, hmem, hbelow, hnb⟩
  choose! f hfJ hflt hfge using key
  -- Fibrewise count of the barriers over their first-crossing steps.
  have hfib : (barrierIdx (p ^ l)).card
      = ∑ n ∈ J, ((barrierIdx (p ^ l)).filter (fun k => f k = n)).card :=
    Finset.card_eq_sum_card_fiberwise hfJ
  have hspace : ∀ n ∈ J,
      2 * p * ((barrierIdx (p ^ l)).filter (fun k => f k = n)).card
        ≤ 2 * p + (u (n + 1) - u n) := by
    intro n _
    refine fibre_card_le_spacing _ (fun k hk => ?_)
    rw [Finset.mem_filter] at hk
    obtain ⟨hkS, hkf⟩ := hk
    have h3 := hflt k hkS
    have h4 := hfge k hkS
    rw [hkf] at h3 h4
    exact ⟨h3, h4⟩
  have hsum1 : 2 * p * (barrierIdx (p ^ l)).card
      ≤ ∑ n ∈ J, (2 * p + (u (n + 1) - u n)) := by
    rw [hfib, Finset.mul_sum]
    exact Finset.sum_le_sum hspace
  have hd : ∀ n ∈ J, 2 * p + (u (n + 1) - u n)
      = (2 * p + 2) + (u (n + 1) - u n - 2) := by
    intro n hn
    have := (hstep n hn).2.2
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

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.mem_barrierIdx_iff
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.epoch_energy_named_crossing_set

end ErdosProblems.Erdos243.PaperCompleteR21
