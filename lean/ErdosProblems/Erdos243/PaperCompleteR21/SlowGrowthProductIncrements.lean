import ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect
import ErdosProblems.Erdos243.PaperCompleteR11.QuantitativeRecordDichotomy

/-!
# Erdős 243: the slow-growth clause of `long243:res:strausbounded`

The theorem "bounded or slowly growing increments of the product ratio"
(`paper/reasoning-parts/erdos243/core.tex`, line 2265) has two clauses for a
strictly increasing positive integer sequence with `a_{n+1}/a_n² → 1` and
`∑ 1/a_n = p/q`, in terms of

`Q_n = (a_1 ⋯ a_{n-1} / a_n) (a_n²/a_{n+1} - 1)`:

* if `limsup Q_n < ∞` the sequence is eventually Sylvester;
* the same conclusion holds if `Q_n ≤ ((1-δ)/q) ℓ(a_1 ⋯ a_{n-1}/a_n)` for some
  `δ > 0` and all large `n`, where `ℓ(x) = log₂ log₂ max(4,x)`.

The first clause is `ErdosProblems.Erdos243.PaperCompleteR7.original_coordinate_bounded_defect`
(its `productDefect` is `Q_n` and `limsup Q_n < ∞` is carried as an eventual
upper bound); it is given a home by the axiom print at the end of this file.

This file supplies the second clause, `original_coordinate_slow_growth_defect`.
The paper's route is through Theorem `long243:res:slownegative`.  The proof
here uses the record coordinate directly, which removes the two asymptotic
steps of the written argument:

* `C_{n+1} = C_n - E_n` and `C_n ≤ H_n = max_{j ≤ n} C_j` give
  `H_{n+1} - H_n ≤ (-E_n)_+`, so a bound `(-E_n)_+ ≤ c ℓ(C_n)` with `c < 1`
  forces `Θ = limsup (H_{n+1} - H_n)/ℓ(H_n) ≤ c < 1`, and the record dichotomy
  `canonical_recordTheta_zero_or_gt_one` then gives `Θ = 0`, i.e. the eventual
  Sylvester recurrence.  This is `recordTheta_le_of_slow_negative` below,
  stated for an arbitrary exact orbit.
* the comparison `ℓ(C_n)/ℓ(P_n/a_n) → 1` of the written argument is replaced by
  the exact inequality `P_n/a_n ≤ C_n`, valid at every index because
  `C_n = q P_n x_n` with `x_n > 1/a_n` and `q ≥ 1`, together with monotonicity
  of `ℓ`.  Likewise the error `E_n + q Q_n = o(1)` is absorbed using `ℓ ≥ 1`
  rather than `ℓ(C_n) → ∞`.

Both the case `0 < δ < 1` and the case `δ ≥ 1` (where the hypothesis forces
`Q_n ≤ 0` eventually) are covered by the single statement, since only
`1 - δ < 1` is used.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open ErdosProblems.Erdos243
open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR11

/-- **The record-coefficient form of the slow negative part.**
For any exact orbit `C_{n+1} + D_n = a_n C_n` with centred error
`E_n = D_n - (a_n - 1) C_n`, an eventual bound `-E_n ≤ c ℓ(C_n)` with `c ≥ 0`
forces `Θ = recordTheta C ≤ c`.

The step is the paper's: `C_{n+1} = C_n - E_n`, and `C_n` never exceeds its own
running maximum, so a new record can overshoot the old one by at most `-E_n`;
`ℓ` is monotone, so `ℓ(C_n) ≤ ℓ(H_n)`. -/
theorem recordTheta_le_of_slow_negative
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ))
    (c : ℝ) (hc0 : 0 ≤ c) (N : ℕ)
    (hslow : ∀ n, N ≤ n → -((E n : ℤ) : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ)) :
    recordTheta C ≤ ((c : ℝ) : EReal) := by
  apply Filter.limsup_le_of_le (by isBoundedDefault)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCH : C n ≤ runningMax C n := le_runningMax C (le_refl n)
  have hCHR : ((C n : ℕ) : ℝ) ≤ ((runningMax C n : ℕ) : ℝ) := by exact_mod_cast hCH
  have hlH : (1 : ℝ) ≤ recordLogLog ((runningMax C n : ℕ) : ℝ) :=
    one_le_recordLogLog _
  have hlC : recordLogLog ((C n : ℕ) : ℝ) ≤ recordLogLog ((runningMax C n : ℕ) : ℝ) :=
    recordLogLog_mono hCHR
  have hmono : c * recordLogLog ((C n : ℕ) : ℝ) ≤
      c * recordLogLog ((runningMax C n : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hlC hc0
  have hRHS : (0 : ℝ) ≤ c * recordLogLog ((runningMax C n : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ recordLogLog ((runningMax C n : ℕ) : ℝ) := by linarith
    exact mul_nonneg hc0 this
  have key : ((runningMax C (n + 1) - runningMax C n : ℕ) : ℝ) ≤
      c * recordLogLog ((runningMax C n : ℕ) : ℝ) := by
    rw [runningMax_true_increment C n]
    by_cases h : C (n + 1) ≤ runningMax C n
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
      exact hRHS
    · have h' : runningMax C n ≤ C (n + 1) := (Nat.not_le.mp h).le
      rw [Nat.cast_sub h']
      have hzStep : ((C (n + 1) : ℕ) : ℤ) = ((C n : ℕ) : ℤ) - E n := by
        have h1 : ((C (n + 1) : ℕ) : ℤ) + ((D n : ℕ) : ℤ) =
            ((a n : ℕ) : ℤ) * ((C n : ℕ) : ℤ) := by exact_mod_cast hstep n
        rw [hE n]; linarith
      have hrStep : ((C (n + 1) : ℕ) : ℝ) = ((C n : ℕ) : ℝ) - ((E n : ℤ) : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hzStep
        push_cast at this ⊢
        linarith [this]
      rw [hrStep]
      have hslown := hslow n hn
      linarith
  have hpos : (0 : ℝ) < recordLogLog ((runningMax C n : ℕ) : ℝ) := by linarith
  have hchar : recordLogLogCharge C n ≤ c := by
    rw [recordLogLogCharge, div_le_iff₀ hpos]
    exact key
  exact_mod_cast hchar

/-- The paper's product ratio never exceeds the canonical numerator:
`P_n/a_n ≤ q P_n x_n = C_n`, because `x_n = ∑_{k ≥ n} 1/a_k > 1/a_n` and
`q ≥ 1`.  This replaces the asymptotic comparison `C_n ∼ q P_n/a_n` of the
written argument. -/
theorem prefix_ratio_le_canonicalNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (prefixProduct a n : ℝ) / (a n : ℝ) ≤
      ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) := by
  obtain ⟨hcpos, hdpos, hc, hd, hrep⟩ := canonical_integer_tail a hpos p q hq hs
  have han : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hpos n
  have hP : (0 : ℝ) < (prefixProduct a n : ℝ) := by
    exact_mod_cast prefixProduct_pos a hpos n
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have htpos : 0 < realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) :=
    realTail_pos _ hs.summable
      (fun k ↦ one_div_pos.mpr (by exact_mod_cast hpos k)) (n + 1)
  have hsplit : realTail (fun k ↦ 1 / (a k : ℝ)) n =
      1 / (a n : ℝ) + realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) :=
    realTail_step _ hs.summable n
  have hDcast : ((canonicalDenominator a q n : ℕ) : ℝ) =
      (q : ℝ) * (prefixProduct a n : ℝ) := by
    simp only [canonicalDenominator, Nat.cast_mul]
  have hr := hrep n
  rw [hDcast, hsplit] at hr
  have hexpand : (q : ℝ) * (prefixProduct a n : ℝ) *
      (1 / (a n : ℝ) + realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1)) =
      (q : ℝ) * ((prefixProduct a n : ℝ) / (a n : ℝ)) +
        (q : ℝ) * (prefixProduct a n : ℝ) *
          realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) := by
    field_simp
  rw [hexpand] at hr
  have hratio : (0 : ℝ) < (prefixProduct a n : ℝ) / (a n : ℝ) := div_pos hP han
  have hextra : (0 : ℝ) < (q : ℝ) * (prefixProduct a n : ℝ) *
      realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) :=
    mul_pos (mul_pos hqR hP) htpos
  nlinarith [hr, hratio, hextra, hq1]

/-- **The slow-growth clause of `long243:res:strausbounded`.**
Let `a₁ < a₂ < ⋯` be positive integers with `a_{n+1}/a_n² → 1` and
`∑ 1/a_n = p/q` with `q` a positive integer.  If for some `δ > 0` and all
large `n`

`Q_n ≤ ((1-δ)/q) ℓ(a_1 ⋯ a_{n-1} / a_n)`,  `ℓ(x) = log₂ log₂ max(4,x)`,

then `a_{n+1} = a_n² - a_n + 1` for all large `n`. -/
theorem original_coordinate_slow_growth_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (δ : ℝ) (hδ : 0 < δ)
    (hslow : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productDefect a n ≤ (1 - δ) / (q : ℝ) *
        recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ))) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  obtain ⟨κ, hκ0, hκ1, hκδ⟩ : ∃ κ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ 1 - δ ≤ κ :=
    ⟨max (1 - δ) 0, le_max_right _ _, max_lt (by linarith) one_pos,
      le_max_left _ _⟩
  obtain ⟨η, hη0, hηsum⟩ : ∃ η : ℝ, 0 < η ∧ κ + η < 1 :=
    ⟨(1 - κ) / 2, by linarith, by linarith⟩
  obtain ⟨N1, hN1⟩ := hslow
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have herror : Tendsto (fun n ↦
      ((centeredState (a n : ℤ) ((canonicalDenominator a q n : ℕ) : ℤ)
          ((canonicalNaturalNumerator a p q n : ℕ) : ℤ) : ℤ) : ℝ) +
        (q : ℝ) * productDefect a n) atTop (nhds 0) :=
    canonical_error_plus_productDefect_tendsto_zero a ha hpos p q hq hs hgrowth
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp herror η hη0
  obtain ⟨hcpos, hdpos, hc, hd, hrep⟩ := canonical_integer_tail a hpos p q hq hs
  have hkey : ∀ n, max N1 N2 ≤ n →
      -((centeredState (a n : ℤ) ((canonicalDenominator a q n : ℕ) : ℤ)
          ((canonicalNaturalNumerator a p q n : ℕ) : ℤ) : ℤ) : ℝ) ≤
        (κ + η) * recordLogLog ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) := by
    intro n hn
    have habs : |((centeredState (a n : ℤ) ((canonicalDenominator a q n : ℕ) : ℤ)
        ((canonicalNaturalNumerator a p q n : ℕ) : ℤ) : ℤ) : ℝ) +
        (q : ℝ) * productDefect a n| < η := by
      simpa only [Real.dist_eq, sub_zero] using
        hN2 n ((le_max_right N1 N2).trans hn)
    have hlow := (abs_lt.mp habs).1
    have hQ := hN1 n ((le_max_left N1 N2).trans hn)
    have hL1ge : (1 : ℝ) ≤ recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ)) :=
      one_le_recordLogLog _
    have hL2ge : (1 : ℝ) ≤
        recordLogLog ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) :=
      one_le_recordLogLog _
    have hL12 : recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ)) ≤
        recordLogLog ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) :=
      recordLogLog_mono (prefix_ratio_le_canonicalNumerator a hpos p q hq hs n)
    have hscaled : (q : ℝ) * productDefect a n ≤
        (1 - δ) * recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ)) := by
      calc (q : ℝ) * productDefect a n
          ≤ (q : ℝ) * ((1 - δ) / (q : ℝ) *
              recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ))) :=
            mul_le_mul_of_nonneg_left hQ hqR.le
        _ = (1 - δ) * recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ)) := by
            field_simp
    have hstep1 : (1 - δ) * recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ)) ≤
        κ * recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ)) :=
      mul_le_mul_of_nonneg_right hκδ (by linarith)
    have hstep2 : κ * recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ)) ≤
        κ * recordLogLog ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hL12 hκ0
    have hηL : η * 1 ≤ η * recordLogLog ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hL2ge hη0.le
    nlinarith [hlow, hscaled, hstep1, hstep2, hηL]
  have hTheta : recordTheta (canonicalNaturalNumerator a p q) ≤ ((κ + η : ℝ) : EReal) :=
    recordTheta_le_of_slow_negative a (canonicalNaturalNumerator a p q)
      (canonicalDenominator a q)
      (fun n ↦ centeredState (a n : ℤ) ((canonicalDenominator a q n : ℕ) : ℤ)
        ((canonicalNaturalNumerator a p q n : ℕ) : ℤ))
      hc (fun n ↦ rfl) (κ + η) (by linarith) (max N1 N2) hkey
  have hzero : recordTheta (canonicalNaturalNumerator a p q) = 0 := by
    rcases canonical_recordTheta_zero_or_gt_one a ha hpos p q hq hs hgrowth with
      h | h
    · exact h
    · exfalso
      have hlt : ((κ + η : ℝ) : EReal) < (1 : EReal) := by
        exact_mod_cast hηsum
      exact absurd (h.trans_le (hTheta.trans hlt.le)) (lt_irrefl _)
  obtain ⟨N, hN⟩ :=
    (canonical_recordTheta_eq_zero_iff a ha hpos p q hq hs hgrowth).mp hzero
  exact ⟨N, fun n hn ↦ by simpa only [sylvesterNext] using hN n hn⟩

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.recordTheta_le_of_slow_negative
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.prefix_ratio_le_canonicalNumerator
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.original_coordinate_slow_growth_defect
#print axioms ErdosProblems.Erdos243.PaperCompleteR7.original_coordinate_bounded_defect

end ErdosProblems.Erdos243.PaperCompleteR21
