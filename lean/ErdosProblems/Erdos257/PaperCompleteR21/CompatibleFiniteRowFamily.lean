import Erdos249257.BooleanMobiusGlobalRepair

/-!
Paper-form restatement of `record:257bm-c3` (`a257_front.tex:4006`),
"A compatible family of finite supports", from the long Erdős #257 manuscript
`paper/reasoning-parts/erdos257/a257_front.tex`.

The paper's bit family `b_{n,d}` with `b_{n+1,d} = b_{n,d}` whenever `2d ≤ n`
is the tree's `BooleanMobiusGlobalRepairTrajectory`; its rows
`E_n = {d : 2 ≤ d ≤ n, b_{n,d} = 1}` and
`D_n = E_n ∩ {2,…,⌊n/2⌋}` are `globalRepairStageSupport` and
`globalRepairLowerSupport`.  `Q`, `S`, `H` and `c_D` are as in
`record:257bm-d2`/`record:257bm-d3`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257

/-! ## The upper-half row value as a dyadic sum -/

private lemma signedDyadicValue_natCast' (y : List ℕ) :
    signedDyadicValue (List.map (fun b : ℕ ↦ (b : ℤ)) y) =
      ((Nat.ofDigits 2 y : ℕ) : ℤ) := by
  induction y with
  | nil => simp [signedDyadicValue]
  | cons b y ih =>
      simp only [List.map_cons, signedDyadicValue, ih, Nat.ofDigits_cons]
      push_cast
      ring

private lemma ofDigits_upperSuffixWord (a : ℕ → ℕ) (R M : ℕ) :
    Nat.ofDigits 2 (upperSuffixWord a R M) =
      ∑ i ∈ Finset.range (M - R), a (M - i) * 2 ^ i := by
  unfold upperSuffixWord
  generalize M - R = m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih,
        Finset.sum_range_succ, List.map_cons, List.map_nil,
        Nat.ofDigits_singleton, List.length_map, List.length_range]
      ring

private lemma upper_word_value (T : BooleanMobiusGlobalRepairTrajectory)
    {n : ℕ} (hn : 2 ≤ n) :
    Nat.ofDigits 2 (globalRepairUpperWord T n) =
      ∑ d ∈ (globalRepairStageSupport T.bit n).filter (fun d ↦ n / 2 < d),
        2 ^ (n - d) := by
  classical
  have hword : Nat.ofDigits 2 (globalRepairUpperWord T n) =
      ∑ i ∈ Finset.range (n - n / 2),
        (if T.bit n (n - i) = true then 2 ^ i else 0) := by
    rw [globalRepairUpperWord, ofDigits_upperSuffixWord]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases h : T.bit n (n - i) = true <;> simp [h]
  have himg : Finset.Ioc (n / 2) n =
      (Finset.range (n - n / 2)).image (fun i ↦ n - i) := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨n - d, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  have hre : ∑ i ∈ Finset.range (n - n / 2),
        (if T.bit n (n - i) = true then 2 ^ i else 0) =
      ∑ d ∈ Finset.Ioc (n / 2) n,
        (if T.bit n d = true then 2 ^ (n - d) else 0) := by
    rw [himg, Finset.sum_image
      (by intro x hx y hy hxy
          simp only [Finset.coe_range, Set.mem_Iio] at hx hy
          have hxy' : n - x = n - y := hxy
          omega)]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp only [Finset.mem_range] at hi
    have hii : n - (n - i) = i := by omega
    rw [hii]
  have hset : (Finset.Ioc (n / 2) n).filter (fun d ↦ T.bit n d = true) =
      (globalRepairStageSupport T.bit n).filter (fun d ↦ n / 2 < d) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc, mem_globalRepairStageSupport]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h2, h3⟩, h1⟩
    · rintro ⟨⟨_, h2, h3⟩, h4⟩
      exact ⟨⟨h4, h2⟩, h3⟩
  rw [hword, hre, ← Finset.sum_filter, hset]

/-! ## `record:257bm-c3` -/

/-- "The bit condition fixes coordinate `d` from row `2d` onward." -/
theorem paper_compatible_bit_stable
    (T : BooleanMobiusGlobalRepairTrajectory) {d n : ℕ} (hdn : 2 * d ≤ n) :
    T.bit n d = T.bit (2 * d) d :=
  T.bit_stable hdn

/-- Paper display of `record:257bm-c3`: the feasibility package of the
compatible-limit construction is exactly the four conditions on the finite
rows, required for every `n ≥ 2`:

* `2^(max{c_{D_n}(n)-1,0}) - 1 ≤ S(D_n,1,n-1)`;
* `∑_{d ∈ E_n, d > ⌊n/2⌋} 2^(n-d) = H(D_n,1,n)`;
* `H(D_n,1,n) < 2^(n-⌊n/2⌋)`;
* `Q(E_n,n) = 2^(n-1) - 1`.

The maximum in the first line is natural-number subtraction at
`c_{D_n}(n) = 0`. -/
theorem paper_compatible_finite_row_conditions
    (T : BooleanMobiusGlobalRepairTrajectory) :
    GlobalBooleanMobiusRepairFeasible T ↔
      ((∀ n : ℕ, 2 ≤ n →
          2 ^ (endpointDivisorContribution
                (globalRepairLowerSupport T.bit n) n - 1) - 1 ≤
            localBinarySuffix (globalRepairLowerSupport T.bit n) 1 (n - 1)) ∧
       (∀ n : ℕ, 2 ≤ n →
          ((∑ d ∈ (globalRepairStageSupport T.bit n).filter
                (fun d ↦ n / 2 < d), 2 ^ (n - d) : ℕ) : ℤ) =
            localRepairInteger (globalRepairLowerSupport T.bit n) 1 n) ∧
       (∀ n : ℕ, 2 ≤ n →
          localRepairInteger (globalRepairLowerSupport T.bit n) 1 n <
            ((2 ^ (n - n / 2) : ℕ) : ℤ)) ∧
       (∀ n : ℕ, 2 ≤ n →
          localPrefixQuotient (globalRepairStageSupport T.bit n) n =
            2 ^ (n - 1) - 1)) := by
  classical
  have hbridge : ∀ n : ℕ, 2 ≤ n →
      (signedDyadicValue
          (List.map (fun b : ℕ ↦ (b : ℤ)) (globalRepairUpperWord T n)) =
        localRepairInteger (globalRepairLowerSupport T.bit n) 1 n ↔
      ((∑ d ∈ (globalRepairStageSupport T.bit n).filter
            (fun d ↦ n / 2 < d), 2 ^ (n - d) : ℕ) : ℤ) =
        localRepairInteger (globalRepairLowerSupport T.bit n) 1 n) := by
    intro n hn
    rw [signedDyadicValue_natCast', upper_word_value T hn]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun n hn ↦ (hbridge n hn).1 (h2 n hn), h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun n hn ↦ (hbridge n hn).2 (h2 n hn), h3, h4⟩

/-- "The first condition implies that the integer in the next two lines is
nonnegative." -/
theorem paper_compatible_first_condition_gives_nonneg
    (T : BooleanMobiusGlobalRepairTrajectory)
    (hbound : ∀ n : ℕ, 2 ≤ n →
      2 ^ (endpointDivisorContribution (globalRepairLowerSupport T.bit n) n - 1)
          - 1 ≤
        localBinarySuffix (globalRepairLowerSupport T.bit n) 1 (n - 1))
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ localRepairInteger (globalRepairLowerSupport T.bit n) 1 n :=
  globalRepairInteger_nonneg T hbound hn

/-- "The rows therefore have a prescribed common limit": through its frozen
half, each row agrees with the diagonal limit support. -/
theorem paper_compatible_rows_agree_with_limit
    (T : BooleanMobiusGlobalRepairTrajectory) {n d : ℕ} (hd : d ≤ n / 2) :
    d ∈ globalRepairStageSupport T.bit n ↔ d ∈ globalRepairLimitSupport T :=
  globalRepairStageSupport_agrees_limit_of_le_half T hd

#print axioms paper_compatible_rows_agree_with_limit
#print axioms paper_compatible_bit_stable
#print axioms paper_compatible_finite_row_conditions
#print axioms paper_compatible_first_condition_gives_nonneg

end ErdosProblems.Erdos257.PaperCompleteR21
