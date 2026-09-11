import Erdos249257.HalfCylinderIntegerGreedy

/-!
# Concrete adapter for the carry-safe seam recurrence

Production implementation of the finite seam word, its concrete
`PerturbedFamily`, the actual adjacent cut, and the identification of the
abstract next residual with `seamIntegerGreedyRemainder`.
-/

namespace Erdos249257.HalfCylinderIntegerGreedy

open HalfCarryReachability
open scoped BigOperators

/-! ## Canonical finite seam words -/

abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool

namespace SeamRowWord

def toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false

def toList {s : ℕ} (b : SeamRowWord s) : List Bool :=
  List.ofFn b

def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)

@[simp] theorem toList_ofList
    {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    toList (ofList bits hlen) = bits := by
  unfold toList ofList
  rw [← List.ofFn_congr hlen bits.get, List.ofFn_get]

theorem toList_injective {s : ℕ} :
    Function.Injective (toList : SeamRowWord s → List Bool) := by
  intro a b hab
  exact List.ofFn_injective hab

end SeamRowWord

theorem seamWeightsFrom_length_eq (s d : ℕ) :
    (seamWeightsFrom s d).length = s - d := by
  by_cases hds : d < s
  · rw [seamWeightsFrom_eq_cons hds, List.length_cons,
      seamWeightsFrom_length_eq s (d + 1)]
    omega
  · rw [seamWeightsFrom_eq_nil (by omega)]
    simp
    omega
termination_by s - d
decreasing_by omega

@[simp] theorem seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  unfold seamWeights
  exact seamWeightsFrom_length_eq s 2

theorem seamWeightsFrom_eq_ofFn
    {s d : ℕ} (hds : d ≤ s) :
    seamWeightsFrom s d =
      List.ofFn (fun i : Fin (s - d) =>
        truncatedMersenneWeight s (d + i)) := by
  by_cases hlt : d < s
  · have hsub : s - d = (s - (d + 1)) + 1 := by omega
    rw [seamWeightsFrom_eq_cons hlt,
      seamWeightsFrom_eq_ofFn (s := s) (d := d + 1) (by omega),
      hsub, List.ofFn_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    congr 1
    simp only [Fin.val_succ]
    omega
  · have hsd : s = d := by omega
    subst d
    simp [seamWeightsFrom_eq_nil]
termination_by s - d
decreasing_by omega

theorem seamWeights_eq_ofFn {s : ℕ} (hs : 2 ≤ s) :
    seamWeights s =
      List.ofFn (fun i : Fin (s - 2) =>
        truncatedMersenneWeight s (i + 2)) := by
  unfold seamWeights
  simpa [Nat.add_comm] using
    (seamWeightsFrom_eq_ofFn (s := s) (d := 2) hs)

theorem weightedBoolSum_ofFn
    {n : ℕ} (w : Fin n → ℕ) (b : Fin n → Bool) :
    weightedBoolSum (List.ofFn w) (List.ofFn b) =
      ∑ i : Fin n, if b i then w i else 0 := by
  induction n with
  | zero => simp [weightedBoolSum]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, Fin.sum_univ_succ]
      by_cases hb : b 0
      · simp [weightedBoolSum, hb, ih]
      · simp [weightedBoolSum, hb, ih]

theorem weightedBoolSum_toList_eq_wordWeightSum
    {s : ℕ} (hs : 2 ≤ s) (b : SeamRowWord s) :
    weightedBoolSum (seamWeights s) b.toList =
      wordWeightSum s b.toNatWord := by
  rw [seamWeights_eq_ofFn hs]
  unfold SeamRowWord.toList
  rw [weightedBoolSum_ofFn]
  unfold wordWeightSum
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have his : (i : ℕ) + 2 < s := by omega
  simp [SeamRowWord.toNatWord, his]

/-! ## Concrete perturbed family -/

def seamPerturbedFamily (s : ℕ) (hs : 3 ≤ s) :
    PerturbedFamily (SeamRowWord s) where
  oldSum b := wordWeightSum s b.toNatWord
  pulse b := wordPulse s b.toNatWord
  gap := 2 ^ (s + 1)
  pulseCap := 2 * (s - 2)
  gap_pos := by positivity
  pulse_le b := wordPulse_le s b.toNatWord
  oldSum_injective := by
    intro a b hab
    change wordWeightSum s a.toNatWord = wordWeightSum s b.toNatWord at hab
    apply SeamRowWord.toList_injective
    by_contra hne
    have hsep := weightedBoolSum_separated
      (gap := 2 ^ (s + 1)) (weights := seamWeights s)
      (by positivity) (seamWeights_gapDominates (by omega))
      (a := a.toList) (b := b.toList)
      (by simp [SeamRowWord.toList])
      (by simp [SeamRowWord.toList]) hne
    rw [weightedBoolSum_toList_eq_wordWeightSum (by omega),
      weightedBoolSum_toList_eq_wordWeightSum (by omega)] at hsep
    have hgapPos : 0 < 2 ^ (s + 1) := by positivity
    omega
  separated := by
    intro a b hab
    change wordWeightSum s a.toNatWord < wordWeightSum s b.toNatWord at hab
    have hne : a ≠ b := by
      intro heq
      subst b
      omega
    have hlistne : a.toList ≠ b.toList := by
      intro heq
      exact hne (SeamRowWord.toList_injective heq)
    have hsep := weightedBoolSum_separated
      (gap := 2 ^ (s + 1)) (weights := seamWeights s)
      (by positivity) (seamWeights_gapDominates (by omega))
      (a := a.toList) (b := b.toList)
      (by simp [SeamRowWord.toList])
      (by simp [SeamRowWord.toList]) hlistne
    rw [weightedBoolSum_toList_eq_wordWeightSum (by omega),
      weightedBoolSum_toList_eq_wordWeightSum (by omega)] at hsep
    rcases hsep with hsep | hsep
    · exact hsep
    · omega
  pulseCap_lt_three_gap := by
    have hpow := two_mul_add_four_lt_two_pow_succ hs
    omega

theorem seamPerturbedFamily_newSum_eq
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    (seamPerturbedFamily s hs).newSum b =
      wordWeightSum (s + 1)
        (extendWord s false b.toNatWord) := by
  rw [wordWeightSum_succ hs b.toNatWord false]
  rfl

theorem seamPulseCap_lt_gap {s : ℕ} (hs : 3 ≤ s) :
    (seamPerturbedFamily s hs).pulseCap <
      (seamPerturbedFamily s hs).gap := by
  dsimp [seamPerturbedFamily]
  have hpow := two_mul_add_four_lt_two_pow_succ hs
  omega

/-! ## The actual adjacent cut -/

def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  SeamRowWord.ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])

@[simp] theorem seamGreedyWord_toList (s : ℕ) :
    (seamGreedyWord s).toList =
      integerGreedyBits (seamWeights s) (seamSubsetTarget s) := by
  simp [seamGreedyWord]

def seamHeadThreeWord (s : ℕ) : SeamRowWord s :=
  fun i => decide ((i : ℕ) < 3)

theorem wordWeightSum_seamHeadThreeWord
    {s : ℕ} (hs : 5 ≤ s) :
    wordWeightSum s (seamHeadThreeWord s).toNatWord =
      truncatedMersenneWeight s 2 +
        truncatedMersenneWeight s 3 +
        truncatedMersenneWeight s 4 := by
  unfold wordWeightSum
  symm
  calc
    truncatedMersenneWeight s 2 +
          truncatedMersenneWeight s 3 +
          truncatedMersenneWeight s 4 =
        ∑ i ∈ Finset.range 3,
          if (seamHeadThreeWord s).toNatWord (i + 2) then
            truncatedMersenneWeight s (i + 2)
          else 0 := by
            norm_num [Finset.sum_range_succ, SeamRowWord.toNatWord,
              seamHeadThreeWord, show 2 < s by omega,
              show 3 < s by omega, show 4 < s by omega]
    _ = ∑ i ∈ Finset.range (s - 2),
          if (seamHeadThreeWord s).toNatWord (i + 2) then
            truncatedMersenneWeight s (i + 2)
          else 0 := by
            apply Finset.sum_subset
            · intro i hi
              exact Finset.mem_range.mpr (by
                have := Finset.mem_range.mp hi
                omega)
            · intro i hi hnot
              have hi3 : 3 ≤ i := by
                exact Nat.not_lt.mp (fun hlt =>
                  hnot (Finset.mem_range.mpr hlt))
              have his : i + 2 < s := by
                have := Finset.mem_range.mp hi
                omega
              simp [SeamRowWord.toNatWord, seamHeadThreeWord, his, hi3]

theorem seamHeadThreeWord_above_target
    {s : ℕ} (hs : 5 ≤ s) :
    seamSubsetTarget s <
      wordWeightSum s (seamHeadThreeWord s).toNatWord := by
  have h2 := scaled_lt_truncatedMersenneWeight_cast_add_one
    (s := s) (d := 2) (by norm_num)
  have h3 := scaled_lt_truncatedMersenneWeight_cast_add_one
    (s := s) (d := 3) (by norm_num)
  have h4 := scaled_lt_truncatedMersenneWeight_cast_add_one
    (s := s) (d := 4) (by norm_num)
  have hsum :
      (19 / 35 : ℝ) * (4 : ℝ) ^ s <
        (truncatedMersenneWeight s 2 : ℝ) +
          (truncatedMersenneWeight s 3 : ℝ) +
          (truncatedMersenneWeight s 4 : ℝ) + 3 := by
    norm_num [mersenneWeight] at h2 h3 h4
    nlinarith
  have hthree : 3 ≤ 2 ^ s := by
    have hp : 2 ^ 2 ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hp ⊢
    omega
  have htopNat : seamSubsetTarget s + 3 ≤ 2 ^ (2 * s - 1) := by
    unfold seamSubsetTarget
    have hp : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have htop :
      ((2 ^ (2 * s - 1) : ℕ) : ℝ) = (4 : ℝ) ^ s / 2 := by
    push_cast
    have hfour : (4 : ℝ) ^ s = (2 : ℝ) ^ (2 * s) := by
      calc
        (4 : ℝ) ^ s = ((2 : ℝ) ^ 2) ^ s := by norm_num
        _ = (2 : ℝ) ^ (2 * s) := by rw [pow_mul]
    have hpowSucc :
        (2 : ℝ) ^ (2 * s) = (2 : ℝ) ^ (2 * s - 1) * 2 := by
      calc
        (2 : ℝ) ^ (2 * s) = (2 : ℝ) ^ ((2 * s - 1) + 1) := by
          congr 1
          omega
        _ = (2 : ℝ) ^ (2 * s - 1) * 2 := by rw [pow_succ]
    rw [hfour]
    rw [hpowSucc]
    ring
  have htarget :
      ((seamSubsetTarget s + 3 : ℕ) : ℝ) <
        (19 / 35 : ℝ) * (4 : ℝ) ^ s := by
    have htopCast :
        ((seamSubsetTarget s + 3 : ℕ) : ℝ) ≤
          ((2 ^ (2 * s - 1) : ℕ) : ℝ) := by
      exact_mod_cast htopNat
    rw [htop] at htopCast
    have hpow : 0 < (4 : ℝ) ^ s := by positivity
    nlinarith
  have hcast :
      ((seamSubsetTarget s + 3 : ℕ) : ℝ) <
        ((truncatedMersenneWeight s 2 +
          truncatedMersenneWeight s 3 +
          truncatedMersenneWeight s 4 + 3 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using htarget.trans hsum
  have hnat :
      seamSubsetTarget s + 3 <
        truncatedMersenneWeight s 2 +
          truncatedMersenneWeight s 3 +
          truncatedMersenneWeight s 4 + 3 := by
    exact_mod_cast hcast
  rw [wordWeightSum_seamHeadThreeWord hs]
  omega

theorem exists_seamWord_minimal_above
    {s : ℕ} (hs : 5 ≤ s) :
    ∃ a : SeamRowWord s,
      seamSubsetTarget s <
          (seamPerturbedFamily s (by omega)).oldSum a ∧
        ∀ x : SeamRowWord s,
          seamSubsetTarget s <
              (seamPerturbedFamily s (by omega)).oldSum x →
            (seamPerturbedFamily s (by omega)).oldSum a ≤
              (seamPerturbedFamily s (by omega)).oldSum x := by
  classical
  let F := seamPerturbedFamily s (by omega)
  let candidates := (Finset.univ : Finset (SeamRowWord s)).filter
    (fun x => seamSubsetTarget s < F.oldSum x)
  have hhead : seamSubsetTarget s < F.oldSum (seamHeadThreeWord s) := by
    simpa [F, seamPerturbedFamily] using seamHeadThreeWord_above_target hs
  have hnonempty : candidates.Nonempty := by
    refine ⟨seamHeadThreeWord s, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhead⟩
  obtain ⟨a, ha, hmin⟩ := candidates.exists_min_image F.oldSum hnonempty
  refine ⟨a, (Finset.mem_filter.mp ha).2, ?_⟩
  intro x hx
  exact hmin x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)

noncomputable def seamAboveWord (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord s :=
  Classical.choose (exists_seamWord_minimal_above hs)

theorem seamAboveWord_strict
    {s : ℕ} (hs : 5 ≤ s) :
    seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) :=
  (Classical.choose_spec (exists_seamWord_minimal_above hs)).1

theorem seamAboveWord_minimal
    {s : ℕ} (hs : 5 ≤ s) (x : SeamRowWord s)
    (hx : seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum x) :
    (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) ≤
      (seamPerturbedFamily s (by omega)).oldSum x :=
  (Classical.choose_spec (exists_seamWord_minimal_above hs)).2 x hx

noncomputable def seamAdjacentCut (s : ℕ) (hs : 5 ≤ s) :
    (seamPerturbedFamily s (by omega)).AdjacentCut
      (seamSubsetTarget s) where
  below := seamGreedyWord s
  above := seamAboveWord s hs
  below_admissible := by
    have hadm := integerGreedyBits_admissible
      (seamWeights s) (seamSubsetTarget s)
    rw [← seamGreedyWord_toList s,
      weightedBoolSum_toList_eq_wordWeightSum (by omega)] at hadm
    exact hadm
  below_maximal := by
    intro x hx
    have hx' :
        weightedBoolSum (seamWeights s) x.toList ≤ seamSubsetTarget s := by
      rw [weightedBoolSum_toList_eq_wordWeightSum (by omega)]
      exact hx
    have hmax := integerGreedyBits_maximal
      (gap := 2 ^ (s + 1)) (by positivity)
      (seamWeights_gapDominates (by omega))
      (bits := x.toList)
      (by simp [SeamRowWord.toList]) hx'
    rw [← seamGreedyWord_toList s,
      weightedBoolSum_toList_eq_wordWeightSum (by omega),
      weightedBoolSum_toList_eq_wordWeightSum (by omega)] at hmax
    exact hmax
  above_strict := seamAboveWord_strict hs
  above_minimal := seamAboveWord_minimal hs

@[simp] theorem seamAdjacentCut_remainder
    {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).remainder =
      seamIntegerGreedyRemainder s := by
  unfold PerturbedFamily.AdjacentCut.remainder seamIntegerGreedyRemainder
  change seamSubsetTarget s -
      wordWeightSum s (seamGreedyWord s).toNatWord = _
  rw [← weightedBoolSum_toList_eq_wordWeightSum (by omega),
    seamGreedyWord_toList]
  rfl

noncomputable local instance adjacentCutSuccessorCarriesDecidable
    {α : Type*} {F : PerturbedFamily α} {C : ℕ}
    (K : F.AdjacentCut C) : Decidable K.successorCarries :=
  Classical.propDecidable _

/-! ## The concrete next word -/

namespace SeamRowWord

def extend {s : ℕ} (b : SeamRowWord s) (beta : Bool) :
    SeamRowWord (s + 1) :=
  fun i => if h : (i : ℕ) < s - 2 then b ⟨i, h⟩ else beta

def dropTerminal {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord (s + 1)) :
    SeamRowWord s :=
  fun i => b ⟨i, by omega⟩

def terminal {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord (s + 1)) : Bool :=
  b ⟨s - 2, by omega⟩

@[simp] theorem dropTerminal_extend
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) (beta : Bool) :
    dropTerminal hs (extend b beta) = b := by
  funext i
  simp [dropTerminal, extend, i.isLt]

@[simp] theorem terminal_extend
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) (beta : Bool) :
    terminal hs (extend b beta) = beta := by
  simp [terminal, extend]

theorem extend_dropTerminal_terminal
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord (s + 1)) :
    extend (dropTerminal hs b) (terminal hs b) = b := by
  funext i
  by_cases hi : (i : ℕ) < s - 2
  · simp [extend, dropTerminal, hi]
  · have hilast : (i : ℕ) = s - 2 := by omega
    have hiFin : i = ⟨s - 2, by omega⟩ := Fin.ext hilast
    rw [hiFin]
    simp [extend, terminal]

theorem toNatWord_extend
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) (beta : Bool) :
    (extend b beta).toNatWord =
      extendWord s beta b.toNatWord := by
  funext d
  by_cases hds : d = s
  · subst d
    have hs2 : 2 ≤ s := by omega
    simp [toNatWord, extend, extendWord, hs2]
  · by_cases hold : 2 ≤ d ∧ d < s
    · have hnew : 2 ≤ d ∧ d < s + 1 := ⟨hold.1, by omega⟩
      have hindex : d - 2 < s - 2 := by omega
      simp [toNatWord, extendWord, extend, hds, hold, hnew, hindex]
    · have hnew : ¬(2 ≤ d ∧ d < s + 1) := by
        intro h
        apply hold
        exact ⟨h.1, by omega⟩
      unfold toNatWord
      rw [dif_neg hnew]
      simp [extendWord, hds, hold]

end SeamRowWord

theorem seamAdjacentCut_newCapacity
    {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).newCapacity = seamSubsetTarget (s + 1) := by
  unfold PerturbedFamily.AdjacentCut.newCapacity
  dsimp [seamPerturbedFamily]
  rw [seamSubsetTarget_succ (by omega)]

@[simp] theorem seamAdjacentCut_terminalWeight
    {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).terminalWeight = 2 ^ (s + 2) + 4 := by
  unfold PerturbedFamily.AdjacentCut.terminalWeight
  dsimp [seamPerturbedFamily]
  rw [show 2 * 2 ^ (s + 1) = 2 ^ (s + 2) by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
    ring]

theorem wordWeightSum_rowWord_extend
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) (beta : Bool) :
    wordWeightSum (s + 1) (b.extend beta).toNatWord =
      (seamPerturbedFamily s hs).newSum b +
        if beta then 2 ^ (s + 2) + 4 else 0 := by
  rw [SeamRowWord.toNatWord_extend hs,
    wordWeightSum_succ hs b.toNatWord beta]
  rfl

theorem seamPrefixChoice_admissible
    {s : ℕ} (hs : 5 ≤ s) :
    let K := seamAdjacentCut s hs
    (seamPerturbedFamily s (by omega)).newSum K.prefixChoice ≤
      K.newCapacity := by
  classical
  dsimp only
  by_cases hcarry : (seamAdjacentCut s hs).successorCarries
  · rw [PerturbedFamily.AdjacentCut.prefixChoice, if_pos hcarry]
    exact ((seamAdjacentCut s hs).above_newSum_le_capacity_iff).2 hcarry
  · rw [PerturbedFamily.AdjacentCut.prefixChoice, if_neg hcarry]
    exact (seamAdjacentCut s hs).below_newSum_le_capacity
      (seamPulseCap_lt_gap (by omega))

noncomputable def seamCutNextWord (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord (s + 1) := by
  classical
  let K := seamAdjacentCut s hs
  exact K.prefixChoice.extend
    (decide (K.terminalWeight ≤ K.prefixRemainder))

theorem seamCutNextWord_sum
    {s : ℕ} (hs : 5 ≤ s) :
    wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord =
      (seamPerturbedFamily s (by omega)).newSum
          (seamAdjacentCut s hs).prefixChoice +
        if (seamAdjacentCut s hs).terminalWeight ≤
            (seamAdjacentCut s hs).prefixRemainder then
          (seamAdjacentCut s hs).terminalWeight else 0 := by
  classical
  let K := seamAdjacentCut s hs
  change wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord =
    (seamPerturbedFamily s (by omega)).newSum K.prefixChoice +
      if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight else 0
  rw [show seamCutNextWord s hs =
      K.prefixChoice.extend
        (decide (K.terminalWeight ≤ K.prefixRemainder)) by
    rfl]
  rw [wordWeightSum_rowWord_extend (by omega)]
  by_cases hterminal : K.terminalWeight ≤ K.prefixRemainder
  · simp [K, seamAdjacentCut_terminalWeight hs]
  · simp [K]

theorem seamCutNextWord_admissible
    {s : ℕ} (hs : 5 ≤ s) :
    wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord ≤
      seamSubsetTarget (s + 1) := by
  classical
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hp : F.newSum K.prefixChoice ≤ K.newCapacity := by
    simpa [F, K] using seamPrefixChoice_admissible hs
  have hrem := K.prefixRemainder_eq_capacity_sub_choice
  have hfill :
      F.newSum K.prefixChoice + K.prefixRemainder = K.newCapacity := by
    rw [hrem, Nat.add_sub_of_le hp]
  have hsum := seamCutNextWord_sum hs
  change wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord =
    F.newSum K.prefixChoice +
      if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight else 0 at hsum
  have hcap := seamAdjacentCut_newCapacity hs
  by_cases hterminal : K.terminalWeight ≤ K.prefixRemainder
  · rw [if_pos hterminal] at hsum
    rw [hsum, ← hcap]
    calc
      F.newSum K.prefixChoice + K.terminalWeight ≤
          F.newSum K.prefixChoice + K.prefixRemainder :=
        Nat.add_le_add_left hterminal _
      _ = K.newCapacity := hfill
  · rw [if_neg hterminal] at hsum
    rw [hsum, ← hcap]
    exact hp

theorem seamCut_nextRemainder_eq_target_sub_sum
    {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).nextRemainder =
      seamSubsetTarget (s + 1) -
        wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord := by
  classical
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hp : F.newSum K.prefixChoice ≤ K.newCapacity := by
    simpa [F, K] using seamPrefixChoice_admissible hs
  have hrem := K.prefixRemainder_eq_capacity_sub_choice
  have hsum := seamCutNextWord_sum hs
  change wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord =
    F.newSum K.prefixChoice +
      if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight else 0 at hsum
  have hcap := seamAdjacentCut_newCapacity hs
  change K.nextRemainder =
    seamSubsetTarget (s + 1) -
      wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord
  unfold PerturbedFamily.AdjacentCut.nextRemainder
  by_cases hterminal : K.terminalWeight ≤ K.prefixRemainder
  · rw [if_pos hterminal] at hsum ⊢
    rw [hsum, ← hcap]
    rw [hrem, Nat.sub_sub]
  · rw [if_neg hterminal] at hsum ⊢
    rw [hsum, ← hcap]
    omega

theorem terminalWeight_le_newSum_gap
    {s : ℕ} (hs : 5 ≤ s) {x y : SeamRowWord s}
    (hxy :
      (seamPerturbedFamily s (by omega)).oldSum x <
        (seamPerturbedFamily s (by omega)).oldSum y) :
    (seamPerturbedFamily s (by omega)).newSum x +
        (seamAdjacentCut s hs).terminalWeight ≤
      (seamPerturbedFamily s (by omega)).newSum y := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hsep := F.separated hxy
  have hpulse := F.pulse_le x
  have hpulseNonneg : 0 ≤ F.pulse y := Nat.zero_le _
  have hpow := two_mul_add_four_lt_two_pow_succ (by omega : 3 ≤ s)
  change F.newSum x + K.terminalWeight ≤ F.newSum y
  unfold PerturbedFamily.newSum PerturbedFamily.AdjacentCut.terminalWeight
  dsimp [F, K, seamPerturbedFamily] at hsep hpulse hpulseNonneg ⊢
  omega

theorem seamCutNextWord_maximal
    {s : ℕ} (hs : 5 ≤ s) {x : SeamRowWord (s + 1)}
    (hx : wordWeightSum (s + 1) x.toNatWord ≤
      seamSubsetTarget (s + 1)) :
    wordWeightSum (s + 1) x.toNatWord ≤
      wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord := by
  classical
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  let q : SeamRowWord s := x.dropTerminal (by omega)
  let beta : Bool := x.terminal (by omega)
  have hxsplit : q.extend beta = x := by
    simpa [q, beta] using
      (SeamRowWord.extend_dropTerminal_terminal (by omega) x)
  have hxsum : wordWeightSum (s + 1) x.toNatWord =
      F.newSum q + if beta then K.terminalWeight else 0 := by
    rw [← hxsplit, wordWeightSum_rowWord_extend (by omega)]
    by_cases hbeta : beta
    · simp [hbeta, F, K, seamAdjacentCut_terminalWeight hs]
    · simp [hbeta, F]
  have hcap : K.newCapacity = seamSubsetTarget (s + 1) :=
    seamAdjacentCut_newCapacity hs
  have hxcap :
      F.newSum q + (if beta then K.terminalWeight else 0) ≤
        K.newCapacity := by
    rw [hcap, ← hxsum]
    exact hx
  have hqadm : F.newSum q ≤ K.newCapacity := by
    have := hxcap
    omega
  have hqmax : F.newSum q ≤ F.newSum K.prefixChoice :=
    K.prefixChoice_maximal (seamPulseCap_lt_gap (by omega)) hqadm
  have hqold : F.oldSum q ≤ F.oldSum K.prefixChoice := by
    by_contra hnot
    have hlt : F.oldSum K.prefixChoice < F.oldSum q :=
      Nat.lt_of_not_ge hnot
    have hnewlt := F.newSum_strictMono hlt
    omega
  have hp : F.newSum K.prefixChoice ≤ K.newCapacity := by
    simpa [F, K] using seamPrefixChoice_admissible hs
  have hrem := K.prefixRemainder_eq_capacity_sub_choice
  have hnextsum := seamCutNextWord_sum hs
  change wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord =
    F.newSum K.prefixChoice +
      if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight else 0
    at hnextsum
  by_cases hterminal : K.terminalWeight ≤ K.prefixRemainder
  · rw [if_pos hterminal] at hnextsum
    rw [hxsum, hnextsum]
    by_cases hbeta : beta <;> simp [hbeta] <;> omega
  · rw [if_neg hterminal] at hnextsum
    rw [hxsum, hnextsum]
    by_cases hbeta : beta
    · simp only [hbeta, if_true]
      rcases hqold.eq_or_lt with heq | hlt
      · have hword : q = K.prefixChoice := F.oldSum_injective heq
        have hsumCapQ :
            F.newSum q + K.terminalWeight ≤ K.newCapacity := by
          simpa only [hbeta, if_true] using hxcap
        have hsumCap :
            F.newSum K.prefixChoice + K.terminalWeight ≤ K.newCapacity := by
          rw [← hword]
          exact hsumCapQ
        have hterminal' : K.terminalWeight ≤ K.prefixRemainder := by
          rw [hrem]
          exact Nat.le_sub_of_add_le (by
            simpa [Nat.add_comm] using hsumCap)
        exact False.elim (hterminal hterminal')
      · exact terminalWeight_le_newSum_gap hs hlt
    · simpa [hbeta, F]

theorem seamCutNextWord_eq_greedyWord_succ
    {s : ℕ} (hs : 5 ≤ s) :
    seamCutNextWord s hs = seamGreedyWord (s + 1) := by
  let Fnext := seamPerturbedFamily (s + 1) (by omega)
  apply Fnext.oldSum_injective
  change wordWeightSum (s + 1) (seamCutNextWord s hs).toNatWord =
    wordWeightSum (s + 1) (seamGreedyWord (s + 1)).toNatWord
  apply Nat.le_antisymm
  · have hcadm :
        weightedBoolSum (seamWeights (s + 1))
            (seamCutNextWord s hs).toList ≤
          seamSubsetTarget (s + 1) := by
      rw [weightedBoolSum_toList_eq_wordWeightSum (by omega)]
      exact seamCutNextWord_admissible hs
    have hmax := integerGreedyBits_maximal
      (gap := 2 ^ (s + 2)) (by positivity)
      (seamWeights_gapDominates (by omega))
      (C := seamSubsetTarget (s + 1))
      (bits := (seamCutNextWord s hs).toList)
      (by simp [SeamRowWord.toList])
      hcadm
    rw [← seamGreedyWord_toList (s + 1),
      weightedBoolSum_toList_eq_wordWeightSum (by omega),
      weightedBoolSum_toList_eq_wordWeightSum (by omega)] at hmax
    exact hmax
  · apply seamCutNextWord_maximal hs
    have hadm := integerGreedyBits_admissible
      (seamWeights (s + 1)) (seamSubsetTarget (s + 1))
    rw [← seamGreedyWord_toList (s + 1),
      weightedBoolSum_toList_eq_wordWeightSum (by omega)] at hadm
    exact hadm

@[simp] theorem seamAdjacentCut_nextRemainder
    {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).nextRemainder =
      seamIntegerGreedyRemainder (s + 1) := by
  rw [seamCut_nextRemainder_eq_target_sub_sum hs,
    seamCutNextWord_eq_greedyWord_succ hs]
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [← seamGreedyWord_toList (s + 1),
    weightedBoolSum_toList_eq_wordWeightSum (by omega)]

#print axioms seamPerturbedFamily_newSum_eq
#print axioms seamCutNextWord_eq_greedyWord_succ
#print axioms seamAdjacentCut_nextRemainder

end Erdos249257.HalfCylinderIntegerGreedy
