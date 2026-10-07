import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Erdős #269: a block-radix irrationality criterion

This module isolates the arithmetic engine behind the irrationality of the
distinct-height sum `𝒟_{2,3,5}`, which is assembled in
`ErdosProblems.Erdos269.DistinctHeightIrrationality`.

A *block letter* is one of the five pairs `(b, μ)`

    (2, 1), (6, 3), (10, 3), (30, 13), (30, 9),

the radix and numerator of a dyadic block of type `∅`, `3`, `5`, `35`, `53`.
Given a word of block letters `(b a, μ a)`, put `P a = b 0 ⋯ b (a - 1)` and
consider the series `∑ a, μ a / P (a + 1)`.  Its normalised tails

    Y a = P a · ∑_{j ≥ a} μ j / P (j + 1)

satisfy `b a · Y a = μ a + Y (a + 1)` (`base_mul_tailState`).

* `tailState_ge`, `tailState_le`: if every three consecutive letters contain one
  with `5 ∣ b`, then `3/10 ≤ Y a ≤ 13/15`.
* `blockLetter_decode`: on `[3/10, 13/15]` the five affine maps
  `y ↦ (μ + y) / b` have pairwise disjoint images, so `Y a` determines the letter
  at `a`, and then `Y (a + 1) = b a · Y a - μ a`.
* `exists_int_mul_tailState`: if the sum is a rational `q`, every
  `q.den · Y a` is an integer; with the bounds, two tails coincide.
* `irrational_tsum_blockTerm`: hence a rational sum forces the letter word to be
  eventually periodic, and a word whose radices are not eventually periodic
  gives an irrational sum.
-/

namespace ErdosProblems.Erdos269.DistinctHeight235

open Finset Filter Topology

/-- The five admissible dyadic block letters `(b, μ)`: the block radix `b` and
the block numerator `μ` for the block types `∅`, `3`, `5`, `35`, `53`. -/
def BlockLetter (b μ : ℕ) : Prop :=
  (b = 2 ∧ μ = 1) ∨ (b = 6 ∧ μ = 3) ∨ (b = 10 ∧ μ = 3) ∨
    (b = 30 ∧ μ = 13) ∨ (b = 30 ∧ μ = 9)

theorem BlockLetter.two_le {b μ : ℕ} (h : BlockLetter b μ) : 2 ≤ b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

theorem BlockLetter.two_mul_le {b μ : ℕ} (h : BlockLetter b μ) : 2 * μ ≤ b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

/-- Partial radix products `P a = b 0 * b 1 * ⋯ * b (a - 1)`. -/
def radixProd (b : ℕ → ℕ) (a : ℕ) : ℕ :=
  ∏ j ∈ range a, b j

/-- The block term `μ a / P (a + 1)`. -/
noncomputable def blockTerm (b μ : ℕ → ℕ) (a : ℕ) : ℝ :=
  (μ a : ℝ) / (radixProd b (a + 1) : ℝ)

/-- The normalised tail `Y a = P a * ∑_{j ≥ a} μ j / P (j + 1)`. -/
noncomputable def tailState (b μ : ℕ → ℕ) (a : ℕ) : ℝ :=
  (radixProd b a : ℝ) * ∑' j, blockTerm b μ (j + a)

@[simp] theorem radixProd_zero (b : ℕ → ℕ) : radixProd b 0 = 1 := by
  simp [radixProd]

theorem radixProd_succ (b : ℕ → ℕ) (a : ℕ) :
    radixProd b (a + 1) = radixProd b a * b a := by
  simp [radixProd, prod_range_succ]

theorem radixProd_dvd_of_le (b : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    radixProd b m ∣ radixProd b n :=
  Dvd.intro _ (prod_range_mul_prod_Ico b h)

theorem blockTerm_nonneg (b μ : ℕ → ℕ) (a : ℕ) : 0 ≤ blockTerm b μ a := by
  unfold blockTerm
  positivity

section Letters

variable {b μ : ℕ → ℕ}

theorem radixProd_pos (hL : ∀ a, BlockLetter (b a) (μ a)) (a : ℕ) :
    0 < radixProd b a :=
  prod_pos fun j _ => lt_of_lt_of_le two_pos (hL j).two_le

theorem two_pow_mul_le_radixProd (hL : ∀ a, BlockLetter (b a) (μ a)) (a j : ℕ) :
    2 ^ j * radixProd b a ≤ radixProd b (j + a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show j + 1 + a = (j + a) + 1 by omega, radixProd_succ, pow_succ]
    calc 2 ^ j * 2 * radixProd b a = (2 ^ j * radixProd b a) * 2 := by ring
      _ ≤ radixProd b (j + a) * b (j + a) := Nat.mul_le_mul ih (hL (j + a)).two_le

/-- One block contributes at most half of its normalising product. -/
theorem radixProd_mul_blockTerm_le (hL : ∀ a, BlockLetter (b a) (μ a)) (a : ℕ) :
    (radixProd b a : ℝ) * blockTerm b μ a ≤ 1 / 2 := by
  have hP : (0 : ℝ) < radixProd b a := by exact_mod_cast radixProd_pos hL a
  have hb : (0 : ℝ) < b a := by exact_mod_cast lt_of_lt_of_le two_pos (hL a).two_le
  have h2 : 2 * (μ a : ℝ) ≤ b a := by exact_mod_cast (hL a).two_mul_le
  have hEq : (radixProd b a : ℝ) * blockTerm b μ a = (μ a : ℝ) / b a := by
    unfold blockTerm
    rw [radixProd_succ, Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hP.ne']
  rw [hEq, div_le_iff₀ hb]
  linarith

/-- The shifted block terms decay geometrically against the normaliser. -/
theorem radixProd_mul_blockTerm_shift_le (hL : ∀ a, BlockLetter (b a) (μ a)) (a j : ℕ) :
    (radixProd b a : ℝ) * blockTerm b μ (j + a) ≤ (1 / 2) ^ (j + 1) := by
  have hmul : (2 : ℝ) ^ j * radixProd b a ≤ radixProd b (j + a) := by
    exact_mod_cast two_pow_mul_le_radixProd hL a j
  have hterm := radixProd_mul_blockTerm_le hL (j + a)
  have hnn := blockTerm_nonneg b μ (j + a)
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have key : (2 : ℝ) ^ j * ((radixProd b a : ℝ) * blockTerm b μ (j + a)) ≤ 1 / 2 := by
    calc (2 : ℝ) ^ j * ((radixProd b a : ℝ) * blockTerm b μ (j + a))
        = ((2 : ℝ) ^ j * radixProd b a) * blockTerm b μ (j + a) := by ring
      _ ≤ (radixProd b (j + a) : ℝ) * blockTerm b μ (j + a) :=
          mul_le_mul_of_nonneg_right hmul hnn
      _ ≤ 1 / 2 := hterm
  have hpow : ((1 : ℝ) / 2) ^ (j + 1) = (1 / 2) / 2 ^ j := by
    rw [pow_succ, one_div_pow]
    ring
  rw [hpow, le_div_iff₀ h2j]
  linarith

theorem summable_blockTerm (hL : ∀ a, BlockLetter (b a) (μ a)) :
    Summable (blockTerm b μ) := by
  refine Summable.of_nonneg_of_le (blockTerm_nonneg b μ) (fun j => ?_)
    ((summable_geometric_two).mul_left (1 / 2))
  have h := radixProd_mul_blockTerm_shift_le hL 0 j
  simp only [radixProd_zero, Nat.cast_one, one_mul, add_zero] at h
  rw [pow_succ] at h
  show blockTerm b μ j ≤ 1 / 2 * (1 / 2) ^ j
  linarith

theorem summable_blockTerm_shift (hL : ∀ a, BlockLetter (b a) (μ a)) (a : ℕ) :
    Summable (fun j => blockTerm b μ (j + a)) :=
  (summable_nat_add_iff a).mpr (summable_blockTerm hL)

theorem tsum_tail_split (hL : ∀ a, BlockLetter (b a) (μ a)) (a : ℕ) :
    ∑' j, blockTerm b μ (j + a) =
      blockTerm b μ a + ∑' j, blockTerm b μ (j + (a + 1)) := by
  rw [(summable_blockTerm_shift hL a).tsum_eq_zero_add]
  simp only [zero_add]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show j + 1 + a = j + (a + 1) by omega]

/-- The exact radix recurrence `b a · Y a = μ a + Y (a + 1)`. -/
theorem base_mul_tailState (hL : ∀ a, BlockLetter (b a) (μ a)) (a : ℕ) :
    (b a : ℝ) * tailState b μ a = μ a + tailState b μ (a + 1) := by
  have hP : (radixProd b a : ℝ) ≠ 0 := by exact_mod_cast (radixProd_pos hL a).ne'
  have hb : (b a : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le two_pos (hL a).two_le).ne'
  have hterm : (radixProd b a : ℝ) * blockTerm b μ a = (μ a : ℝ) / b a := by
    unfold blockTerm
    rw [radixProd_succ, Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hP]
  unfold tailState
  rw [tsum_tail_split hL a, radixProd_succ, Nat.cast_mul, mul_add, hterm, mul_add,
    mul_comm (b a : ℝ) ((μ a : ℝ) / b a), div_mul_cancel₀ _ hb]
  ring

theorem tailState_nonneg (b μ : ℕ → ℕ) (a : ℕ) : 0 ≤ tailState b μ a := by
  unfold tailState
  exact mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun j => blockTerm_nonneg b μ _)

theorem tailState_le_one (hL : ∀ a, BlockLetter (b a) (μ a)) (a : ℕ) :
    tailState b μ a ≤ 1 := by
  have hgeom : Summable (fun j : ℕ => ((1 : ℝ) / 2) ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr summable_geometric_two
  have hsum : ∑' j : ℕ, ((1 : ℝ) / 2) ^ (j + 1) = 1 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_two]
    norm_num
  unfold tailState
  rw [← tsum_mul_left]
  calc ∑' j, (radixProd b a : ℝ) * blockTerm b μ (j + a)
      ≤ ∑' j : ℕ, ((1 : ℝ) / 2) ^ (j + 1) :=
        Summable.tsum_le_tsum (fun j => radixProd_mul_blockTerm_shift_le hL a j)
          ((summable_blockTerm_shift hL a).mul_left _) hgeom
    _ = 1 := hsum

theorem tailState_ge (hL : ∀ a, BlockLetter (b a) (μ a)) (a : ℕ) :
    3 / 10 ≤ tailState b μ a := by
  have hrec := base_mul_tailState hL a
  have hnn := tailState_nonneg b μ (a + 1)
  rcases hL a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] at hrec <;> push_cast at hrec <;> linarith

theorem tailState_le_step (hL : ∀ a, BlockLetter (b a) (μ a)) (a : ℕ) :
    tailState b μ a ≤ (1 + tailState b μ (a + 1)) / 2 := by
  have hrec := base_mul_tailState hL a
  have hnn := tailState_nonneg b μ (a + 1)
  rcases hL a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] at hrec <;> push_cast at hrec <;> linarith

theorem tailState_le_of_five_dvd (hL : ∀ a, BlockLetter (b a) (μ a)) (a : ℕ)
    (h5 : 5 ∣ b a) : tailState b μ a ≤ 7 / 15 := by
  have hrec := base_mul_tailState hL a
  have hle := tailState_le_one hL (a + 1)
  rcases hL a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1] at h5 <;> rw [h1, h2] at hrec <;> push_cast at hrec <;>
    first
      | (exfalso; omega)
      | linarith

/-- **The two-sided tail bound.**  If every three consecutive letters contain a
radix divisible by `5`, every normalised tail lies in `[3/10, 13/15]`. -/
theorem tailState_le (hL : ∀ a, BlockLetter (b a) (μ a))
    (hspace : ∀ a, 5 ∣ b a ∨ 5 ∣ b (a + 1) ∨ 5 ∣ b (a + 2)) (a : ℕ) :
    tailState b μ a ≤ 13 / 15 := by
  have s0 := tailState_le_step hL a
  have s1 : tailState b μ (a + 1) ≤ (1 + tailState b μ (a + 2)) / 2 :=
    tailState_le_step hL (a + 1)
  rcases hspace a with h | h | h
  · have := tailState_le_of_five_dvd hL a h
    linarith
  · have := tailState_le_of_five_dvd hL (a + 1) h
    linarith
  · have := tailState_le_of_five_dvd hL (a + 2) h
    linarith

end Letters

/-- **Separation.**  The images of `[3/10, 13/15]` under the five maps
`y ↦ (μ + y) / b` are pairwise disjoint, so the common value determines the
letter. -/
theorem blockLetter_decode {b₁ μ₁ b₂ μ₂ : ℕ} {v y₁ y₂ : ℝ}
    (h₁ : BlockLetter b₁ μ₁) (h₂ : BlockLetter b₂ μ₂)
    (hy₁ : 3 / 10 ≤ y₁) (hy₁' : y₁ ≤ 13 / 15) (hy₂ : 3 / 10 ≤ y₂) (hy₂' : y₂ ≤ 13 / 15)
    (e₁ : (b₁ : ℝ) * v = μ₁ + y₁) (e₂ : (b₂ : ℝ) * v = μ₂ + y₂) :
    b₁ = b₂ ∧ μ₁ = μ₂ := by
  rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  push_cast at e₁ e₂ <;>
  first
    | exact ⟨rfl, rfl⟩
    | (exfalso; linarith)

section Periodicity

variable {b μ : ℕ → ℕ}

/-- **Integrality.**  If the block series has a rational value `q`, every
normalised tail becomes an integer after multiplication by `q.den`: the finite
prefix is cleared by `P a` because `P (j + 1) ∣ P a` for `j < a`. -/
theorem exists_int_mul_tailState (hL : ∀ a, BlockLetter (b a) (μ a)) {q : ℚ}
    (hq : ∑' a, blockTerm b μ a = q) (a : ℕ) :
    ∃ z : ℤ, (q.den : ℝ) * tailState b μ a = z := by
  have hsplit := (summable_blockTerm hL).sum_add_tsum_nat_add a
  have hfin : ∃ n : ℕ, ∑ i ∈ range a, (radixProd b a : ℝ) * blockTerm b μ i = n := by
    refine ⟨∑ i ∈ range a, μ i * (radixProd b a / radixProd b (i + 1)), ?_⟩
    rw [Nat.cast_sum]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨c, hc⟩ := radixProd_dvd_of_le b (show i + 1 ≤ a from mem_range.mp hi)
    have hpos := radixProd_pos hL (i + 1)
    have hQ : (radixProd b (i + 1) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [hc, Nat.mul_div_cancel_left c hpos]
    unfold blockTerm
    push_cast
    rw [mul_comm ((radixProd b (i + 1) : ℝ) * (c : ℝ)), ← mul_assoc, div_mul_cancel₀ _ hQ]
  obtain ⟨n, hn⟩ := hfin
  have hnum : (q.den : ℝ) * (q : ℝ) = q.num := by exact_mod_cast Rat.den_mul_eq_num q
  refine ⟨(radixProd b a : ℤ) * q.num - (q.den : ℤ) * n, ?_⟩
  have htail : tailState b μ a =
      (radixProd b a : ℝ) * q - ∑ i ∈ range a, (radixProd b a : ℝ) * blockTerm b μ i := by
    unfold tailState
    rw [← hq, ← hsplit, ← mul_sum]
    ring
  rw [htail, hn]
  push_cast
  linear_combination (radixProd b a : ℝ) * hnum

/-- **Return.**  Bounded tails with a common integral denominator take finitely
many values, so two distinct tails coincide. -/
theorem exists_lt_tailState_eq (hL : ∀ a, BlockLetter (b a) (μ a)) {K : ℕ} (hK : 0 < K)
    (hint : ∀ a, ∃ z : ℤ, (K : ℝ) * tailState b μ a = z) :
    ∃ a a', a < a' ∧ tailState b μ a = tailState b μ a' := by
  choose z hz using hint
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmaps : ∀ a ∈ range (K + 2), z a ∈ Icc (0 : ℤ) K := by
    intro a _
    have h0 := tailState_nonneg b μ a
    have h1 := tailState_le_one hL a
    have hlo : (0 : ℝ) ≤ z a := by
      rw [← hz a]
      exact mul_nonneg hKR.le h0
    have hhi : (z a : ℝ) ≤ K := by
      rw [← hz a]
      exact mul_le_of_le_one_right hKR.le h1
    rw [mem_Icc]
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hcard : (Icc (0 : ℤ) K).card < (range (K + 2)).card := by
    rw [Int.card_Icc, card_range]
    omega
  obtain ⟨x, -, y, -, hxy, hzxy⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun a ha => hmaps a ha)
  have heq : tailState b μ x = tailState b μ y := by
    have h := hz x
    rw [hzxy, ← hz y] at h
    exact mul_left_cancel₀ hKR.ne' h
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, y, h, heq⟩
  · exact ⟨y, x, h, heq.symm⟩

/-- **Determinism.**  Equal tails have equal futures: the decoded letters agree
at every later block. -/
theorem tailState_shift_eq (hL : ∀ a, BlockLetter (b a) (μ a))
    (hspace : ∀ a, 5 ∣ b a ∨ 5 ∣ b (a + 1) ∨ 5 ∣ b (a + 2)) {a a' : ℕ}
    (h : tailState b μ a = tailState b μ a') (j : ℕ) :
    tailState b μ (a + j) = tailState b μ (a' + j) ∧ b (a + j) = b (a' + j) := by
  have decode : ∀ n n', tailState b μ n = tailState b μ n' → b n = b n' ∧ μ n = μ n' := by
    intro n n' hn
    have e₁ := base_mul_tailState hL n
    have e₂ := base_mul_tailState hL n'
    rw [hn] at e₁
    exact blockLetter_decode (hL n) (hL n') (tailState_ge hL _) (tailState_le hL hspace _)
      (tailState_ge hL _) (tailState_le hL hspace _) e₁ e₂
  have hY : ∀ j, tailState b μ (a + j) = tailState b μ (a' + j) := by
    intro j
    induction j with
    | zero => simpa using h
    | succ j ih =>
      obtain ⟨hb, hm⟩ := decode _ _ ih
      have e₁ := base_mul_tailState hL (a + j)
      have e₂ := base_mul_tailState hL (a' + j)
      rw [ih, hb, hm] at e₁
      have : tailState b μ (a + j + 1) = tailState b μ (a' + j + 1) := by linarith
      simpa [Nat.add_assoc] using this
  exact ⟨hY j, (decode _ _ (hY j)).1⟩

/-- **The block-radix irrationality criterion.**  Let every letter be admissible,
let every three consecutive radices include a multiple of `5`, and suppose the
radix word is not eventually periodic.  Then `∑ a, μ a / P (a + 1)` is
irrational. -/
theorem irrational_tsum_blockTerm (hL : ∀ a, BlockLetter (b a) (μ a))
    (hspace : ∀ a, 5 ∣ b a ∨ 5 ∣ b (a + 1) ∨ 5 ∣ b (a + 2))
    (hnp : ∀ a d, 0 < d → ∃ j, b (a + d + j) ≠ b (a + j)) :
    Irrational (∑' a, blockTerm b μ a) := by
  rintro ⟨q, hq⟩
  obtain ⟨a, a', haa', heq⟩ :=
    exists_lt_tailState_eq hL q.den_pos (exists_int_mul_tailState hL hq.symm)
  obtain ⟨j, hj⟩ := hnp a (a' - a) (by omega)
  apply hj
  rw [show a + (a' - a) + j = a' + j by omega]
  exact (tailState_shift_eq hL hspace heq j).2.symm

end Periodicity

end ErdosProblems.Erdos269.DistinctHeight235
