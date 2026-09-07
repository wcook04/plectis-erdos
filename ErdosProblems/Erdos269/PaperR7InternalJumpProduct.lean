import ErdosProblems.Erdos269.PaperR7ActualOrbit

/-!
# Round 7: the product over the actual internal prime-power jumps

The long record prints a product over pairs `(p,e)`, not just the four-case
alphabet. Each channel's unique exponent is selected from its actual existence
predicate. The list need not be sorted: multiplication of natural numbers is
commutative. Its exact membership theorem excludes spurious or missing jumps.

Validation: authored, not compiled. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped Classical in
noncomputable def channelJumpList (p a : ℕ) : List (ℕ × ℕ) :=
  if h : ∃ e, DyadicInternalPower p a e then [(p, Classical.choose h)] else []

noncomputable def internalJumps235 (a : ℕ) : List (ℕ × ℕ) :=
  channelJumpList 3 a ++ channelJumpList 5 a

theorem mem_channelJumpList {p a q e : ℕ} (hp : 2 ≤ p) :
    (q, e) ∈ channelJumpList p a ↔ q = p ∧ DyadicInternalPower q a e := by
  classical
  by_cases h : ∃ f, DyadicInternalPower p a f
  · simp only [channelJumpList, dif_pos h, List.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, Classical.choose_spec h⟩
    · rintro ⟨rfl, he⟩
      exact ⟨rfl, dyadicInternalPower_exponent_unique hp he (Classical.choose_spec h)⟩
  · simp only [channelJumpList, dif_neg h, List.not_mem_nil, false_iff, not_and]
    intro hqp
    subst q
    exact fun he => h ⟨e, he⟩

theorem mem_internalJumps235 (a p e : ℕ) :
    (p, e) ∈ internalJumps235 a ↔
      (p = 3 ∨ p = 5) ∧ DyadicInternalPower p a e := by
  rw [internalJumps235, List.mem_append,
    mem_channelJumpList (by norm_num : 2 ≤ (3 : ℕ)),
    mem_channelJumpList (by norm_num : 2 ≤ (5 : ℕ))]
  tauto

/-- No channel repeats in the list; every listed exponent is the actual one. -/
theorem internalJumpPrimes_nodup (a : ℕ) :
    ((internalJumps235 a).map Prod.fst).Nodup := by
  classical
  by_cases h3 : ∃ e, DyadicInternalPower 3 a e <;>
    by_cases h5 : ∃ e, DyadicInternalPower 5 a e <;>
    simp [internalJumps235, channelJumpList, h3, h5]

theorem internalJump_product (a : ℕ) :
    dyadicBlockBase235 a = 2 * ((internalJumps235 a).map Prod.fst).prod := by
  classical
  by_cases h3 : ∃ e, DyadicInternalPower 3 a e <;>
    by_cases h5 : ∃ e, DyadicInternalPower 5 a e <;>
    simp [internalJumps235, channelJumpList, dyadicBlockBase235, h3, h5]

/-- All equalities, alphabet alternatives and both bounds in long `res:dyadic-alphabet`. -/
theorem long_dyadic_alphabet (a : ℕ) :
    (dyadicBlockBase235 a : ℚ) =
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) /
        (threePrimeHeight 2 3 5 (2 ^ a) : ℚ) ∧
    dyadicBlockBase235 a = 2 * ((internalJumps235 a).map Prod.fst).prod ∧
    (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
      dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30) ∧
    2 ≤ dyadicBlockBase235 a ∧ dyadicBlockBase235 a ≤ 30 :=
  ⟨radix_eq_height_ratio a, internalJump_product a, dyadicBlockBase235_cases a,
    dyadicBlockBase235_mem_interval a⟩

end ErdosProblems.Erdos269.PaperR7
