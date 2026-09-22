import Erdos249257.HalfCutLocator

/-! Generalizes the existing HalfCutLocator half-target straddle proof;
its prefix induction does not depend on the target being one half. -/
namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257

theorem straddle_agrees_greedy {t : ℝ}
    {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix t u d) :
    ∀ n : ℕ, 0 < n → n ≤ d →
      (n ∈ u ↔ n ∈ greedyMersenneSupport t) := by
  induction d generalizing u with
  | zero =>
      intro n hn hnd
      omega
  | succ d ih =>
      have hparent := hu.erase_top
      have hagreeParent := ih hparent
      intro n hn hnd
      by_cases htopIndex : n = d + 1
      · subst n
        have hprefix :
            mersenneSupportPrefix
                (greedyMersenneSupport t) d =
              positiveMersenneSupportValue
                (↑(u.erase (d + 1)) : Set ℕ) :=
          mersenneSupportPrefix_eq_coe_finset hparent.mem_bounds
            (fun m hm hmd => (hagreeParent m hm hmd).symm)
        have hgreedy :=
          greedyMersenne_prefix_add_remainder t d
        change t =
            mersenneSupportPrefix
                (greedyMersenneSupport t) d +
              greedyMersenneRemainder t d at hgreedy
        by_cases htopMem : d + 1 ∈ u
        · constructor
          · intro _
            rw [succ_mem_greedyMersenneSupport_iff]
            have hnot : d + 1 ∉ u.erase (d + 1) :=
              Finset.notMem_erase _ _
            have hvalue :
                positiveMersenneSupportValue (↑u : Set ℕ) =
                  mersenneWeight (d + 1) +
                    positiveMersenneSupportValue
                      (↑(u.erase (d + 1)) : Set ℕ) := by
              calc
                positiveMersenneSupportValue (↑u : Set ℕ) =
                    positiveMersenneSupportValue
                      (↑(insert (d + 1) (u.erase (d + 1))) : Set ℕ) :=
                  congrArg
                    (fun v : Finset ℕ =>
                      positiveMersenneSupportValue (↑v : Set ℕ))
                    (Finset.insert_erase htopMem).symm
                _ = mersenneWeight (d + 1) +
                      positiveMersenneSupportValue
                        (↑(u.erase (d + 1)) : Set ℕ) :=
                  positiveMersenneSupportValue_insert hnot
            linarith [hu.value_le, hvalue]
          · intro _
            exact htopMem
        · constructor
          · exact fun h => (htopMem h).elim
          · intro hselected
            have htake :=
              (succ_mem_greedyMersenneSupport_iff t d).1 hselected
            have herase : u.erase (d + 1) = u :=
              Finset.erase_eq_of_notMem htopMem
            rw [herase] at hprefix
            have hgap := mersenneTail_lt_weight (Nat.succ_pos d)
            linarith [hu.le_value_add_tail]
      · have hnd : n ≤ d := by omega
        have hagree := hagreeParent n hn hnd
        simpa [Finset.mem_erase, htopIndex] using hagree


/-- Literal finite internal gap over a positive finite prefix. -/
def InternalMersenneGap (x : ℝ) : Prop :=
  ∃ (D : Finset ℕ) (m : ℕ), 1 ≤ m ∧
    (∀ n ∈ D, 0 < n ∧ n < m) ∧
    positiveMersenneSupportValue (D : Set ℕ)+mersenneTail m < x ∧
    x < positiveMersenneSupportValue (D : Set ℕ)+mersenneWeight m

theorem internal_gap_excludes_membership {x : ℝ} (h : InternalMersenneGap x) :
    x ∉ mersenneAchievementSet := by
  obtain ⟨D, m, hm, hD, hlo, hhi⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hb : ∀ n ∈ D, 0 < n ∧ n ≤ d := by
    intro n hn; have := hD n hn; omega
  have hs : IsStraddlePrefix x D d := by
    refine ⟨hb, ?_, ?_⟩
    · linarith [mersenneTail_nonneg (d+1)]
    · have ht := mersenneTail_eq_weight_add d
      linarith [mersenneTail_nonneg (d+1)]
  have hag := straddle_agrees_greedy hs
  rintro ⟨A, hA0, hv⟩
  have heq : greedyMersenneSupport x = A := by
    rw [hv, greedySupport_supportValue_eq A hA0]
  have hp := mersenneSupportPrefix_eq_coe_finset (A := A) hb
    (fun n hn hnd ↦ by rw [← heq]; exact (hag n hn hnd).symm)
  exact (positiveMersenneSupportValue_ne_of_rank_gap
    (by rw [hp]; exact hlo) (by rw [hp]; exact hhi)) hv.symm

theorem general_target_gap_iff {x : ℝ} (hx : 0 ≤ x)
    (hE : x ≤ erdosBorweinMersenneConstant) :
    x ∉ mersenneAchievementSet ↔ InternalMersenneGap x := by
  constructor
  · intro hnot
    by_contra hgap
    apply hnot
    apply mem_mersenneAchievementSet_of_straddle_all_depths
    intro d
    induction d with
    | zero =>
      refine ⟨∅, by simp, ?_, ?_⟩
      · simpa [positiveMersenneSupportValue] using hx
      · simpa [positiveMersenneSupportValue, erdosBorweinMersenneConstant] using hE
    | succ d ih =>
      obtain ⟨D, hD⟩ := ih
      rcases isStraddlePrefix_step_trichotomy hD with h | h | h
      · exact ⟨D, h⟩
      · exact ⟨insert (d+1) D, h⟩
      · exfalso
        apply hgap
        refine ⟨D, d+1, by omega, ?_, h.1, h.2⟩
        intro n hn
        have := hD.mem_bounds n hn
        omega
  · exact internal_gap_excludes_membership

/-- Both endpoints of every positive finite-prefix gap are achievable. -/
theorem internal_gap_endpoints (D : Finset ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hD : ∀ n ∈ D, 0 < n ∧ n < m) :
    (positiveMersenneSupportValue (D : Set ℕ)+mersenneTail m) ∈ mersenneAchievementSet ∧
    (positiveMersenneSupportValue (D : Set ℕ)+mersenneWeight m) ∈ mersenneAchievementSet := by
  classical
  constructor
  · let A : Set ℕ := (D : Set ℕ) ∪ Set.Ioi m
    have ha0 : 0 ∉ A := by
      rintro (h | h)
      · have := (hD 0 h).1; omega
      · change m < 0 at h; omega
    have hp : mersenneSupportPrefix A m = positiveMersenneSupportValue (D : Set ℕ) := by
      apply mersenneSupportPrefix_eq_coe_finset
      · intro n hn; have := hD n hn; exact ⟨this.1, this.2.le⟩
      · intro n hn hnm
        change (n ∈ D ∨ m < n) ↔ n ∈ D
        constructor
        · rintro (h | h)
          · exact h
          · exact False.elim ((not_lt_of_ge hnm) h)
        · exact Or.inl
    have hs : positiveMersenneSupportSuffix A m = mersenneTail m := by
      unfold positiveMersenneSupportSuffix mersenneTail
      apply tsum_congr
      intro k
      rw [Set.indicator_of_mem (show m+k+1 ∈ A from Or.inr (by change m < m+k+1; omega))]
    refine ⟨A, ha0, ?_⟩
    have he := positiveMersenneSupportValue_eq_prefix_add_suffix A m
    change positiveMersenneSupportValue A = mersenneSupportPrefix A m + positiveMersenneSupportSuffix A m at he
    rw [hp, hs] at he
    exact he.symm
  · have hn : m ∉ D := by intro h; have := (hD m h).2; omega
    refine ⟨(↑(insert m D) : Set ℕ), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_insert]
      rintro (h | h)
      · omega
      · have := (hD 0 h).1; omega
    · rw [positiveMersenneSupportValue_insert hn]
      ring

/-- Entire general-target finite-gap observation, including achievable endpoints. -/
theorem paper_general_target_gap :
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x)) ∧
    (∀ (D : Finset ℕ) (m : ℕ), 1 ≤ m →
      (∀ n ∈ D, 0 < n ∧ n < m) →
      (positiveMersenneSupportValue (D : Set ℕ)+mersenneTail m) ∈ mersenneAchievementSet ∧
      (positiveMersenneSupportValue (D : Set ℕ)+mersenneWeight m) ∈ mersenneAchievementSet) :=
  ⟨fun _ hx hE ↦ general_target_gap_iff hx hE, internal_gap_endpoints⟩

/-- Both clauses of the long paper's greedy-survival theorem. -/
theorem paper_greedy_survival :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x)) :=
  ⟨mem_mersenneAchievementSet_iff_greedy_survival,
    fun _ hx hE ↦ general_target_gap_iff hx hE⟩

#print axioms paper_general_target_gap
#print axioms general_target_gap_iff
#print axioms paper_greedy_survival
end ErdosProblems.Erdos257.PaperCompleteR20
