import ErdosProblems.Skip.D3

/-! Adversarial verification scratch file for `ErdosProblems/Skip/D3.lean`. -/

namespace Erdos249257
namespace SkipD3

-- axioms of every theorem in D3
#print axioms largestSkipLateAt_of_late_skip
#print axioms lateZone_dichotomy
#print axioms threeCofOdd_late
#print axioms threeCofEven_late
#print axioms halfCof_not_late
#print axioms largestSkipLateAt_of_threeCofOdd_skip
#print axioms largestSkipLateAt_of_threeCofEven_skip
#print axioms late_divisor_cofactor_three
#print axioms wgt_eq
#print axioms seamWeights_eq_wgt
#print axioms gb_eq
#print axioms gb_length
#print axioms seamGreedyWord_apply
#print axioms mem_support_iff
#print axioms notMem_support_of_gb_false
#print axioms isLargestFalseRank_of_rowChk
#print axioms largestSkipLateAt_of_rowChk
#print axioms lateAt_102
#print axioms lateAt_103
#print axioms lateAt_104
#print axioms lateAt_123
#print axioms lateAt_124
#print axioms lateAt_125
#print axioms lateAt_165
#print axioms lateAt_166
#print axioms lateAt_167
#print axioms lateAt_315
#print axioms lateAt_316
#print axioms lateAt_317
#print axioms lateAt_546
#print axioms lateAt_547
#print axioms lateAt_548
#print axioms lateAt_630
#print axioms lateAt_631
#print axioms lateAt_632
#print axioms lateAt_1113
#print axioms lateAt_1114
#print axioms lateAt_1115
#print axioms cofSkip_103_69
#print axioms lateAt_103_via_cofactor
#print axioms cofSkip_124_83
#print axioms lateAt_124_via_cofactor
#print axioms cofSkip_166_111
#print axioms lateAt_166_via_cofactor
#print axioms cofSkip_316_211
#print axioms lateAt_316_via_cofactor
#print axioms cofSkip_547_365
#print axioms lateAt_547_via_cofactor
#print axioms cofSkip_631_421
#print axioms lateAt_631_via_cofactor
#print axioms cofSkip_1114_743
#print axioms lateAt_1114_via_cofactor
#print axioms hcof_fails_101
#print axioms cofSkip_123_62
#print axioms hcof_fails_122
#print axioms cofSkip_165_83
#print axioms hcof_fails_164
#print axioms cofSkip_315_158
#print axioms hcof_fails_314
#print axioms hcof_fails_545
#print axioms hcof_fails_629
#print axioms cofSkip_1113_557
#print axioms hcof_fails_1112
#print axioms skipDichotomy_survivors
#print axioms hcof_fails_survivors
#print axioms threeCof_skipDichotomy
#print axioms lateCofRanks_subset_cofRanks
#print axioms lateCofRanks_cases
#print axioms lateCofRanks_ge
#print axioms lateCofRanks_disjoint
#print axioms lateCofFloor_le_lateCofPulse
#print axioms lateTotalFloor_le_belowPulse
#print axioms lateCofFloor_le_two
#print axioms lateTotalFloor_le_eleven
#print axioms twelve_le_lateStep
#print axioms lateStep_zero
#print axioms lateRun_eq_zero_of_le
#print axioms twelve_le_lateRun_of_le
#print axioms lateRun_ne_zero_of_twelve_le_four
#print axioms lateRun_20_four
#print axioms lateRun_314_four
#print axioms lateRun_545_four
#print axioms lateRun_629_four
#print axioms lateRun_1112_four
#print axioms lateRun_101_three
#print axioms lateRun_122_three
#print axioms lateRun_164_three
#print axioms lateRun_twenty_ne_zero
#print axioms lateRun_314_ne_zero
#print axioms lateRun_545_ne_zero
#print axioms lateRun_629_ne_zero
#print axioms lateRun_1112_ne_zero
#print axioms lateCofFloor_add_period
#print axioms lateTotalFloor_add_period
#print axioms lateRun_add_period
#print axioms lateRun_add_mul_period
#print axioms lateRun_progression_ne_zero
#print axioms lateRatchet_survivor_count
#print axioms seamGreedyUnboundedSkippedRanksAlong_of_lateAlong
#print axioms half_mem_of_lateAlong
#print axioms half_mem_of_lateCofinal
#print axioms eventually_threeCof_selected_or_half_mem

/-! ### Numerical probes: is the "87 survive at every depth" prose a theorem? -/

-- survivors of the late-only ratchet at depth 12
#eval ((List.range 2730).filter (fun D => lateRun D 12 ≠ 0)).length
-- how many of those have budget >= 12 at depth 12 (the only proved escape route)
#eval ((List.range 2730).filter (fun D => 12 ≤ lateRun D 12)).length
-- minimum budget among depth-12 survivors
#eval ((List.range 2730).filter (fun D => lateRun D 12 ≠ 0)).map (fun D => lateRun D 12)
        |>.foldl min 999
-- do any survivors die later?
#eval ((List.range 2730).filter (fun D => lateRun D 24 ≠ 0)).length
#eval ((List.range 2730).filter (fun D => lateRun D 40 ≠ 0)).length
-- the seven classes: which survive the late-only ratchet?
#eval [101, 122, 164, 314, 545, 629, 1112].map (fun D => (D, lateRun D 12))

/-! ### Is the left disjunct of the global dichotomy plausibly false?
Count rows s in [200,1200) where the three-cofactor is actually skipped. -/

#eval Id.run do
  let mut skipped := 0
  let mut total := 0
  for s in [200:400] do
    if s % 3 == 1 then
      let m := (2 * s + 1) / 3
      total := total + 1
      if (gb s).getD (m - 2) false = false then skipped := skipped + 1
    else if s % 3 == 2 then
      let m := 2 * (s + 1) / 3
      total := total + 1
      if (gb s).getD (m - 2) false = false then skipped := skipped + 1
  return (skipped, total)

/-! ### How much of AngleB2's conditional theorem is actually vacuous?
`hcof D` asks that every cofactor rank at rows `D+1, D+2, D+3` is selected.
Count the `D` in `[60,400)` where that holds. -/

def cofRanksL (s : ℕ) : List ℕ :=
  if s % 6 == 1 then [(2 * s + 1) / 3, (s + 1) / 2]
  else if s % 6 == 2 then [2 * (s + 1) / 3]
  else if s % 6 == 3 then [(s + 1) / 2]
  else if s % 6 == 4 then [(2 * s + 1) / 3]
  else if s % 6 == 5 then [2 * (s + 1) / 3, (s + 1) / 2]
  else []

def hcofHolds (D : ℕ) : Bool :=
  [D + 1, D + 2, D + 3].all (fun s => (cofRanksL s).all (fun m => (gb s).getD (m - 2) false))

#eval ((List.range 340).map (fun i => 60 + i)).filter hcofHolds |>.length
#eval ((List.range 340).map (fun i => 60 + i)).length
-- sanity: the seven classes must all fail hcof (matches `hcof_fails_survivors`)
#eval [101, 122, 164, 314, 545, 629, 1112].map hcofHolds
-- sanity: the file's own certified largest-false-ranks, recomputed
#eval [(102,101),(123,121),(165,162),(315,314),(546,545),(630,628),(1113,1111)].map
        (fun p => rowChk p.1 p.2)

/-! ### Is the hypothesis of `half_mem_of_lateCofinal` as hard as its conclusion?

The corpus already has
`half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse`.  A false terminal
bit at row `p+1` is exactly a skipped *top* rank `p`, which is trivially the
largest false rank of that row and is late.  So the converse of
`half_mem_of_lateCofinal` holds too, i.e. its hypothesis is *equivalent* to its
conclusion. -/

open Filter HalfCylinderIntegerGreedy in
theorem lateCofinal_of_half_mem (h : (1 / 2 : ℝ) ∈ mersenneAchievementSet) :
    ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ LargestSkipLateAt s := by
  obtain ⟨p, hp5, hp, hterm⟩ :=
    half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse.mp h
  intro N
  obtain ⟨j, hj⟩ := (Filter.tendsto_atTop.mp hp N).exists
  refine ⟨p j + 1, by omega, ⟨p j, ⟨by have := hp5 j; omega, by omega, ?_, ?_⟩, by
    have := hp5 j; omega⟩⟩
  · intro hmem
    obtain ⟨i, hi, hrank⟩ := mem_seamWordSupport_iff.mp hmem
    have hidx : i = ⟨p j - 2, by have := hp5 j; omega⟩ := by
      apply Fin.ext
      have := hp5 j
      simp only
      omega
    rw [hidx] at hi
    have hterm' := hterm j
    rw [SeamRowWord.terminal] at hterm'
    rw [hterm'] at hi
    exact Bool.false_ne_true hi
  · intro e hde hes
    omega

/-- Hence `half_mem_of_lateCofinal` is one direction of an equivalence: cofinally
many late rows *is* the `#257` endpoint, not a route to it. -/
theorem lateCofinal_iff_half_mem :
    (∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧ LargestSkipLateAt s) ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  ⟨half_mem_of_lateCofinal, lateCofinal_of_half_mem⟩

#print axioms lateCofinal_of_half_mem
#print axioms lateCofinal_iff_half_mem

end SkipD3
end Erdos249257
