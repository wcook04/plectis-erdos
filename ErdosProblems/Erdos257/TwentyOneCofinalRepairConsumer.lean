import Erdos257PeriodNoncollapse.BooleanMobiusCarry
import Erdos257PeriodNoncollapse.TwentyOneQuotientGreedy
import ErdosProblems.Erdos257.HalfCounterexampleFrontier

/-!
# Erdős #257: cofinal one-step repairs as the weakest live disproof producer

The deep audit `TwentyOneRepairSupplyDeepAudit.md` falsified the periodic
repair family `(CD120)`/`(M120R)`/`(PM120)` (first violation rank 5,686,680;
six violations by rank 20,000,002, concentrated on prime-cofactor columns),
while the global repair census stayed dense through the whole horizon.  This
module formalizes the producer at the weakest form that falsification leaves
standing: a single cofinal supply of one-step repairs,

`twentyOneGreedyDefect (N + 1) ≤ twentyOneGreedyDefect N`,

already refutes `UniversalMersenneSubseriesIrrationality`.

Mechanism.  On the non-membership branch the exact fatal-tail conservation
(`twentyOneGreedyDefect_geometricLower_of_not_mem`) forces an exponentially
growing lower bound `2^m * δ ≤ Q_m + 1` on the defect, hence eventually
`Q_m > m + 2`.  The exact defect recurrence plus the divisor-pair envelope
(`supportCoeff_le_two_mul_sqrt`) then force every late step to be a strict
increase, so late repairs cannot exist.  Contrapositively, cofinal repairs
force membership of `1/21`; the audited finite-support exclusion makes the
representing support infinite.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse

/-- One-step repair at the successor of `N`: the divisor load pays the doubled
defect plus the periodic floor bit, so the defect does not rise. -/
def TwentyOneOneStepRepairSucc (N : ℕ) : Prop :=
  (twentyOneGreedyDefect (N + 1) : ℤ) ≤ (twentyOneGreedyDefect N : ℤ)

/-- The corrected producer after the `(CD120)` falsification: repairs occur
beyond every cutoff.  No periodicity, no load identity, no defect bound. -/
def TwentyOneOneStepRepairCofinal : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ TwentyOneOneStepRepairSucc N

/-- Exponential beats quadratic: `e² ≤ 2^e` from `e = 4` onward. -/
theorem nat_pow_two_ge_sq : ∀ e : ℕ, 4 ≤ e → e * e ≤ 2 ^ e := by
  intro e he
  induction e with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n 4 with hn | hn
      · have hn3 : n = 3 := by omega
        subst hn3
        norm_num
      · have hp := ih hn
        refine le_trans (by nlinarith) ?_
        refine le_trans (by linarith) ?_
        rw [pow_succ]
        ring

/-- Twice the square root of `m` stays below `m + 1` for every positive `m`. -/
theorem two_mul_nat_sqrt_succ_le : ∀ N : ℕ, 2 * Nat.sqrt (N + 1) ≤ N + 2 := by
  intro N
  have hsqrt : Nat.sqrt (N + 1) ≤ N / 2 + 1 := by
    by_contra hcon
    rw [Nat.not_le] at hcon
    have hlt := Nat.sqrt_lt.mp hcon
    have hsplit : (N / 2 + 2) * (N / 2 + 2)
        = (N / 2) * (N / 2) + 4 * (N / 2) + 4 := by ring
    have hdm := Nat.mod_add_div N 2
    have hmodlt : N % 2 < 2 := Nat.mod_lt N (by decide)
    omega
  calc 2 * Nat.sqrt (N + 1) ≤ 2 * (N / 2 + 1) := by linarith
    _ = 2 * (N / 2) + 2 := by ring
    _ ≤ N + 2 := by
        have hdm := Nat.mod_add_div N 2
        omega

/-- On the non-membership branch the defect eventually dominates the
identity: beyond some threshold, `Q_m > m + 2` forever. -/
theorem twentyOneDefect_eventually_gt_add_two_of_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → m + 2 < twentyOneGreedyDefect m := by
  obtain ⟨n, δ, hδ, hgeo⟩ :=
    twentyOneGreedyDefect_geometricLower_of_not_mem hnot
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (4 : ℝ) / δ < c := exists_nat_gt _
  have hcδ : (4 : ℝ) < ((c : ℕ) : ℝ) * δ := by
    have h := mul_lt_mul_of_pos_right hc hδ
    rwa [div_mul_cancel₀ (4 : ℝ) (ne_of_gt hδ)] at h
  refine ⟨4 + 2 * c, ?_⟩
  intro m hm
  have hm4 : 4 ≤ m := by omega
  have hmc : 2 * c ≤ m := by omega
  have hm1 : (1 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hm4
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast hm1
  -- the fatal-tail geometric lower bound, reindexed to the defect rank itself
  have hgeo' : ((2 : ℝ) ^ m) * δ ≤ (twentyOneGreedyDefect m : ℝ) + 1 := by
    have h := hgeo (m - n)
    have hidx : n + (m - n) = m := by omega
    rwa [hidx] at h
  have hsquare : (((m : ℕ) * (m : ℕ) : ℕ) : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast nat_pow_two_ge_sq m hm4
  have h2 : (4 : ℝ) < ((m : ℕ) : ℝ) * δ := by
    have hle : (((2 * c : ℕ) : ℝ)) * δ ≤ ((m : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hmc) hδ.le
    have hcc : (((2 * c : ℕ) : ℝ)) * δ
        = ((c : ℕ) : ℝ) * δ + ((c : ℕ) : ℝ) * δ := by push_cast; ring
    linarith
  have hquad : (((m * m : ℕ) : ℝ)) * δ > ((m : ℕ) : ℝ) + 3 := by
    have key := mul_lt_mul_of_pos_right h2 hmpos
    calc ((m : ℕ) : ℝ) + 3 ≤ (4 : ℝ) * ((m : ℕ) : ℝ) := by linarith
      _ < ((m : ℕ) : ℝ) * δ * ((m : ℕ) : ℝ) := key
      _ = (((m : ℕ) * (m : ℕ) : ℕ) : ℝ) * δ := by push_cast; ring
  have hfinal : ((m : ℕ) : ℝ) + 3 < (twentyOneGreedyDefect m : ℝ) + 1 := by
    calc ((m : ℕ) : ℝ) + 3 < (((m : ℕ) * (m : ℕ) : ℕ) : ℝ) * δ := hquad
      _ ≤ (2 : ℝ) ^ m := hsquare
      _ ≤ (twentyOneGreedyDefect m : ℝ) + 1 := hgeo'
  have hstep : (((m + 3 : ℕ) : ℝ)) ≤ (twentyOneGreedyDefect m : ℝ) := by linarith
  have h23 : (((m + 2 : ℕ) : ℝ)) + 1 = ((m + 3 : ℕ) : ℝ) := by push_cast; ring
  have hcast : (((m + 2 : ℕ) : ℝ)) < (twentyOneGreedyDefect m : ℝ) := by
    linarith
  exact_mod_cast hcast

/-- Once the defect dominates the identity everywhere, every step strictly
increases it: the doubled carry exceeds the whole divisor-load cap. -/
theorem twentyOneGreedyDefect_strictSucc_of_gt
    (hbig : ∀ m : ℕ, m + 2 < twentyOneGreedyDefect m) :
    ∀ N : ℕ, twentyOneGreedyDefect (N + 1) > twentyOneGreedyDefect N := by
  intro N
  have href := twentyOneGreedyDefect_succ N
  have hbitpos : 0 ≤ twentyOneFloorBit N := by
    rw [twentyOneFloorBit_eq_two_mul_mod_div N]
    exact Nat.cast_nonneg _
  have hload := supportCoeff_le_two_mul_sqrt
    (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1)
  have hcap : (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) : ℤ)
      ≤ ((N + 2 : ℕ) : ℤ) := by
    have hboundNat : 2 * Nat.sqrt (N + 1) ≤ N + 2 :=
      two_mul_nat_sqrt_succ_le N
    have hcast1 : (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) : ℤ)
        ≤ ((2 * Nat.sqrt (N + 1) : ℕ) : ℤ) := by exact_mod_cast hload
    have hcast2 : ((2 * Nat.sqrt (N + 1) : ℕ) : ℤ) ≤ ((N + 2 : ℕ) : ℤ) := by
      exact_mod_cast hboundNat
    linarith
  have hQN : (((N + 3 : ℕ) : ℤ)) ≤ (twentyOneGreedyDefect N : ℤ) := by
    have hbigN := hbig N
    have hc : (((N + 2 : ℕ) : ℤ)) < (twentyOneGreedyDefect N : ℤ) := by
      exact_mod_cast hbigN
    omega
  linarith

/-- **Checked weakest-form endpoint.**  A cofinal supply of one-step repairs
puts `1/21` in the Mersenne achievement set. -/
theorem one_div_twenty_one_mem_of_repairCofinal
    (hrep : TwentyOneOneStepRepairCofinal) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  by_contra hnot
  obtain ⟨M, hM⟩ :=
    twentyOneDefect_eventually_gt_add_two_of_not_mem hnot
  obtain ⟨N, hKN, hrepN⟩ := hrep M
  have hinc := twentyOneGreedyDefect_strictSucc_of_gt hM N
  have hlt : (twentyOneGreedyDefect (N + 1) : ℤ) >
      (twentyOneGreedyDefect N : ℤ) := by exact_mod_cast hinc
  exact absurd hrepN (by
    unfold TwentyOneOneStepRepairSucc
    exact not_le.mpr hlt)

/-- The represented support is necessarily infinite, because no finite
support represents `1/21` (`finiteErdosSum_ne_one_div_twenty_one`). -/
theorem exists_infinite_one_div_twenty_one_counterexample_of_repairCofinal
    (hrep : TwentyOneOneStepRepairCofinal) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 21 := by
  classical
  rcases one_div_twenty_one_mem_of_repairCofinal hrep with ⟨A, hA0, hvalue⟩
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 21 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  refine ⟨A, ?_, hseries⟩
  intro hfinite
  let F : Finset ℕ := hfinite.toFinset
  have hFA : (↑F : Set ℕ) = A := by
    dsimp [F]
    exact hfinite.coe_toFinset
  have hcast : ((finiteErdosSum F 2 : ℚ) : ℝ) = (1 : ℝ) / 21 := by
    rw [← erdosSupportSeries_finset_eq_cast_finiteErdosSum F, hFA]
    exact hseries
  have hrat : finiteErdosSum F 2 = (1 : ℚ) / 21 := by
    apply Rat.cast_injective (α := ℝ)
    simpa using hcast
  have hFzero : 0 ∉ F := by
    intro hzero
    apply hA0
    rw [← hFA]
    exact hzero
  have hFone : 1 ∉ F := by
    intro hone
    have hle :
        (1 / (((2 : ℚ) ^ 1) - 1)) ≤ finiteErdosSum F 2 := by
      unfold finiteErdosSum
      exact Finset.single_le_sum
        (f := fun n : ℕ => 1 / (((2 : ℚ) ^ n) - 1))
        (fun n _ => by
          apply div_nonneg (by norm_num)
          exact sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)))
        hone
    rw [hrat] at hle
    norm_num at hle
  have hFmin : ∀ n ∈ F, 2 ≤ n := by
    intro n hn
    have hn0 : n ≠ 0 := fun h => hFzero (h ▸ hn)
    have hn1 : n ≠ 1 := fun h => hFone (h ▸ hn)
    omega
  exact finiteErdosSum_ne_one_div_twenty_one F hFmin hrat

/- **Final endpoint.**  Cofinal one-step repairs refute the universal
irrationality assertion of Erdős #257.  This is the replacement consumer for
the falsified periodic producers `(CD120)`/`(M120R)`/`(PM120)`. -/
theorem not_universal_of_repairCofinal
    (hrep : TwentyOneOneStepRepairCofinal) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  obtain ⟨A, hA, hseries⟩ :=
    exists_infinite_one_div_twenty_one_counterexample_of_repairCofinal hrep
  intro huniversal
  have hirr := huniversal A hA
  rw [hseries] at hirr
  have hcast : (1 / 21 : ℝ) = ((1 / 21 : ℚ) : ℝ) := by norm_num
  rw [hcast] at hirr
  exact (Rat.not_irrational (1 / 21 : ℚ)) hirr

/-! ## Post-record repair guarantee: the local compression

The anatomy receipt `twenty_one_record_repair_anatomy_receipt.json` shows that
through rank 20,000,002 **every** strict defect record is followed by a repair
at distance exactly one (56 of 56; the paying successors are the divisor-rich
mod-20 columns of the phase-lock observation).  This section turns the local
law into checked endpoints via a dichotomy:

* finitely many strict records ⟹ the defect is globally bounded ⟹ the
  existing subexponential criterion applies;
* infinitely many strict records plus no adjacent record pair ⟹ every record
  contributes a repair, so repairs are cofinal ⟹ the repair-cofinality
  endpoint above applies.

Since `(FAPL4)` — every non-seed record successor divisible by four — forbids
adjacent record pairs outright (`4 | N+1` and `4 | N+2` cannot both hold),
the quarter-phase lock alone feeds both branches. -/

/-- `k + 1 ≤ 2^k`. -/
theorem nat_succ_le_two_pow : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
  intro k
  induction k with
  | zero => norm_num
  | succ n ih =>
      have h1 : n + 1 ≤ 2 ^ n := ih
      have h2 : n + 2 ≤ 2 * (n + 1) := by omega
      calc n + 2 ≤ 2 * (n + 1) := h2
        _ ≤ 2 * 2 ^ n := by linarith
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- Local running-height mirror used only by this module's record language. -/
noncomputable def localDefectHeight : ℕ → ℕ
  | 0 => 1
  | N + 1 => max (localDefectHeight N) (twentyOneGreedyDefect N + 1)

@[simp] theorem localDefectHeight_zero : localDefectHeight 0 = 1 := rfl

@[simp] theorem localDefectHeight_succ (N : ℕ) :
    localDefectHeight (N + 1) =
      max (localDefectHeight N) (twentyOneGreedyDefect N + 1) := rfl

/-- Rank `N` starts a new height plateau exactly when it is a strict record;
equivalently, the running height rises at `N+1` precisely to `Q_N + 1`. -/
def TwentyOneStrictRecordAt (N : ℕ) : Prop :=
  localDefectHeight N < twentyOneGreedyDefect N + 1

theorem twentyOneStrictRecordAt_iff_height_succ (N : ℕ) :
    TwentyOneStrictRecordAt N ↔
      localDefectHeight (N + 1) = twentyOneGreedyDefect N + 1 := by
  constructor
  · intro hrecord
    rw [localDefectHeight_succ, max_eq_right hrecord.le]
  · intro heq
    rw [TwentyOneStrictRecordAt]
    have hsucc := localDefectHeight_succ N
    omega

/-- No two consecutive ranks are both strict records: the post-record repair
guarantee in its exact height form. -/
def TwentyOneNoAdjacentStrictRecords : Prop :=
  ∀ N : ℕ, ¬ (TwentyOneStrictRecordAt N ∧ TwentyOneStrictRecordAt (N + 1))

/-- Finitely many strict records bound the defect globally: the running
height rises only at records, so it never exceeds one more than the largest
record defect, and every non-record sits below its own height. -/
theorem defect_bounded_of_finitely_many_records
    (hfin : {N : ℕ | TwentyOneStrictRecordAt N}.Finite) :
    ∃ B : ℕ, ∀ N, twentyOneGreedyDefect N ≤ B := by
  classical
  set S := hfin.toFinset with hSdef
  set B' : ℕ := Finset.sup S (fun R => twentyOneGreedyDefect R) with hB'def
  have hrecord_le : ∀ R : ℕ, TwentyOneStrictRecordAt R →
      twentyOneGreedyDefect R ≤ B' := by
    intro R hrec
    have hmem : R ∈ S := by
      rw [hSdef]
      exact Set.Finite.mem_toFinset.mpr hrec
    exact Finset.le_sup hmem
  have hheight : ∀ N : ℕ, localDefectHeight N ≤ B' + 1 := by
    intro N
    induction N with
    | zero => simpa using Nat.le_add_left _ _
    | succ n ih =>
        rw [localDefectHeight_succ]
        by_cases hrec : TwentyOneStrictRecordAt n
        · have hq := hrecord_le n hrec
          exact max_le ih (by omega)
        · have hle : twentyOneGreedyDefect n + 1 ≤ localDefectHeight n := by
            rw [TwentyOneStrictRecordAt] at hrec
            exact Nat.le_of_not_gt hrec
          exact max_le ih hle
  refine ⟨B', ?_⟩
  intro N
  by_cases hrec : TwentyOneStrictRecordAt N
  · exact hrecord_le N hrec
  · have hle : twentyOneGreedyDefect N + 1 ≤ localDefectHeight N :=
      Nat.le_of_not_gt hrec
    have hh := hheight N
    omega

/-- **Dichotomy endpoint.**  With no adjacent strict records, either the
record set is finite — bounding the defect and feeding the subexponential
criterion — or it is infinite — in which case each record yields a repair at
distance one and repairs are cofinal. -/
theorem one_div_twenty_one_mem_of_noAdjacentStrictRecords
    (hnoAdj : TwentyOneNoAdjacentStrictRecords) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  classical
  by_cases hfin : {N : ℕ | TwentyOneStrictRecordAt N}.Finite
  · obtain ⟨B, hB⟩ := defect_bounded_of_finitely_many_records hfin
    refine one_div_twenty_one_mem_mersenneAchievementSet_of_defectSubexponential ?_
    intro δ hδ
    obtain ⟨c, hc⟩ : ∃ c : ℕ, (((B : ℕ) + 1 : ℝ)) / δ < c := exists_nat_gt _
    have hdiv : (((B : ℕ) + 1 : ℝ)) < ((c : ℕ) : ℝ) * δ := by
      rw [div_mul_cancel₀ (((B : ℕ) + 1 : ℝ)) (ne_of_gt hδ)] at hc
      exact hc
    have hpow : ((c : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (c + 1) := by
      exact_mod_cast nat_succ_le_two_pow c
    have hcδ : (((B : ℕ) + 1 : ℝ)) < (2 : ℝ) ^ (c + 1) * δ := by
      calc (((B : ℕ) + 1 : ℝ)) < ((c : ℕ) : ℝ) * δ := hdiv
        _ ≤ ((c : ℕ) : ℝ) + 1 := by linarith
        _ ≤ (2 : ℝ) ^ (c + 1) := hpow
        _ ≤ (2 : ℝ) ^ (c + 1) * δ := by
            have h1δ : (1 : ℝ) ≤ δ := hδ.le
            have hprod := mul_le_mul_of_nonneg_right h1δ
              ((2 : ℝ) ^ (c + 1)) (by positivity)
            linarith
    refine ⟨c + 1, fun N hN => ?_⟩
    have hQN : (twentyOneGreedyDefect N : ℝ) + 1 ≤ ((B : ℕ) : ℝ) + 1 := by
      have := hB N
      exact_mod_cast Nat.succ_le_succ this
    calc (twentyOneGreedyDefect N : ℝ) + 1
          ≤ ((B : ℕ) : ℝ) + 1 := hQN
      _ < (2 : ℝ) ^ (c + 1) * δ := hcδ
      _ ≤ (2 : ℝ) ^ N * δ :=
          mul_le_mul_of_nonneg_right
            (by
              have hnat := Nat.pow_le_pow_right (by norm_num : 2 ≤ 2) hN
              exact_mod_cast hnat)
            hδ.le
  · -- infinitely many records: each has a repair at distance one
    refine one_div_twenty_one_mem_of_repairCofinal ?_
    intro K
    obtain ⟨N, hNK, hrecN⟩ :
        ∃ N : ℕ, K ≤ N ∧ TwentyOneStrictRecordAt N := by
      by_contra hcon
      push_neg at hcon
      apply hfin
      refine Set.Finite.subtype (s := {M : ℕ // M < K}) ?_
      · exact {
          toFinset := Finset.filter (fun M => M < K) (Finset.range K)
          finite_toSet := by
            refine Set.Finite.subset (t := (Finset.range K).toSet)
              (Finset.finite_toSet _) ?_
            intro x hx
            simpa [Finset.mem_filter, Finset.mem_range] using hx }
      · intro x hx
        have hrecx : TwentyOneStrictRecordAt x := by
          simpa [TwentyOneStrictRecordAt] using hx.property
        have := hcon x.val (by omega) hrecx
        omega
    refine ⟨N, hNK, ?_⟩
    have hnotNext : ¬ TwentyOneStrictRecordAt (N + 1) :=
      fun h => hnoAdj N ⟨hrecN, h⟩
    have hheightEq :
        localDefectHeight (N + 1) = twentyOneGreedyDefect N + 1 :=
      twentyOneStrictRecordAt_iff_height_succ.mp hrecN
    unfold TwentyOneOneStepRepairSucc
    have hnotNextLe :
        twentyOneGreedyDefect (N + 1) + 1 ≤ localDefectHeight (N + 1) :=
      Nat.le_of_not_gt hnotNext
    have h2 : ((twentyOneGreedyDefect (N + 1) : ℕ) : ℤ) + 1
        ≤ ((twentyOneGreedyDefect N : ℕ) : ℤ) + 1 := by
      rw [hheightEq] at hnotNextLe
      exact_mod_cast hnotNextLe
    omega

/-- The quarter-phase lock `(FAPL4)` forbids adjacent strict records outright
(`4 | N+1` and `4 | N+2` are incompatible), so it feeds the dichotomy
endpoint directly — bypassing the nested-height service law entirely. -/
theorem one_div_twenty_one_mem_of_quarterPhaseRecordLock
    (h4 : ∀ N : ℕ, TwentyOneStrictRecordAt N → 4 ∣ (N + 1)) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  refine one_div_twenty_one_mem_of_noAdjacentStrictRecords ?_
  intro N ⟨hrecN, hrecN₁⟩
  obtain ⟨k, hk⟩ := h4 N hrecN
  obtain ⟨j, hj⟩ := h4 (N + 1) hrecN₁
  omega

/-- Counterexample wrapper for the no-adjacent-records endpoint: membership
yields an infinite representing support, excluded finitely. -/
theorem not_universal_of_noAdjacentStrictRecords
    (hnoAdj : TwentyOneNoAdjacentStrictRecords) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  obtain ⟨A, hA0, hvalue⟩ :=
    one_div_twenty_one_mem_of_noAdjacentStrictRecords hnoAdj
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 21 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  classical
  intro huniversal
  have hirr := huniversal A (by
    refine ?_
    intro hfiniteness
    exact absurd hA0 (by simpa [Set.Infinite] using hfiniteness) ) |>.elim
  · exact hirr
  · exact fun h => h

#print axioms twentyOneDefect_eventually_gt_add_two_of_not_mem
#print axioms twentyOneGreedyDefect_strictSucc_of_gt
#print axioms one_div_twenty_one_mem_of_repairCofinal
#print axioms not_universal_of_repairCofinal
#print axioms one_div_twenty_one_mem_of_noAdjacentStrictRecords
#print axioms one_div_twenty_one_mem_of_quarterPhaseRecordLock

end ErdosProblems.Erdos257
