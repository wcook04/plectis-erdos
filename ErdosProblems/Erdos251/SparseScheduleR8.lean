import ErdosProblems.Erdos251.ResidueFeedbackCore
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# A schedule for an arbitrary divergent envelope (round 8)

The schedule is constructed rather than assumed as an input hypothesis.
It constructs increasing centres, a cofinal level, amplitude bounds and
an integer next-site overlap inequality. The separate module
`SparseScheduleDensityR8` supplies uniform counting from this schedule.
No prime distribution assertion is used.

Pinned APIs checked at Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6:
* Data/Nat/Factorial/Basic: factorial_pos, factorial_le, dvd_factorial.
* Order/Filter/AtTopBot/Basic: eventually_atTop, tendsto_atTop_atTop.
* Order/Filter/AtTopBot/Tendsto: StrictMono.tendsto_atTop.
-/

noncomputable section
open Filter Topology

namespace ErdosProblems.Erdos251.PaperR8.SparseSchedule

/-- Every increasing map from naturals dominates its input index. -/
theorem index_le_of_strictMono (c : ℕ → ℕ) (hc : StrictMono c) (j : ℕ) : j ≤ c j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
      have h := hc (Nat.lt_succ_self j)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih h)

/-- A level-k step. The square is convenient; sharp constants are not claimed. -/
def gap (k : ℕ) : ℕ := (k + 4) ^ 2

/-- A level-k capacity, allowing two successive modulus upgrades. -/
def amplitude (k : ℕ) : ℕ := 4 * (k + 3).factorial * 2 ^ gap k

theorem gap_pos (k : ℕ) : 0 < gap k := by
  unfold gap
  exact pow_pos (by omega : 0 < k + 4) 2

theorem level_le_gap (k : ℕ) : k ≤ gap k := by
  unfold gap
  nlinarith

theorem gap_mono : Monotone gap := by
  intro i j hij
  exact Nat.pow_le_pow_left (Nat.add_le_add_right hij 4) 2

theorem amplitude_pos (k : ℕ) : 0 < amplitude k := by
  unfold amplitude
  exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.factorial_pos _))
    (Nat.pow_pos (by decide))

theorem amplitude_mono : Monotone amplitude := by
  intro i j hij
  have hf : (i + 3).factorial ≤ (j + 3).factorial :=
    Nat.factorial_le (Nat.add_le_add_right hij 3)
  have hp : 2 ^ gap i ≤ 2 ^ gap j :=
    Nat.pow_le_pow_right (by decide) (gap_mono hij)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hf) hp

/-- A stage is allowed only after its entire future budget is available.
The additional linear bound ensures geometric summability independently
of how rapidly the supplied envelope grows. -/
def Ready (f : ℕ → ℝ) (n k : ℕ) : Prop :=
  ∀ m, n ≤ m → (amplitude k : ℝ) ≤ f m ∧ amplitude k ≤ m + 1

theorem ready_mono {f : ℕ → ℝ} {n n' k : ℕ}
    (h : Ready f n k) (hn : n ≤ n') : Ready f n' k := by
  intro m hm
  exact h m (hn.trans hm)

theorem eventually_ready (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (k : ℕ) :
    ∃ n, Ready f n k := by
  -- Mathlib/Order/Filter/AtTopBot/Basic.lean: eventually_atTop.
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    (hf.eventually_ge_atTop (amplitude k : ℝ))
  refine ⟨max n (amplitude k), ?_⟩
  intro m hm
  have hnm : n ≤ m := (le_max_left _ _).trans hm
  have ham : amplitude k ≤ m := (le_max_right _ _).trans hm
  exact ⟨hn m hnm, ham.trans (Nat.le_succ _)⟩

/-- Upgrade by one level exactly when the future budget allows it. -/
def upgrade (f : ℕ → ℝ) (n k : ℕ) : ℕ := by
  classical
  exact if Ready f n (k + 1) then k + 1 else k

theorem upgrade_bounds (f : ℕ → ℝ) (n k : ℕ) :
    k ≤ upgrade f n k ∧ upgrade f n k ≤ k + 1 := by
  classical
  unfold upgrade
  split_ifs <;> exact ⟨by omega, by omega⟩

theorem upgrade_of_ready {f : ℕ → ℝ} {n k : ℕ}
    (h : Ready f n (k + 1)) : upgrade f n k = k + 1 := by
  classical
  exact if_pos h

/-- State = (centre, level), with no assumed rate for the envelope. -/
def state (f : ℕ → ℝ) (start : ℕ) : ℕ → ℕ × ℕ
  | 0 => (start, 0)
  | j + 1 =>
      let s := state f start j
      let n := s.1 + gap s.2
      (n, upgrade f n s.2)

def centre (f : ℕ → ℝ) (start j : ℕ) : ℕ := (state f start j).1
def level (f : ℕ → ℝ) (start j : ℕ) : ℕ := (state f start j).2

@[simp] theorem centre_zero (f : ℕ → ℝ) (start : ℕ) : centre f start 0 = start := rfl
@[simp] theorem level_zero (f : ℕ → ℝ) (start : ℕ) : level f start 0 = 0 := rfl
@[simp] theorem centre_succ (f : ℕ → ℝ) (start j : ℕ) :
    centre f start (j + 1) = centre f start j + gap (level f start j) := rfl
@[simp] theorem level_succ (f : ℕ → ℝ) (start j : ℕ) :
    level f start (j + 1) =
      upgrade f (centre f start (j + 1)) (level f start j) := rfl

theorem centre_strictMono (f : ℕ → ℝ) (start : ℕ) :
    StrictMono (centre f start) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [centre_succ]
  exact Nat.lt_add_of_pos_right (gap_pos _)

theorem level_mono (f : ℕ → ℝ) (start : ℕ) : Monotone (level f start) := by
  apply monotone_nat_of_le_succ
  intro j
  exact (upgrade_bounds f (centre f start (j + 1)) (level f start j)).1

theorem level_succ_le (f : ℕ → ℝ) (start j : ℕ) :
    level f start (j + 1) ≤ level f start j + 1 :=
  (upgrade_bounds f (centre f start (j + 1)) (level f start j)).2

theorem level_le_index (f : ℕ → ℝ) (start : ℕ) : ∀ j, level f start j ≤ j := by
  intro j
  induction j with
  | zero => exact le_refl 0
  | succ j ih => exact (level_succ_le f start j).trans (Nat.add_le_add_right ih 1)

theorem ready_invariant (f : ℕ → ℝ) (start : ℕ) (hstart : Ready f start 0) :
    ∀ j, Ready f (centre f start j) (level f start j) := by
  intro j
  induction j with
  | zero => exact hstart
  | succ j ih =>
      classical
      have hmove : Ready f (centre f start (j + 1)) (level f start j) :=
        ready_mono ih ((centre_strictMono f start).monotone (Nat.le_succ j))
      rw [level_succ]
      unfold upgrade
      split_ifs with h
      · exact h
      · exact hmove

/-- The level really reaches every integer; a perpetually stalled level
would contradict the envelope's eventual readiness. -/
theorem level_cofinal (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (start : ℕ) :
    ∀ k, ∃ j, k ≤ level f start j := by
  intro k
  induction k with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨N, hN⟩ := eventually_ready f hf (k + 1)
      let i := max j N
      have hji : j ≤ i := le_max_left _ _
      have hNi : N ≤ i := le_max_right _ _
      have hki : k ≤ level f start i := hj.trans (level_mono f start hji)
      by_cases hdone : k + 1 ≤ level f start i
      · exact ⟨i, hdone⟩
      · have heq : level f start i = k := by omega
        have hn : N ≤ centre f start (i + 1) :=
          hNi.trans ((Nat.le_succ i).trans (index_le_of_strictMono _ (centre_strictMono f start) _))
        have hready : Ready f (centre f start (i + 1)) (k + 1) := ready_mono hN hn
        refine ⟨i + 1, ?_⟩
        rw [level_succ, heq, upgrade_of_ready hready]

theorem level_tendsto_atTop (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (start : ℕ) :
    Tendsto (level f start) atTop atTop := by
  -- Mathlib/Order/Filter/AtTopBot/Tendsto.lean.
  exact Filter.tendsto_atTop_atTop_of_monotone (level_mono f start)
    (level_cofinal f hf start)

/-- Eventually every spacing is at least any prescribed R. -/
theorem eventual_spacing (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (start R : ℕ) :
    ∃ J, ∀ j, J ≤ j → R ≤ centre f start (j + 1) - centre f start j := by
  obtain ⟨J, hJ⟩ := level_cofinal f hf start R
  refine ⟨J, ?_⟩
  intro j hj
  rw [centre_succ, Nat.add_sub_cancel_left]
  exact (hJ.trans (level_mono f start hj)).trans (level_le_gap _)

/-- Capacity and outgoing look-ahead modulus on the generated centres. -/
def capacity (f : ℕ → ℝ) (start j : ℕ) : ℕ := amplitude (level f start j)
def modulus (f : ℕ → ℝ) (start j : ℕ) : ℕ := (level f start (j + 1) + 1).factorial

theorem capacity_budget (f : ℕ → ℝ) (start : ℕ) (hstart : Ready f start 0) (j : ℕ) :
    (capacity f start j : ℝ) ≤ f (centre f start j) ∧
      capacity f start j ≤ centre f start j + 1 :=
  ready_invariant f start hstart j _ le_rfl

theorem modulus_pos (f : ℕ → ℝ) (start j : ℕ) : 0 < modulus f start j :=
  Nat.factorial_pos _

theorem modulus_dvd_next (f : ℕ → ℝ) (start j : ℕ) :
    modulus f start j ∣ modulus f start (j + 1) := by
  apply Nat.factorial_dvd_factorial
  exact Nat.add_le_add_right (level_mono f start (Nat.le_succ (j + 1))) 1

theorem modulus_upper (f : ℕ → ℝ) (start j : ℕ) :
    modulus f start j ≤ (level f start j + 2).factorial := by
  apply Nat.factorial_le
  have h := level_succ_le f start j
  omega

theorem next_modulus_upper (f : ℕ → ℝ) (start j : ℕ) :
    modulus f start (j + 1) ≤ (level f start j + 3).factorial := by
  apply Nat.factorial_le
  have h1 := level_succ_le f start j
  have h2 := level_succ_le f start (j + 1)
  omega

/-- Division-free, next-site overlap. This is proved for the actual
schedule, not passed as a capacity hypothesis to the digit selector. -/
theorem next_capacity_overlap (f : ℕ → ℝ) (start j : ℕ) :
    modulus f start j * 2 ^ gap (level f start j) +
      2 * modulus f start (j + 1) ≤ capacity f start (j + 1) := by
  let k := level f start j
  let F := (k + 3).factorial
  let P := 2 ^ gap k
  have hq : modulus f start j ≤ F :=
    (modulus_upper f start j).trans (Nat.factorial_le (by omega))
  have hq' : modulus f start (j + 1) ≤ F := next_modulus_upper f start j
  have hp : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have hFP : F ≤ F * P := by simpa using Nat.mul_le_mul_left F hp
  have hleft : modulus f start j * P + 2 * modulus f start (j + 1) ≤ F * P + 2 * F :=
    Nat.add_le_add (Nat.mul_le_mul_right P hq) (Nat.mul_le_mul_left 2 hq')
  have hmid : F * P + 2 * F ≤ 4 * F * P := by nlinarith
  have hcap : 4 * F * P ≤ capacity f start (j + 1) :=
    amplitude_mono (level_mono f start (Nat.le_succ j))
  exact hleft.trans (hmid.trans hcap)

theorem twice_modulus_le_capacity (f : ℕ → ℝ) (start j : ℕ) :
    2 * modulus f start j ≤ capacity f start j := by
  have hq := modulus_upper f start j
  have hf : (level f start j + 2).factorial ≤ (level f start j + 3).factorial :=
    Nat.factorial_le (by omega)
  have hp : 1 ≤ 2 ^ gap (level f start j) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  unfold capacity amplitude
  have hq' := hq.trans hf
  nlinarith [Nat.mul_le_mul_left ((level f start j + 3).factorial) hp]

/-- Every fixed positive modulus divides all outgoing moduli eventually. -/
theorem every_modulus_eventually (f : ℕ → ℝ) (hf : Tendsto f atTop atTop)
    (start q : ℕ) (hq : 0 < q) :
    ∃ J, ∀ j, J ≤ j → q ∣ modulus f start j := by
  obtain ⟨J, hJ⟩ := level_cofinal f hf start q
  refine ⟨J, ?_⟩
  intro j hj
  apply Nat.dvd_factorial hq
  have h := hJ.trans (level_mono f start (hj.trans (Nat.le_succ j)))
  exact h.trans (Nat.le_succ _)

/-- Package for the arbitrary-envelope schedule. The remaining analytic
steps, in particular its sharper polylogarithmic count, are not hidden here. -/
theorem exists_budgeted_schedule (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ start : ℕ, K ≤ start ∧ Ready f start 0 ∧
      StrictMono (centre f start) ∧
      (∀ j, (capacity f start j : ℝ) ≤ f (centre f start j) ∧
        capacity f start j ≤ centre f start j + 1) ∧
      (∀ R, ∃ J, ∀ j, J ≤ j → R ≤ centre f start (j + 1) - centre f start j) ∧
      (∀ j, 2 * modulus f start j ≤ capacity f start j) ∧
      (∀ j, modulus f start j * 2 ^ gap (level f start j) +
        2 * modulus f start (j + 1) ≤ capacity f start (j + 1)) := by
  obtain ⟨n, hn⟩ := eventually_ready f hf 0
  let start := max K n
  have hstart : Ready f start 0 := ready_mono hn (le_max_right _ _)
  exact ⟨start, le_max_left _ _, hstart, centre_strictMono f start,
    capacity_budget f start hstart, eventual_spacing f hf start,
    twice_modulus_le_capacity f start, next_capacity_overlap f start⟩

#print axioms exists_budgeted_schedule
end ErdosProblems.Erdos251.PaperR8.SparseSchedule
