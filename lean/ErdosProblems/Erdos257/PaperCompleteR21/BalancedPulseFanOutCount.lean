import Erdos249257.GenericTailOrbitRigidity
import Mathlib.Order.Interval.Set.Nat

/-!
Long Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`,
`prop:finite-state-nogo` (line 7587).

The proposition has three mathematical clauses:

1. no `decode : State → ℕ` recovers the pulse parameter from a predecessor
   state that is constant across the family;
2. a parenthetical fan-out lower bound, "`≥ ⌊m/2⌋ + 2` at `m = 2k`";
3. a finite `State` needs `card State ≥ radius + 1`, unbounded in `m`.

Clauses 1 and 3 are restated and discharged below from the tree.  Clause 2 is
FALSE as written.  The balanced-pulse family at location `m` is
`{balancedPulseCoeff m r : 0 ≤ r ≤ balancedPulseRadius m}` with
`balancedPulseRadius m = ⌊(m+1)/2⌋`, and `r ↦ balancedPulseCoeff m r` is
injective, so the family has exactly `⌊(m+1)/2⌋ + 1` members.  At `m = 2k`
that count is `k + 1`, while the asserted bound reads `⌊m/2⌋ + 2 = k + 2`:
the bound exceeds the true fan-out by one at every even `m`.  At odd
`m = 2k+1` the count is `k + 2 = ⌊m/2⌋ + 2` and the asserted bound is exactly
attained.  The corrected uniform statement is
`fan-out = balancedPulseRadius m + 1 = ⌊(m+1)/2⌋ + 1`, which is still
unbounded in `m`, so clauses 1 and 3 are unaffected.

`paper_balanced_pulse_fanout_is_radius_succ` proves the exact count,
`paper_balanced_pulse_fanout_floor_bound_fails_at_even` exhibits the failure,
and `paper_balanced_pulse_fanout_floor_bound_sharp_at_odd` records the odd
case where the manuscript's constant is correct.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257

/-! ## The balanced-pulse family and its exact fan-out -/

/-- The displayed balanced-pulse family at location `m`: the coefficient
sequences `balancedPulseCoeff m r` for the admissible parameters
`0 ≤ r ≤ balancedPulseRadius m`.  These are exactly the parameters for which
the pulse is mass preserving and stays in the linear-growth class
(`balancedPulseCoeff_le_self`). -/
def balancedPulseFamily (m : ℕ) : Set (ℕ → ℕ) :=
  balancedPulseCoeff m '' Set.Iic (balancedPulseRadius m)

/-- The radius is the manuscript's `⌊(m+1)/2⌋`. -/
private theorem radius_eq (m : ℕ) : balancedPulseRadius m = (m + 1) / 2 := rfl

/-- Distinct pulse parameters give distinct members: the right site already
separates them, since `balancedPulseCoeff m r (m+1) = 2r`. -/
theorem balancedPulseCoeff_injective (m : ℕ) :
    Function.Injective (balancedPulseCoeff m) := by
  intro r s hrs
  have h := congrArg (fun c => c (m + 1)) hrs
  simp only [balancedPulseCoeff_at_right] at h
  omega

/-- **The exact fan-out.**  The balanced-pulse family at location `m` has
exactly `balancedPulseRadius m + 1 = ⌊(m+1)/2⌋ + 1` members. -/
theorem paper_balanced_pulse_fanout_is_radius_succ (m : ℕ) :
    (balancedPulseFamily m).ncard = balancedPulseRadius m + 1 ∧
      (balancedPulseFamily m).ncard = (m + 1) / 2 + 1 := by
  have hcard : (balancedPulseFamily m).ncard = balancedPulseRadius m + 1 := by
    rw [balancedPulseFamily,
      Set.ncard_image_of_injective _ (balancedPulseCoeff_injective m),
      Set.ncard_Iic_nat]
  refine ⟨hcard, ?_⟩
  have hr := radius_eq m
  omega

/-- **The defect.**  At every even location `m = 2k` the family has exactly
`k + 1` members, so the manuscript's parenthetical lower bound
`⌊m/2⌋ + 2 = k + 2` fails: it is one too large. -/
theorem paper_balanced_pulse_fanout_floor_bound_fails_at_even (k : ℕ) :
    (balancedPulseFamily (2 * k)).ncard = k + 1 ∧
      ¬ (2 * k / 2 + 2 ≤ (balancedPulseFamily (2 * k)).ncard) := by
  have h := (paper_balanced_pulse_fanout_is_radius_succ (2 * k)).1
  have hr := radius_eq (2 * k)
  refine ⟨by omega, ?_⟩
  omega

/-- At every odd location `m = 2k+1` the family has exactly `k + 2` members,
which is the manuscript's `⌊m/2⌋ + 2`; there the parenthetical constant is
correct, and attained with equality. -/
theorem paper_balanced_pulse_fanout_floor_bound_sharp_at_odd (k : ℕ) :
    (balancedPulseFamily (2 * k + 1)).ncard = (2 * k + 1) / 2 + 2 := by
  have h := (paper_balanced_pulse_fanout_is_radius_succ (2 * k + 1)).1
  have hr := radius_eq (2 * k + 1)
  omega

/-- The corrected fan-out statement, in the manuscript's "unbounded" form:
the fan-out at `m` is `⌊(m+1)/2⌋ + 1`, it never drops below `⌊m/2⌋ + 1`, and
it exceeds every `N` for suitable `m`. -/
theorem paper_balanced_pulse_fanout_unbounded_corrected :
    (∀ m : ℕ, m / 2 + 1 ≤ (balancedPulseFamily m).ncard) ∧
      ∀ N : ℕ, ∃ m : ℕ, N ≤ (balancedPulseFamily m).ncard := by
  constructor
  · intro m
    have h := (paper_balanced_pulse_fanout_is_radius_succ m).2
    omega
  · intro N
    refine ⟨2 * N, ?_⟩
    have h := (paper_balanced_pulse_fanout_is_radius_succ (2 * N)).2
    omega

/-! ## The two clauses that do hold -/

/-- `prop:finite-state-nogo`, decoder clause.  For a balanced-pulse family at
location `m ≥ 2`, a predecessor state constant across the family admits no
function `decode : State → ℕ` recovering the parameter `r` from `state r` for
every `r`. -/
theorem paper_pulse_family_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r :=
  balancedPulse_no_autonomous_decoder m hm state hstate

/-- `prop:finite-state-nogo`, cardinality clause.  A finite state type
carrying an exact decoder for the family at `m` has at least
`balancedPulseRadius m + 1` elements, and that quantity is unbounded in `m`. -/
theorem paper_pulse_family_finite_state_card
    {m : ℕ} {State : Type*} [Fintype State]
    (state : Fin (balancedPulseRadius m + 1) → State)
    (decode : State → ℕ) (hdecode : ∀ r, decode (state r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card State ∧
      ∀ N : ℕ, ∃ m' : ℕ, N ≤ balancedPulseRadius m' + 1 :=
  ⟨balancedPulse_label_card_lower_bound state decode hdecode,
    fun N => ⟨2 * N, by have hr := radius_eq (2 * N); omega⟩⟩

#print axioms balancedPulseCoeff_injective
#print axioms paper_balanced_pulse_fanout_is_radius_succ
#print axioms paper_balanced_pulse_fanout_floor_bound_fails_at_even
#print axioms paper_balanced_pulse_fanout_floor_bound_sharp_at_odd
#print axioms paper_balanced_pulse_fanout_unbounded_corrected
#print axioms paper_pulse_family_no_autonomous_decoder
#print axioms paper_pulse_family_finite_state_card

end ErdosProblems.Erdos257.PaperCompleteR21
