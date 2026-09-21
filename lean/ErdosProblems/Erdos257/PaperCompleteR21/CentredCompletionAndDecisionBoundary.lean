import Erdos249257.TropicalCurvatureCarry
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet

/-!
Paper-form restatements of asserted environments of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`:

* `prop:2adic-nogo` (line 7362) — centred completion of fixed-precision
  2-adic data, in the manuscript's indexed-family form;
* the untitled Theorem C (line 7153) — the one-sided finite decision
  boundary: the checked greedy-survival equivalence, the finite fatal
  certificate for nonmembership, and the all-rank requirement for
  membership;
* `prop:finite-state-nogo` (line 7587) — the balanced-pulse family admits no
  autonomous decoder, and a finite state type needs at least `radius + 1`
  elements.  The manuscript's parenthetical fan-out constant is recorded
  here in its exact form (see `paper_balanced_pulse_fanout_count`).
* a constant used by the untitled Theorem A (line 7118): `B r ^ 2 ≤ 2^(r+5)`
  for `r ≥ 10`, where `B r = 2 ^ ⌊(r+4)/2⌋ + 2r + 3`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257

/-! ## `prop:2adic-nogo` -/

/-- Long `prop:2adic-nogo`, in the manuscript's indexed form.  Fix `u ≥ 1`
and a finite list of valuations `v i` and odd units `a i`, `i < m`.  For
every initial integer `e 0 = e₀` there are integers `z i` and successors
`e (i+1)` with `e (i+1) = 2 * e i + 2 ^ (v i) * (a i + 2 ^ u * z i)` and
`|e (i+1)| ≤ 2 ^ (v i + u - 1)`. -/
theorem paper_centred_completion_of_fixed_precision
    (u : ℕ) (hu : 1 ≤ u) (m : ℕ) (v : ℕ → ℕ) (a : ℕ → ℤ)
    (hodd : ∀ i, i < m → Odd (a i)) (e₀ : ℤ) :
    ∃ e z : ℕ → ℤ, e 0 = e₀ ∧
      ∀ i, i < m →
        e (i + 1) = 2 * e i + 2 ^ (v i) * (a i + 2 ^ u * z i) ∧
          |e (i + 1)| ≤ 2 ^ (v i + u - 1) := by
  classical
  induction m with
  | zero =>
      exact ⟨fun _ => e₀, fun _ => 0, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ m ih =>
      obtain ⟨e, z, he0, hstep⟩ := ih (fun i hi => hodd i (by omega))
      obtain ⟨c, e', hcompat, hstepEq, hbound⟩ :=
        TotientTailPeriodKiller.vu_step_has_centred_completion u
          ⟨v m, a m⟩ (by omega) (hodd m (by omega)) (e m)
      obtain ⟨-, zm, hc⟩ := hcompat
      have hc' : c = 2 ^ (v m) * (a m + 2 ^ u * zm) := hc
      have hbound' : |e'| ≤ 2 ^ (v m + u - 1) := hbound
      refine ⟨fun k => if k = m + 1 then e' else e k,
        fun k => if k = m then zm else z k, by simpa using he0, ?_⟩
      intro i hi
      by_cases hlt : i < m
      · have h1 : i + 1 ≠ m + 1 := by omega
        have h2 : i ≠ m + 1 := by omega
        have h3 : i ≠ m := by omega
        simpa [h1, h2, h3] using hstep i hlt
      · have him : i = m := by omega
        subst him
        have h2 : i ≠ i + 1 := by omega
        have hstep' : e' = 2 * e i + 2 ^ (v i) * (a i + 2 ^ u * zm) := by
          rw [hstepEq, hc']
        refine ⟨?_, ?_⟩
        · simp only [if_pos rfl, if_neg h2]
          exact hstep'
        · simp only [if_pos rfl]
          exact hbound'

/-! ## Theorem C: the one-sided finite decision boundary -/

/-- Long untitled Theorem C (line 7153), its three mathematical clauses.
The checked equivalence; a fatal greedy state at a finite rank is a
certificate of nonmembership; membership requires survival at every rank. -/
theorem paper_one_sided_finite_decision_boundary :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
        0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
      (∀ x : ℝ, (∃ n : ℕ, mersenneTail n < greedyMersenneRemainder x n) →
        x ∉ mersenneAchievementSet) ∧
      (∀ x : ℝ, x ∈ mersenneAchievementSet →
        ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) := by
  refine ⟨mem_mersenneAchievementSet_iff_greedy_survival, ?_, ?_⟩
  · rintro x ⟨n, hn⟩ hmem
    exact absurd (((mem_mersenneAchievementSet_iff_greedy_survival x).1 hmem).2 n)
      (not_le_of_gt hn)
  · intro x hmem
    exact ((mem_mersenneAchievementSet_iff_greedy_survival x).1 hmem).2

/-! ## `prop:finite-state-nogo` -/

/-- Long `prop:finite-state-nogo`, decoder clause.  For a balanced-pulse
family at location `m ≥ 2` with radius `(m+1)/2`, a predecessor state that is
constant across the family admits no function `decode : State → ℕ` recovering
the parameter `r` from `state r` for every `r`. -/
theorem paper_balanced_pulse_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r :=
  balancedPulse_no_autonomous_decoder m hm state hstate

/-- Long `prop:finite-state-nogo`, cardinality clause.  A finite state type
carrying an exact decoder for the balanced-pulse family at `m` has at least
`balancedPulseRadius m + 1` elements, which is unbounded in `m`. -/
theorem paper_balanced_pulse_finite_state_card
    {m : ℕ} {State : Type*} [Fintype State]
    (state : Fin (balancedPulseRadius m + 1) → State)
    (decode : State → ℕ) (hdecode : ∀ r, decode (state r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card State ∧
      ∀ N : ℕ, ∃ m' : ℕ, N ≤ balancedPulseRadius m' + 1 :=
  ⟨balancedPulse_label_card_lower_bound state decode hdecode,
    fun N => ⟨2 * N, by unfold balancedPulseRadius; omega⟩⟩

/-- The exact fan-out of the balanced-pulse family: at `m = 2k` the family
has `balancedPulseRadius (2k) + 1 = k + 1` members, so the manuscript's
parenthetical lower bound `⌊m/2⌋ + 2 = k + 2` at `m = 2k` is one too large;
the bound `⌊m/2⌋ + 2` is the correct count at odd `m = 2k+1`. -/
theorem paper_balanced_pulse_fanout_count (k : ℕ) :
    balancedPulseRadius (2 * k) + 1 = k + 1 ∧
      balancedPulseRadius (2 * k + 1) + 1 = (2 * k + 1) / 2 + 2 ∧
      ∀ m : ℕ, m / 2 + 1 ≤ balancedPulseRadius m + 1 := by
  refine ⟨by unfold balancedPulseRadius; omega,
    by unfold balancedPulseRadius; omega, ?_⟩
  intro m
  unfold balancedPulseRadius
  omega

/-! ## A constant of the untitled Theorem A -/

private theorem three_mul_four_mul_add_le_pow {m : ℕ} (hm : 7 ≤ m) :
    3 * (4 * m + 3) ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega

/-- The constant recorded inside the untitled Theorem A (line 7118): with
`B r = 2 ^ ⌊(r+4)/2⌋ + 2r + 3`, one has `B r ^ 2 ≤ 2 ^ (r+5)` for `r ≥ 10`. -/
theorem paper_resetCrossingBound_square_le {r : ℕ} (hr : 10 ≤ r) :
    (2 ^ ((r + 4) / 2) + 2 * r + 3) ^ 2 ≤ 2 ^ (r + 5) := by
  have hm : 7 ≤ (r + 4) / 2 := by omega
  have hb : 2 * r + 3 ≤ 4 * ((r + 4) / 2) + 3 := by omega
  have hpow := three_mul_four_mul_add_le_pow hm
  have hA : 3 * (2 * r + 3) ≤ 2 ^ ((r + 4) / 2) := by omega
  have hsq : (2 ^ ((r + 4) / 2) + 2 * r + 3) ^ 2 ≤
      2 * (2 ^ ((r + 4) / 2)) ^ 2 := by nlinarith [hA, Nat.zero_le (2 * r + 3)]
  have hstep : 2 * (2 ^ ((r + 4) / 2)) ^ 2 = 2 ^ (2 * ((r + 4) / 2) + 1) := by
    rw [pow_succ, two_mul ((r + 4) / 2), pow_add]
    ring
  have hle : 2 * ((r + 4) / 2) + 1 ≤ r + 5 := by omega
  calc (2 ^ ((r + 4) / 2) + 2 * r + 3) ^ 2
      ≤ 2 * (2 ^ ((r + 4) / 2)) ^ 2 := hsq
    _ = 2 ^ (2 * ((r + 4) / 2) + 1) := hstep
    _ ≤ 2 ^ (r + 5) := Nat.pow_le_pow_right (by norm_num) hle

#print axioms paper_centred_completion_of_fixed_precision
#print axioms paper_one_sided_finite_decision_boundary
#print axioms paper_balanced_pulse_no_autonomous_decoder
#print axioms paper_balanced_pulse_finite_state_card
#print axioms paper_balanced_pulse_fanout_count
#print axioms paper_resetCrossingBound_square_le

end ErdosProblems.Erdos257.PaperCompleteR21
