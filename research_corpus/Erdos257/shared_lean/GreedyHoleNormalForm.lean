import Erdos257PeriodNoncollapse.GreedyAchievementSet

/-!
# The greedy hole normal form

Membership in the Mersenne achievement set is decided by a *doubling map with holes*.
In scaled coordinates `y n = 2^n * R n`, the take branch carries `[b n, τ n]` **onto**
`[0, τ (n+1)]` (`two_mul_scaledTail_sub_scaledWeight` below), and the skip branch carries
`[0, τ (n+1) / 2]` onto `[0, τ (n+1)]`.  Super-increasingness leaves exactly one gap
uncovered, and falling into it is the *only* way the greedy recursion can die.
-/

namespace Erdos257PeriodNoncollapse

/-- The exact surjectivity identity behind the normal form: after scaling, the take
branch maps the whole survival ceiling at depth `n` onto the ceiling at depth `n+1`. -/
theorem two_mul_scaledTail_sub_scaledWeight (n : ℕ) :
    2 * (2 ^ n * mersenneTail n) - 2 ^ (n + 1) * mersenneWeight (n + 1)
      = 2 ^ (n + 1) * mersenneTail (n + 1) := by
  rw [mersenneTail_eq_weight_add n]; ring

/-- The fatal window at depth `n`: the residual already exceeds the mass available after
`n + 1`, yet is too small to take exponent `n + 1`.  The greedy recursion must skip, and
the skip is unrecoverable. -/
def GreedyMersenneHoleAt (x : ℝ) (n : ℕ) : Prop :=
  mersenneTail (n + 1) < greedyMersenneRemainder x n ∧
    greedyMersenneRemainder x n < mersenneWeight (n + 1)

/-- Death is entered only through the hole: the first fatal depth is always a skip out of
the window `(T (n+1), w (n+1))`. -/
theorem greedyMersenneHoleAt_of_first_fatal {x : ℝ} {n : ℕ}
    (hsafe : ¬ GreedyMersenneFatalAt x n)
    (hfatal : GreedyMersenneFatalAt x (n + 1)) :
    GreedyMersenneHoleAt x n := by
  unfold GreedyMersenneFatalAt at hsafe hfatal
  push_neg at hsafe
  have htail := mersenneTail_eq_weight_add n
  by_cases htake : mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n
  · rw [greedyMersenneRemainder_succ, if_pos htake] at hfatal
    exact absurd hsafe (by linarith)
  · rw [greedyMersenneRemainder_succ, if_neg htake] at hfatal
    push_neg at htake
    exact ⟨hfatal, htake⟩

/-- Avoiding every hole keeps the recursion out of the fatal region at every depth. -/
theorem not_greedyMersenneFatalAt_of_holeFree {x : ℝ}
    (h0 : x ≤ mersenneTail 0)
    (hfree : ∀ n : ℕ, ¬ GreedyMersenneHoleAt x n) (n : ℕ) :
    ¬ GreedyMersenneFatalAt x n := by
  induction n with
  | zero => simpa [GreedyMersenneFatalAt] using not_lt.mpr h0
  | succ n ih =>
      intro hfatal
      exact hfree n (greedyMersenneHoleAt_of_first_fatal ih hfatal)

/-- **Normal form.**  For `0 ≤ x ≤ T 0`, membership in the Mersenne achievement set is
*equivalent* to the greedy orbit avoiding every hole. -/
theorem mem_mersenneAchievementSet_iff_holeFree {x : ℝ} (hx : 0 ≤ x)
    (h0 : x ≤ mersenneTail 0) :
    x ∈ mersenneAchievementSet ↔ ∀ n : ℕ, ¬ GreedyMersenneHoleAt x n := by
  constructor
  · intro hmem n hhole
    obtain ⟨-, hsurv⟩ := greedy_survives_of_mem_mersenneAchievementSet hmem
    have hskip : ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n :=
      not_le.mpr hhole.2
    have hnext := hsurv (n + 1)
    rw [greedyMersenneRemainder_succ, if_neg hskip] at hnext
    exact absurd hhole.1 (not_lt.mpr hnext)
  · intro hfree
    refine mem_mersenneAchievementSet_of_greedy_survival hx (fun n => ?_)
    have hn := not_greedyMersenneFatalAt_of_holeFree h0 hfree n
    unfold GreedyMersenneFatalAt at hn
    exact not_lt.mp hn

end Erdos257PeriodNoncollapse
