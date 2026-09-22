import Erdos249257.DyadicPrefixCompression
import Erdos249257.CertificateKernel

/-!
Paper-form restatement of `lem:no-ties` (line 5907) of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

The greedy orbit for the target `1/2` and the weights `x_n = 1/(2^n - 1)` is
the tree's `greedyMersenneRemainder (1/2 : ℝ)`: `greedyMersenneRemainder
(1/2) n` is the residual `ρ` after the ranks `1, …, n`, so the residual
entering rank `k` is `greedyMersenneRemainder (1/2) (k - 1)`.  The tail past
rank `k` is `T_{k+1} = ∑_{j > k} x_j = mersenneTail k`.
-/

set_option autoImplicit false

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257

/-- Every rank selected by a finite rational greedy run is at most the run
length. -/
theorem mem_greedyMersennePrefixRat_le {x : ℚ} {n d : ℕ}
    (hd : d ∈ greedyMersennePrefixRat x n) : d ≤ n := by
  classical
  unfold greedyMersennePrefixRat at hd
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
  have hkn := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  omega

/-- The rational greedy residual for the target `1/2`, cast to `ℝ`, is the
real greedy residual. -/
theorem cast_halfGreedyRemainderRat (n : ℕ) :
    ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ)
      = greedyMersenneRemainder (1 / 2 : ℝ) n := by
  have hhalf : (((1 : ℚ) / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
  have hcast := cast_greedyMersenneRemainderRat (1 / 2 : ℚ) n
  rw [hhalf] at hcast
  exact hcast

/-- Every Mersenne tail is irrational.  The base case is Erdős's 1948 theorem
for the Erdős–Borwein constant, instantiated at `b = 2`; each further tail
differs from the previous one by a rational weight. -/
theorem irrational_mersenneTail : ∀ n : ℕ, Irrational (mersenneTail n) := by
  intro n
  induction n with
  | zero =>
      have h := irrational_erdosBorwein_series
      have heq : mersenneTail 0 = ∑' k : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) - 1) := by
        unfold mersenneTail
        simp [mersenneWeight]
      rw [heq]
      exact h
  | succ n ih =>
      have hrec := mersenneTail_eq_weight_add n
      have hsub : mersenneTail (n + 1) = mersenneTail n - mersenneWeight (n + 1) := by
        rw [hrec]
        ring
      rw [hsub]
      rintro ⟨q, hq⟩
      refine ih ⟨q + mersenneWeightRat (n + 1), ?_⟩
      have hcast : ((q + mersenneWeightRat (n + 1) : ℚ) : ℝ)
          = (q : ℝ) + mersenneWeight (n + 1) := by
        rw [Rat.cast_add, cast_mersenneWeightRat]
      rw [hcast, hq]
      ring

/-- Long `lem:no-ties`, take boundary (parity).  The residual after any finite
greedy prefix has even reduced denominator, while every Mersenne weight has odd
denominator, so the take comparison is never a tie. -/
theorem paper_no_ties_take (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneWeight (n + 1) := by
  classical
  intro heq
  have hrat : greedyMersenneRemainderRat (1 / 2 : ℚ) n = mersenneWeightRat (n + 1) := by
    have h1 : ((greedyMersenneRemainderRat (1 / 2 : ℚ) n : ℚ) : ℝ)
        = ((mersenneWeightRat (n + 1) : ℚ) : ℝ) := by
      rw [cast_halfGreedyRemainderRat, cast_mersenneWeightRat]
      exact heq
    exact_mod_cast h1
  have hsub := greedyMersenneRemainderRat_eq_sub_finiteErdosSum (1 / 2 : ℚ) n
  rw [hrat] at hsub
  have hnotmem : (n + 1) ∉ greedyMersennePrefixRat (1 / 2 : ℚ) n := by
    intro hmem
    have hle := mem_greedyMersennePrefixRat_le hmem
    omega
  have hsplit :
      finiteErdosSum (insert (n + 1) (greedyMersennePrefixRat (1 / 2 : ℚ) n)) 2
        = mersenneWeightRat (n + 1) +
          finiteErdosSum (greedyMersennePrefixRat (1 / 2 : ℚ) n) 2 := by
    unfold finiteErdosSum mersenneWeightRat
    rw [Finset.sum_insert hnotmem]
    norm_num
  have hinsert :
      finiteErdosSum (insert (n + 1) (greedyMersennePrefixRat (1 / 2 : ℚ) n)) 2
        = (1 / 2 : ℚ) := by
    rw [hsplit]
    linarith [hsub]
  have h0 : (0 : ℕ) ∉ insert (n + 1) (greedyMersennePrefixRat (1 / 2 : ℚ) n) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · omega
    · exact (zero_not_mem_greedyMersennePrefixRat (1 / 2 : ℚ) n) h
  have hodd :=
    finiteErdosSum_den_odd (insert (n + 1) (greedyMersennePrefixRat (1 / 2 : ℚ) n)) h0
  rw [hinsert] at hodd
  obtain ⟨k, hk⟩ := hodd
  norm_num at hk
  omega

/-- Long `lem:no-ties`, skip-safety boundary (irrationality).  The residual
after a finite Boolean prefix is rational, while every tail `T_{k+1}` is
irrational, so the skip-safety comparison is never a tie either. -/
theorem paper_no_ties_skip (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneTail (n + 1) := by
  intro heq
  refine irrational_mersenneTail (n + 1) ⟨greedyMersenneRemainderRat (1 / 2 : ℚ) n, ?_⟩
  rw [cast_halfGreedyRemainderRat]
  exact heq

/-- Long `lem:no-ties`, in the paper's indexing.  At every rank `k ≥ 2` of the
full greedy orbit for the target `1/2`, both defining comparisons are strict:
`ρ ≠ x_k` and `ρ ≠ T_{k+1}`.  Both boundaries of the fatal interval
`(T_{k+1}, x_k)` are therefore approached only strictly, at every rank,
unconditionally. -/
theorem paper_no_ties (k : ℕ) (hk : 2 ≤ k) :
    greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneWeight k ∧
      greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneTail k := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  have e : m + 1 - 1 = m := by omega
  rw [e]
  exact ⟨paper_no_ties_take m, paper_no_ties_skip m⟩

/-! ## `prop:one-orbit` (line 5888): stability of each fixed greedy prefix -/

/-- The greedy rule applied to an arbitrary target `t` and an arbitrary weight
system `v`, in increasing order of rank, starting at rank `2`.
`tailGreedyRemainder t v m` is the residual after the ranks `2, …, m + 1`, so
the decision at rank `n ≥ 2` is `v n ≤ tailGreedyRemainder t v (n - 2)`. -/
noncomputable def tailGreedyRemainder (t : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | m + 1 =>
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m

theorem tailGreedyRemainder_zero (t : ℝ) (v : ℕ → ℝ) :
    tailGreedyRemainder t v 0 = t := rfl

theorem tailGreedyRemainder_succ (t : ℝ) (v : ℕ → ℝ) (m : ℕ) :
    tailGreedyRemainder t v (m + 1) =
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m := rfl

/-- Rank one is always skipped by the real half-greedy rule, since
`x_1 = 1 > 1/2`; so the real orbit on ranks `≥ 2` starts from `1/2`. -/
theorem halfGreedyRemainder_one :
    greedyMersenneRemainder (1 / 2 : ℝ) 1 = 1 / 2 := by
  have hw : mersenneWeight 1 = 1 := by norm_num [mersenneWeight]
  rw [greedyMersenneRemainder_succ (1 / 2 : ℝ) 0]
  simp only [greedyMersenneRemainder_zero, Nat.zero_add, hw]
  norm_num

/-- The real half-greedy rule, read as a rule on ranks `≥ 2`. -/
theorem tailGreedyRemainder_mersenne (m : ℕ) :
    tailGreedyRemainder (1 / 2 : ℝ) mersenneWeight m
      = greedyMersenneRemainder (1 / 2 : ℝ) (m + 1) := by
  induction m with
  | zero => exact halfGreedyRemainder_one.symm
  | succ m ih =>
      by_cases h : mersenneWeight (m + 1 + 1) ≤
          greedyMersenneRemainder (1 / 2 : ℝ) (m + 1)
      · rw [tailGreedyRemainder_succ, ih, if_pos h,
          greedyMersenneRemainder_succ (1 / 2 : ℝ) (m + 1), if_pos h]
      · rw [tailGreedyRemainder_succ, ih, if_neg h,
          greedyMersenneRemainder_succ (1 / 2 : ℝ) (m + 1), if_neg h]

/-- The inductive core of `prop:one-orbit`: at every fixed depth the
approximate residual converges to the real one, and the decisions up to that
depth eventually agree. -/
theorem approx_orbit_induction
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n))) :
    ∀ r : ℕ,
      Filter.Tendsto (fun j => tailGreedyRemainder (t j) (v j) r) Filter.atTop
          (nhds (greedyMersenneRemainder (1 / 2 : ℝ) (r + 1))) ∧
        ∀ᶠ j in Filter.atTop, ∀ n : ℕ, 2 ≤ n → n ≤ r + 1 →
          ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
            (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))) := by
  intro r
  induction r with
  | zero =>
      refine ⟨?_, Filter.Eventually.of_forall
        (fun _ n hn2 hn => absurd hn (by omega))⟩
      have h1 : greedyMersenneRemainder (1 / 2 : ℝ) (0 + 1) = 1 / 2 := by
        rw [Nat.zero_add]
        exact halfGreedyRemainder_one
      rw [h1]
      simpa only [tailGreedyRemainder_zero] using ht
  | succ r ih =>
      obtain ⟨hR, hB⟩ := ih
      have hw := hv (r + 1 + 1) (by omega)
      have hne := paper_no_ties_take (r + 1)
      have hdiff := hR.sub hw
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hstep :
            greedyMersenneRemainder (1 / 2 : ℝ) (r + 1 + 1)
              = greedyMersenneRemainder (1 / 2 : ℝ) (r + 1) := by
          rw [greedyMersenneRemainder_succ (1 / 2 : ℝ) (r + 1),
            if_neg (not_le.mpr hlt)]
        have hneg : greedyMersenneRemainder (1 / 2 : ℝ) (r + 1)
            - mersenneWeight (r + 1 + 1) < 0 := by linarith
        have hev : ∀ᶠ j in Filter.atTop,
            tailGreedyRemainder (t j) (v j) r - v j (r + 1 + 1) < 0 :=
          hdiff.eventually (gt_mem_nhds hneg)
        have hevSkip : ∀ᶠ j in Filter.atTop,
            tailGreedyRemainder (t j) (v j) r
              = tailGreedyRemainder (t j) (v j) (r + 1) := by
          filter_upwards [hev] with j hj
          rw [tailGreedyRemainder_succ, if_neg (not_le.mpr (by linarith))]
        refine ⟨?_, ?_⟩
        · rw [hstep]
          exact Filter.Tendsto.congr' hevSkip hR
        · filter_upwards [hB, hev] with j hBj hevj
          intro n hn2 hn
          by_cases hnle : n ≤ r + 1
          · exact hBj n hn2 hnle
          · have hneq : n = r + 1 + 1 := by omega
            subst hneq
            have e1 : r + 1 + 1 - 2 = r := by omega
            have e2 : r + 1 + 1 - 1 = r + 1 := by omega
            rw [e1, e2]
            exact iff_of_false (not_le.mpr (by linarith)) (not_le.mpr hlt)
      · have hstep :
            greedyMersenneRemainder (1 / 2 : ℝ) (r + 1 + 1)
              = greedyMersenneRemainder (1 / 2 : ℝ) (r + 1)
                - mersenneWeight (r + 1 + 1) := by
          rw [greedyMersenneRemainder_succ (1 / 2 : ℝ) (r + 1), if_pos hgt.le]
        have hposDiff : (0 : ℝ) < greedyMersenneRemainder (1 / 2 : ℝ) (r + 1)
            - mersenneWeight (r + 1 + 1) := by linarith
        have hev : ∀ᶠ j in Filter.atTop,
            0 < tailGreedyRemainder (t j) (v j) r - v j (r + 1 + 1) :=
          hdiff.eventually (lt_mem_nhds hposDiff)
        have hevTake : ∀ᶠ j in Filter.atTop,
            tailGreedyRemainder (t j) (v j) r - v j (r + 1 + 1)
              = tailGreedyRemainder (t j) (v j) (r + 1) := by
          filter_upwards [hev] with j hj
          rw [tailGreedyRemainder_succ, if_pos (by linarith)]
        refine ⟨?_, ?_⟩
        · rw [hstep]
          exact Filter.Tendsto.congr' hevTake hdiff
        · filter_upwards [hB, hev] with j hBj hevj
          intro n hn2 hn
          by_cases hnle : n ≤ r + 1
          · exact hBj n hn2 hnle
          · have hneq : n = r + 1 + 1 := by omega
            subst hneq
            have e1 : r + 1 + 1 - 2 = r := by omega
            have e2 : r + 1 + 1 - 1 = r + 1 := by omega
            rw [e1, e2]
            exact iff_of_true (by linarith) hgt.le

/-- Long `prop:one-orbit` (line 5888).  Let `t_j → 1/2` and, for each fixed
`n ≥ 2`, let `v_n^{(j)} → x_n` with `v_n^{(j)} > 0`.  Apply the greedy rule
with target `t_j` and weights `v_n^{(j)}` in increasing order of `n`, through
depths `m_j → ∞`.  Then for every fixed depth `K`, the decisions at the ranks
`2, …, K` eventually agree with those of the real half-greedy rule (and the
approximate run eventually reaches depth `K`). -/
theorem paper_one_orbit_stability
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (dep : ℕ → ℕ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n)))
    (hvpos : ∀ j n : ℕ, 0 < v j n)
    (hdep : Filter.Tendsto dep Filter.atTop Filter.atTop)
    (K : ℕ) :
    ∀ᶠ j in Filter.atTop, K ≤ dep j ∧
      ∀ n : ℕ, 2 ≤ n → n ≤ K →
        ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
          (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))) := by
  have hK := (approx_orbit_induction t v ht hv K).2
  have hdepK : ∀ᶠ j in Filter.atTop, K ≤ dep j := hdep.eventually_ge_atTop K
  filter_upwards [hK, hdepK] with j hKj hdepj
  exact ⟨hdepj, fun n hn2 hn => hKj n hn2 (by omega)⟩

#print axioms mem_greedyMersennePrefixRat_le
#print axioms cast_halfGreedyRemainderRat
#print axioms irrational_mersenneTail
#print axioms paper_no_ties_take
#print axioms paper_no_ties_skip
#print axioms paper_no_ties
#print axioms halfGreedyRemainder_one
#print axioms tailGreedyRemainder_mersenne
#print axioms approx_orbit_induction
#print axioms paper_one_orbit_stability
#print axioms Erdos249257.finiteErdosSum_den_odd
#print axioms Erdos249257.halfGreedyPrefixDenominator_odd
#print axioms Erdos249257.irrational_erdosBorwein_series

end ErdosProblems.Erdos257.PaperCompleteR21
