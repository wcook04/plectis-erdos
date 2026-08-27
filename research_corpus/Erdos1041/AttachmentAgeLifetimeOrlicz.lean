import Mathlib.Tactic

/-!
# Erdős 1041: attachment-age/lifetime Orlicz consumers

The companion note proves the analytic change of variables
`I_k (exp (-k*x)) = k * Phi x`.  This module checks the algebraic consumers
after that identity and convexity of `Phi` have been supplied.
-/

namespace ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz

/-- The exact edge transform immediately converts a lifetime upper bound into
the corresponding Orlicz upper bound. -/
theorem orlicz_le_of_lifetime_le
    {lifetime size phi budget : ℝ}
    (hsize : 0 < size)
    (hexact : lifetime = size * phi)
    (hbudget : lifetime ≤ budget) :
    phi ≤ budget / size := by
  rw [hexact] at hbudget
  exact (le_div_iff₀ hsize).2 (by simpa [mul_comm] using hbudget)

/-- The scalar chain consumer: after the analytic argument supplies the
ordered comparison between the floor and weighted values, positivity of the
total size transfers the weighted lifetime lower bound to the floor value.
The upstream child-size relation `2 * totalAge ≤ weightedAge` is not an input
to this ordered-algebra lemma. -/
theorem weighted_chain_consumer
    {lifetime totalSize phiAtWeighted phiAtFloor : ℝ}
    (hsize : 0 < totalSize)
    (hexact : lifetime ≥ totalSize * phiAtWeighted)
    (hmono : phiAtFloor ≤ phiAtWeighted) :
    totalSize * phiAtFloor ≤ lifetime := by
  have hmul : totalSize * phiAtFloor ≤ totalSize * phiAtWeighted := by
    exact mul_le_mul_of_nonneg_left hmono (le_of_lt hsize)
  linarith

/-- A sublinear-at-zero Orlicz transform cannot dominate age by any positive
universal linear constant. -/
theorem no_positive_uniform_linear_lower
    (Phi : ℝ → ℝ)
    (hsublinear : ∀ c : ℝ, 0 < c → ∃ x : ℝ, 0 < x ∧ Phi x < c * x) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x → c * x ≤ Phi x := by
  rintro ⟨c, hc, hlower⟩
  obtain ⟨x, hx, hstrict⟩ := hsublinear c hc
  exact (not_lt_of_ge (hlower x hx)) hstrict

/-- Once the root-summed age/product identity is known, the elementary
ordered-age argument selects two roots below the sharp `total/(k-1)`
threshold.  This scalar declaration is the final step of Corollary D1. -/
theorem second_age_le_of_tail_lower
    {secondAge total count : ℝ}
    (hcount : 1 < count)
    (htail : (count - 1) * secondAge ≤ total) :
    secondAge ≤ total / (count - 1) := by
  exact (le_div_iff₀ (sub_pos.mpr hcount)).2 (by simpa [mul_comm] using htail)

end ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz
