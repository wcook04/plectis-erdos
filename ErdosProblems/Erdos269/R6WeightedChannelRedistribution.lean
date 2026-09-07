import ErdosProblems.Erdos269.ThreeChannelBlockRigidity
import Mathlib.Tactic

/-!
# Finite identities for source-compatible channel redistributions

Authored in the round-6 review; NOT compiled in that review environment.
The ordinary memorandum proves the infinite interval-realisation theorem.
This file only supplies finite algebra that such a formalisation can use.
It does not construct the ordered-power word, prove the narrow-cell count,
prove an infinite interval theorem, or prove irrationality of any series.
-/

namespace ErdosProblems.Erdos269.R6

open scoped BigOperators

/-- The unweighted prefix of a vertex coboundary. -/
theorem prefix_coboundary {G : Type*} [AddCommGroup G]
    (v : ℕ → G) (N : ℕ) :
    (∑ n ∈ Finset.range N, (v (n + 1) - v n)) = v N - v 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      abel

/-- A potential vanishing on a selected family of boundaries preserves
all complete blocks between those boundaries. The selected family can be
the union of the 2-power and 3-power boundaries. -/
theorem selected_boundary_prefixes_equal
    {ι G : Type*} [AddCommGroup G]
    (word : ℕ → ι) (selected : ι → Prop) (v : ℕ → G)
    (hv : ∀ n, selected (word n) → v n = 0)
    {a b : ℕ} (ha : selected (word a)) (hb : selected (word b)) :
    channelPrefix (fun n => v (n + 1) - v n) a =
      channelPrefix (fun n => v (n + 1) - v n) b := by
  unfold channelPrefix
  rw [prefix_coboundary, prefix_coboundary, hv a ha, hv b hb]

/-- Exact weighted summation by parts, including the terminal boundary.
For reciprocal heights, w n = 1/H_n. -/
theorem weighted_coboundary_sum
    {R : Type*} [CommRing R] (v w : ℕ → R) (N : ℕ) :
    (∑ n ∈ Finset.range N, (v (n + 1) - v n) * w n) =
      v N * w N - v 0 * w 0 +
        ∑ n ∈ Finset.range N, v (n + 1) * (w n - w (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      ring

/-- The local positivity check for a signed redistribution. -/
theorem redistributed_multiplicity_pos
    {μ vnext vnow : ℤ} (hnext : 0 ≤ vnext) (hcapacity : vnow < μ) :
    0 < μ + (vnext - vnow) := by
  omega

/-- Integer potentials divisible by M preserve every multiplicity modulo M. -/
theorem redistribution_modulus (M a b : ℤ) : M ∣ (M * b - M * a) := by
  refine ⟨b - a, ?_⟩
  ring

/-- A pulse at a five-power boundary has weighted coefficient 4/H_after. -/
theorem five_pulse_weight (h v : ℚ) (hh : h ≠ 0) :
    v * (1 / h - 1 / (5 * h)) = 4 * v / (5 * h) := by
  field_simp [hh]
  <;> ring

/-- The strict numerical margin in the 25-point circle-cover certificate.
The identification of this quantity with the maximum gap is separately
checked by the exact Python certificate and proved in the memorandum. -/
theorem cover_margin : (5 : ℚ) ^ 22 / 2 ^ 51 < 27 / 25 := by
  norm_num

/-- A uniform height-ratio budget for selected five-power exponents whose
gaps are at most three. The reduction from heights to these powers belongs
to the ordinary proof, rather than to this numerical lemma. -/
theorem selected_height_budget : 2 ^ 7 * 3 ^ 5 * 5 ^ 3 = (3888000 : ℕ) := by
  norm_num

end ErdosProblems.Erdos269.R6
