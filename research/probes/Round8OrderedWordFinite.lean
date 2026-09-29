import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Ordered affine words: proposed finite proof primitives

Round-8 p2, source 0268dd8bfb2a556a0c93078337d42c6d07138fa2.
UNRUN: no Lean compiler was available in the return environment.
These lemmas are candidate proofs, not kernel receipts. They deliberately do
not assert the independent-clock theorem without its analytic development.
First-letter-outermost convention: T_(a b) = T_a ∘ T_b.
-/

namespace ErdosProblems.Erdos269.OrderedWordTransfer

noncomputable def affine (b c x : ℝ) : ℝ := (c + x) / b

theorem affine_comp (b d c e x : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) :
    affine b c (affine d e x) = affine (b * d) (c * d + e) x := by
  unfold affine
  field_simp
  <;> ring

theorem swap_difference (b d c e x : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) :
    affine b c (affine d e x) - affine d e (affine b c x) =
      (c * (d - 1) - e * (b - 1)) / (b * d) := by
  unfold affine
  field_simp
  <;> ring

theorem affine_difference (b c x y : ℝ) :
    affine b c x - affine b c y = (x - y) / b := by
  unfold affine
  ring

theorem commutator_zero_iff_fixed_point_ratios (b d c e : ℝ)
    (hb : b - 1 ≠ 0) (hd : d - 1 ≠ 0) :
    c * (d - 1) = e * (b - 1) ↔ c / (b - 1) = e / (d - 1) := by
  rw [div_eq_div_iff hb hd]

theorem common_fixed_point (b lam : ℝ) (hb : b ≠ 0) :
    affine b (lam * (b - 1)) lam = lam := by
  unfold affine
  field_simp
  <;> ring

/-- An exact source-known collision. Different four-prime words need not decode. -/
theorem four_prime_collision (x : ℝ) :
    affine 5 1 (affine 7 1 (affine 3 1 (affine 2 1 x))) =
      affine 7 1 (affine 2 1 (affine 3 1 (affine 5 1 x))) := by
  unfold affine
  ring

theorem four_prime_collision_map (x : ℝ) :
    affine 5 1 (affine 7 1 (affine 3 1 (affine 2 1 x))) =
      (51 + x) / 210 := by
  unfold affine
  ring

theorem three_integer_collision (x : ℝ) :
    affine 4 1 (affine 5 1 (affine 2 1 x)) =
      affine 5 1 (affine 2 1 (affine 4 1 x)) := by
  unfold affine
  ring

theorem width_one_endpoint_collision : affine 2 0 1 = affine 2 1 0 := by
  norm_num [affine]

/-- Distinct points whose K-multiples are integers are at least 1/K apart. -/
theorem lattice_separation {x y K : ℝ} {m n : ℤ}
    (hK : 0 < K) (hx : K * x = (m : ℝ)) (hy : K * y = (n : ℝ))
    (hne : x ≠ y) : 1 / K ≤ |x - y| := by
  have hmn : m - n ≠ 0 := by
    intro h
    have heq : m = n := sub_eq_zero.mp h
    have hxy : K * x = K * y := by rw [hx, hy, heq]
    exact hne (mul_left_cancel₀ (ne_of_gt hK) hxy)
  have hZ : (1 : ℤ) ≤ |m - n| := Int.one_le_abs hmn
  have hR : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by exact_mod_cast hZ
  have hid : |(m : ℝ) - (n : ℝ)| = K * |x - y| := by
    rw [← hx, ← hy, ← mul_sub, abs_mul, abs_of_pos hK]
  rw [hid] at hR
  apply (div_le_iff₀ hK).2
  simpa [mul_comm] using hR

/-- Minimal interface consumed by the late-swap proof after taking closure. -/
theorem no_arbitrarily_close_distinct_lattice_pairs (S : Set ℝ) (K : ℝ)
    (hK : 0 < K)
    (hints : ∀ x ∈ S, ∃ m : ℤ, K * x = (m : ℝ))
    (hclose : ∀ eps : ℝ, 0 < eps →
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ |x - y| < eps) : False := by
  obtain ⟨x, hxS, y, hyS, hne, hlt⟩ := hclose (1 / K) (by positivity)
  obtain ⟨m, hm⟩ := hints x hxS
  obtain ⟨n, hn⟩ := hints y hyS
  exact (not_lt_of_ge (lattice_separation hK hm hn hne)) hlt

#print axioms affine_comp
#print axioms swap_difference
#print axioms affine_difference
#print axioms commutator_zero_iff_fixed_point_ratios
#print axioms common_fixed_point
#print axioms four_prime_collision
#print axioms four_prime_collision_map
#print axioms three_integer_collision
#print axioms width_one_endpoint_collision
#print axioms lattice_separation
#print axioms no_arbitrarily_close_distinct_lattice_pairs
#check swap_difference
#check four_prime_collision
#check lattice_separation
#check no_arbitrarily_close_distinct_lattice_pairs

end ErdosProblems.Erdos269.OrderedWordTransfer
