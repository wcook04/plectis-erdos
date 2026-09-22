import ErdosProblems.Erdos243.PaperCompleteR11.CubicZeroDensityShape
import ErdosProblems.Erdos243.PaperCompleteR11.CubicGcdFence

/-!
# Erdős 243: gcd stabilisation and the primitive shape, in paper form

Paper-form restatement of `long243:res:gcdshape` of the long note
`paper/reasoning-parts/erdos243/core.tex`.

The ambient data is the paper's: positive integers `a, C, D` with
`C (n+1) = a n * C n - D n` and `D (n+1) = a n * D n` (written here without
natural subtraction as `C (n+1) + D n = a n * C n`), a rational `A > 0`, a
rational `B`, the proposed profile `P n = A * n * (n+1) * (n+2) + B`, and the
exceptional set `S = {n | C n ≠ P n}` of zero lower density.

The lemma asserts four things, and all four appear in the statement below:

* `6 * A` is a positive integer `M`;
* `G n = gcd (C n, D n)` divides `M` **at every index**, not only late ones;
* `G n` is eventually equal to a positive integer `g`;
* on that tail, with `u n = C n / g`, `v n = D n / g` and `Q n = P n / g`,
  the primitive recurrences `u (n+1) = a n * u n - v n`, `v (n+1) = a n * v n`,
  `gcd (u n, v n) = 1` and `gcd (u n, u (n+1)) = 1` hold
  (`long243:eq:primitivetail`), and there are an integer `m > 0` and
  `c = ±1` with `Q n = (m / 6) * n * (n+1) * (n+2) + c`
  (`long243:eq:Qmc`).

The stabilisation, primitivity, unit constant and profile identity are
supplied by `rational_cubic_zero_density_primitive_shape`; the divisibility
`G n ∣ 6 * A` at every index is proved here from a clean four-index window.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

open ErdosProblems.Erdos243.PaperCompleteR11

/-- The common divisor of the state at **any** index divides the cleared
leading coefficient `6 * A`, because arbitrarily late blocks of four
consecutive indices are exception-free and the third difference of the profile
across such a block is exactly `6 * A`. -/
private theorem state_gcd_dvd_six_leading
    (a C D : ℕ → ℕ) (A B : ℚ) (M : ℤ) (hM : (M : ℚ) = 6 * A)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hzero : ZeroLowerDensity
      {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B})
    (s : ℕ) : (Nat.gcd (C s) (D s) : ℤ) ∣ M := by
  classical
  have hlow : ¬ LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
      (1 / ((4 : ℕ) : ℝ)) := by
    have h := hzero.not_positive_lower_bound (1 / 4) (by norm_num)
    simpa using h
  obtain ⟨n, hsn, hn⟩ := clean_windows_of_not_lower_density
    {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
    4 (by decide) hlow s
  have hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ)
      = A * ((n + j : ℕ) : ℚ) * (((n + j : ℕ) : ℚ) + 1) * (((n + j : ℕ) : ℚ) + 2) + B := by
    intro j hj
    exact not_ne_iff.mp (hn j hj)
  have h0 := hagree 0 (by decide)
  have h1 := hagree 1 (by decide)
  have h2 := hagree 2 (by decide)
  have h3 := hagree 3 (by decide)
  simp only [Nat.add_zero] at h0
  have hthird : (C (n + 3) : ℤ) - 3 * (C (n + 2) : ℤ)
      + 3 * (C (n + 1) : ℤ) - (C n : ℤ) = M := by
    have hQ : (C (n + 3) : ℚ) - 3 * (C (n + 2) : ℚ)
        + 3 * (C (n + 1) : ℚ) - (C n : ℚ) = (M : ℚ) := by
      rw [hM]
      push_cast at h0 h1 h2 h3 ⊢
      linear_combination h3 - 3 * h2 + 3 * h1 - h0
    exact_mod_cast hQ
  have hdvdNat : ∀ j : ℕ, Nat.gcd (C s) (D s) ∣ C (n + j) := by
    intro j
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show s ≤ n + j by omega)
    have h := natural_orbit_common_divisor_tail a C D hC hD s
      (Nat.gcd (C s) (D s)) (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) k
    simpa only [← hk] using h.1
  have hd0 : (Nat.gcd (C s) (D s) : ℤ) ∣ (C n : ℤ) := by
    have := hdvdNat 0
    simp only [Nat.add_zero] at this
    exact_mod_cast this
  have hd1 : (Nat.gcd (C s) (D s) : ℤ) ∣ (C (n + 1) : ℤ) := by
    exact_mod_cast hdvdNat 1
  have hd2 : (Nat.gcd (C s) (D s) : ℤ) ∣ (C (n + 2) : ℤ) := by
    exact_mod_cast hdvdNat 2
  have hd3 : (Nat.gcd (C s) (D s) : ℤ) ∣ (C (n + 3) : ℤ) := by
    exact_mod_cast hdvdNat 3
  rw [← hthird]
  exact dvd_sub (dvd_add (dvd_sub hd3 (dvd_mul_of_dvd_right hd2 3))
    (dvd_mul_of_dvd_right hd1 3)) hd0

/-- **gcd stabilisation and the primitive shape (`long243:res:gcdshape`).**

For a positive orbit `C (n+1) + D n = a n * C n`, `D (n+1) = a n * D n` whose
exceptional set against the cubic profile `A * n * (n+1) * (n+2) + B` has zero
lower density: `6 * A` is a positive integer `M`; every state gcd divides `M`;
the state gcd is eventually a positive constant `g`; and on that tail the
quotients `C n / g`, `D n / g` satisfy the primitive recurrences and both
coprimality relations, while the scaled profile is
`(m / 6) * n * (n+1) * (n+2) + c` for an integer `m > 0` and `c = ±1`. -/
theorem cubic_profile_gcd_stabilisation_and_primitive_shape
    (a C D : ℕ → ℕ) (A B : ℚ) (hA : 0 < A)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hzero : ZeroLowerDensity
      {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}) :
    ∃ M : ℤ, 0 < M ∧ (M : ℚ) = 6 * A ∧
      (∀ n : ℕ, (Nat.gcd (C n) (D n) : ℤ) ∣ M) ∧
      ∃ g N : ℕ, 0 < g ∧
        (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
        ∃ m c : ℤ, 0 < m ∧ (c = 1 ∨ c = -1) ∧
          (∀ n : ℕ,
            (A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B) / (g : ℚ)
              = (m : ℚ) / 6 * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + (c : ℚ)) ∧
          (∀ n, N ≤ n →
            C (n + 1) / g + D n / g = a n * (C n / g) ∧
            D (n + 1) / g = a n * (D n / g) ∧
            Nat.Coprime (C n / g) (D n / g) ∧
            Nat.Coprime (C n / g) (C (n + 1) / g) ∧
            0 < C n / g ∧ 0 < D n / g) := by
  obtain ⟨N, g, m, c, hg, hm, hc, hmcoeff, hccoeff, hprofile, htail⟩ :=
    rational_cubic_zero_density_primitive_shape a C D A B hA hCpos hDpos hC hD hzero
  have hgQ : ((g : ℤ) : ℚ) = (g : ℚ) := by push_cast; ring
  have hMval : ((m * (g : ℤ) : ℤ) : ℚ) = 6 * A := by
    push_cast
    exact_mod_cast hmcoeff
  refine ⟨m * (g : ℤ), ?_, hMval, ?_, g, N, hg, ?_, m, c, hm, hc, ?_, ?_⟩
  · exact mul_pos hm (by exact_mod_cast hg)
  · intro n
    exact state_gcd_dvd_six_leading a C D A B (m * (g : ℤ)) hMval hC hD hzero n
  · intro n hn
    exact (htail n hn).1
  · intro n
    have h := hprofile n
    have hb : (6 : ℚ) * (risingBinomial n : ℚ)
        = (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) := by
      exact_mod_cast six_mul_risingBinomial n
    have hcast : ((m * risingBinomial n + c : ℤ) : ℚ)
        = (m : ℚ) * (risingBinomial n : ℚ) + (c : ℚ) := by push_cast; ring
    rw [h, hcast]
    linear_combination (m : ℚ) / 6 * hb
  · intro n hn
    obtain ⟨_hgcd, hpC, hpD, hcop, hadj, hnum, hden⟩ := htail n hn
    exact ⟨hnum, hden, hcop, hadj, hpC, hpD⟩

#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.cubic_profile_gcd_stabilisation_and_primitive_shape

end ErdosProblems.Erdos243.PaperCompleteR21
