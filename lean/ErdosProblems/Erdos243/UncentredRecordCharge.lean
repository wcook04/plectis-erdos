import ErdosProblems.Erdos243.CoefficientDivisorFence
import ErdosProblems.Erdos243.LcmRecordCrossing

/-!
# Finite ingredients for record charging without centring

Candidate source, review r6. NOT COMPILED in this review.

These statements are finite arithmetic implications. They do not assert the
infinite weighted theorem, Dirichlet's theorem, or the endpoint of Erdős #243.
The existing CRT construction and coefficient fence are reused explicitly.
No barrel or Comparator changes are requested.
-/

namespace ErdosProblems.Erdos243.UncentredRecordCharge

open CoefficientDivisorFence LcmRecordCrossing

/-- An overlap record pays its new height from raw error, once its endpoint
is at least the fixed baseline. No centring hypothesis occurs. -/
theorem nonfresh_record_pays
    (u R y rho B : ℤ)
    (huR : u ≤ R) (hy : 0 < y) (hrho : 2 ≤ rho) (hyB : B ≤ y) :
    y - R ≤ rho * y - u - B := by
  have hprod : 2 * y ≤ rho * y := by nlinarith
  nlinarith

/-- Separate actual jump from overlap cost. -/
theorem raw_error_eq_jump_add_overlap (u y rho : ℤ) :
    rho * y - u = (y - u) + (rho - 1) * y := by ring

/-- A covered first crossing at a fresh step has jump above the baseline,
independently of the coefficient b. -/
theorem fresh_crossing_exceeds_baseline
    (u y L a b tau B : ℤ)
    (hsource : u < tau) (hcross : tau ≤ y)
    (hstep : y = a * u - b * L)
    (hcover : ∀ z : ℤ, tau - B ≤ z → z < tau →
      ∃ m : ℤ, B < m ∧ m ∣ L ∧ m ∣ z) :
    B < y - u := by
  by_contra hnot
  have hsmall : y - u ≤ B := by omega
  obtain ⟨m, hm, hmL, hmu⟩ := hcover u (by omega) hsource
  have hpos : 0 < y - u := by omega
  have hdiv : m ∣ y - u := divides_jump a b L u y m hstep hmu hmL
  have hle : m ≤ y - u := Int.le_of_dvd hpos hdiv
  omega

/-- First-crossed integral heights at an overlap record cost no more than
its record increment. The enclosing interval is (R,y], not (u,y]. -/
theorem crossed_heights_card_le_record_increment
    (walls : Finset ℕ) (R y : ℕ)
    (hmem : ∀ t ∈ walls, R < t ∧ t ≤ y) :
    walls.card ≤ y - R := by
  have hsub : walls ⊆ Finset.Ioc R y := by
    intro t ht
    exact Finset.mem_Ioc.mpr (hmem t ht)
  have hc := Finset.card_le_card hsub
  simpa using hc

/-- The last step of the local realisation lemma: an integral positive
coefficient exists once the congruence and the size inequality are supplied.
The prime in the required residue class is an external Dirichlet input. -/
theorem coefficient_of_divisible_positive_difference
    (a U v L : ℤ) (hL : 0 < L)
    (hpos : v < a * U) (hdiv : L ∣ a * U - v) :
    ∃ b : ℤ, 0 < b ∧ v = a * U - b * L := by
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨b, ?_, ?_⟩
  · by_contra hnot
    have hbnonpos : b ≤ 0 := by omega
    have hprod : L * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hL) hbnonpos
    nlinarith
  · nlinarith [hb]

/-- Compose the already-supplied CRT covering with the already-checked
coefficient fence. This discharges the finite covering hypothesis from an
actual old pairwise-coprime family; it does not produce that family from
an infinite orbit. All hypotheses apply on the chosen shifted tail. -/
theorem bounded_of_old_coprime_moduli
    (a b L U rho : ℕ → ℤ) (B : ℕ) (m : Fin B → ℕ)
    (hm : ∀ i, B < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (hU : ∀ n, 0 < U n)
    (hrho : ∀ n, 1 ≤ rho n)
    (hcap : ∀ n, rho n * U (n + 1) ≤ U n + B)
    (hstep : ∀ n, rho n * U (n + 1) = a n * U n - b n * L n)
    (hmL : ∀ n i, (m i : ℤ) ∣ L n) :
    ∃ H : ℤ, ∀ n, U n < H := by
  classical
  obtain ⟨x, hBP, hPx, _hxhi, hcover⟩ :=
    exists_crt_covering_progression m hm hpair
  let P : ℕ := ∏ i, m i
  let k : ℕ := (U 0).toNat + B + 1
  let z : ℕ := x + k * P
  have hP : 1 ≤ P := by dsimp [P]; omega
  have hxB : B < x := by omega
  have hkP : k ≤ k * P := by nlinarith
  have hzB : (B : ℤ) < z := by
    have hzNat : B < z := by dsimp [z]; omega
    exact_mod_cast hzNat
  have hcastU : ((U 0).toNat : ℤ) = U 0 :=
    Int.toNat_of_nonneg (le_of_lt (hU 0))
  have hstart : U 0 < (z : ℤ) + B := by
    have hnat : (U 0).toNat < z := by dsimp [z, k] at *; omega
    have hcast : (((U 0).toNat : ℕ) : ℤ) < z := by exact_mod_cast hnat
    omega
  have hwall : ((x + B + k * P : ℕ) : ℤ) = (z : ℤ) + B := by
    dsimp [z]
    push_cast
    ring
  refine ⟨(z : ℤ) + B, ?_⟩
  apply stays_below_fence a b L U rho (B : ℤ) (z : ℤ)
    hU hrho (by positivity) hzB hcap hstep hstart
  intro n w hlo hhi
  have hleft : ((x + B + k * P : ℕ) : ℤ) - B ≤ w := by omega
  have hright : w < ((x + B + k * P : ℕ) : ℤ) := by omega
  obtain ⟨d, hd, hdL, hdw⟩ := hcover (L n) (hmL n) k w hleft hright
  exact ⟨d, hd, hdw, hdL⟩

end ErdosProblems.Erdos243.UncentredRecordCharge
