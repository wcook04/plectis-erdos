import ErdosProblems.Erdos243.PaperCompleteR11.RecordDivisibility

/-!
# Coprime cores of a finite non-coprime family

Removing gcd(A_i, product of all other A_j) yields pairwise-coprime
cores. The loss is bounded by the product of the pairwise gcds. This avoids
an unproved supply of pairwise-coprime original multipliers in the
non-stabilised-gcd branch of the inclusive argument.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators

/-- Dividing by a larger divisor leaves a divisor of the smaller quotient. -/
theorem quotient_dvd_quotient_of_dvd
    (A G d : ℕ) (hA : 0 < A) (hdG : d ∣ G) (hGA : G ∣ A) :
    A / G ∣ A / d := by
  obtain ⟨k, hk⟩ := hdG
  have hdA : d ∣ A := (show d ∣ G from ⟨k, hk⟩).trans hGA
  have hd : d ≠ 0 := by
    intro h0
    have hz := hdA
    rw [h0] at hz
    simp only [zero_dvd_iff] at hz
    omega
  refine ⟨k, ?_⟩
  apply mul_right_cancel₀ hd
  calc
    (A / d) * d = A := Nat.div_mul_cancel hdA
    _ = (A / G) * G := (Nat.div_mul_cancel hGA).symm
    _ = ((A / G) * k) * d := by rw [hk]; ring

/-- Gcd with a product divides the product of the individual gcds. -/
theorem gcd_prod_dvd_prod_gcd {ι : Type*} [DecidableEq ι]
    (A : ℕ) (s : Finset ι) (f : ι → ℕ) :
    Nat.gcd A (∏ j ∈ s, f j) ∣ ∏ j ∈ s, Nat.gcd A (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj]
      exact (_root_.gcd_mul_dvd_mul_gcd A (f j) (∏ k ∈ s, f k)).trans
        (mul_dvd_mul (dvd_refl _) ih)

noncomputable def coreDenom {B : ℕ} (A : Fin B → ℕ) (i : Fin B) : ℕ :=
  Nat.gcd (A i) (∏ j ∈ Finset.univ.erase i, A j)

noncomputable def coprimeCore {B : ℕ} (A : Fin B → ℕ) (i : Fin B) : ℕ :=
  A i / coreDenom A i

theorem coprimeCore_mul_denom {B : ℕ} (A : Fin B → ℕ) (i : Fin B) :
    coprimeCore A i * coreDenom A i = A i :=
  Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)

theorem coprimeCore_dvd {B : ℕ} (A : Fin B → ℕ) (i : Fin B) :
    coprimeCore A i ∣ A i := ⟨coreDenom A i, (coprimeCore_mul_denom A i).symm⟩

theorem pair_gcd_dvd_coreDenom {B : ℕ} (A : Fin B → ℕ)
    {i j : Fin B} (hij : i ≠ j) : Nat.gcd (A i) (A j) ∣ coreDenom A i := by
  apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
  apply (Nat.gcd_dvd_right (A i) (A j)).trans
  apply Finset.dvd_prod_of_mem
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  exact Ne.symm hij

/-- Pairwise coprimality does not require that any original pair be coprime. -/
theorem coprimeCore_pairwise {B : ℕ} (A : Fin B → ℕ)
    (hA : ∀ i, 0 < A i) :
    ∀ i j, i ≠ j → Nat.Coprime (coprimeCore A i) (coprimeCore A j) := by
  intro i j hij
  have hqi : coprimeCore A i ∣ A i / Nat.gcd (A i) (A j) :=
    quotient_dvd_quotient_of_dvd (A i) (coreDenom A i) (Nat.gcd (A i) (A j))
      (hA i) (pair_gcd_dvd_coreDenom A hij) (Nat.gcd_dvd_left _ _)
  have hqj : coprimeCore A j ∣ A j / Nat.gcd (A i) (A j) := by
    rw [Nat.gcd_comm (A i) (A j)]
    exact quotient_dvd_quotient_of_dvd (A j) (coreDenom A j) (Nat.gcd (A j) (A i))
      (hA j) (pair_gcd_dvd_coreDenom A (Ne.symm hij)) (Nat.gcd_dvd_left _ _)
  have hc := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left (A j) (hA i))
  exact (hc.of_dvd_left hqi).of_dvd_right hqj

/-- Quantified loss: each core loses at most one factor H per other member. -/
theorem le_coprimeCore_mul_gcd_bound {B : ℕ} (A : Fin B → ℕ)
    (hA : ∀ i, 0 < A i) (H : ℕ)
    (hpair : ∀ i j, i ≠ j → Nat.gcd (A i) (A j) ≤ H) (i : Fin B) :
    A i ≤ coprimeCore A i * H ^ (B - 1) := by
  classical
  have hprodpos : 0 < ∏ j ∈ Finset.univ.erase i, Nat.gcd (A i) (A j) := by
    apply Finset.prod_pos
    intro j hj
    exact Nat.gcd_pos_of_pos_left (A j) (hA i)
  have hGle : coreDenom A i ≤ ∏ j ∈ Finset.univ.erase i, Nat.gcd (A i) (A j) :=
    Nat.le_of_dvd hprodpos (gcd_prod_dvd_prod_gcd (A i) (Finset.univ.erase i) A)
  have hprodle : (∏ j ∈ Finset.univ.erase i, Nat.gcd (A i) (A j)) ≤ H ^ (B - 1) := by
    calc
      (∏ j ∈ Finset.univ.erase i, Nat.gcd (A i) (A j)) ≤
          ∏ _j ∈ Finset.univ.erase i, H := by
        apply Finset.prod_le_prod'
        intro j hj
        exact hpair i j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = H ^ (B - 1) := by simp
  calc
    A i = coprimeCore A i * coreDenom A i := (coprimeCore_mul_denom A i).symm
    _ ≤ coprimeCore A i * H ^ (B - 1) := Nat.mul_le_mul_left _ (hGle.trans hprodle)

/-- A genuinely constructed large pairwise-coprime family for CRT. The
size condition is an explicit finite inequality, not a hidden prime supplier. -/
theorem large_coprime_cores {B : ℕ} (A : Fin B → ℕ)
    (hA : ∀ i, 0 < A i) (H : ℕ)
    (hpair : ∀ i j, i ≠ j → Nat.gcd (A i) (A j) ≤ H)
    (hlarge : ∀ i, B * H ^ (B - 1) < A i) :
    (∀ i, B < coprimeCore A i) ∧
    (∀ i j, i ≠ j → Nat.Coprime (coprimeCore A i) (coprimeCore A j)) ∧
    (∀ i, coprimeCore A i ∣ A i) ∧
    (∏ i, coprimeCore A i) ≤ ∏ i, A i := by
  refine ⟨?_, coprimeCore_pairwise A hA, coprimeCore_dvd A, ?_⟩
  · intro i
    have hloss := le_coprimeCore_mul_gcd_bound A hA H hpair i
    have hl := hlarge i
    by_contra hn
    have hmul := Nat.mul_le_mul_right (H ^ (B - 1)) (show coprimeCore A i ≤ B by omega)
    omega
  · apply Finset.prod_le_prod'
    intro i hi
    exact Nat.le_of_dvd (hA i) (coprimeCore_dvd A i)

/-- Combining the constructed cores, bounded CRT phase and nonprimitive
record fence. The infinite log-log argument must still verify the displayed
size and record-cap inequalities; neither is hidden in an existence record. -/
theorem coprime_core_record_fence
    (U : ℕ → ℕ) (D a b : ℕ → ℤ) (T B H : ℕ) (hB : 0 < B)
    (A : Fin B → ℕ) (hA : ∀ i, 0 < A i)
    (hC : ∀ n, (U (n + 1) : ℤ) = a n * U n - b n * D n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hpair : ∀ i j, i ≠ j → Nat.gcd (A i) (A j) ≤ H)
    (hlarge : ∀ i, (max B (runningMax U T)) * H ^ (B - 1) < A i)
    (hOld : ∀ i n, T ≤ n → (A i : ℤ) ∣ D n) :
    ∃ x P : ℕ, P ≤ x ∧ x < 2 * P ∧ P ≤ (∏ i, A i) ∧
      runningMax U T < x ∧
      ((∀ n, T ≤ n → runningMax U n < x + B →
          runningMax U n < U (n + 1) →
          U (n + 1) - runningMax U n ≤ B) →
        ∀ n, U n < x + B) := by
  classical
  have hcores : ∀ i, max B (runningMax U T) < coprimeCore A i := by
    intro i
    have hloss := le_coprimeCore_mul_gcd_bound A hA H hpair i
    have hl := hlarge i
    by_contra hnot
    have hmul := Nat.mul_le_mul_right (H ^ (B - 1))
      (show coprimeCore A i ≤ max B (runningMax U T) by omega)
    omega
  let m : Fin B → ℕ := coprimeCore A
  have hm : ∀ i, B < m i := fun i ↦ (le_max_left B _).trans_lt (hcores i)
  have hpairm := coprimeCore_pairwise A hA
  obtain ⟨x, hBP, hPx, hxP, hcover⟩ :=
    LcmRecordCrossing.exists_crt_covering_progression m hm hpairm
  let P : ℕ := ∏ i, m i
  have hprodpos : 0 < P := by
    apply Finset.prod_pos
    intro i hi
    have hh := hm i
    omega
  let i0 : Fin B := ⟨0, hB⟩
  have hdiv : m i0 ∣ P := by
    dsimp [P]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i0)
  have hR : runningMax U T < x := by
    have hh := hcores i0
    have hmle := Nat.le_of_dvd hprodpos hdiv
    have hmax := le_max_right B (runningMax U T)
    exact (hmax.trans_lt hh).trans_le (hmle.trans hPx)
  have hprodle : P ≤ ∏ i, A i := by
    apply Finset.prod_le_prod'
    intro i hi
    exact Nat.le_of_dvd (hA i) (coprimeCore_dvd A i)
  refine ⟨x, P, hPx, hxP, hprodle, hR, ?_⟩
  intro hcap
  apply bounded_by_record_cover U D a b T x B hC hD hR
  · intro j hj z hzlo hzhi
    have hmD : ∀ i, (m i : ℤ) ∣ D j := by
      intro i
      exact (Int.natCast_dvd_natCast.mpr (coprimeCore_dvd A i)).trans (hOld i j hj)
    obtain ⟨d, hd, hdD, hdz⟩ := hcover (D j) hmD 0 (z : ℤ)
      (by push_cast; omega) (by push_cast; omega)
    exact ⟨d, hd, hdz, hdD⟩
  · exact hcap

end ErdosProblems.Erdos243.PaperCompleteR11
