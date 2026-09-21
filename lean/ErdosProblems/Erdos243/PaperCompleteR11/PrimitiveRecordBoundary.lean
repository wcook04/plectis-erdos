import ErdosProblems.Erdos243.PaperCompleteR11.SubcriticalRecordBoundary
import ErdosProblems.Erdos243.PaperCompleteR11.PresievedCRT
import ErdosProblems.Erdos243.PaperCompleteR7.Reduction
import Mathlib.Data.Fintype.EquivFin

/-!
# Strict primitive totient amplification


The physical width is W*k^2, whereas only phi(W)*k^2 consecutive
multipliers are needed. The exact cardinality supplies the assignment;
the actual denominator supplies the product-height estimate. Neither
CRT phases nor growing blocks are supplied as extra hypotheses.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open PaperCompleteR7
open scoped BigOperators

/-- A convenient elementary bound for a terminal selected multiplier. -/
theorem twice_index_le_two_pow (n : ℕ) (hn : 2 ≤ n) : 2 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      omega

/-- An old denominator factor is coprime to every later multiplier of a
primitive orbit, with the ordering condition explicitly retained. -/
theorem primitive_old_factor_coprime
    (a U D : ℕ → ℕ)
    (hred : ∀ n, Nat.Coprime (U n) (D n))
    (hU : ∀ n, U (n + 1) + D n = a n * U n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (W S n : ℕ) (hWS : W ∣ D S) (hSn : S ≤ n) :
    Nat.Coprime W (a n) := by
  have hWD := dvd_denState_of_le a D 0 W S (fun n _ ↦ hD n)
    (Nat.zero_le S) hWS n hSn
  have hacop := (persistent_coprimality a U D hred hU hD).1 n
  have hd : Nat.gcd W (a n) ∣ 1 := by
    simpa only [hacop.gcd_eq_one] using Nat.dvd_gcd
      (Nat.gcd_dvd_right W (a n)) ((Nat.gcd_dvd_left W (a n)).trans hWD)
  exact Nat.dvd_one.mp hd

/-- The complete strict boundary for a primitive exact orbit. The
coefficient condition is division-free: c*phi(W) < W. -/
theorem no_primitive_totient_record_cap
    (a U D : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (hUpos : ∀ n, 0 < U n) (hDpos : ∀ n, 0 < D n)
    (hU : ∀ n, U (n + 1) + D n = a n * U n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hred : ∀ n, Nat.Coprime (U n) (D n))
    (hlower : ∃ N : ℕ, ∀ k, 2 * binaryTower k ≤ a (N + k))
    (hrecord : ∃ K : ℕ, ∀ n, runningMax U n ≤ 2 ^ (K + n))
    (hden : ∃ L : ℕ, ∀ n, D n ≤ binaryTower (n + L))
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n)
    (W S : ℕ) (hW : 1 < W) (hWS : W ∣ D S)
    (g : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hcW : c * Nat.totient W < W) :
    ¬ ∃ T : ℕ, ∀ n, T ≤ n → runningMax U n < U (n + 1) →
      ((U (n + 1) - runningMax U n : ℕ) : ℝ) ≤
        c * recordLogLog (g * runningMax U n : ℕ) := by
  classical
  rintro ⟨T, hcap⟩
  obtain ⟨N, hN⟩ := hlower
  obtain ⟨K, hK⟩ := hrecord
  obtain ⟨L, hL⟩ := hden
  obtain ⟨k₀, hk₀⟩ := eventual_quadratic_budget c (Nat.totient W) W
    (N + L + g + 2) hc0 hcW
  let k := max (K + N + 3) (max (S + T + W) k₀)
  let B := W * k ^ 2
  let Q := Nat.totient W * k ^ 2
  let J := N + k
  let M := J + Q
  let I := {r // r ∈ presievedOffsets W B}
  have hklarge : K + N + 3 ≤ k := le_max_left _ _
  have hkSTW : S + T + W ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  have hk₀k : k₀ ≤ k := (le_max_right _ _).trans (le_max_right _ _)
  have hkpos : 0 < k := by omega
  have hphipos : 0 < Nat.totient W := Nat.totient_pos.mpr (by omega)
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hcard : Fintype.card I = Q := by
    simpa [I, B, Q, Nat.mul_comm] using presievedOffsets_card_mul W (k ^ 2)
  let e : I ≃ Fin Q := Fintype.equivFinOfCardEq hcard
  let m : I → ℕ := fun i ↦ a (J + e i)
  let P : ℕ := W * ∏ i, m i
  have hprod : (∏ i, m i) = ∏ j : Fin Q, a (J + j) := by
    exact e.prod_comp (fun j : Fin Q ↦ a (J + j))
  have hSJ : S ≤ J := by dsimp [J]; omega
  have hTM : T ≤ M := by dsimp [M, J]; omega
  have hWold : ∀ n, M ≤ n → W ∣ D n := by
    intro n hn
    exact dvd_denState_of_le a D 0 W S (fun n _ ↦ hD n)
      (Nat.zero_le S) hWS n (by dsimp [M] at hn; omega)
  have hm : ∀ i, 1 < m i := by
    intro i
    have hlo := hN k
    have hmono := ha.monotone (show N + k ≤ J + e i by dsimp [J]; omega)
    have ht := binaryTower_pos k
    dsimp [m]
    omega
  have hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j) := by
    intro i j hij
    apply (persistent_coprimality a U D hred hU hD).2.1
    intro heq
    apply hij
    apply e.injective
    apply Fin.ext
    omega
  have hWm : ∀ i, Nat.Coprime W (m i) := by
    intro i
    exact primitive_old_factor_coprime a U D hred hU hD W S (J + e i)
      hWS (by omega)
  have hmold : ∀ i n, M ≤ n → m i ∣ D n := by
    intro i n hn
    exact multiplier_block_old a D hD J Q (e i) n hn
  have hPD : P ≤ D M := by
    have hWDJ : W ≤ D J := Nat.le_of_dvd (hDpos J)
      (dvd_denState_of_le a D 0 W S (fun n _ ↦ hD n)
        (Nat.zero_le S) hWS J hSJ)
    dsimp [P, M]
    rw [hprod, denominator_block_product a D hD J Q]
    exact Nat.mul_le_mul_right _ hWDJ
  have hsize : runningMax U M < P := by
    let n := k + Q - 1
    have hn2 : 2 ≤ n := by dsimp [n]; omega
    have hMN : M = N + n + 1 := by dsimp [M, J, n]; omega
    have hexp : K + M ≤ 2 ^ n := by
      have hkn : K + M ≤ 2 * n := by dsimp [M, J, n]; omega
      exact hkn.trans (twice_index_le_two_pow n hn2)
    have hrec : runningMax U M ≤ binaryTower n := (hK M).trans (two_pow_mono hexp)
    let j : Fin Q := ⟨Q - 1, by omega⟩
    have hjidx : J + j = N + n := by dsimp [J, j, n]; omega
    have hlast : a (N + n) ≤ ∏ j : Fin Q, a (J + j) := by
      have hd : a (J + j) ∣ ∏ j : Fin Q, a (J + j) :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      have hp : 0 < ∏ j : Fin Q, a (J + j) :=
        Finset.prod_pos (fun j _ ↦ hapos _)
      simpa only [hjidx] using Nat.le_of_dvd hp hd
    have hprodP : (∏ j : Fin Q, a (J + j)) ≤ P := by
      dsimp [P]
      rw [hprod]
      have hW1 : 1 ≤ W := by omega
      simpa only [one_mul] using Nat.mul_le_mul_right
        (∏ j : Fin Q, a (J + j)) hW1
    have halarge := hN n
    exact (lt_of_le_of_lt hrec (by have := binaryTower_pos n; omega :
      binaryTower n < a (N + n))).trans_le (hlast.trans hprodP)
  obtain ⟨x, hPx, hxP, hfence⟩ := presieved_primitive_record_fence_from_moduli
    U D W B M (by omega) m hm hpair hWm (fun n _ ↦ hred n) hWold hmold hsize
  have hPtower : P ≤ binaryTower (M + L) := hPD.trans (hL M)
  have hBtower : B ≤ binaryTower (M + L) := by
    have hkpow : k ≤ 2 ^ k := by have := index_succ_le_two_pow k; omega
    have hWk : W ≤ k := by omega
    have hBcube : B ≤ k ^ 3 := by
      dsimp [B]
      calc
        W * k ^ 2 ≤ k * k ^ 2 := Nat.mul_le_mul_right _ hWk
        _ = k ^ 3 := by ring
    have hcube : k ^ 3 ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left hkpow 3
    have hk2 : 2 ≤ k := by omega
    have h3k : 3 * k ≤ 2 ^ (k + 1) := by
      have hh := twice_index_le_two_pow k hk2
      rw [pow_succ]
      omega
    have hh : (2 ^ k) ^ 3 ≤ binaryTower (k + 1) := by
      rw [← pow_mul]
      exact two_pow_mono (by omega)
    exact (hBcube.trans (hcube.trans hh)).trans
      (binaryTower_mono (by dsimp [M, J]; omega))
  have hheight := scaled_crt_height_logLog g P B (M + L) hPtower hBtower
  have hbudget : c * (M + L + g + 2 : ℕ) ≤ (B : ℝ) := by
    have hh := hk₀ k hk₀k
    dsimp [M, J, Q, B]
    push_cast
    push_cast at hh
    nlinarith
  have hbounded : ∀ n, U n < x + B := by
    apply hfence
    intro n hn hR hnew
    have hfirst := hcap n (hTM.trans hn) hnew
    have hRbound : runningMax U n ≤ 2 * P + B :=
      (Nat.le_of_lt hR).trans (Nat.add_le_add_right (Nat.le_of_lt hxP) B)
    have hRheight : recordLogLog (g * runningMax U n : ℕ) ≤
        recordLogLog (g * (2 * P + B) : ℕ) :=
      recordLogLog_nat_mul_mono g hRbound
    have hfinal : ((U (n + 1) - runningMax U n : ℕ) : ℝ) ≤ (B : ℝ) :=
      hfirst.trans ((mul_le_mul_of_nonneg_left (hRheight.trans hheight) hc0).trans hbudget)
    exact_mod_cast hfinal
  obtain ⟨n, hn⟩ := hunbounded (x + B)
  exact (not_lt_of_ge hn) (hbounded n)

/-- A fixed old modulus greater than one gives a coefficient strictly
above one. This is a statement about every sufficiently late prefix. -/
theorem primitive_cofinal_record_exceeds_totient
    (a U D : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (hUpos : ∀ n, 0 < U n) (hDpos : ∀ n, 0 < D n)
    (hU : ∀ n, U (n + 1) + D n = a n * U n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hred : ∀ n, Nat.Coprime (U n) (D n))
    (hlower : ∃ N : ℕ, ∀ k, 2 * binaryTower k ≤ a (N + k))
    (hrecord : ∃ K : ℕ, ∀ n, runningMax U n ≤ 2 ^ (K + n))
    (hden : ∃ L : ℕ, ∀ n, D n ≤ binaryTower (n + L))
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n)
    (W S : ℕ) (hW : 1 < W) (hWS : W ∣ D S)
    (g : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hcW : c * Nat.totient W < W) (T : ℕ) :
    ∃ n, T ≤ n ∧ runningMax U n < U (n + 1) ∧
      c * recordLogLog (g * runningMax U n : ℕ) <
        ((U (n + 1) - runningMax U n : ℕ) : ℝ) := by
  by_contra hnot
  apply no_primitive_totient_record_cap a U D ha hapos hUpos hDpos hU hD hred
    hlower hrecord hden hunbounded W S hW hWS g c hc0 hcW
  refine ⟨T, fun n hn hnew ↦ ?_⟩
  by_contra hh
  exact hnot ⟨n, hn, hnew, lt_of_not_ge hh⟩

end ErdosProblems.Erdos243.PaperCompleteR11
