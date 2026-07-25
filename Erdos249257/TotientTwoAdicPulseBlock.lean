import Erdos249257.TotientTailCarryPeriod

/-!
# Arbitrary two-adic totient pulse blocks

This module isolates the CRT--Dirichlet construction of long totient-increment
blocks modulo powers of two and their exact transfer through the integral tail
carry recurrence.
-/

namespace Erdos249257

open TotientTailPeriodKiller

/-- A prime divisor congruent to one modulo `2^K` forces `2^K` to divide
the totient. -/
theorem twoPow_dvd_totient_of_prime_modEq_one_dvd
    {K r n : ℕ} (hr : r.Prime) (hrK : r ≡ 1 [MOD 2 ^ K]) (hrn : r ∣ n) :
    2 ^ K ∣ Nat.totient n := by
  have hpred : 2 ^ K ∣ r - 1 :=
    (Nat.modEq_iff_dvd' hr.one_le).mp hrK.symm
  have htot : Nat.totient r ∣ Nat.totient n :=
    Nat.totient_dvd_of_dvd hrn
  rw [Nat.totient_prime hr] at htot
  exact hpred.trans htot

/-- The negative of the unique order-two residue modulo `2^K` is the same
residue. -/
theorem neg_twoPow_pred_modEq_self {K : ℕ} (hK : 1 ≤ K) :
    -(2 : ℤ) ^ (K - 1) ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  have hpow : (2 : ℤ) ^ K = 2 * (2 : ℤ) ^ (K - 1) := by
    calc
      (2 : ℤ) ^ K = (2 : ℤ) ^ ((K - 1) + 1) :=
        congrArg (fun e : ℕ => (2 : ℤ) ^ e) (Nat.sub_add_cancel hK).symm
      _ = 2 * (2 : ℤ) ^ (K - 1) := by rw [pow_succ]; ring
  apply Int.modEq_iff_dvd.mpr
  refine ⟨1, ?_⟩
  rw [hpow]
  ring

set_option maxHeartbeats 1000000 in
/-- **Arbitrary two-adic pulse producer, in its stronger divisor form.**
For every `K ≥ 2` and every shift `H > K`, there are cofinally many prime
positions `p` such that

* `p = 1 + 2^(K-1) (mod 2^K)`;
* `2^K ∣ φ(p+H)`;
* for every `1 ≤ j < K`, both `φ(p-j)` and `φ(p-j+H)` are divisible
  by `2^K`.

The proof uses one fresh prime for `p+H` and two fresh primes for every
preceding position.  A single finite CRT glues those conditions to the
half-turn dyadic residue, and Dirichlet supplies the prime `p`. -/
theorem exists_prime_totient_twoAdic_pulse_divisors
    (H K B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧
      2 ^ K ∣ Nat.totient (p + H) ∧
      ∀ j : ℕ, 1 ≤ j → j < K →
        2 ^ K ∣ Nat.totient (p - j) ∧
        2 ^ K ∣ Nat.totient (p - j + H) := by
  classical
  let κ := Unit ⊕ (Fin (K - 1) ⊕ Fin (K - 1))
  let T := 2 ^ K
  let C := max (H + K) T
  have hTpos : 0 < T := by simp [T]
  obtain ⟨q, hq_inj, hq⟩ :=
    exists_large_distinct_primes_modEq_one (ι := κ) K C
  have hqHK (x : κ) : H + K < q x :=
    (Nat.le_max_left (H + K) T).trans_lt (hq x).2.2
  have hqT (x : κ) : T < q x :=
    (Nat.le_max_right (H + K) T).trans_lt (hq x).2.2
  let modulus : Option κ → ℕ
    | none => T
    | some x => q x
  let residue : Option κ → ℕ
    | none => 1 + 2 ^ (K - 1)
    | some (.inl u) => q (.inl u) - H
    | some (.inr (.inl i)) => i.val + 1
    | some (.inr (.inr i)) => q (.inr (.inr i)) + (i.val + 1) - H
  have hmodulus_ne (x : Option κ) : modulus x ≠ 0 := by
    cases x with
    | none => exact hTpos.ne'
    | some x => exact (hq x).1.ne_zero
  have hmodulus_pairwise :
      Set.Pairwise (↑(Finset.univ : Finset (Option κ)) : Set (Option κ))
        (Function.onFun Nat.Coprime modulus) := by
    intro x _ y _ hxy
    cases x with
    | none =>
        cases y with
        | none => exact (hxy rfl).elim
        | some y =>
            have hnot : ¬ q y ∣ T := Nat.not_dvd_of_pos_of_lt hTpos (hqT y)
            exact ((hq y).1.coprime_iff_not_dvd.mpr hnot).symm
    | some x =>
        cases y with
        | none =>
            have hnot : ¬ q x ∣ T := Nat.not_dvd_of_pos_of_lt hTpos (hqT x)
            exact (hq x).1.coprime_iff_not_dvd.mpr hnot
        | some y =>
            have hxy' : x ≠ y := by
              intro h
              apply hxy
              simp [h]
            have hqne : q x ≠ q y := fun h => hxy' (hq_inj h)
            apply ((hq x).1.coprime_iff_not_dvd).2
            intro hdvd
            have heq : q y = q x :=
              (((hq y).1.dvd_iff_eq (hq x).1.ne_one).mp hdvd)
            exact hqne heq.symm
  have hresidue_bounds (x : κ) :
      0 < residue (some x) ∧ residue (some x) < q x := by
    cases x with
    | inl u =>
        cases u
        simp only [residue]
        have hlarge := hqHK (Sum.inl PUnit.unit)
        omega
    | inr x =>
        cases x with
        | inl i =>
            simp only [residue]
            have hi := i.isLt
            have hlarge := hqHK (Sum.inr (Sum.inl i))
            omega
        | inr i =>
            simp only [residue]
            have hi := i.isLt
            have hlarge := hqHK (Sum.inr (Sum.inr i))
            omega
  have hresidue_coprime (x : Option κ) :
      (residue x).Coprime (modulus x) := by
    cases x with
    | none =>
        have hodd : Odd (1 + 2 ^ (K - 1)) := by
          rw [Nat.odd_iff, show K - 1 = (K - 2) + 1 by omega, pow_succ]
          simp
        simpa [residue, modulus, T] using hodd.coprime_two_right.pow_right K
    | some x =>
        have hb := hresidue_bounds x
        have hnot : ¬ q x ∣ residue (some x) :=
          Nat.not_dvd_of_pos_of_lt hb.1 hb.2
        simpa [modulus] using
          (((hq x).1.coprime_iff_not_dvd).2 hnot).symm
  let crt := Nat.chineseRemainderOfFinset residue modulus Finset.univ
    (fun x _ => hmodulus_ne x) hmodulus_pairwise
  let Q := ∏ x : Option κ, modulus x
  have hcrt (x : Option κ) : crt.val ≡ residue x [MOD modulus x] :=
    crt.property x (Finset.mem_univ x)
  have hQ_ne : Q ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x _ => hmodulus_ne x
  have hmodulus_dvd_Q (x : Option κ) : modulus x ∣ Q :=
    Finset.dvd_prod_of_mem modulus (Finset.mem_univ x)
  have hcrt_coprime_Q : crt.val.Coprime Q := by
    rw [Nat.coprime_prod_right_iff]
    intro x _
    rw [Nat.coprime_iff_gcd_eq_one, (hcrt x).gcd_eq]
    simpa [Nat.coprime_iff_gcd_eq_one] using hresidue_coprime x
  obtain ⟨p, hpBound, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (H + K))
      (q := Q) (a := crt.val) hQ_ne hcrt_coprime_Q
  have hpB : B < p := (Nat.le_max_left B (H + K)).trans_lt hpBound
  have hpHK : H + K < p :=
    (Nat.le_max_right B (H + K)).trans_lt hpBound
  have hpLocal (x : Option κ) : p ≡ residue x [MOD modulus x] :=
    (hpmod.of_dvd (hmodulus_dvd_Q x)).trans (hcrt x)
  have hpTwo : p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] := by
    simpa [residue, modulus, T] using hpLocal none
  let top : κ := Sum.inl ()
  have htopDvd : q top ∣ p + H := by
    have hm := (hpLocal (some top)).add_right H
    have hqH : H ≤ q top := by have := hqHK top; omega
    have hm0 : p + H ≡ 0 [MOD q top] := by
      simpa [top, modulus, residue, Nat.ModEq, Nat.sub_add_cancel hqH] using hm
    exact Nat.modEq_zero_iff_dvd.mp hm0
  have htopTot : 2 ^ K ∣ Nat.totient (p + H) := by
    exact twoPow_dvd_totient_of_prime_modEq_one_dvd
      (hq top).1 (by simpa [T] using (hq top).2.1) htopDvd
  refine ⟨p, hpB, hpHK, hp, hpTwo, htopTot, ?_⟩
  intro j hj1 hjK
  let i : Fin (K - 1) := ⟨j - 1, by omega⟩
  let left : κ := Sum.inr (Sum.inl i)
  let right : κ := Sum.inr (Sum.inr i)
  have hi : i.val + 1 = j := by dsimp [i]; omega
  have hjp : j ≤ p := by omega
  have hleftDvd : q left ∣ p - j := by
    have hm : p ≡ j [MOD q left] := by
      simpa [left, modulus, residue, hi] using hpLocal (some left)
    exact (Nat.modEq_iff_dvd' hjp).mp hm.symm
  have hrightDvd : q right ∣ p - j + H := by
    have hm := (hpLocal (some right)).add_right H
    have hsum : H ≤ q right + j := by
      have := hqHK right
      omega
    have hmj : p + H ≡ j [MOD q right] := by
      simpa [right, modulus, residue, hi, Nat.ModEq,
        Nat.sub_add_cancel hsum] using hm
    have hdvd : q right ∣ p + H - j :=
      (Nat.modEq_iff_dvd' (by omega : j ≤ p + H)).mp hmj.symm
    simpa [show p - j + H = p + H - j by omega] using hdvd
  constructor
  · exact twoPow_dvd_totient_of_prime_modEq_one_dvd
      (hq left).1 (by simpa [T] using (hq left).2.1) hleftDvd
  · exact twoPow_dvd_totient_of_prime_modEq_one_dvd
      (hq right).1 (by simpa [T] using (hq right).2.1) hrightDvd

/-- The divisor producer rewritten as the desired `deltaTotient` pulse block:
the preceding `K-1` letters vanish modulo `2^K`, while the terminal prime
letter is the half-turn `2^(K-1)`. -/
theorem exists_prime_deltaTotient_twoAdic_pulseBlock
    (H K B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K] := by
  obtain ⟨p, hpB, hpHK, hp, hpTwo, htop, hlower⟩ :=
    exists_prime_totient_twoAdic_pulse_divisors H K B hK hHK
  have hpPred : p - 1 ≡ 2 ^ (K - 1) [MOD 2 ^ K] := by
    have hsub := hpTwo.sub hp.one_le (by simp : 1 ≤ 1 + 2 ^ (K - 1))
      (Nat.ModEq.refl 1)
    simpa using hsub
  have hpTotNat : Nat.totient p ≡ 2 ^ (K - 1) [MOD 2 ^ K] := by
    simpa [Nat.totient_prime hp] using hpPred
  have hpTotInt :
      (Nat.totient p : ℤ) ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
    simpa using Int.natCast_modEq_iff.mpr hpTotNat
  have htopInt :
      (Nat.totient (p + H) : ℤ) ≡ 0 [ZMOD (2 : ℤ) ^ K] := by
    apply Int.modEq_zero_iff_dvd.mpr
    exact_mod_cast htop
  have hterminalNeg :
      deltaTotient H p ≡ -(2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
    simpa [deltaTotient] using htopInt.sub hpTotInt
  refine ⟨p, hpB, hpHK, hp,
    hterminalNeg.trans (neg_twoPow_pred_modEq_self (by omega)), ?_⟩
  intro j hj1 hjK
  obtain ⟨hbot, htopj⟩ := hlower j hj1 hjK
  have hbotInt : (2 : ℤ) ^ K ∣ (Nat.totient (p - j) : ℤ) := by
    exact_mod_cast hbot
  have htopjInt : (2 : ℤ) ^ K ∣ (Nat.totient (p - j + H) : ℤ) := by
    exact_mod_cast htopj
  apply Int.modEq_zero_iff_dvd.mpr
  simpa [deltaTotient] using dvd_sub htopjInt hbotInt

/-- A discrepancy word vanishes modulo `P` when every letter in the word
vanishes modulo `P`. -/
theorem windowDiscrepancy_modEq_zero_of_delta_zero
    {h N L : ℕ} {P : ℤ}
    (hzero : ∀ i : ℕ, i < L → deltaTotient h (N + i + 1) ≡ 0 [ZMOD P]) :
    windowDiscrepancy h N L ≡ 0 [ZMOD P] := by
  induction L with
  | zero => simp [windowDiscrepancy]
  | succ L ih =>
      rw [windowDiscrepancy_succ]
      have hprefix := ih (fun i hi => hzero i (Nat.lt_succ_of_lt hi))
      have hlast := hzero L (Nat.lt_succ_self L)
      simpa using (hprefix.mul_left 2).add hlast

/-- A zero prefix followed by a half-turn pulse makes the entire length-`K`
discrepancy word a half-turn modulo `2^K`. -/
theorem windowDiscrepancy_modEq_half_of_twoAdic_pulse
    {H K p : ℕ} (hK : 2 ≤ K) (hpK : K ≤ p)
    (hterminal : deltaTotient H p ≡ (2 : ℤ) ^ (K - 1)
      [ZMOD (2 : ℤ) ^ K])
    (hzero : ∀ j : ℕ, 1 ≤ j → j < K →
      deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) :
    windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1)
      [ZMOD (2 : ℤ) ^ K] := by
  have hzero' : ∀ i : ℕ, i < K - 1 →
      deltaTotient H ((p - K) + i + 1) ≡ 0 [ZMOD (2 : ℤ) ^ K] := by
    intro i hi
    let j := K - i - 1
    have hj1 : 1 ≤ j := by dsimp [j]; omega
    have hjK : j < K := by dsimp [j]; omega
    have hpos : (p - K) + i + 1 = p - j := by dsimp [j]; omega
    rw [hpos]
    exact hzero j hj1 hjK
  have hprefix : windowDiscrepancy H (p - K) (K - 1) ≡ 0
      [ZMOD (2 : ℤ) ^ K] :=
    windowDiscrepancy_modEq_zero_of_delta_zero hzero'
  have hKsplit : (K - 1) + 1 = K := Nat.sub_add_cancel (by omega)
  have hrec : windowDiscrepancy H (p - K) K =
      2 * windowDiscrepancy H (p - K) (K - 1) +
        deltaTotient H ((p - K) + (K - 1) + 1) := by
    calc
      windowDiscrepancy H (p - K) K =
          windowDiscrepancy H (p - K) ((K - 1) + 1) :=
        congrArg (windowDiscrepancy H (p - K)) hKsplit.symm
      _ = 2 * windowDiscrepancy H (p - K) (K - 1) +
          deltaTotient H ((p - K) + (K - 1) + 1) :=
        windowDiscrepancy_succ H (p - K) (K - 1)
  rw [hrec]
  have hsum := (hprefix.mul_left 2).add hterminal
  simpa [show (p - K) + (K - 1) + 1 = p by omega] using hsum

/-- **Exact arbitrary-depth orbit transfer.**  Starting at `p-K`, the
homogeneous state is multiplied by `2^K` and disappears modulo `2^K`; the
zero prefix contributes nothing, and the terminal half-turn survives its
sign because it is the unique order-two residue. -/
theorem integral_tailDiff_modEq_half_of_twoAdic_pulse
    {H K N₀ p : ℕ} (hK : 2 ≤ K) (hpN : N₀ + K ≤ p)
    (hterminal : deltaTotient H p ≡ (2 : ℤ) ^ (K - 1)
      [ZMOD (2 : ℤ) ^ K])
    (hzero : ∀ j : ℕ, 1 ≤ j → j < K →
      deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K])
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  have hpK : K ≤ p := by omega
  obtain ⟨d, hd⟩ := hint (p - K) (by omega)
  let z := carryOrbit H (p - K) d K
  have hz : (z : ℝ) = totientTail (p + H) - totientTail p := by
    dsimp [z]
    simpa [Nat.sub_add_cancel hpK] using carryOrbit_eq_tail_diff hd K
  have hreset := carryOrbit_modEq_neg_windowDiscrepancy H (p - K) d K
  have hwindow :=
    windowDiscrepancy_modEq_half_of_twoAdic_pulse hK hpK hterminal hzero
  have hzneg : z ≡ -(2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
    exact hreset.trans hwindow.neg
  exact ⟨z, hz, hzneg.trans (neg_twoPow_pred_modEq_self (by omega))⟩

/-- Under eventual integrality, the CRT producer yields cofinally many actual
tail-difference representatives in the half-turn class modulo `2^K`. -/
theorem eventual_integral_tailDiff_has_cofinal_twoAdic_half_pulse
    {H K N₀ : ℕ} (hK : 2 ≤ K) (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] := by
  intro B
  obtain ⟨p, hpBound, _hpHK, hp, hterminal, hzero⟩ :=
    exists_prime_deltaTotient_twoAdic_pulseBlock H K (max B (N₀ + K)) hK hHK
  have hpN : N₀ + K ≤ p :=
    (Nat.le_max_right B (N₀ + K)).trans hpBound.le
  obtain ⟨z, hz, hzmod⟩ :=
    integral_tailDiff_modEq_half_of_twoAdic_pulse hK hpN hterminal hzero hint
  exact ⟨p, (Nat.le_max_left B (N₀ + K)).trans_lt hpBound,
    hp, z, hz, hzmod⟩

end Erdos249257
