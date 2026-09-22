import ErdosProblems.Erdos257.PaperCompleteR21.LogarithmicInitialInterval

/-!
# Residue counts over a full period (long #257, line 9212)

The sampling facts of the long Erdős #257 `thm` "arithmetic logarithmic
counterexample" (`paper/reasoning-parts/erdos257/a257_front.tex:9212`).  The
theorem samples `N` uniformly modulo `Q` subject to `L ∣ N`, so every event it
uses is a divisibility condition `a ∣ m + c` on a uniform `m` over a full
period, and the paper asserts

* "the event `q ∣ N + r` has probability `1/q`"  (`freq_dvd_add`);
* "conditional on one such event, the tag-prime events remain independent by the
  Chinese remainder theorem"  (`freq_dvd_add_pair`, the pairwise form, which is
  all that Chebyshev's inequality needs).

Both are proved here as exact counts over `Finset.range M`: the solutions of one
divisibility condition form a single residue class, which has exactly `M/a`
representatives when `a ∣ M`, and two conditions with coprime moduli merge into
one residue class modulo `a b`.  The real-valued forms `freq_dvd_add` and
`freq_dvd_add_pair` are stated so that they are literally the marginal and
pairwise hypotheses of the second-moment estimate in
`ArithmeticCounterexampleChebyshev.lean`.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset

/-! ### One residue class over a full period -/

/-- A residue class modulo `a` meets `{0, …, M-1}` in exactly `M/a` points when
`a ∣ M`. -/
theorem card_filter_mod_eq {M a r : ℕ} (ha : 0 < a) (hr : r < a) (hdvd : a ∣ M) :
    ((Finset.range M).filter (fun m => m % a = r)).card = M / a := by
  classical
  obtain ⟨t, rfl⟩ := hdvd
  have hMt : a * t / a = t := Nat.mul_div_cancel_left t ha
  have himg : (Finset.range (a * t)).filter (fun m => m % a = r)
      = (Finset.range t).image (fun k => a * k + r) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hm, hmod⟩
      refine ⟨m / a, ?_, ?_⟩
      · have h := Nat.div_lt_div_of_lt_of_dvd ⟨t, rfl⟩ hm
        rwa [hMt] at h
      · conv_rhs => rw [← Nat.div_add_mod m a]
        rw [hmod]
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, ?_⟩
      · have h1 : a * k + r < a * (k + 1) := by
          have : a * (k + 1) = a * k + a := by ring
          omega
        have h2 : a * (k + 1) ≤ a * t := Nat.mul_le_mul_left a hk
        omega
      · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hinj : Function.Injective (fun k : ℕ => a * k + r) := by
    intro k1 k2 h
    simp only at h
    have : a * k1 = a * k2 := by omega
    exact Nat.eq_of_mul_eq_mul_left ha this
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_range, hMt]

/-- The solutions of `a ∣ m + c` form one residue class modulo `a`. -/
theorem exists_residue_dvd_add (a c : ℕ) (ha : 0 < a) :
    ∃ r, r < a ∧ ∀ m : ℕ, (a ∣ m + c ↔ m % a = r) := by
  set r : ℕ := (a - c % a) % a with hrdef
  have hrlt : r < a := Nat.mod_lt _ ha
  have hbase : a ∣ r + c := by
    have hdm := Nat.div_add_mod c a
    have hmod : c % a < a := Nat.mod_lt _ ha
    rcases Nat.eq_zero_or_pos (c % a) with h0 | hpos
    · have hr0 : r = 0 := by rw [hrdef, h0]; simp
      refine ⟨c / a, ?_⟩
      omega
    · have hr1 : r = a - c % a := by
        rw [hrdef]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨c / a + 1, ?_⟩
      have : a * (c / a + 1) = a * (c / a) + a := by ring
      omega
  refine ⟨r, hrlt, fun m => ?_⟩
  have hrr : r % a = r := Nat.mod_eq_of_lt hrlt
  constructor
  · intro hm
    have h1 : m + c ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr hm
    have h2 : r + c ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr hbase
    have h3 : m + c ≡ r + c [MOD a] := h1.trans h2.symm
    have h4 : m ≡ r [MOD a] := Nat.ModEq.add_right_cancel' c h3
    rw [Nat.ModEq] at h4
    rw [h4, hrr]
  · intro hm
    have h4 : m ≡ r [MOD a] := by
      rw [Nat.ModEq, hrr]
      exact hm
    have h5 : m + c ≡ r + c [MOD a] := h4.add_right c
    have h2 : r + c ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr hbase
    exact (Nat.modEq_zero_iff_dvd).mp (h5.trans h2)

/-- The paper's "the event `q ∣ N + r` has probability `1/q`", as a count. -/
theorem card_filter_dvd_add {M a c : ℕ} (ha : 0 < a) (hdvd : a ∣ M) :
    ((Finset.range M).filter (fun m => a ∣ m + c)).card = M / a := by
  classical
  obtain ⟨r, hrlt, hiff⟩ := exists_residue_dvd_add a c ha
  have hfil : (Finset.range M).filter (fun m => a ∣ m + c)
      = (Finset.range M).filter (fun m => m % a = r) := by
    refine Finset.filter_congr ?_
    intro m _
    exact ⟨fun h => (hiff m).mp h, fun h => (hiff m).mpr h⟩
  rw [hfil, card_filter_mod_eq ha hrlt hdvd]

/-- "Conditional on one such event, the tag-prime events remain independent by
the Chinese remainder theorem": two divisibility conditions with coprime moduli
merge into one residue class modulo the product. -/
theorem card_filter_dvd_add_pair {M a b c d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hdvd : a * b ∣ M) :
    ((Finset.range M).filter (fun m => a ∣ m + c ∧ b ∣ m + d)).card
      = M / (a * b) := by
  classical
  obtain ⟨r, hrlt, hiffa⟩ := exists_residue_dvd_add a c ha
  obtain ⟨s, hslt, hiffb⟩ := exists_residue_dvd_add b d hb
  obtain ⟨k, hka, hkb⟩ := Nat.chineseRemainder hab r s
  have hab0 : 0 < a * b := Nat.mul_pos ha hb
  have hklt : k % (a * b) < a * b := Nat.mod_lt _ hab0
  have hka' : k % a = r := by
    have h : k % a = r % a := hka
    rw [h, Nat.mod_eq_of_lt hrlt]
  have hkb' : k % b = s := by
    have h : k % b = s % b := hkb
    rw [h, Nat.mod_eq_of_lt hslt]
  have hfil : (Finset.range M).filter (fun m => a ∣ m + c ∧ b ∣ m + d)
      = (Finset.range M).filter (fun m => m % (a * b) = k % (a * b)) := by
    refine Finset.filter_congr ?_
    intro m _
    constructor
    · rintro ⟨h1, h2⟩
      have e1 : m ≡ k [MOD a] := by
        show m % a = k % a
        rw [(hiffa m).mp h1, hka']
      have e2 : m ≡ k [MOD b] := by
        show m % b = k % b
        rw [(hiffb m).mp h2, hkb']
      exact (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨e1, e2⟩
    · intro h
      have hmul : m ≡ k [MOD a * b] := h
      obtain ⟨e1, e2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hab).mpr hmul
      refine ⟨(hiffa m).mpr ?_, (hiffb m).mpr ?_⟩
      · have he : m % a = k % a := e1
        rw [he, hka']
      · have he : m % b = k % b := e2
        rw [he, hkb']
  rw [hfil, card_filter_mod_eq hab0 hklt hdvd]

/-! ### The frequencies in the form Chebyshev's inequality consumes -/

/-- `ℙ(a ∣ m + c) = 1/a` over a full period. -/
theorem freq_dvd_add {M a c : ℕ} (ha : 0 < a) (hdvd : a ∣ M) :
    ((((Finset.range M).filter (fun m => a ∣ m + c)).card : ℕ) : ℝ)
      = ((Finset.range M).card : ℝ) * (1 / (a : ℝ)) := by
  classical
  obtain ⟨t, rfl⟩ := hdvd
  rw [card_filter_dvd_add ha ⟨t, rfl⟩, Finset.card_range,
    Nat.mul_div_cancel_left t ha]
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  push_cast
  field_simp

/-- `ℙ(a ∣ m + c and b ∣ m + d) = (1/a)(1/b)` over a full period, for coprime
`a` and `b`. -/
theorem freq_dvd_add_pair {M a b c d : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hdvd : a * b ∣ M) :
    ((((Finset.range M).filter (fun m => a ∣ m + c ∧ b ∣ m + d)).card : ℕ) : ℝ)
      = ((Finset.range M).card : ℝ) * ((1 / (a : ℝ)) * (1 / (b : ℝ))) := by
  classical
  have hab0 : 0 < a * b := Nat.mul_pos ha hb
  obtain ⟨t, rfl⟩ := hdvd
  rw [card_filter_dvd_add_pair ha hb hab ⟨t, rfl⟩, Finset.card_range,
    Nat.mul_div_cancel_left t hab0]
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  push_cast
  field_simp

#print axioms card_filter_mod_eq
#print axioms exists_residue_dvd_add
#print axioms card_filter_dvd_add
#print axioms card_filter_dvd_add_pair
#print axioms freq_dvd_add
#print axioms freq_dvd_add_pair

end ErdosProblems.Erdos257.PaperCompleteR21

end
