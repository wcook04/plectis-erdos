import ErdosProblems.Erdos257.PaperCompleteR21.LogarithmicInitialInterval

/-!
# Chinese remainder counts over a full period (long #257, line 9212)

The multi-modulus form of the sampling facts used by the long Erdős #257 `thm`
"arithmetic logarithmic counterexample"
(`paper/reasoning-parts/erdos257/a257_front.tex:9212`).  The theorem samples
`N = L m` with `m` uniform over a full period, so every event it uses is a
divisibility condition `a ∣ L m + c` with `a` coprime to `L`, and the paper
asserts that families of such events "remain independent by the Chinese
remainder theorem" and that "different parent groups depend on disjoint prime
coordinates, so the `E_q` are independent".

This module proves the exact finite-family count

  `#{m < M : ∀ i ∈ S, n i ∣ L m + c i} = M / ∏_{i ∈ S} n i`

for pairwise coprime `n i` each coprime to `L`, with `∏ n i ∣ M`, which is that
independence as a statement about counts, for any number of moduli.  It rests on
two steps: the solutions of one condition `a ∣ L m + c` form a single residue
class modulo `a` (`crtExists_residue_dvd_linear`), and a family of congruences
with pairwise coprime moduli is one congruence modulo the product
(`crtModEq_prod_iff`, with `Nat.chineseRemainderOfFinset` supplying a solution).

`crtCard_filter_mod_eq` is the same one-residue-class count as
`card_filter_mod_eq` in
`ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCounterexampleResidueCounts.lean`,
repeated here under a fresh name because that module had no `.olean` when this
one was written and so could not be imported.  Credit for it belongs to that
module; the two-modulus case proved there is the special case `#S = 2` of
`crtCard_filter_dvd_linear_family` with `L = 1`.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset

/-! ### One residue class over a full period -/

/-- A residue class modulo `a` meets `{0, …, M-1}` in exactly `M/a` points when
`a ∣ M`.  (Fresh-name copy of `card_filter_mod_eq`; see the module docstring.) -/
theorem crtCard_filter_mod_eq {M a r : ℕ} (ha : 0 < a) (hr : r < a) (hdvd : a ∣ M) :
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
    have hmul : a * k1 = a * k2 := by omega
    exact Nat.eq_of_mul_eq_mul_left ha hmul
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_range, hMt]

/-! ### The linear condition `a ∣ L m + c` -/

/-- With `a` coprime to `L`, the solutions of `a ∣ L m + c` form a single
residue class modulo `a`.  For `L = 1` this is "the event `q ∣ N + r` has
probability `1/q`"; the general `L` is the paper's sampling of `N = L m`. -/
theorem crtExists_residue_dvd_linear {L a c : ℕ} (ha : 0 < a)
    (hcop : Nat.Coprime a L) :
    ∃ r, r < a ∧ ∀ m : ℕ, (a ∣ L * m + c ↔ m % a = r) := by
  classical
  have hinj : Set.InjOn (fun m => (L * m + c) % a) (Finset.range a : Set ℕ) := by
    intro m1 h1 m2 h2 heq
    simp only at heq
    have hm1 : m1 < a := Finset.mem_range.mp (Finset.mem_coe.mp h1)
    have hm2 : m2 < a := Finset.mem_range.mp (Finset.mem_coe.mp h2)
    have hmod : L * m1 + c ≡ L * m2 + c [MOD a] := heq
    have hcancel : L * m1 ≡ L * m2 [MOD a] := Nat.ModEq.add_right_cancel' c hmod
    have hfin : m1 ≡ m2 [MOD a] := Nat.ModEq.cancel_left_of_coprime hcop hcancel
    have hmm : m1 % a = m2 % a := hfin
    rwa [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2] at hmm
  have hmaps : (Finset.range a).image (fun m => (L * m + c) % a) ⊆ Finset.range a := by
    intro y hy
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr (Nat.mod_lt _ ha)
  have himg : (Finset.range a).image (fun m => (L * m + c) % a) = Finset.range a := by
    refine Finset.eq_of_subset_of_card_le hmaps (le_of_eq ?_)
    rw [Finset.card_image_of_injOn hinj]
  have h0 : (0 : ℕ) ∈ (Finset.range a).image (fun m => (L * m + c) % a) := by
    rw [himg]
    exact Finset.mem_range.mpr ha
  obtain ⟨r, hrmem, hr0⟩ := Finset.mem_image.mp h0
  have hrlt : r < a := Finset.mem_range.mp hrmem
  have hbase : a ∣ L * r + c := Nat.dvd_of_mod_eq_zero hr0
  refine ⟨r, hrlt, fun m => ?_⟩
  constructor
  · intro h
    have h1 : L * m + c ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr h
    have h2 : L * r + c ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr hbase
    have h3 : L * m + c ≡ L * r + c [MOD a] := h1.trans h2.symm
    have h4 : L * m ≡ L * r [MOD a] := Nat.ModEq.add_right_cancel' c h3
    have h5 : m ≡ r [MOD a] := Nat.ModEq.cancel_left_of_coprime hcop h4
    have h6 : m % a = r % a := h5
    rwa [Nat.mod_eq_of_lt hrlt] at h6
  · intro h
    have h5 : m ≡ r [MOD a] := by
      show m % a = r % a
      rw [h, Nat.mod_eq_of_lt hrlt]
    have h4 : L * m ≡ L * r [MOD a] := h5.mul_left L
    have h3 : L * m + c ≡ L * r + c [MOD a] := h4.add_right c
    have h2 : L * r + c ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr hbase
    exact (Nat.modEq_zero_iff_dvd).mp (h3.trans h2)

/-! ### Families of congruences with pairwise coprime moduli -/

/-- A family of congruences with pairwise coprime moduli is one congruence
modulo the product. -/
theorem crtModEq_prod_iff {ι : Type*} [DecidableEq ι] (S : Finset ι) (n : ι → ℕ)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (n i) (n j)) (x y : ℕ) :
    (x ≡ y [MOD ∏ i ∈ S, n i]) ↔ ∀ i ∈ S, x ≡ y [MOD n i] := by
  classical
  revert hcop
  induction S using Finset.induction_on with
  | empty =>
      intro _
      simp [Nat.modEq_one]
  | insert b T hb ih =>
      intro hcop
      have hcopT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Nat.Coprime (n i) (n j) :=
        fun i hi j hj hij =>
          hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hbT : Nat.Coprime (n b) (∏ i ∈ T, n i) :=
        Nat.Coprime.prod_right fun i hi =>
          hcop b (Finset.mem_insert_self b T) i (Finset.mem_insert_of_mem hi)
            (fun h => hb (by rw [h]; exact hi))
      rw [Finset.prod_insert hb, ← Nat.modEq_and_modEq_iff_modEq_mul hbT]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact h1
        · exact (ih hcopT).mp h2 i hi'
      · intro h
        exact ⟨h b (Finset.mem_insert_self b T),
          (ih hcopT).mpr fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

/-- A simultaneous system of congruences with pairwise coprime moduli has a
solution: `Nat.chineseRemainderOfFinset`. -/
theorem crtExists_common {ι : Type*} (S : Finset ι) (n r : ι → ℕ)
    (hn : ∀ i ∈ S, 0 < n i)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (n i) (n j)) :
    ∃ k : ℕ, ∀ i ∈ S, k ≡ r i [MOD n i] := by
  classical
  have hpp : Set.Pairwise (↑S : Set ι) (Function.onFun Nat.Coprime n) := by
    intro i hi j hj hij
    exact hcop i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij
  refine ⟨(Nat.chineseRemainderOfFinset r n S (fun i hi => (hn i hi).ne') hpp).1, ?_⟩
  exact (Nat.chineseRemainderOfFinset r n S (fun i hi => (hn i hi).ne') hpp).2

/-- The count of a simultaneous residue condition over a full period. -/
theorem crtCard_filter_mod_family {ι : Type*} [DecidableEq ι] {M : ℕ}
    (S : Finset ι) (n r : ι → ℕ)
    (hn : ∀ i ∈ S, 0 < n i) (hr : ∀ i ∈ S, r i < n i)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (n i) (n j))
    (hdvd : (∏ i ∈ S, n i) ∣ M) :
    ((Finset.range M).filter (fun m => ∀ i ∈ S, m % n i = r i)).card
      = M / ∏ i ∈ S, n i := by
  classical
  obtain ⟨k, hk⟩ := crtExists_common S n r hn hcop
  have hprodpos : 0 < ∏ i ∈ S, n i := Finset.prod_pos hn
  have hklt : k % (∏ i ∈ S, n i) < ∏ i ∈ S, n i := Nat.mod_lt _ hprodpos
  have hfil : (Finset.range M).filter (fun m => ∀ i ∈ S, m % n i = r i)
      = (Finset.range M).filter
          (fun m => m % (∏ i ∈ S, n i) = k % (∏ i ∈ S, n i)) := by
    refine Finset.filter_congr ?_
    intro m _
    have hkey : (∀ i ∈ S, m % n i = r i) ↔ (∀ i ∈ S, m ≡ k [MOD n i]) := by
      constructor
      · intro h i hi
        show m % n i = k % n i
        have hki : k % n i = r i % n i := hk i hi
        rw [h i hi, hki, Nat.mod_eq_of_lt (hr i hi)]
      · intro h i hi
        have h1 : m % n i = k % n i := h i hi
        have h2 : k % n i = r i % n i := hk i hi
        rw [h1, h2, Nat.mod_eq_of_lt (hr i hi)]
    rw [hkey, ← crtModEq_prod_iff S n hcop m k]
    exact Iff.rfl
  rw [hfil, crtCard_filter_mod_eq hprodpos hklt hdvd]

/-- The paper's independence of the sampled divisibility events, as an exact
count: for pairwise coprime moduli each coprime to `L`, with the product
dividing the period,

  `#{m < M : ∀ i ∈ S, n i ∣ L m + c i} = M / ∏_{i ∈ S} n i`. -/
theorem crtCard_filter_dvd_linear_family {ι : Type*} [DecidableEq ι] {M L : ℕ}
    (S : Finset ι) (n c : ι → ℕ)
    (hn : ∀ i ∈ S, 0 < n i)
    (hcopL : ∀ i ∈ S, Nat.Coprime (n i) L)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (n i) (n j))
    (hdvd : (∏ i ∈ S, n i) ∣ M) :
    ((Finset.range M).filter (fun m => ∀ i ∈ S, n i ∣ L * m + c i)).card
      = M / ∏ i ∈ S, n i := by
  classical
  have hex : ∀ i : ι, i ∈ S →
      ∃ ri, ri < n i ∧ ∀ m : ℕ, (n i ∣ L * m + c i ↔ m % n i = ri) :=
    fun i hi => crtExists_residue_dvd_linear (hn i hi) (hcopL i hi)
  choose! r hrlt hriff using hex
  have hfil : (Finset.range M).filter (fun m => ∀ i ∈ S, n i ∣ L * m + c i)
      = (Finset.range M).filter (fun m => ∀ i ∈ S, m % n i = r i) := by
    refine Finset.filter_congr ?_
    intro m _
    exact forall_congr' fun i => imp_congr_right fun hi => hriff i hi m
  rw [hfil, crtCard_filter_mod_family S n r hn hrlt hcop hdvd]

/-- The same count as a frequency, in the shape the second-moment estimate of
`ArithmeticCounterexampleChebyshev.lean` consumes. -/
theorem crtFreq_dvd_linear_family {ι : Type*} [DecidableEq ι] {M L : ℕ}
    (S : Finset ι) (n c : ι → ℕ)
    (hn : ∀ i ∈ S, 0 < n i)
    (hcopL : ∀ i ∈ S, Nat.Coprime (n i) L)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (n i) (n j))
    (hdvd : (∏ i ∈ S, n i) ∣ M) :
    ((((Finset.range M).filter (fun m => ∀ i ∈ S, n i ∣ L * m + c i)).card : ℕ) : ℝ)
      = ((Finset.range M).card : ℝ) * (1 / ((∏ i ∈ S, n i : ℕ) : ℝ)) := by
  classical
  have hprodpos : 0 < ∏ i ∈ S, n i := Finset.prod_pos hn
  obtain ⟨t, ht⟩ := hdvd
  have hcount := crtCard_filter_dvd_linear_family S n c hn hcopL hcop ⟨t, ht⟩
  rw [hcount, Finset.card_range, ht, Nat.mul_div_cancel_left t hprodpos]
  have hR : (0 : ℝ) < ((∏ i ∈ S, n i : ℕ) : ℝ) := by exact_mod_cast hprodpos
  have hne : ((∏ i ∈ S, n i : ℕ) : ℝ) ≠ 0 := ne_of_gt hR
  have hsimp : (((∏ i ∈ S, n i : ℕ) : ℝ) * (t : ℝ)) * (1 / ((∏ i ∈ S, n i : ℕ) : ℝ))
      = (t : ℝ) := by field_simp
  rw [Nat.cast_mul, hsimp]

#print axioms crtCard_filter_mod_eq
#print axioms crtExists_residue_dvd_linear
#print axioms crtModEq_prod_iff
#print axioms crtExists_common
#print axioms crtCard_filter_mod_family
#print axioms crtCard_filter_dvd_linear_family
#print axioms crtFreq_dvd_linear_family

end ErdosProblems.Erdos257.PaperCompleteR21

end
