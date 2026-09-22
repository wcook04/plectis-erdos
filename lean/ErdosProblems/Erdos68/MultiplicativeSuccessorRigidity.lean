import ErdosProblems.Erdos68.FactorialGapPlateauCore

/-!
# Erdős #68: multiplicative rigidity of the strict successors

Let

`N m = strictFacTopRat (factorialGapPrefix m) m = ⌊m! · P m⌋ + 1`,   `P m = ∑_{n=2}^m 1/(n!-1)`.

`FactorialGapPlateauCore` proves the exact radix recurrence

`N m = m · N (m-1) + 1 - carry m`

together with `carry m = 1 ↔ (m : ℤ) ∣ N m`, and

`irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses`.

The observation formalised here is that these two facts already force the
rational branch to be **purely multiplicative**: on the rational branch the
carry is pinned to `1`, the additive term `1 - carry m` vanishes identically,
and the recurrence degenerates to `N m = m · N (m-1)`.  Consequently

* `N j ∣ N m` for every `j ≤ m` past the branch threshold, and
* `j! · N m = m! · N j`, so `N m / m!` is *eventually constant*.

Two consequences are recorded.

`eventually_dvd_gapSuccessor_of_not_irrational` — the positive theorem: if the
series is not irrational then **every** fixed modulus `d` eventually divides
`N m`.  In particular `N m` is eventually even.

`irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor` — its
contrapositive, a producer family indexed by `d`: a cofinal failure of the
single congruence `N m ≡ 0 (mod d)` proves irrationality.  At `d = 2` this is
`irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor`: it suffices to
show that `N m` is odd infinitely often.

Relation to the canonical producer.  The canonical open producer is the
*exact equivalence* `irrational ↔ cofinally many m with ¬ m ∣ N m`, which tests
the full residue of `N m` modulo the moving index `m`.  The statements here are
strictly weaker hypotheses in the logical sense — each is sufficient, none is
equivalent — and they do not replace it.  Their content is that the test may be
carried out against one *fixed* modulus, chosen in advance and independent of
`m`, which moves the remaining obstruction out of the Archimedean
shrinking-target category and into a fixed-density congruence category.  Nothing
below proves that any such cofinal failure occurs.
-/

namespace ErdosProblems.Erdos68

/-- The exact integer strict successor of the rational prefix at index `m`. -/
def gapSuccessor (m : ℕ) : ℤ :=
  strictFacTopRat (factorialGapPrefix m) m

theorem gapSuccessor_def (m : ℕ) :
    gapSuccessor m = strictFacTopRat (factorialGapPrefix m) m := rfl

/-! ## The rational branch is multiplicative -/

/-- **Degenerate recurrence.**  At an index carrying the unit rounding digit
the additive term of the radix recurrence vanishes and the strict successor is
exactly `m` times its predecessor. -/
theorem gapSuccessor_eq_mul_pred_of_dvd
    {m : ℕ} (hm : 3 ≤ m) (h : (m : ℤ) ∣ gapSuccessor m) :
    gapSuccessor m = (m : ℤ) * gapSuccessor (m - 1) := by
  have hcarry : factorialGapStepCarry m = 1 :=
    (factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm).2 h
  have hstep :=
    strictFacTop_factorialGapPrefix_step (m := m) (by omega)
  rw [strictFacTop_ratCast, strictFacTop_ratCast, hcarry] at hstep
  simpa [gapSuccessor] using hstep

/-- **Divisibility chain.**  Past the branch threshold every strict successor
divides all later ones. -/
theorem gapSuccessor_dvd_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m → gapSuccessor j ∣ gapSuccessor m := by
  intro m hjm
  induction m, hjm using Nat.le_induction with
  | base => exact dvd_rfl
  | succ n hn ih =>
      have hn1 : M ≤ n + 1 := le_trans hj (by omega)
      have h3 : 3 ≤ n + 1 := le_trans hM hn1
      have hstep := gapSuccessor_eq_mul_pred_of_dvd h3 (h (n + 1) hn1)
      simp only [Nat.add_sub_cancel] at hstep
      rw [hstep]
      exact ih.mul_left _

/-- **Multiplicative normal form.**  Past the branch threshold `N m / m!` is
constant: `j! · N m = m! · N j` for all `j ≤ m`. -/
theorem factorial_mul_gapSuccessor_eq_of_eventually_dvd
    {M : ℕ} (hM : 3 ≤ M)
    (h : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k)
    {j : ℕ} (hj : M ≤ j + 1) :
    ∀ m, j ≤ m →
      (j.factorial : ℤ) * gapSuccessor m = (m.factorial : ℤ) * gapSuccessor j := by
  intro m hjm
  induction m, hjm using Nat.le_induction with
  | base => ring
  | succ n hn ih =>
      have hn1 : M ≤ n + 1 := le_trans hj (by omega)
      have h3 : 3 ≤ n + 1 := le_trans hM hn1
      have hstep := gapSuccessor_eq_mul_pred_of_dvd h3 (h (n + 1) hn1)
      simp only [Nat.add_sub_cancel] at hstep
      have hfac : ((n + 1).factorial : ℤ) = ((n : ℤ) + 1) * (n.factorial : ℤ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hstep, hfac]
      push_cast
      linear_combination ((n : ℤ) + 1) * ih

/-! ## Fixed-modulus rigidity and its producer -/

/-- **Rigidity.**  If the Erdős #68 series is not irrational then every fixed
modulus eventually divides the strict successor.  The modulus is chosen in
advance and does not move with the index. -/
theorem eventually_dvd_gapSuccessor_of_not_irrational
    {d : ℕ} (hd : 0 < d)
    (hrat : ¬ Irrational _root_.Erdos68.factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (d : ℤ) ∣ gapSuccessor m := by
  rw [irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses] at hrat
  push_neg at hrat
  obtain ⟨B, hB⟩ := hrat
  set M : ℕ := max (B + 1) 3 with hMdef
  have hM3 : 3 ≤ M := le_max_right _ _
  have hMB : B + 1 ≤ M := le_max_left _ _
  have hdvd : ∀ k, M ≤ k → (k : ℤ) ∣ gapSuccessor k := by
    intro k hk
    exact hB k (by omega)
  refine ⟨M + d, fun m hm ↦ ?_⟩
  -- the largest multiple of `d` at or below `m` still lies past the threshold
  set j : ℕ := d * (m / d) with hjdef
  have hsplit : j + m % d = m := Nat.div_add_mod m d
  have hmod : m % d < d := Nat.mod_lt _ hd
  have hjle : j ≤ m := by omega
  have hjM : M ≤ j := by omega
  have hdjNat : d ∣ j := ⟨m / d, rfl⟩
  have hdj : (d : ℤ) ∣ (j : ℤ) := Int.natCast_dvd_natCast.mpr hdjNat
  have hchain : gapSuccessor j ∣ gapSuccessor m :=
    gapSuccessor_dvd_of_eventually_dvd hM3 hdvd (by omega) m hjle
  exact hdj.trans ((hdvd j hjM).trans hchain)

/-- **Producer family.**  A cofinal failure of the single fixed congruence
`N m ≡ 0 (mod d)` proves that the Erdős #68 series is irrational.  This is a
sufficient condition, strictly stronger than the canonical equivalence
`irrational ↔ cofinally many m with ¬ m ∣ N m`; it does not replace it. -/
theorem irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor
    {d : ℕ} (hd : 0 < d)
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (d : ℤ) ∣ gapSuccessor m) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  by_contra hrat
  obtain ⟨B, hB⟩ := eventually_dvd_gapSuccessor_of_not_irrational hd hrat
  obtain ⟨m, hmB, hmnot⟩ := h B
  exact hmnot (hB m hmB)

/-- **Parity producer.**  It suffices to prove that the exact strict successor
`⌊m! · P m⌋ + 1` is odd for infinitely many `m`. -/
theorem irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor
    (h : ∀ B : ℕ, ∃ m : ℕ, B < m ∧ ¬ (2 : ℤ) ∣ gapSuccessor m) :
    Irrational _root_.Erdos68.factorialGapSeries :=
  irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor (d := 2)
    (by norm_num) h

/-- Contrapositive form used by the finite certificates: a single odd strict
successor past the branch threshold is inconsistent with the rational branch. -/
theorem not_eventually_odd_gapSuccessor_of_not_irrational
    (hrat : ¬ Irrational _root_.Erdos68.factorialGapSeries) :
    ∃ B : ℕ, ∀ m : ℕ, B < m → (2 : ℤ) ∣ gapSuccessor m :=
  eventually_dvd_gapSuccessor_of_not_irrational (d := 2) (by norm_num) hrat

#print axioms gapSuccessor_eq_mul_pred_of_dvd
#print axioms gapSuccessor_dvd_of_eventually_dvd
#print axioms factorial_mul_gapSuccessor_eq_of_eventually_dvd
#print axioms eventually_dvd_gapSuccessor_of_not_irrational
#print axioms irrational_factorialGapSeries_of_cofinal_not_dvd_gapSuccessor
#print axioms irrational_factorialGapSeries_of_cofinal_odd_gapSuccessor
#print axioms not_eventually_odd_gapSuccessor_of_not_irrational

end ErdosProblems.Erdos68
