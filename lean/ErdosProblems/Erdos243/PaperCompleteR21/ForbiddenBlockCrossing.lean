import ErdosProblems.Erdos243.ReciprocalTailRigidity

/-!
# Erdős 243: the shifted CRT block and the bounded-increment barrier

Paper-form restatements of two environments of the long note
`paper/reasoning-parts/erdos243/core.tex`:

* `long243:res:crt`, the shifted block of consecutive multiples, stated for
  the paper's index range `i < B` rather than for `Fin B`;
* `long243:res:barrier`, the exclusion of a family of fresh pairwise coprime
  moduli avoided by a diverging sequence with bounded upward increments,
  stated as the paper's non-existence of such a family and with the paper's
  `gcd (m i) (u t) = 1` in place of `Nat.Coprime`.

Both are immediate specialisations of existing tree declarations: the tree
indexes the block by `Fin B` and carries an extra starting index `N`, which
the paper fixes at `0`.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

/-- **Shifted blocks of consecutive multiples (`long243:res:crt`).**
Let `m 0, …, m (B-1)` be pairwise coprime and at least `2`.  For every bound
`L` there is a `t` beyond it with `m i ∣ t + i` for each `i < B`. -/
theorem exists_shiftedBlock_consecutiveMultiples
    (B : ℕ) (m : ℕ → ℕ)
    (hm : ∀ i, i < B → 2 ≤ m i)
    (hpair : ∀ i, i < B → ∀ j, j < B → i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ t, L < t ∧ ∀ i, i < B → m i ∣ t + i := by
  obtain ⟨x, hxL, hxdvd⟩ :=
    exists_shifted_consecutiveMultiples (k := B) (fun i : Fin B => m i.1)
      (fun i => show 1 < m i.1 by have := hm i.1 i.2; omega)
      (fun i j hij => hpair i.1 i.2 j.1 j.2 (fun hcontra => hij (Fin.ext hcontra)))
      L
  exact ⟨x, hxL, fun i hi => hxdvd ⟨i, hi⟩⟩

/-- **Bounded increases and coprimality to earlier moduli
(`long243:res:barrier`).**
Let `u : ℕ → ℕ` tend to infinity with `u (n+1) ≤ u n + B` for a fixed
integer `B ≥ 1`.  Then there is no family of pairwise coprime `m i ≥ 2`, one
for each index, such that `gcd (m i) (u t) = 1` whenever `i < t`. -/
theorem no_boundedRise_coprimeToEarlierModuli
    (u : ℕ → ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hrise : ∀ n, u (n + 1) ≤ u n + B)
    (hTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    ¬ ∃ m : ℕ → ℕ,
      (∀ i, 2 ≤ m i) ∧
      (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) ∧
      (∀ i t, i < t → Nat.gcd (m i) (u t) = 1) := by
  rintro ⟨m, hm, hpair, havoid⟩
  refine no_boundedRise_of_tailAvoidance u m 0 B (by omega) ?_ ?_ ?_ ?_ hTop
  · intro n _
    have := hm n
    omega
  · intro i j _ _ hij
    exact hpair i j hij
  · intro i t _ hit
    exact havoid i t hit
  · intro n _
    exact hrise n

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exists_shiftedBlock_consecutiveMultiples
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.no_boundedRise_coprimeToEarlierModuli

end ErdosProblems.Erdos243.PaperCompleteR21
