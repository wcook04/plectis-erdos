import ErdosProblems.DemandLedger.Basic
open Erdos249257 Erdos249257.TotientTailPeriodKiller
namespace DemandLedger.ClusterD

/-!
# Cluster D edges: rank-2 q-ray (G099), cone non-flatness menu (G095), prime jump (G098)

The three statements, as the kernel records them:

* `G095` — `∀ t₀, ∃ t ≥ t₀, ∃ L Q, Q ≠ [] ∧ (∀ q ∈ Q, 0 < q) ∧
  (∀ q ∈ Q, q·H_t + L + 2 < 2^L) ∧ coneNonflatCert H_t L Q`,
  where `coneNonflatCert H L Q` says every menu vertex `qᵢ` has a partner `qⱼ`
  with `qⱼ·H + L + 2 < (P_L(qᵢH) − P_L(qⱼH)) % 2^L` (`P_L = windowNumerator`).
* `G098` — `∀ t₀, ∃ t ≥ t₀, ∃ p L, 0 < p ∧ primeJumpSharpKill H_t p L`, a band
  condition on the four-vertex commutator
  `J = P_L(2pH) − P_L(pH) − p·P_L(2H) + p·P_L(H)` at radius `3pH + (p+1)(L+2)`.
* `G099` — `∀ t₀, ∃ t ≥ t₀, ∃ q L, 0 < q ∧ certifiedRank2Kill H_t (q·H_t) L`, a
  band condition at radius `2((q+2)H + L + 2)` on the second difference
  `A₂ = P_L((q+2)H) − 2·P_L((q+1)H) + P_L(qH)`.

The edge proved here is `G099 → G095`.  A rank-2 band at radius `2r` forces one
of the two consecutive first differences out of the radius-`r` band (if both
first differences sat within `r` of `0` on the circle `ℤ/2^L`, their difference
would sit within `2r` of `0`), and `r = (q+2)H + L + 2` is exactly the budget a
two-vertex non-flatness menu `[q+1, q]` or `[q+2, q+1]` needs.

## The five pairs not proved in this file

The elementary finite-certificate conversions attempted here do not prove:

* `G095 → G099`, `G095 → G098`.  A fired menu is a *one-sided lower* bound on
  residues of FIRST differences.  Both targets are bands on a *cancelling*
  combination (`A₂`, resp. `J`), and a combination of quantities each far from
  `0` is not itself far from `0`.  The implication would have to manufacture a
  finite certificate out of a weaker finite certificate about different data.
* `G098 → G095`, `G098 → G099`.  The only elementary route out of a `J`-band is
  to write `J = Σ cₖ (P_L(bₖH) − P_L(aₖH))` and conclude that some `Dₖ` escapes
  a band, at total cost `Σ |cₖ|·(max(aₖ,bₖ)·H + L + 2)`.  Since `J` has
  coefficient `+1` at the vertex `2pH` and total weight `p` at the vertices
  `H, 2H`, every such representation costs at least `4pH + (p+1)(L+2)`, whereas
  `primeJumpSharpRadius H p L = 3pH + (p+1)(L+2)` supplies only that much.  The
  deficit is `pH`, which is unbounded, so no choice of depth `L` closes it.
  (`PrimeJumpWindow` states exactly this: the sharp radius is deliberately
  smaller than "the larger `4pH` radius belonging to the two-cell disjunction".)
  So `G098` is a strictly *weaker-looking* hypothesis than the disjunction it
  would need to feed, and nothing here consumes it.
* `G099 → G098`.  Symmetric to the above: a rank-2 band on the `q`-ray gives no
  control on the four-vertex commutator, whose `p·P_L(2H)` term is not a
  second difference along any ray.

`DemandLedger/edges/Bridge2.lean` later proves the corresponding gap statements
equivalent through the irrationality hub.  The discussion above is therefore a
no-go for these direct finite-certificate conversions, not a claim that the
logical implications remain open in the repository.
-/

/-! ## Window arithmetic -/

/-- The window discrepancy is the difference of the two window numerators. -/
private lemma clusterD_windowDiscrepancy_eq (h N L : ℕ) :
    windowDiscrepancy h N L
      = (windowNumerator (N + h) L : ℤ) - (windowNumerator N L : ℤ) := by
  unfold windowDiscrepancy windowNumerator
  push_cast
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Negating a residue that is not already `0`. -/
private lemma clusterD_emod_neg {x P : ℤ} (hP : 0 < P) (hx : 0 < x % P) :
    (-x) % P = P - x % P := by
  have hlt : x % P < P := Int.emod_lt_of_pos x hP
  have e1 : (-x) % P = (-(x % P)) % P := by
    have h0 : (0 - x) % P = (0 % P - x % P) % P := Int.sub_emod 0 x P
    simpa using h0
  have e2 : (-(x % P)) % P = P - x % P := by
    rw [show -(x % P) = (P - x % P) + P * (-1) from by ring, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [e1, e2]

/-! ## The circle split: a rank-2 band forces a rank-1 band -/

/-- If `B - A` avoids the radius-`2r` neighbourhood of `0` modulo `2^L`, then at
least one of `A`, `B` avoids the radius-`r` neighbourhood of `0`. -/
private lemma clusterD_band_split {A B r : ℤ} {L : ℕ}
    (hlow : 2 * r < (B - A) % 2 ^ L)
    (hhigh : (B - A) % 2 ^ L < 2 ^ L - 2 * r) :
    (r < A % 2 ^ L ∧ A % 2 ^ L < 2 ^ L - r) ∨
      (r < B % 2 ^ L ∧ B % 2 ^ L < 2 ^ L - r) := by
  have hPpos : (0 : ℤ) < 2 ^ L := by positivity
  have hA0 : 0 ≤ A % 2 ^ L := Int.emod_nonneg A hPpos.ne'
  have hA1 : A % 2 ^ L < 2 ^ L := Int.emod_lt_of_pos A hPpos
  have hB0 : 0 ≤ B % 2 ^ L := Int.emod_nonneg B hPpos.ne'
  have hB1 : B % 2 ^ L < 2 ^ L := Int.emod_lt_of_pos B hPpos
  have hsub : (B - A) % 2 ^ L = (B % 2 ^ L - A % 2 ^ L) % 2 ^ L := Int.sub_emod B A (2 ^ L)
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hA' : A % 2 ^ L ≤ r ∨ 2 ^ L - r ≤ A % 2 ^ L := by
    rcases le_or_gt (A % 2 ^ L) r with hc | hc
    · exact Or.inl hc
    · exact Or.inr (hA hc)
  have hB' : B % 2 ^ L ≤ r ∨ 2 ^ L - r ≤ B % 2 ^ L := by
    rcases le_or_gt (B % 2 ^ L) r with hc | hc
    · exact Or.inl hc
    · exact Or.inr (hB hc)
  rcases le_or_gt 0 (B % 2 ^ L - A % 2 ^ L) with hd | hd
  · rw [hsub, Int.emod_eq_of_lt hd (by omega)] at hlow hhigh
    omega
  · have heq : (B % 2 ^ L - A % 2 ^ L) % 2 ^ L = B % 2 ^ L - A % 2 ^ L + 2 ^ L := by
      have hshift : B % 2 ^ L - A % 2 ^ L
          = (B % 2 ^ L - A % 2 ^ L + 2 ^ L) + 2 ^ L * (-1) := by ring
      conv_lhs => rw [hshift]
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hsub, heq] at hlow hhigh
    omega

/-! ## A two-vertex non-flatness menu out of a one-sided band -/

/-- A first difference `P_L(vH) - P_L(uH)` living strictly inside the band
`(u·H+L+2, 2^L - (v·H+L+2))` fires the two-vertex menu `[v, u]`. -/
private lemma clusterD_cone_pair {H L u v : ℕ}
    (h1 : (u : ℤ) * H + L + 2
        < ((windowNumerator (v * H) L : ℤ) - (windowNumerator (u * H) L : ℤ)) % 2 ^ L)
    (h2 : ((windowNumerator (v * H) L : ℤ) - (windowNumerator (u * H) L : ℤ)) % 2 ^ L
        < 2 ^ L - ((v : ℤ) * H + L + 2)) :
    coneNonflatCert H L [v, u] := by
  have hPpos : (0 : ℤ) < 2 ^ L := by positivity
  have hbase : (0 : ℤ) ≤ (u : ℤ) * H + L + 2 := by positivity
  have hpos : (0 : ℤ)
      < ((windowNumerator (v * H) L : ℤ) - (windowNumerator (u * H) L : ℤ)) % 2 ^ L := by
    linarith
  have hneg : (-((windowNumerator (v * H) L : ℤ) - (windowNumerator (u * H) L : ℤ))) % 2 ^ L
      = 2 ^ L - ((windowNumerator (v * H) L : ℤ) - (windowNumerator (u * H) L : ℤ)) % 2 ^ L :=
    clusterD_emod_neg hPpos hpos
  intro qi hqi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hqi
  rcases hqi with rfl | rfl
  · exact ⟨u, by simp, h1⟩
  · refine ⟨v, by simp, ?_⟩
    rw [show ((windowNumerator (qi * H) L : ℤ) - (windowNumerator (v * H) L : ℤ))
        = -((windowNumerator (v * H) L : ℤ) - (windowNumerator (qi * H) L : ℤ)) from by ring,
      hneg]
    linarith

/-! ## The edge -/

/-- **G099 → G095.**  A certified rank-2 kill on the `q`-ray of the lcm cone
splits into a certified first-difference band at one of the two consecutive
cone cells `(q, q+1)`, `(q+1, q+2)`, and the doubled rank-2 radius
`2((q+2)H + L + 2)` pays in full for the two-vertex non-flatness menu there. -/
theorem e_G099_G095 : G099 → G095 := by
  unfold G099 G095
  intro h t₀
  obtain ⟨t, ht, q, L, hq, hkill⟩ := h t₀
  obtain ⟨hlow, hhigh⟩ := hkill
  have hHnn : (0 : ℤ) ≤ (periodLcm t : ℤ) := Int.natCast_nonneg _
  have hLnn : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg _
  have hd2 : windowDiscrepancy2 (periodLcm t) (q * periodLcm t) L
      = ((windowNumerator ((q + 2) * periodLcm t) L : ℤ)
            - (windowNumerator ((q + 1) * periodLcm t) L : ℤ))
        - ((windowNumerator ((q + 1) * periodLcm t) L : ℤ)
            - (windowNumerator (q * periodLcm t) L : ℤ)) := by
    have e1 : q * periodLcm t + periodLcm t = (q + 1) * periodLcm t := by ring
    have e2 : q * periodLcm t + periodLcm t + periodLcm t = (q + 2) * periodLcm t := by ring
    show windowDiscrepancy (periodLcm t) (q * periodLcm t + periodLcm t) L
        - windowDiscrepancy (periodLcm t) (q * periodLcm t) L = _
    rw [clusterD_windowDiscrepancy_eq (periodLcm t) (q * periodLcm t + periodLcm t) L,
      clusterD_windowDiscrepancy_eq (periodLcm t) (q * periodLcm t) L, e2, e1]
  rw [hd2] at hlow hhigh
  rcases clusterD_band_split hlow hhigh with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · -- the low cell: menu `[q+1, q]`
    push_cast at hb1 hb2
    have hc1 : (q : ℤ) * (periodLcm t : ℤ) + (L : ℤ) + 2
        < ((windowNumerator ((q + 1) * periodLcm t) L : ℤ)
            - (windowNumerator (q * periodLcm t) L : ℤ)) % 2 ^ L := by linarith
    have hc2 : ((windowNumerator ((q + 1) * periodLcm t) L : ℤ)
            - (windowNumerator (q * periodLcm t) L : ℤ)) % 2 ^ L
        < 2 ^ L - (((q + 1 : ℕ) : ℤ) * (periodLcm t : ℤ) + (L : ℤ) + 2) := by
      push_cast; linarith
    refine ⟨t, ht, L, [q + 1, q], by simp, ?_, ?_, clusterD_cone_pair hc1 hc2⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      have hbase : (0 : ℤ) ≤ (q : ℤ) * (periodLcm t : ℤ) + (L : ℤ) + 2 := by positivity
      rcases hx with rfl | rfl
      · push_cast at hc2 ⊢; linarith
      · push_cast at hc2 ⊢; linarith
  · -- the high cell: menu `[q+2, q+1]`
    push_cast at hb1 hb2
    have hc1 : ((q + 1 : ℕ) : ℤ) * (periodLcm t : ℤ) + (L : ℤ) + 2
        < ((windowNumerator ((q + 2) * periodLcm t) L : ℤ)
            - (windowNumerator ((q + 1) * periodLcm t) L : ℤ)) % 2 ^ L := by
      push_cast; linarith
    have hc2 : ((windowNumerator ((q + 2) * periodLcm t) L : ℤ)
            - (windowNumerator ((q + 1) * periodLcm t) L : ℤ)) % 2 ^ L
        < 2 ^ L - (((q + 2 : ℕ) : ℤ) * (periodLcm t : ℤ) + (L : ℤ) + 2) := by
      push_cast; linarith
    refine ⟨t, ht, L, [q + 2, q + 1], by simp, ?_, ?_, clusterD_cone_pair hc1 hc2⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      have hbase : (0 : ℤ) ≤ ((q + 1 : ℕ) : ℤ) * (periodLcm t : ℤ) + (L : ℤ) + 2 := by
        positivity
      rcases hx with rfl | rfl
      · push_cast at hc1 hc2 ⊢; linarith
      · push_cast at hc1 hc2 ⊢; linarith

end DemandLedger.ClusterD
