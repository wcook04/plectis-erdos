import ErdosProblems.DemandLedger.Basic

/-!
# Bridge set 2: the `certifiedKill` supplies against non-integrality and non-flatness

Left set (kill vocabulary)

* `G096` — `∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (H (t+1) - H t) (H t) L`
* `G097` — `∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (H t) (H t) L`
* `G100` — `∀ t₀, ∃ t ≥ t₀, ∃ q m L, 0 < q ∧ certifiedKill (m * H t) (q * H t) L`
* `G103` — `∀ t₀ N₀, ∃ t ≥ t₀, ∃ N ≥ N₀, ∃ L, certifiedKill (H t) N L`

Right set (non-integrality / non-flatness / prime-jump vocabulary)

* `G093` — `∀ t₀, ∃ t ≥ t₀, R_{H t + H t} - R_{H t} ∉ ℤ`
* `G101` — `∀ t₀, ∃ t ≥ t₀, ∃ q m, 0 < q ∧ R_{qH+mH} - R_{qH} ∉ ℤ`
* `G095` — `∀ t₀, ∃ t ≥ t₀, ∃ L Q, Q ≠ [] ∧ (∀ q ∈ Q, 0 < q) ∧ floors ∧ coneNonflatCert (H t) L Q`
* `G098` — `∀ t₀, ∃ t ≥ t₀, ∃ p L, 0 < p ∧ primeJumpSharpKill (H t) p L`

where `H t = periodLcm t = lcm(1..t)`.

**Result: the two vocabularies are the same vocabulary.  All 32 ordered
cross-pairs are edges, and every gap on both sides is equivalent to Erdős #249
itself.**

Three of the crossings are proved *directly*, without routing through
irrationality, and they are the structural content of this file:

* `e_G097_G093_direct` / `e_G093_G097_direct` — certificate soundness and
  certificate completeness.  `G097` and `G093` are the *same statement* read
  through a receipt: `∃ L, certifiedKill h N L ↔ R_{N+h} - R_N ∉ ℤ`.
* `e_G100_G101_direct` / `e_G101_G100_direct` — the same collapse one cone cell
  up.
* `e_G097_G095_direct` — a diagonal endpoint certificate at scale `H`, depth `L`
  *is* a firing two-vertex non-flatness menu `Q = [1, 2]` at the same scale and
  the same depth.  `certifiedKill (H) (H) L` charges the radius `2H+L+2` on both
  sides of `0`; the menu rows at `qi = 2` and `qi = 1` charge `H+L+2` and
  `2H+L+2` on one side each, and the two one-sided charges are exactly the two
  halves of the pairwise band.  So the wave-25 menu refuter, advertised as
  strictly stronger than the pairwise certificate, is *supplied* by the pairwise
  certificate on the two-vertex menu.

`G098` is reached in the other direction by proving completeness of
`primeJumpSharpKill` (`b2_exists_primeJumpSharpKill_of_notMem_int`), which the
corpus states only in the sound direction: the four-vertex commutator
`J(H,p) = D(pH) - p·D(H)` has a sharp radius growing *linearly* in the depth `L`
while the dyadic modulus grows exponentially, so a non-integral commutator is
certified at every sufficiently large depth.  Irrationality makes `J(H,2)`
non-integral because the shift identity turns it into `u(u-1)²(u+2)·S` minus an
integer, with `u = 2^H ≥ 2`.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller
open Erdos249257.PrimeJumpWindow

namespace DemandLedger.Bridge2

/-! ## Hub infrastructure: irrationality kills every positive window -/

/-- **The necessity bridge.**  If `S = ∑ φ(n)/2ⁿ` is irrational then no tail
difference with a positive window is an integer: by the shift identity
`R_{N+h} - R_N = 2^N(2^h-1)·S - (Φ_{N+h} - Φ_N)`, one integral difference
already exhibits `S` as a rational. -/
theorem b2_tail_diff_notMem_int_of_irrational {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨d, hd⟩
  have h1 := two_pow_mul_totient_series_eq (N + h)
  have h2 := two_pow_mul_totient_series_eq N
  have hnat : (2 : ℕ) ^ 1 ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hlt : (1 : ℝ) < (2 : ℝ) ^ h := by
    have hc : ((2 ^ 1 : ℕ) : ℝ) ≤ ((2 ^ h : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at hc
    linarith
  have h2N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hden : ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1)) ≠ 0 :=
    ne_of_gt (mul_pos h2N (by linarith))
  have hkey : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = ((d + (totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℝ) := by
    have expand : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        = (2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
          - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
      rw [pow_add]; ring
    rw [expand, h1, h2]
    push_cast
    linarith
  refine hirr ⟨((d + (totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℚ)
      / ((2 : ℚ) ^ N * ((2 : ℚ) ^ h - 1)), ?_⟩
  push_cast
  rw [div_eq_iff hden]
  push_cast at hkey
  linear_combination -hkey

/-- Irrationality supplies a firing endpoint certificate at every cell with a
positive window. -/
theorem b2_exists_certifiedKill_of_irrational {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ L, certifiedKill h N L :=
  exists_certifiedKill_of_tail_diff_notMem_int (b2_tail_diff_notMem_int_of_irrational hh hirr)

/-- The lcm ladder climbs infinitely often. -/
theorem b2_exists_strict_jump (t₀ : ℕ) :
    ∃ t, t₀ ≤ t ∧ periodLcm t < periodLcm (t + 1) := by
  by_contra hcon
  have hcon' : ∀ t, t₀ ≤ t → periodLcm (t + 1) ≤ periodLcm t := fun t ht =>
    not_lt.mp fun hlt => hcon ⟨t, ht, hlt⟩
  have hconst : ∀ k, periodLcm (t₀ + k) = periodLcm t₀ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hle := hcon' (t₀ + k) (Nat.le_add_right _ _)
        have hdvd := periodLcm_dvd_succ (t₀ + k)
        have hge : periodLcm (t₀ + k) ≤ periodLcm (t₀ + k + 1) :=
          Nat.le_of_dvd (periodLcm_pos _) hdvd
        have heq : periodLcm (t₀ + k + 1) = periodLcm (t₀ + k) := le_antisymm hle hge
        rw [show t₀ + (k + 1) = t₀ + k + 1 from rfl, heq, ih]
  have hbig := le_periodLcm (t₀ + (periodLcm t₀ + 1))
  rw [hconst] at hbig
  omega

/-! ## Each gap implies #249 (the corpus supply theorems) -/

theorem b2_irrational_of_G096 (h : G096) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G096 at h
  exact Erdos249257.irrational_totient_series_of_lcm_jump_window_kill_supply h

theorem b2_irrational_of_G097 (h : G097) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G097 at h
  exact irrational_totient_series_of_lcm_diagonal_certificate_supply h

theorem b2_irrational_of_G100 (h : G100) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G100 at h
  exact Erdos249257.irrational_totient_series_of_lcm_cone_window_kill_supply h

theorem b2_irrational_of_G103 (h : G103) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G103 at h
  exact Erdos249257.irrational_totient_series_of_lcm_window_kill_supply h

theorem b2_irrational_of_G093 (h : G093) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G093 at h
  exact Erdos249257.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply h

theorem b2_irrational_of_G101 (h : G101) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G101 at h
  exact Erdos249257.irrational_totient_series_of_lcm_cone_nonintegrality_supply h

theorem b2_irrational_of_G095 (h : G095) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G095 at h
  exact Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonflat_supply h

theorem b2_irrational_of_G098 (h : G098) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G098 at h
  exact Erdos249257.PrimeJumpWindow.irrational_totient_series_of_primeJumpSharpKill_supply h

/-! ## The kill side of #249 -/

theorem b2_G096_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G096 := by
  unfold G096
  intro t₀
  obtain ⟨t, ht, hjump⟩ := b2_exists_strict_jump t₀
  exact ⟨t, ht, b2_exists_certifiedKill_of_irrational (Nat.sub_pos_of_lt hjump) hirr⟩

theorem b2_G097_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G097 := by
  unfold G097
  intro t₀
  exact ⟨t₀, le_rfl, b2_exists_certifiedKill_of_irrational (periodLcm_pos t₀) hirr⟩

theorem b2_G100_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G100 := by
  unfold G100
  intro t₀
  obtain ⟨L, hL⟩ := b2_exists_certifiedKill_of_irrational
    (h := 1 * periodLcm t₀) (N := 1 * periodLcm t₀) (by simpa using periodLcm_pos t₀) hirr
  exact ⟨t₀, le_rfl, 1, 1, L, Nat.one_pos, hL⟩

theorem b2_G103_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G103 := by
  unfold G103
  intro t₀ N₀
  exact ⟨t₀, le_rfl, N₀, le_rfl,
    b2_exists_certifiedKill_of_irrational (periodLcm_pos t₀) hirr⟩

/-! ## The non-integrality side of #249 -/

theorem b2_G093_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G093 := by
  unfold G093
  intro t₀
  exact ⟨t₀, le_rfl, b2_tail_diff_notMem_int_of_irrational (periodLcm_pos t₀) hirr⟩

theorem b2_G101_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G101 := by
  unfold G101
  intro t₀
  exact ⟨t₀, le_rfl, 1, 1, Nat.one_pos,
    b2_tail_diff_notMem_int_of_irrational (h := 1 * periodLcm t₀) (N := 1 * periodLcm t₀)
      (by simpa using periodLcm_pos t₀) hirr⟩

/-! ## Soundness/completeness crossings: kill ↔ non-integrality -/

/-- Diagonal certificate ⟹ diagonal non-integrality (certificate soundness). -/
theorem e_G097_G093_direct : G097 → G093 := by
  unfold G097 G093
  intro h t₀
  obtain ⟨t, ht, L, hkill⟩ := h t₀
  exact ⟨t, ht, tail_diff_notMem_int_of_certifiedKill hkill⟩

/-- Diagonal non-integrality ⟹ diagonal certificate (certificate completeness). -/
theorem e_G093_G097_direct : G093 → G097 := by
  unfold G093 G097
  intro h t₀
  obtain ⟨t, ht, hnon⟩ := h t₀
  exact ⟨t, ht, exists_certifiedKill_of_tail_diff_notMem_int hnon⟩

/-- Cone certificate ⟹ cone non-integrality (certificate soundness). -/
theorem e_G100_G101_direct : G100 → G101 := by
  unfold G100 G101
  intro h t₀
  obtain ⟨t, ht, q, m, L, hq, hkill⟩ := h t₀
  exact ⟨t, ht, q, m, hq, tail_diff_notMem_int_of_certifiedKill hkill⟩

/-- Cone non-integrality ⟹ cone certificate (certificate completeness). -/
theorem e_G101_G100_direct : G101 → G100 := by
  unfold G101 G100
  intro h t₀
  obtain ⟨t, ht, q, m, hq, hnon⟩ := h t₀
  obtain ⟨L, hL⟩ := exists_certifiedKill_of_tail_diff_notMem_int hnon
  exact ⟨t, ht, q, m, L, hq, hL⟩

/-- Jump certificate ⟹ cone non-integrality: the jump `H (t+1) - H t` is the
cone cell `(q, m) = (1, k-1)` where `H (t+1) = k · H t`. -/
theorem e_G096_G101_direct : G096 → G101 := by
  unfold G096 G101
  intro h t₀
  obtain ⟨t, ht, L, hkill⟩ := h t₀
  obtain ⟨k, hk⟩ := periodLcm_dvd_succ t
  refine ⟨t, ht, 1, k - 1, Nat.one_pos, ?_⟩
  have hm : (k - 1) * periodLcm t = periodLcm (t + 1) - periodLcm t := by
    rw [hk, Nat.sub_one_mul, mul_comm k (periodLcm t)]
  rw [hm, one_mul]
  exact tail_diff_notMem_int_of_certifiedKill hkill

/-! ## The non-flatness crossing: a pairwise certificate is a two-vertex menu -/

/-- The window discrepancy is the difference of the two window numerators. -/
theorem b2_windowDiscrepancy_eq (h N L : ℕ) :
    windowDiscrepancy h N L
      = (windowNumerator (N + h) L : ℤ) - (windowNumerator N L : ℤ) := by
  unfold windowDiscrepancy windowNumerator
  push_cast
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]

/-- Negating a residue that is not `0` mod `2^L`. -/
theorem b2_neg_emod {a : ℤ} {L : ℕ} (h0 : 0 < a % 2 ^ L) :
    (-a) % 2 ^ L = 2 ^ L - a % 2 ^ L := by
  have hP : (0 : ℤ) < 2 ^ L := by positivity
  have hlt : a % 2 ^ L < 2 ^ L := Int.emod_lt_of_pos a hP
  have hrepr : -a = (2 ^ L - a % 2 ^ L) + 2 ^ L * (-(a / 2 ^ L) - 1) := by
    linear_combination Int.mul_ediv_add_emod a (2 ^ L)
  rw [hrepr, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- **The crossing.**  A diagonal endpoint certificate at scale `H` and depth
`L` fires the two-vertex non-flatness menu `Q = [1, 2]` at the same scale and
depth, floors included.  The pairwise band `2H+L+2 < A % 2^L < 2^L - (2H+L+2)`
splits into the two one-sided menu rows: the row at `qi = 2` needs
`H+L+2 < A % 2^L` and the row at `qi = 1` needs `2H+L+2 < (-A) % 2^L`. -/
theorem b2_coneNonflatCert_of_diagonal_certifiedKill {H L : ℕ}
    (hkill : certifiedKill H H L) :
    (∀ q ∈ ([1, 2] : List ℕ), (q * H + L + 2 : ℤ) < 2 ^ L)
      ∧ coneNonflatCert H L [1, 2] := by
  obtain ⟨hlow, hhigh⟩ := hkill
  set A : ℤ := windowDiscrepancy H H L with hAdef
  have hA : A = (windowNumerator (H + H) L : ℤ) - (windowNumerator H L : ℤ) :=
    b2_windowDiscrepancy_eq H H L
  have hH : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg H
  have hL0 : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  have h0 : 0 < A % 2 ^ L := by omega
  have hneg : (-A) % 2 ^ L = 2 ^ L - A % 2 ^ L := b2_neg_emod h0
  have h1H : (1 : ℕ) * H = H := one_mul H
  have h2H : (2 : ℕ) * H = H + H := two_mul H
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · push_cast
      omega
    · push_cast
      omega
  · intro qi hqi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hqi
    rcases hqi with rfl | rfl
    · refine ⟨2, by simp, ?_⟩
      rw [h1H, h2H, show ((windowNumerator H L : ℤ) - (windowNumerator (H + H) L : ℤ))
        = -A from by rw [hA]; ring, hneg]
      push_cast
      omega
    · refine ⟨1, by simp, ?_⟩
      rw [h1H, h2H, show ((windowNumerator (H + H) L : ℤ) - (windowNumerator H L : ℤ))
        = A from hA.symm]
      push_cast
      omega

/-- **Diagonal certificate ⟹ cone non-flatness menu.**  Wave 25's menu refuter
is supplied by wave 23's pairwise diagonal certificate, at the same scale and
the same depth, on the menu `[1, 2]`. -/
theorem e_G097_G095_direct : G097 → G095 := by
  unfold G097 G095
  intro h t₀
  obtain ⟨t, ht, L, hkill⟩ := h t₀
  obtain ⟨hfloor, hcert⟩ := b2_coneNonflatCert_of_diagonal_certifiedKill hkill
  refine ⟨t, ht, L, [1, 2], by simp, ?_, hfloor, hcert⟩
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> norm_num

theorem b2_G095_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G095 :=
  e_G097_G095_direct (b2_G097_of_irrational hirr)

/-! ## The prime-jump crossing

The corpus states `primeJumpSharpKill` only in the sound direction.  Its
completeness is what carries `G098` into the collapse: the sharp radius grows
linearly in the depth while the dyadic modulus grows exponentially, so a
non-integral four-vertex commutator is certified at every sufficiently large
depth. -/

private lemma b2_summable_linear_half :
    Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
  simpa using summable_pow_mul_geometric_of_norm_lt_one 1
    (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)

private lemma b2_summable_const_add_mul_half (C : ℝ) :
    Summable (fun j : ℕ => (C + (j : ℝ)) * (1 / 2 : ℝ) ^ j) := by
  have h1 : Summable (fun j : ℕ => C * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  exact (h1.add b2_summable_linear_half).congr fun j => by ring

/-- A linear factor loses to the dyadic modulus at some depth. -/
private lemma b2_exists_depth_lt (C δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℕ, (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L < δ := by
  have htend := (b2_summable_const_add_mul_half C).tendsto_atTop_zero
  have hev : ∀ᶠ L : ℕ in Filter.atTop, (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L ∈ Set.Iio δ :=
    htend.eventually_mem (Iio_mem_nhds hδ)
  obtain ⟨L, hL⟩ := hev.exists
  exact ⟨L, hL⟩

/-- A non-integer keeps a positive distance from the whole integer lattice. -/
private lemma b2_exists_dist_pos {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℤ, δ ≤ |x - (z : ℝ)| := by
  obtain ⟨g, hg⟩ := exists_floor x
  have hgle : (g : ℝ) ≤ x := (hg g).mp le_rfl
  have hglt : x < (g : ℝ) + 1 := by
    by_contra hle
    have hle' : (g : ℝ) + 1 ≤ x := not_lt.mp hle
    have h1 : ((g + 1 : ℤ) : ℝ) ≤ x := by push_cast; linarith
    have h2 : g + 1 ≤ g := (hg (g + 1)).mpr h1
    omega
  have hf0 : 0 < x - (g : ℝ) := by
    rcases eq_or_lt_of_le (show 0 ≤ x - (g : ℝ) by linarith) with heq | hlt
    · exact absurd (show x ∈ Set.range ((↑) : ℤ → ℝ) from ⟨g, by linarith⟩) hx
    · exact hlt
  refine ⟨min (x - (g : ℝ)) (1 - (x - (g : ℝ))), lt_min hf0 (by linarith), fun z => ?_⟩
  have hmin1 := min_le_left (x - (g : ℝ)) (1 - (x - (g : ℝ)))
  have hmin2 := min_le_right (x - (g : ℝ)) (1 - (x - (g : ℝ)))
  by_cases hz : z ≤ g
  · have hz' : (z : ℝ) ≤ (g : ℝ) := by exact_mod_cast hz
    have hlow : min (x - (g : ℝ)) (1 - (x - (g : ℝ))) ≤ x - (z : ℝ) := by linarith
    exact hlow.trans (le_abs_self _)
  · have hz1 : g + 1 ≤ z := Int.lt_iff_add_one_le.mp (not_le.mp hz)
    have hz' : (g : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz1
    have hup : min (x - (g : ℝ)) (1 - (x - (g : ℝ))) ≤ (z : ℝ) - x := by linarith
    calc min (x - (g : ℝ)) (1 - (x - (g : ℝ))) ≤ (z : ℝ) - x := hup
      _ ≤ |(z : ℝ) - x| := le_abs_self _
      _ = |x - (z : ℝ)| := abs_sub_comm _ _

/-- **Sharp prime-jump completeness.**  If the four-vertex commutator
`J(H,p) = D(pH) - p·D(H)` is not an integer then some depth certifies it.  The
exact radius `3pH + (p+1)(L+2)` is linear in `L`, so at any depth where
`2·radius < δ·2^L` (with `δ` the distance from `J` to the lattice) the central
residue is forced strictly inside the admissible band. -/
theorem b2_exists_primeJumpSharpKill_of_notMem_int {H p : ℕ}
    (hnon : primeJumpTailCommutator H p ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ L, primeJumpSharpKill H p L := by
  obtain ⟨δ, hδ0, hdist⟩ := b2_exists_dist_pos hnon
  obtain ⟨L, hLdepth⟩ := b2_exists_depth_lt (3 * (p : ℝ) * (H : ℝ) + 2)
    (δ / (2 * ((p : ℝ) + 1))) (by positivity)
  obtain ⟨e, hsplit, hbound⟩ := primeJumpTailCommutator_eq_window_add_remainder H p L
  refine ⟨L, ?_⟩
  have h2L : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hRreal : ((primeJumpSharpRadius H p L : ℤ) : ℝ)
      = 3 * (p : ℝ) * (H : ℝ) + ((p : ℝ) + 1) * ((L : ℝ) + 2) := by
    unfold primeJumpSharpRadius
    push_cast
    ring
  -- the chosen depth beats twice the sharp radius
  have hbig : 2 * ((primeJumpSharpRadius H p L : ℤ) : ℝ) < δ * 2 ^ L := by
    have hmul := mul_lt_mul_of_pos_right hLdepth
      (show (0 : ℝ) < (2 : ℝ) ^ L * (2 * ((p : ℝ) + 1)) by positivity)
    have e1 : (3 * (p : ℝ) * (H : ℝ) + 2 + (L : ℝ)) * (1 / 2 : ℝ) ^ L
          * ((2 : ℝ) ^ L * (2 * ((p : ℝ) + 1)))
        = (3 * (p : ℝ) * (H : ℝ) + 2 + (L : ℝ)) * (2 * ((p : ℝ) + 1)) := by
      rw [div_pow, one_pow]
      field_simp
    have e2 : δ / (2 * ((p : ℝ) + 1)) * ((2 : ℝ) ^ L * (2 * ((p : ℝ) + 1))) = δ * 2 ^ L := by
      field_simp
    rw [e1, e2] at hmul
    have hle : 2 * (3 * (p : ℝ) * (H : ℝ) + ((p : ℝ) + 1) * ((L : ℝ) + 2))
        ≤ (3 * (p : ℝ) * (H : ℝ) + 2 + (L : ℝ)) * (2 * ((p : ℝ) + 1)) := by
      nlinarith [mul_nonneg (mul_nonneg hp0 hp0) hH0, mul_nonneg hp0 hH0,
        mul_nonneg hp0 hL0, hp0, hH0, hL0]
    rw [hRreal]
    linarith
  unfold primeJumpSharpKill
  set A : ℤ := primeJumpWindowCommutator H p L with hAdef
  set R : ℤ := primeJumpSharpRadius H p L with hRdef
  set k : ℤ := A / 2 ^ L with hkdef
  set r : ℤ := A % 2 ^ L with hrdef
  have hPpos : (0 : ℤ) < (2 : ℤ) ^ L := by positivity
  have hr0 : 0 ≤ r := Int.emod_nonneg A (ne_of_gt hPpos)
  have hrP : r < (2 : ℤ) ^ L := Int.emod_lt_of_pos A hPpos
  have hdm : (2 : ℤ) ^ L * k + r = A := Int.mul_ediv_add_emod A ((2 : ℤ) ^ L)
  have hrreal0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  have hrrealP : (r : ℝ) < (2 : ℝ) ^ L := by
    have h := hrP
    have h' : ((r : ℤ) : ℝ) < (((2 : ℤ) ^ L : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hAreal : (A : ℝ) = (2 : ℝ) ^ L * (k : ℝ) + (r : ℝ) := by
    have h' : ((A : ℤ) : ℝ) = (((2 : ℤ) ^ L * k + r : ℤ) : ℝ) := by exact_mod_cast hdm.symm
    push_cast at h'
    exact h'
  have hxmul : primeJumpTailCommutator H p * (2 : ℝ) ^ L = (A : ℝ) + e * 2 ^ L := by
    rw [hsplit, add_mul, div_mul_cancel₀ _ h2L.ne']
  have hxA : primeJumpTailCommutator H p * (2 : ℝ) ^ L
      = (2 : ℝ) ^ L * (k : ℝ) + (r : ℝ) + e * 2 ^ L := by
    rw [hxmul, hAreal]
  have hEq1 : (primeJumpTailCommutator H p - (k : ℝ)) * 2 ^ L = (r : ℝ) + e * 2 ^ L := by
    linear_combination hxA
  have hEq2 : (primeJumpTailCommutator H p - ((k + 1 : ℤ) : ℝ)) * 2 ^ L
      = (r : ℝ) + e * 2 ^ L - 2 ^ L := by
    push_cast
    linear_combination hxA
  have habs1 : δ * 2 ^ L ≤ |(r : ℝ) + e * 2 ^ L| := by
    rw [← hEq1, abs_mul, abs_of_pos h2L]
    exact mul_le_mul_of_nonneg_right (hdist k) h2L.le
  have habs2 : δ * 2 ^ L ≤ |(r : ℝ) + e * 2 ^ L - 2 ^ L| := by
    rw [← hEq2, abs_mul, abs_of_pos h2L]
    exact mul_le_mul_of_nonneg_right (hdist (k + 1)) h2L.le
  have hbnd := abs_le.mp hbound
  refine ⟨?_, ?_⟩
  · have hlow : ((R : ℤ) : ℝ) < (r : ℝ) := by
      rcases le_abs.mp habs1 with hc | hc
      · linarith [hbnd.2]
      · linarith [hbnd.1]
    exact_mod_cast hlow
  · have hhigh : (r : ℝ) < ((((2 : ℤ) ^ L - R : ℤ)) : ℝ) := by
      push_cast
      rcases le_abs.mp habs2 with hc | hc
      · linarith [hbnd.2]
      · linarith [hbnd.1]
    exact_mod_cast hhigh

/-- `u(u-1)²(u+2) > 0` for `u ≥ 2`: the coefficient of `S` in the `p = 2`
commutator. -/
private lemma b2_quartic_pos {u : ℝ} (hu : 2 ≤ u) : 0 < u ^ 4 - u ^ 2 - 2 * (u ^ 2 - u) := by
  have hfac : u ^ 4 - u ^ 2 - 2 * (u ^ 2 - u) = u * (u - 1) ^ 2 * (u + 2) := by ring
  rw [hfac]
  have h1 : (0 : ℝ) < u := by linarith
  have h2 : (0 : ℝ) < (u - 1) ^ 2 := by nlinarith
  have h3 : (0 : ℝ) < u + 2 := by linarith
  exact mul_pos (mul_pos h1 h2) h3

/-- **Irrationality kills the four-vertex commutator at `p = 2`.**  The shift
identity turns `J(H,2)` into `(u⁴ - 3u² + 2u)·S` minus an integer, with
`u = 2^H ≥ 2`, and `u⁴ - 3u² + 2u = u(u-1)²(u+2) ≠ 0`. -/
theorem b2_primeJumpTailCommutator_two_notMem_int_of_irrational {H : ℕ} (hH : 0 < H)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    primeJumpTailCommutator H 2 ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨d, hd⟩
  have hR : ∀ N : ℕ, totientTail N
      = (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (totientPrefix N : ℝ) := by
    intro N
    have h := two_pow_mul_totient_series_eq N
    linarith
  have hu2 : (2 : ℝ) ^ (2 * H) = ((2 : ℝ) ^ H) ^ 2 := by
    rw [← pow_mul, mul_comm H 2]
  have hu4 : (2 : ℝ) ^ (2 * (2 * H)) = ((2 : ℝ) ^ H) ^ 4 := by
    rw [← pow_mul, show H * 4 = 2 * (2 * H) from by ring]
  unfold primeJumpTailCommutator diagonalTailDifferenceAt at hd
  rw [hR (2 * (2 * H)), hR (2 * H), hR H, hu4, hu2] at hd
  have hnat : (2 : ℕ) ^ 1 ≤ 2 ^ H := Nat.pow_le_pow_right (by norm_num) hH
  have hu : (2 : ℝ) ≤ (2 : ℝ) ^ H := by
    have hc : ((2 ^ 1 : ℕ) : ℝ) ≤ ((2 ^ H : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at hc
    linarith
  have hcpos := b2_quartic_pos hu
  have hcne : (((2 : ℝ) ^ H) ^ 4 - ((2 : ℝ) ^ H) ^ 2
      - 2 * (((2 : ℝ) ^ H) ^ 2 - (2 : ℝ) ^ H)) ≠ 0 := ne_of_gt hcpos
  refine hirr ⟨((d + (totientPrefix (2 * (2 * H)) : ℤ) - (totientPrefix (2 * H) : ℤ)
        - 2 * ((totientPrefix (2 * H) : ℤ) - (totientPrefix H : ℤ)) : ℤ) : ℚ)
      / (((2 : ℚ) ^ H) ^ 4 - ((2 : ℚ) ^ H) ^ 2
        - 2 * (((2 : ℚ) ^ H) ^ 2 - (2 : ℚ) ^ H)), ?_⟩
  push_cast
  rw [div_eq_iff hcne]
  push_cast at hd
  linear_combination hd

theorem b2_G098_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G098 := by
  unfold G098
  intro t₀
  obtain ⟨L, hL⟩ := b2_exists_primeJumpSharpKill_of_notMem_int
    (b2_primeJumpTailCommutator_two_notMem_int_of_irrational (periodLcm_pos t₀) hirr)
  exact ⟨t₀, le_rfl, 2, L, by norm_num, hL⟩

/-! ## The non-flatness crossing at full cone generality

The two-vertex construction is not special to the diagonal: any cone cell
certificate `certifiedKill (m·H) (q·H) L` is the two-vertex menu `[q, q+m]` at
the same scale and depth. -/

theorem b2_coneNonflatCert_of_certifiedKill {H q m L : ℕ} (hq : 0 < q)
    (hkill : certifiedKill (m * H) (q * H) L) :
    (∀ x ∈ ([q, q + m] : List ℕ), (x * H + L + 2 : ℤ) < 2 ^ L)
      ∧ coneNonflatCert H L [q, q + m] := by
  obtain ⟨hlow, hhigh⟩ := hkill
  push_cast at hlow hhigh
  set A : ℤ := windowDiscrepancy (m * H) (q * H) L with hAdef
  have hA : A = (windowNumerator (q * H + m * H) L : ℤ) - (windowNumerator (q * H) L : ℤ) :=
    b2_windowDiscrepancy_eq (m * H) (q * H) L
  have hqm : (q + m) * H = q * H + m * H := by ring
  have hqH : (0 : ℤ) ≤ (q : ℤ) * (H : ℤ) :=
    mul_nonneg (Int.natCast_nonneg q) (Int.natCast_nonneg H)
  have hmH : (0 : ℤ) ≤ (m : ℤ) * (H : ℤ) :=
    mul_nonneg (Int.natCast_nonneg m) (Int.natCast_nonneg H)
  have hL0 : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  have h0 : 0 < A % 2 ^ L := by linarith
  have hneg : (-A) % 2 ^ L = 2 ^ L - A % 2 ^ L := b2_neg_emod h0
  constructor
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · linarith
    · push_cast
      linarith
  · intro qi hqi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hqi
    rcases hqi with rfl | rfl
    · refine ⟨qi + m, by simp, ?_⟩
      rw [hqm, show ((windowNumerator (qi * H) L : ℤ)
        - (windowNumerator (qi * H + m * H) L : ℤ)) = -A from by rw [hA]; ring, hneg]
      push_cast
      linarith
    · refine ⟨q, by simp, ?_⟩
      rw [hqm, show ((windowNumerator (q * H + m * H) L : ℤ)
        - (windowNumerator (q * H) L : ℤ)) = A from hA.symm]
      linarith

/-- **Cone certificate ⟹ cone non-flatness menu.** -/
theorem e_G100_G095_direct : G100 → G095 := by
  unfold G100 G095
  intro h t₀
  obtain ⟨t, ht, q, m, L, hq, hkill⟩ := h t₀
  obtain ⟨hfloor, hcert⟩ := b2_coneNonflatCert_of_certifiedKill hq hkill
  refine ⟨t, ht, L, [q, q + m], by simp, ?_, hfloor, hcert⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hq
  · omega

/-! ## All 32 ordered cross-pairs

Left → right. -/

theorem e_G096_G093 : G096 → G093 := fun h => b2_G093_of_irrational (b2_irrational_of_G096 h)
theorem e_G096_G101 : G096 → G101 := e_G096_G101_direct
theorem e_G096_G095 : G096 → G095 := fun h => b2_G095_of_irrational (b2_irrational_of_G096 h)
theorem e_G096_G098 : G096 → G098 := fun h => b2_G098_of_irrational (b2_irrational_of_G096 h)

theorem e_G097_G093 : G097 → G093 := e_G097_G093_direct
theorem e_G097_G101 : G097 → G101 := fun h => b2_G101_of_irrational (b2_irrational_of_G097 h)
theorem e_G097_G095 : G097 → G095 := e_G097_G095_direct
theorem e_G097_G098 : G097 → G098 := fun h => b2_G098_of_irrational (b2_irrational_of_G097 h)

theorem e_G100_G093 : G100 → G093 := fun h => b2_G093_of_irrational (b2_irrational_of_G100 h)
theorem e_G100_G101 : G100 → G101 := e_G100_G101_direct
theorem e_G100_G095 : G100 → G095 := e_G100_G095_direct
theorem e_G100_G098 : G100 → G098 := fun h => b2_G098_of_irrational (b2_irrational_of_G100 h)

theorem e_G103_G093 : G103 → G093 := fun h => b2_G093_of_irrational (b2_irrational_of_G103 h)
theorem e_G103_G101 : G103 → G101 := fun h => b2_G101_of_irrational (b2_irrational_of_G103 h)
theorem e_G103_G095 : G103 → G095 := fun h => b2_G095_of_irrational (b2_irrational_of_G103 h)
theorem e_G103_G098 : G103 → G098 := fun h => b2_G098_of_irrational (b2_irrational_of_G103 h)

/-! Right → left. -/

theorem e_G093_G096 : G093 → G096 := fun h => b2_G096_of_irrational (b2_irrational_of_G093 h)
theorem e_G093_G097 : G093 → G097 := e_G093_G097_direct
theorem e_G093_G100 : G093 → G100 := fun h => b2_G100_of_irrational (b2_irrational_of_G093 h)
theorem e_G093_G103 : G093 → G103 := fun h => b2_G103_of_irrational (b2_irrational_of_G093 h)

theorem e_G101_G096 : G101 → G096 := fun h => b2_G096_of_irrational (b2_irrational_of_G101 h)
theorem e_G101_G097 : G101 → G097 := fun h => b2_G097_of_irrational (b2_irrational_of_G101 h)
theorem e_G101_G100 : G101 → G100 := e_G101_G100_direct
theorem e_G101_G103 : G101 → G103 := fun h => b2_G103_of_irrational (b2_irrational_of_G101 h)

theorem e_G095_G096 : G095 → G096 := fun h => b2_G096_of_irrational (b2_irrational_of_G095 h)
theorem e_G095_G097 : G095 → G097 := fun h => b2_G097_of_irrational (b2_irrational_of_G095 h)
theorem e_G095_G100 : G095 → G100 := fun h => b2_G100_of_irrational (b2_irrational_of_G095 h)
theorem e_G095_G103 : G095 → G103 := fun h => b2_G103_of_irrational (b2_irrational_of_G095 h)

theorem e_G098_G096 : G098 → G096 := fun h => b2_G096_of_irrational (b2_irrational_of_G098 h)
theorem e_G098_G097 : G098 → G097 := fun h => b2_G097_of_irrational (b2_irrational_of_G098 h)
theorem e_G098_G100 : G098 → G100 := fun h => b2_G100_of_irrational (b2_irrational_of_G098 h)
theorem e_G098_G103 : G098 → G103 := fun h => b2_G103_of_irrational (b2_irrational_of_G098 h)

/-! ## The collapse, stated once

The kill vocabulary, the non-integrality vocabulary, the cone non-flatness menu
and the sharp prime-jump commutator are four names for Erdős #249. -/

theorem G093_iff_irrational :
    G093 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨b2_irrational_of_G093, b2_G093_of_irrational⟩

theorem G101_iff_irrational :
    G101 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨b2_irrational_of_G101, b2_G101_of_irrational⟩

theorem G095_iff_irrational :
    G095 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨b2_irrational_of_G095, b2_G095_of_irrational⟩

theorem G098_iff_irrational :
    G098 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨b2_irrational_of_G098, b2_G098_of_irrational⟩

/-- `G097` and `G093` are the same statement: the diagonal endpoint certificate
is a receipt for diagonal non-integrality, and completeness turns the receipt
back on. -/
theorem G097_iff_G093 : G097 ↔ G093 := ⟨e_G097_G093_direct, e_G093_G097_direct⟩

/-- `G100` and `G101` are the same statement, one cone cell up. -/
theorem G100_iff_G101 : G100 ↔ G101 := ⟨e_G100_G101_direct, e_G101_G100_direct⟩

end DemandLedger.Bridge2
