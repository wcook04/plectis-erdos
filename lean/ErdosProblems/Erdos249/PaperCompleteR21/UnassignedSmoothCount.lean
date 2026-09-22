import ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCut
import ErdosProblems.Shared.MertensSecond

/-! Clauses (b), (c) and (d) of the long #249 paper's `prop:dickman`
("A one-sided bound for the unassigned terms",
`paper/reasoning-parts/erdos249/a249_front.tex`), and the assembled
proposition `prop_dickman`.

The paper's statement: fix `h, s` and choose the admissible depth `L`
minimally for each large `X`; put `t = L - s + 1 = O_{h,s}(log X)` and
`y_X = 4√X + 2t/√X`.  (a) An unassigned `n = N + t` has `P(n) ≤ y_X`.
Consequently (b) `#{N ∈ [X, 2X) : N ∉ 𝒜} ≤ Ψ(2X+t-1, y_X) - Ψ(X+t-1, y_X)`,
and (c) this difference is `(1 - log 2 + o(1)) X`, (d) `< (8/25) X` for all
sufficiently large `X`.  `Ψ(x, y)` counts the positive integers at most `x`
whose prime factors are all at most `y`.

Clause (a) is `largest_prime_factor_le_dickmanCut` in `UnassignedSmoothCut`.
Dictionary for the rest:

* `smoothCount x y` is `Ψ(x, y)`, defined plainly as a count;
* `AdmissibleDepth h s X L` is the pair of depth conditions `h ≤ L - s` and
  `16 (2X + h + L + 2) ≤ 2^L` that `DTWPivotResidualDecorrelation` imposes;
* `minimalDepth h s X` is the least admissible `L` (`Nat.find`);
* `minimalOffset h s X` is `t = L - s + 1` (the tree's `pivotOffset`) and
  `minimalCut h s X` is `y_X` (the tree's `dickmanCut X t`);
* `𝒜` is the tree's assigned set `pivotSupplierBases X L s`.

The paper derives (c) from the cited fixed-`u` asymptotic
`Ψ(x, x^{1/u}) ~ ρ(u) x` and `ρ(2) = 1 - log 2`.  No Dickman function is
needed here.  Since `y_X ≥ 4√X` exceeds `√(2X + t - 1)`, every integer of
the window has at most one prime factor above `y_X`, which gives the exact
identity (`smoothCount_sub_eq`)
`Ψ(x₂, y) - Ψ(x₁, y) = (x₂ - x₁) - ∑_{y < p ≤ x₂} (⌊x₂/p⌋ - ⌊x₁/p⌋)`
with `x₁ = X + t - 1`, `x₂ = 2X + t - 1`.  Each bracket is `X/p` up to an
error of at most one, there are `O(X / log X)` primes in the range, and the
difference form of Mertens' second theorem (`ErdosProblems.Shared.Mertens`)
gives `∑_{y < p ≤ x₂} 1/p = log 2 + O(1 / log X)`.  The result carries an
explicit rate, `|Ψ(x₂, y_X) - Ψ(x₁, y_X) - (1 - log 2) X| ≤ 40 X / log X`
for `X ≥ max 625 (4h + 44)` (`abs_minimalWindow_sub_le`); the constant is not
optimised and no crossover scale for (d) is asserted.  Clause (b) bounds the
unassigned count from above only; no asymptotic for that count is asserted. -/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Shared.Mertens
open Finset Filter Topology

/-! ## The smooth-number count `Ψ(x, y)` -/

/-- `Ψ(x, y)`: the number of positive integers `n ≤ x` all of whose prime
factors are at most `y`. -/
noncomputable def smoothCount (x : ℕ) (y : ℝ) : ℕ :=
  ((Icc 1 x).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card

/-- In the range `x < y²` a non-`y`-smooth integer has exactly one prime factor
above `y`, so `Ψ(x, y) = x - ∑_{y < p ≤ x} ⌊x/p⌋`. -/
theorem smoothCount_add_sum_div {x : ℕ} {y : ℝ} (hy : 0 ≤ y) (hxy : (x : ℝ) < y * y) :
    smoothCount x y + ∑ p ∈ (Ioc ⌊y⌋₊ x).filter Nat.Prime, x / p = x := by
  have hcompl : (Icc 1 x).filter (fun n => ¬ ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)
      = ((Ioc ⌊y⌋₊ x).filter Nat.Prime).biUnion
          (fun p => (Ioc 0 x).filter (fun n => p ∣ n)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_Ioc,
      not_forall, not_le, exists_prop]
    constructor
    · rintro ⟨⟨hn1, hnx⟩, q, hq, hqy⟩
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqn := Nat.dvd_of_mem_primeFactors hq
      exact ⟨q, ⟨⟨(Nat.floor_lt hy).mpr hqy,
        le_trans (Nat.le_of_dvd (by omega) hqn) hnx⟩, hqp⟩, ⟨by omega, hnx⟩, hqn⟩
    · rintro ⟨q, ⟨⟨hyq, hqx⟩, hqp⟩, ⟨hn0, hnx⟩, hqn⟩
      exact ⟨⟨by omega, hnx⟩, q, Nat.mem_primeFactors.mpr ⟨hqp, hqn, by omega⟩,
        (Nat.floor_lt hy).mp hyq⟩
  have hdisj : (((Ioc ⌊y⌋₊ x).filter Nat.Prime : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun p => (Ioc 0 x).filter (fun n => p ∣ n)) := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro n hnp hnq
    have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    have hnp' := Finset.mem_filter.mp hnp
    have hnq' := Finset.mem_filter.mp hnq
    have hpy : y < p := (Nat.floor_lt hy).mp (Finset.mem_Ioc.mp hp'.1).1
    have hqy : y < q := (Nat.floor_lt hy).mp (Finset.mem_Ioc.mp hq'.1).1
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hnp'.1).1
    have hnx : n ≤ x := (Finset.mem_Ioc.mp hnp'.1).2
    have hdvd : p * q ∣ n :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hp'.2 hq'.2).mpr hpq) hnp'.2 hnq'.2
    have hle : p * q ≤ x := le_trans (Nat.le_of_dvd hn0 hdvd) hnx
    have hleR : ((p * q : ℕ) : ℝ) ≤ x := by exact_mod_cast hle
    push_cast at hleR
    have hlt : y * y < (p : ℝ) * q := mul_lt_mul'' hpy hqy hy hy
    linarith
  have hcard := Finset.card_filter_add_card_filter_not (s := Icc 1 x)
    (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)
  rw [hcompl, Finset.card_biUnion hdisj, Nat.card_Icc] at hcard
  simp only [Nat.Ioc_filter_dvd_card_eq_div] at hcard
  unfold smoothCount
  simpa using hcard

/-- `Ψ(x₂, y) = Ψ(x₁, y) + #{x₁ < n ≤ x₂ : n is y-smooth}`. -/
theorem smoothCount_eq_add_card_Ioc {x₁ x₂ : ℕ} (y : ℝ) (h : x₁ ≤ x₂) :
    smoothCount x₂ y = smoothCount x₁ y
      + ((Ioc x₁ x₂).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card := by
  unfold smoothCount
  have hU : Icc 1 x₂ = Icc 1 x₁ ∪ Ioc x₁ x₂ := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hU, Finset.filter_union, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro n h1 h2
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
  omega

/-- The exact window identity: for `x₁ ≤ x₂ < y²`,
`Ψ(x₂, y) - Ψ(x₁, y) = (x₂ - x₁) - ∑_{y < p ≤ x₂} (⌊x₂/p⌋ - ⌊x₁/p⌋)`. -/
theorem smoothCount_sub_eq {x₁ x₂ : ℕ} {y : ℝ} (hy : 0 ≤ y) (h12 : x₁ ≤ x₂)
    (hxy : (x₂ : ℝ) < y * y) :
    (smoothCount x₂ y : ℝ) - smoothCount x₁ y
      = ((x₂ : ℝ) - x₁) - ∑ p ∈ (Ioc ⌊y⌋₊ x₂).filter Nat.Prime,
          (((x₂ / p : ℕ) : ℝ) - ((x₁ / p : ℕ) : ℝ)) := by
  have hx1y : (x₁ : ℝ) < y * y := lt_of_le_of_lt (by exact_mod_cast h12) hxy
  have e2 := smoothCount_add_sum_div hy hxy
  have e1 := smoothCount_add_sum_div hy hx1y
  have hsub : ∑ p ∈ (Ioc ⌊y⌋₊ x₁).filter Nat.Prime, x₁ / p
      = ∑ p ∈ (Ioc ⌊y⌋₊ x₂).filter Nat.Prime, x₁ / p := by
    apply Finset.sum_subset
    · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right h12)
    · intro p hp hnot
      have hp2 := Finset.mem_filter.mp hp
      have hpI := Finset.mem_Ioc.mp hp2.1
      have hpx : ¬ p ≤ x₁ := fun hle =>
        hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpI.1, hle⟩, hp2.2⟩)
      exact Nat.div_eq_of_lt (by omega)
  rw [hsub] at e1
  have e2R : (smoothCount x₂ y : ℝ)
      + ∑ p ∈ (Ioc ⌊y⌋₊ x₂).filter Nat.Prime, ((x₂ / p : ℕ) : ℝ) = x₂ := by
    exact_mod_cast e2
  have e1R : (smoothCount x₁ y : ℝ)
      + ∑ p ∈ (Ioc ⌊y⌋₊ x₂).filter Nat.Prime, ((x₁ / p : ℕ) : ℝ) = x₁ := by
    exact_mod_cast e1
  rw [Finset.sum_sub_distrib]
  linarith

/-- Replacing `⌊x₂/p⌋ - ⌊x₁/p⌋` by `(x₂ - x₁)/p` costs at most `1`. -/
theorem abs_natDiv_sub_natDiv_sub_le {x₁ x₂ p : ℕ} (hp : 0 < p) :
    |((x₂ / p : ℕ) : ℝ) - ((x₁ / p : ℕ) : ℝ) - ((x₂ : ℝ) - x₁) / p| ≤ 1 := by
  have a2 := div_sub_one_le_natDiv x₂ p hp
  have a1 := div_sub_one_le_natDiv x₁ p hp
  have b2 : ((x₂ / p : ℕ) : ℝ) ≤ (x₂ : ℝ) / p := Nat.cast_div_le
  have b1 : ((x₁ / p : ℕ) : ℝ) ≤ (x₁ : ℝ) / p := Nat.cast_div_le
  rw [sub_div, abs_le]
  constructor <;> linarith

/-- Summed over a finite set of positive integers, the floor error is at most
the number of terms. -/
theorem abs_sum_window_sub_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 0 < p) (x₁ x₂ : ℕ) :
    |∑ p ∈ Q, (((x₂ / p : ℕ) : ℝ) - ((x₁ / p : ℕ) : ℝ))
        - ((x₂ : ℝ) - x₁) * ∑ p ∈ Q, (1 : ℝ) / p| ≤ Q.card := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ p ∈ Q, ((((x₂ / p : ℕ) : ℝ) - ((x₁ / p : ℕ) : ℝ)) - ((x₂ : ℝ) - x₁) * (1 / p))|
      ≤ ∑ p ∈ Q, |(((x₂ / p : ℕ) : ℝ) - ((x₁ / p : ℕ) : ℝ)) - ((x₂ : ℝ) - x₁) * (1 / p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ Q, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [mul_one_div]
        exact abs_natDiv_sub_natDiv_sub_le (hQ p hp)
    _ = Q.card := by simp

/-- `|log v| ≤ 2 |v - 1|` for `v ≥ 1/2`. -/
theorem abs_log_le_two_mul_abs_sub_one {v : ℝ} (hv : 1 / 2 ≤ v) :
    |Real.log v| ≤ 2 * |v - 1| := by
  have hv0 : 0 < v := by linarith
  have h1 : Real.log v ≤ v - 1 := Real.log_le_sub_one_of_pos hv0
  have h2 : 1 - v⁻¹ ≤ Real.log v := Real.one_sub_inv_le_log_of_pos hv0
  have h3 : -(2 * |v - 1|) ≤ 1 - v⁻¹ := by
    have hform : 1 - v⁻¹ = (v - 1) / v := by field_simp
    rw [hform]
    rcases le_or_gt 1 v with h | h
    · have : 0 ≤ (v - 1) / v := div_nonneg (by linarith) hv0.le
      have : 0 ≤ |v - 1| := abs_nonneg _
      linarith
    · rw [abs_of_neg (by linarith : v - 1 < 0), le_div_iff₀ hv0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hv) (le_of_lt (sub_pos.mpr h))]
  rw [abs_le]
  constructor
  · linarith
  · have : v - 1 ≤ |v - 1| := le_abs_self _
    linarith

/-- If `2B - c ≤ A ≤ 2B` with `0 ≤ c ≤ B`, then `|log A - log B - log 2| ≤ c / B`. -/
theorem abs_log_sub_log_sub_log_two_le {A B c : ℝ} (hB : 0 < B) (hA : 0 < A)
    (hlow : 2 * B - c ≤ A) (hup : A ≤ 2 * B) (hc : c ≤ B) :
    |Real.log A - Real.log B - Real.log 2| ≤ c / B := by
  have hv : Real.log A - Real.log B - Real.log 2 = Real.log (A / (2 * B)) := by
    rw [Real.log_div hA.ne' (by positivity), Real.log_mul (by norm_num) hB.ne']; ring
  have hv1 : |A / (2 * B) - 1| ≤ c / (2 * B) := by
    have hform : A / (2 * B) - 1 = (A - 2 * B) / (2 * B) := by field_simp
    rw [hform, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * B)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [abs_le]; constructor <;> linarith
  have hhalf : c / (2 * B) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hvhalf : 1 / 2 ≤ A / (2 * B) := by
    have := neg_abs_le (A / (2 * B) - 1)
    linarith
  rw [hv]
  calc |Real.log (A / (2 * B))| ≤ 2 * |A / (2 * B) - 1| := abs_log_le_two_mul_abs_sub_one hvhalf
    _ ≤ 2 * (c / (2 * B)) := by linarith
    _ = c / B := by field_simp

/-! ## Clause (b): the unassigned indices inject into the smooth window -/

/-- The unassigned indices of `[X, 2X)` are exactly the tree's
`pivotNonSupplierBases`, the index set of the fourth budget term. -/
theorem filter_not_mem_pivotSupplierBases (X L s : ℕ) :
    (Ico X (2 * X)).filter (fun N => N ∉ pivotSupplierBases X L s)
      = pivotNonSupplierBases X L s := by
  ext N
  simp only [Finset.mem_filter, pivotNonSupplierBases, pivotSupplierBases]
  constructor
  · rintro ⟨hN, hnot⟩; exact ⟨hN, fun hs => hnot ⟨hN, hs⟩⟩
  · rintro ⟨hN, hnot⟩; exact ⟨hN, fun hh => hnot hh.2⟩

/-- `N ↦ N + t` maps the unassigned `N ∈ [X, 2X)` injectively into the
`y_X`-smooth integers of `(X + t - 1, 2X + t - 1]`. -/
theorem card_unassigned_le_card_smooth_window {X L s : ℕ} (hX : 0 < X) :
    ((Ico X (2 * X)).filter (fun N => N ∉ pivotSupplierBases X L s)).card
      ≤ ((Ioc (X + pivotOffset L s - 1) (2 * X + pivotOffset L s - 1)).filter
          (fun n => ∀ p ∈ n.primeFactors,
            ((p : ℕ) : ℝ) ≤ dickmanCut X (pivotOffset L s))).card := by
  have ht : 1 ≤ pivotOffset L s := by simp [pivotOffset]
  apply Finset.card_le_card_of_injOn (fun N => N + pivotOffset L s)
  · intro N hN
    have hN' := Finset.mem_filter.mp (Finset.mem_coe.mp hN)
    have hNI := Finset.mem_Ico.mp hN'.1
    have hnot : ¬ pivotSupplier X L s N := fun hs =>
      hN'.2 (Finset.mem_filter.mpr ⟨hN'.1, hs⟩)
    have hn : 1 < pivotArgument N L s := by simp only [pivotArgument]; omega
    apply Finset.mem_coe.mpr
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, primeFactors_le_dickmanCut hX hNI.2 hn hnot⟩
  · intro a _ b _ hab
    simpa using hab

/-- **Clause (b)** for every depth `L`:
`#{N ∈ [X, 2X) : N ∉ 𝒜} ≤ Ψ(2X + t - 1, y_X) - Ψ(X + t - 1, y_X)`. -/
theorem card_unassigned_le_smoothCount_sub {X L s : ℕ} (hX : 0 < X) :
    (((Ico X (2 * X)).filter (fun N => N ∉ pivotSupplierBases X L s)).card : ℝ)
      ≤ (smoothCount (2 * X + pivotOffset L s - 1) (dickmanCut X (pivotOffset L s)) : ℝ)
        - smoothCount (X + pivotOffset L s - 1) (dickmanCut X (pivotOffset L s)) := by
  have h := smoothCount_eq_add_card_Ioc (dickmanCut X (pivotOffset L s))
    (show X + pivotOffset L s - 1 ≤ 2 * X + pivotOffset L s - 1 by omega)
  have hb := card_unassigned_le_card_smooth_window (L := L) (s := s) hX
  rw [h, Nat.cast_add]
  have hbR : ((((Ico X (2 * X)).filter (fun N => N ∉ pivotSupplierBases X L s)).card : ℕ) : ℝ)
      ≤ (((Ioc (X + pivotOffset L s - 1) (2 * X + pivotOffset L s - 1)).filter
          (fun n => ∀ p ∈ n.primeFactors,
            ((p : ℕ) : ℝ) ≤ dickmanCut X (pivotOffset L s))).card : ℝ) := by
    exact_mod_cast hb
  linarith

/-! ## Clause (c): the smooth window has `(1 - log 2 + o(1)) X` elements -/

/-- **Clause (c), explicit form.**  For `X ≥ 625` and any offset `1 ≤ t ≤ X/2`,
`|Ψ(2X + t - 1, y_X) - Ψ(X + t - 1, y_X) - (1 - log 2) X| ≤ 40 X / log X`. -/
theorem abs_smoothWindow_sub_le {X t : ℕ} (hX : 625 ≤ X) (ht : 1 ≤ t) (htX : 2 * t ≤ X) :
    |((smoothCount (2 * X + t - 1) (dickmanCut X t) : ℝ)
        - smoothCount (X + t - 1) (dickmanCut X t)) - (1 - Real.log 2) * X|
      ≤ 40 * X / Real.log X := by
  -- Real-number facts about `X`, `√X`, `t`.
  have hXR : (625 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htXR : 2 * (t : ℝ) ≤ X := by exact_mod_cast htX
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hs25 : (25 : ℝ) ≤ Real.sqrt X := by
    have h625 : Real.sqrt (625 : ℝ) = 25 := by
      rw [show (625 : ℝ) = 25 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h625]; exact Real.sqrt_le_sqrt hXR
  have hs0 : 0 < Real.sqrt X := by linarith
  have h25s : 25 * Real.sqrt X ≤ X := by
    have := mul_le_mul_of_nonneg_right hs25 hs0.le
    linarith
  have hty : 2 * (t : ℝ) / Real.sqrt X ≤ Real.sqrt X := by
    rw [div_le_iff₀ hs0]; linarith
  have hty0 : 0 ≤ 2 * (t : ℝ) / Real.sqrt X := by positivity
  -- The cut `y = y_X` and its floor `M`.
  generalize hydef : dickmanCut X t = y
  have hy : y = 4 * Real.sqrt X + 2 * (t : ℝ) / Real.sqrt X := by rw [← hydef]; rfl
  have hy4 : 4 * Real.sqrt X ≤ y := by rw [hy]; linarith
  have hy5 : y ≤ 5 * Real.sqrt X := by rw [hy]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hyy : 16 * (X : ℝ) ≤ y * y := by
    have := mul_le_mul hy4 hy4 (by positivity) hy0
    nlinarith [this, hsq]
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, ⌊y⌋₊ = M := ⟨_, rfl⟩
  have hMy : (M : ℝ) ≤ y := hMdef ▸ Nat.floor_le hy0
  have hyM : y < (M : ℝ) + 1 := hMdef ▸ Nat.lt_floor_add_one y
  have hM3 : 3 * Real.sqrt X ≤ (M : ℝ) := by linarith
  have hM5 : (M : ℝ) ≤ 5 * Real.sqrt X := by linarith
  have hMM3 : 9 * (X : ℝ) ≤ (M : ℝ) ^ 2 := by
    have := mul_le_mul hM3 hM3 (by positivity) (Nat.cast_nonneg M)
    nlinarith [this, hsq]
  have hMM5 : (M : ℝ) ^ 2 ≤ 25 * X := by
    have := mul_le_mul hM5 hM5 (Nat.cast_nonneg M) (by positivity)
    nlinarith [this, hsq]
  -- The two endpoints `x₁ = X + t - 1`, `x₂ = 2X + t - 1`.
  generalize hx₁ : X + t - 1 = x₁
  generalize hx₂ : 2 * X + t - 1 = x₂
  have hx₂R : (x₂ : ℝ) = 2 * X + t - 1 := by
    rw [← hx₂, Nat.cast_sub (by omega)]; push_cast; ring
  have hx₁R : (x₁ : ℝ) = X + t - 1 := by
    rw [← hx₁, Nat.cast_sub (by omega)]; push_cast; ring
  have h12 : x₁ ≤ x₂ := by omega
  have hdiff : (x₂ : ℝ) - x₁ = X := by rw [hx₂R, hx₁R]; ring
  have hx₂y : (x₂ : ℝ) < y * y := by rw [hx₂R]; linarith
  have hM2 : 2 ≤ M := by
    have h2 : (2 : ℝ) ≤ M := by linarith
    exact_mod_cast h2
  have hMx₂ : M ≤ x₂ := by
    have h2 : (M : ℝ) ≤ x₂ := by rw [hx₂R]; linarith
    exact_mod_cast h2
  -- The exact identity, the floor error, the prime count and Mertens II.
  have hid := smoothCount_sub_eq hy0 h12 hx₂y
  rw [hMdef] at hid
  have hQpos : ∀ p ∈ (Ioc M x₂).filter Nat.Prime, 0 < p :=
    fun p hp => (Finset.mem_filter.mp hp).2.pos
  have hE := abs_sum_window_sub_le ((Ioc M x₂).filter Nat.Prime) hQpos x₁ x₂
  rw [hdiff] at hE
  have hcount := card_primes_Ioc_mul_log_le (M := M) (x := x₂) (by omega)
  have hmert := abs_sum_inv_primes_sub_loglog_le hM2 hMx₂
  -- Logarithms.
  have hMR2 : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogMX : Real.log X ≤ 2 * Real.log M := by
    have h1 : Real.log (Real.sqrt X) ≤ Real.log M := Real.log_le_log hs0 (by linarith)
    have h2 : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
    linarith
  have hx₂pos : (0 : ℝ) < x₂ := by rw [hx₂R]; linarith
  have hx₂1 : (1 : ℝ) < x₂ := by rw [hx₂R]; linarith
  have hlogx₂ : 0 < Real.log x₂ := Real.log_pos hx₂1
  have hMpos : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  have hA_up : Real.log x₂ ≤ 2 * Real.log M := by
    have hle : (x₂ : ℝ) ≤ (M : ℝ) ^ 2 := by rw [hx₂R]; linarith
    calc Real.log x₂ ≤ Real.log ((M : ℝ) ^ 2) := Real.log_le_log hx₂pos hle
      _ = 2 * Real.log M := by rw [Real.log_pow]; norm_num
  have hA_low : 2 * Real.log M - 6 * Real.log 2 ≤ Real.log x₂ := by
    have hle : (M : ℝ) ^ 2 ≤ 2 ^ 6 * x₂ := by rw [hx₂R]; linarith
    have h := Real.log_le_log hMpos hle
    rw [Real.log_pow, Real.log_mul (by positivity) hx₂pos.ne', Real.log_pow] at h
    push_cast at h
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  have hc : 6 * Real.log 2 ≤ Real.log M := by
    have hM64 : (64 : ℝ) ≤ M := by linarith
    have h := Real.log_le_log (by norm_num) hM64
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow] at h
    push_cast at h
    linarith
  have hLL := abs_log_sub_log_sub_log_two_le hlogM hlogx₂ hA_low hA_up hc
  -- Combine.
  have hS : |∑ p ∈ (Ioc M x₂).filter Nat.Prime, (1 : ℝ) / p - Real.log 2|
      ≤ (10 + 6 * Real.log 2) / Real.log M := by
    rw [add_div]
    calc |∑ p ∈ (Ioc M x₂).filter Nat.Prime, (1 : ℝ) / p - Real.log 2|
        ≤ |∑ p ∈ (Ioc M x₂).filter Nat.Prime, (1 : ℝ) / p
            - (Real.log (Real.log x₂) - Real.log (Real.log M))|
          + |Real.log (Real.log x₂) - Real.log (Real.log M) - Real.log 2| := abs_sub_le _ _ _
      _ ≤ 10 / Real.log M + 6 * Real.log 2 / Real.log M := add_le_add hmert hLL
  have hQ : ((((Ioc M x₂).filter Nat.Prime).card : ℕ) : ℝ)
      ≤ 6 * Real.log 2 * X / Real.log M := by
    rw [le_div_iff₀ hlogM]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hx₂3 : (x₂ : ℝ) ≤ 3 * X := by rw [hx₂R]; linarith
    calc ((((Ioc M x₂).filter Nat.Prime).card : ℕ) : ℝ) * Real.log M
        ≤ Real.log 4 * x₂ := hcount
      _ = 2 * Real.log 2 * x₂ := by rw [h4]
      _ ≤ 2 * Real.log 2 * (3 * X) := by
          apply mul_le_mul_of_nonneg_left hx₂3; linarith
      _ = 6 * Real.log 2 * X := by ring
  rw [hid, hdiff]
  generalize hW : ∑ p ∈ (Ioc M x₂).filter Nat.Prime,
    (((x₂ / p : ℕ) : ℝ) - ((x₁ / p : ℕ) : ℝ)) = W at hE ⊢
  generalize hSdef : ∑ p ∈ (Ioc M x₂).filter Nat.Prime, (1 : ℝ) / p = S at hE hS
  have key : |(X : ℝ) - W - (1 - Real.log 2) * X|
      ≤ |W - X * S| + X * |S - Real.log 2| := by
    have hform : (X : ℝ) - W - (1 - Real.log 2) * X
        = -(W - X * S) - X * (S - Real.log 2) := by ring
    rw [hform]
    calc |-(W - X * S) - X * (S - Real.log 2)|
        ≤ |-(W - X * S)| + |X * (S - Real.log 2)| := abs_sub _ _
      _ = |W - X * S| + X * |S - Real.log 2| := by rw [abs_neg, abs_mul, abs_of_pos hX0]
  have hc20 : 10 + 12 * Real.log 2 ≤ 20 := by linarith
  calc |(X : ℝ) - W - (1 - Real.log 2) * X|
      ≤ |W - X * S| + X * |S - Real.log 2| := key
    _ ≤ 6 * Real.log 2 * X / Real.log M + X * ((10 + 6 * Real.log 2) / Real.log M) :=
        add_le_add (le_trans hE hQ) (mul_le_mul_of_nonneg_left hS hX0.le)
    _ = (10 + 12 * Real.log 2) * X / Real.log M := by ring
    _ ≤ 20 * X / Real.log M := by
        apply div_le_div_of_nonneg_right _ hlogM.le
        exact mul_le_mul_of_nonneg_right hc20 hX0.le
    _ ≤ 40 * X / Real.log X := by
        rw [div_le_div_iff₀ hlogM hlogX]
        calc 20 * (X : ℝ) * Real.log X ≤ 20 * X * (2 * Real.log M) :=
              mul_le_mul_of_nonneg_left hlogMX (by positivity)
          _ = 40 * X * Real.log M := by ring

/-! ## The minimal admissible depth -/

/-- The admissibility conditions on the depth `L` from the four-term
decomposition (`FirstHarmonicPivot.DTWPivotResidualDecorrelation`):
`h ≤ L - s` and `16 (2X + h + L + 2) ≤ 2^L`. -/
def AdmissibleDepth (h s X L : ℕ) : Prop :=
  h ≤ L - s ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L

instance (h s X : ℕ) : DecidablePred (AdmissibleDepth h s X) := fun L => by
  unfold AdmissibleDepth; infer_instance

/-- An explicit admissible depth: `L = h + s + ⌊log₂ X⌋ + 10`. -/
theorem admissibleDepth_witness (h s X : ℕ) :
    AdmissibleDepth h s X (h + s + Nat.log 2 X + 10) := by
  refine ⟨by omega, ?_⟩
  have hA : h + s + 1 ≤ 2 ^ (h + s) := Nat.lt_two_pow_self
  have hB : X + 1 ≤ 2 * 2 ^ (Nat.log 2 X) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    rw [pow_succ] at this; omega
  have hlog : Nat.log 2 X ≤ X := Nat.log_le_self 2 X
  have hpow : 2 ^ (h + s + Nat.log 2 X + 10) = 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by
    rw [pow_add, pow_add]; norm_num
  rw [hpow]
  have hprod : (h + s + 1) * (X + 1) ≤ 2 ^ (h + s) * (2 * 2 ^ (Nat.log 2 X)) :=
    Nat.mul_le_mul hA hB
  have h1 : 16 * (2 * X + h + (h + s + Nat.log 2 X + 10) + 2)
      ≤ 512 * ((h + s + 1) * (X + 1)) := by
    nlinarith [Nat.zero_le (h * X), Nat.zero_le (s * X)]
  have h2 : 512 * ((h + s + 1) * (X + 1)) ≤ 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by
    calc 512 * ((h + s + 1) * (X + 1))
        ≤ 512 * (2 ^ (h + s) * (2 * 2 ^ (Nat.log 2 X))) := Nat.mul_le_mul_left _ hprod
      _ = 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by ring
  omega

theorem exists_admissibleDepth (h s X : ℕ) : ∃ L, AdmissibleDepth h s X L :=
  ⟨_, admissibleDepth_witness h s X⟩

/-- The minimal admissible depth `L(X)` for fixed `h, s`. -/
def minimalDepth (h s X : ℕ) : ℕ := Nat.find (exists_admissibleDepth h s X)

theorem minimalDepth_admissible (h s X : ℕ) :
    AdmissibleDepth h s X (minimalDepth h s X) :=
  Nat.find_spec (exists_admissibleDepth h s X)

theorem minimalDepth_le {h s X L : ℕ} (hL : AdmissibleDepth h s X L) :
    minimalDepth h s X ≤ L :=
  Nat.find_min' (exists_admissibleDepth h s X) hL

/-- The paper's offset `t = L - s + 1` at the minimal admissible depth. -/
def minimalOffset (h s X : ℕ) : ℕ := pivotOffset (minimalDepth h s X) s

/-- The paper's cut `y_X = 4√X + 2t/√X` at the minimal admissible depth. -/
noncomputable def minimalCut (h s X : ℕ) : ℝ := dickmanCut X (minimalOffset h s X)

theorem one_le_minimalOffset (h s X : ℕ) : 1 ≤ minimalOffset h s X := by
  simp [minimalOffset, pivotOffset]

/-- `t = O_{h,s}(log X)`, explicitly `t ≤ h + ⌊log₂ X⌋ + 11`. -/
theorem minimalOffset_le (h s X : ℕ) : minimalOffset h s X ≤ h + Nat.log 2 X + 11 := by
  have hle := minimalDepth_le (admissibleDepth_witness h s X)
  simp only [minimalOffset, pivotOffset]
  omega

theorem four_mul_log_two_le {X : ℕ} (hX : 16 ≤ X) : 4 * Nat.log 2 X ≤ X := by
  have hk : 4 ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hpow : 2 ^ Nat.log 2 X ≤ X := Nat.pow_log_le_self 2 (by omega)
  have key : ∀ k, 4 ≤ k → 4 * k ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  exact le_trans (key _ hk) hpow

theorem two_mul_minimalOffset_le {h s X : ℕ} (hX : 4 * h + 44 ≤ X) (hX16 : 16 ≤ X) :
    2 * minimalOffset h s X ≤ X := by
  have h1 := minimalOffset_le h s X
  have h2 := four_mul_log_two_le hX16
  omega

/-- **Clause (c), explicit rate at the minimal depth.** -/
theorem abs_minimalWindow_sub_le {h s X : ℕ} (hX : max 625 (4 * h + 44) ≤ X) :
    |((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
        - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X))
        - (1 - Real.log 2) * X|
      ≤ 40 * X / Real.log X := by
  have h625 : 625 ≤ X := le_trans (le_max_left _ _) hX
  have h4h : 4 * h + 44 ≤ X := le_trans (le_max_right _ _) hX
  exact abs_smoothWindow_sub_le h625 (one_le_minimalOffset h s X)
    (two_mul_minimalOffset_le h4h (by omega))

/-- **Clause (c).** `(Ψ(2X + t - 1, y_X) - Ψ(X + t - 1, y_X)) / X → 1 - log 2`. -/
theorem tendsto_minimalWindow_div (h s : ℕ) :
    Tendsto (fun X : ℕ =>
        ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) / X)
      atTop (𝓝 (1 - Real.log 2)) := by
  have hg : Tendsto (fun X : ℕ => (40 : ℝ) / Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun X => norm_nonneg _)) ?_ hg
  filter_upwards [eventually_ge_atTop (max 625 (4 * h + 44))] with X hX
  have hb := abs_minimalWindow_sub_le (s := s) hX
  have hX625 : 625 ≤ X := le_trans (le_max_left _ _) hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [Real.norm_eq_abs]
  have hform : ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
        - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) / X - (1 - Real.log 2)
      = (((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
        - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X))
          - (1 - Real.log 2) * X) / X := by
    field_simp
  rw [hform, abs_div, abs_of_pos hX0, div_le_iff₀ hX0]
  calc _ ≤ 40 * X / Real.log X := hb
    _ = 40 / Real.log X * X := by ring

/-- **Clause (d).** `Ψ(2X + t - 1, y_X) - Ψ(X + t - 1, y_X) < (8/25) X` for all
sufficiently large `X`. -/
theorem eventually_minimalWindow_lt (h s : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
        - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) < 8 / 25 * X := by
  have hlt : 1 - Real.log 2 < 8 / 25 := by linarith [Real.log_two_gt_d9]
  filter_upwards [(tendsto_minimalWindow_div h s).eventually_lt_const hlt,
    eventually_gt_atTop 0] with X hX hX0
  have hX0' : (0 : ℝ) < X := by exact_mod_cast hX0
  rwa [div_lt_iff₀ hX0'] at hX

/-- **`prop:dickman`** of the long #249 paper ("A one-sided bound for the
unassigned terms"), for every fixed `h, s`, with `L = minimalDepth h s X`,
`t = L - s + 1 = minimalOffset h s X`, `y_X = minimalCut h s X`,
`𝒜 = pivotSupplierBases X L s` and `Ψ = smoothCount`.  The six conjuncts are:

1. `L` is the minimal admissible depth for each `X`;
2. `t = O_{h,s}(log X)`, explicitly `t ≤ h + ⌊log₂ X⌋ + 11`;
3. (a) an unassigned `n = N + t` with `N ∈ [X, 2X)` has `P(n) ≤ y_X`;
4. (b) `#{N ∈ [X, 2X) : N ∉ 𝒜} ≤ Ψ(2X+t-1, y_X) - Ψ(X+t-1, y_X)`;
5. (c) `(Ψ(2X+t-1, y_X) - Ψ(X+t-1, y_X)) / X → 1 - log 2`, the `o(1)` of
   the paper written as a limit;
6. (d) for all sufficiently large `X`, `Ψ(2X+t-1, y_X) - Ψ(X+t-1, y_X) < (8/25) X`
   and hence `#{N ∈ [X, 2X) : N ∉ 𝒜} < (8/25) X`. -/
theorem prop_dickman (h s : ℕ) :
    (∀ X, AdmissibleDepth h s X (minimalDepth h s X) ∧
        ∀ L, AdmissibleDepth h s X L → minimalDepth h s X ≤ L) ∧
    (∀ X, minimalOffset h s X ≤ h + Nat.log 2 X + 11) ∧
    (∀ X N, 0 < X → N ∈ Ico X (2 * X) → N ∉ pivotSupplierBases X (minimalDepth h s X) s →
      ∀ hn : 1 < N + minimalOffset h s X,
        (((N + minimalOffset h s X).primeFactors.max'
            (Nat.nonempty_primeFactors.mpr hn) : ℕ) : ℝ) ≤ minimalCut h s X) ∧
    (∀ X, 0 < X →
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        ≤ (smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) ∧
    Tendsto (fun X : ℕ =>
        ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) / X)
      atTop (𝓝 (1 - Real.log 2)) ∧
    (∀ᶠ X : ℕ in atTop,
      ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) < 8 / 25 * X ∧
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        < 8 / 25 * X) := by
  refine ⟨fun X => ⟨minimalDepth_admissible h s X, fun L hL => minimalDepth_le hL⟩,
    minimalOffset_le h s, ?_, ?_, tendsto_minimalWindow_div h s, ?_⟩
  · intro X N hX hN hnotA hn
    have hnot : ¬ pivotSupplier X (minimalDepth h s X) s N := fun hs =>
      hnotA (Finset.mem_filter.mpr ⟨hN, hs⟩)
    exact largest_prime_factor_le_dickmanCut hX (Finset.mem_Ico.mp hN).2 hn hnot
  · intro X hX
    exact card_unassigned_le_smoothCount_sub hX
  · filter_upwards [eventually_minimalWindow_lt h s, eventually_gt_atTop 0] with X hX hX0
    exact ⟨hX, lt_of_le_of_lt (card_unassigned_le_smoothCount_sub hX0) hX⟩

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.smoothCount_sub_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.card_unassigned_le_smoothCount_sub
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.abs_smoothWindow_sub_le
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tendsto_minimalWindow_div
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.prop_dickman
