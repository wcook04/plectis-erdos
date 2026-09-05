import ErdosProblems.Erdos243.DynamicCancellation

open scoped BigOperators

/-!
# Erdős 243: valuation-weighted CRT repair

This module formalizes the honest repaired-transversal consequences of the
exact cancellation payment.  It deliberately does not claim that the
unrestricted Erdős 243 orbit terminates.
-/

namespace ErdosProblems.Erdos243

/-- Product of the primitive-denominator factors deleted on `[s,t)`. -/
def deletionProduct (c : ℕ → ℕ) (s t : ℕ) : ℕ :=
  ∏ n ∈ Finset.Ico s t, c n

/-- Product of the exact common-scale growth factors on `[s,t)`. -/
def scaleProduct (h : ℕ → ℕ) (s t : ℕ) : ℕ :=
  ∏ n ∈ Finset.Ico s t, h n

/-- An initial modulus is repaired by time `t` when all of its prime-power
debt occurs in the deletion product on `[s,t)`. -/
def repairedAt (c : ℕ → ℕ) (s t m : ℕ) : Prop :=
  m ∣ deletionProduct c s t

/-- Recursive survivor after `k` exact denominator-deletion steps.  This is
the proof-friendly form of `m / gcd(m, deletionProduct c s (s+k))`. -/
def survivorSteps (c : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, m => m
  | s, k + 1, m =>
      survivorSteps c (s + 1) k (m / Nat.gcd m (c s))

/-- At one deletion step, the part of `m` not removed by `c` still divides
the quotient denominator. -/
theorem survivor_oneStep_dvd
    {m c v : ℕ}
    (hmv : m ∣ v)
    (hcv : c ∣ v) :
    m / Nat.gcd m c ∣ v / c := by
  by_cases hc : c = 0
  · simp [hc]
  have hcPos : 0 < c := Nat.pos_of_ne_zero hc
  have hgPos : 0 < Nat.gcd m c := Nat.gcd_pos_of_pos_right m hcPos
  have hgDvdM : Nat.gcd m c ∣ m := Nat.gcd_dvd_left m c
  have hlcm :
      c * (m / Nat.gcd m c) = Nat.lcm m c := by
    apply Nat.eq_of_mul_eq_mul_left hgPos
    calc
      Nat.gcd m c * (c * (m / Nat.gcd m c)) =
          c * (Nat.gcd m c * (m / Nat.gcd m c)) := by ring
      _ = c * m := by rw [Nat.mul_div_cancel' hgDvdM]
      _ = m * c := by ring
      _ = Nat.gcd m c * Nat.lcm m c := by
        rw [Nat.gcd_mul_lcm]
  rw [Nat.dvd_div_iff_mul_dvd hcv, hlcm]
  exact Nat.lcm_dvd hmv hcv

/-- Iterating the one-step survivor lemma preserves a divisor of every later
primitive denominator. -/
theorem survivor_interval_dvd_denominator
    (c α v : ℕ → ℕ)
    (hcdvd : ∀ n, c n ∣ v n)
    (hstep : ∀ n, v (n + 1) = α n * (v n / c n)) :
    ∀ {s k m}, m ∣ v s → survivorSteps c s k m ∣ v (s + k) := by
  intro s k
  induction k generalizing s with
  | zero =>
      intro m hm
      simpa [survivorSteps] using hm
  | succ k ih =>
      intro m hm
      have hone :
          m / Nat.gcd m (c s) ∣ v (s + 1) := by
        rw [hstep s]
        exact dvd_mul_of_dvd_right
          (survivor_oneStep_dvd hm (hcdvd s)) (α s)
      have htail := ih (s := s + 1) hone
      change survivorSteps c (s + 1) k (m / Nat.gcd m (c s)) ∣
        v (s + (k + 1))
      simpa [Nat.add_assoc, Nat.add_comm k 1] using htail

/-- Squared local deletion charges multiply without loss over an interval. -/
theorem deletionProduct_sq_dvd_scaleProduct
    (c h : ℕ → ℕ) (s t : ℕ)
    (hsq : ∀ n ∈ Finset.Ico s t, c n ^ 2 ∣ h n) :
    deletionProduct c s t ^ 2 ∣ scaleProduct h s t := by
  have hprod :
      (∏ n ∈ Finset.Ico s t, c n ^ 2) ∣
        ∏ n ∈ Finset.Ico s t, h n :=
    Finset.prod_dvd_prod_of_dvd _ _ hsq
  simpa [deletionProduct, scaleProduct, Finset.prod_pow] using hprod

/-- The lcm of any finite repaired family divides the total deletion
product.  Overlapping prime demands are therefore charged by a maximum
valuation, exactly as lcm requires. -/
theorem repairedFamily_lcm_dvd_deletionProduct
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ) (c : ℕ → ℕ) (s t : ℕ)
    (hrepair : ∀ r ∈ R, repairedAt c s t (m r)) :
    R.lcm m ∣ deletionProduct c s t := by
  apply Finset.lcm_dvd
  intro r hr
  exact hrepair r hr

/-- A repaired family pays the square of its transversal lcm into exact
scale growth. -/
theorem repairedFamily_lcm_sq_dvd_scaleGrowth
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ) (c h : ℕ → ℕ) (s t : ℕ)
    (hrepair : ∀ r ∈ R, repairedAt c s t (m r))
    (hsq : ∀ n ∈ Finset.Ico s t, c n ^ 2 ∣ h n) :
    (R.lcm m) ^ 2 ∣ scaleProduct h s t := by
  exact (pow_dvd_pow_of_dvd (repairedFamily_lcm_dvd_deletionProduct
    R m c s t hrepair) 2).trans
      (deletionProduct_sq_dvd_scaleProduct c h s t hsq)

/-- Square repair payments also compose over disjoint episodes; no
coprimality between episode lcms is needed. -/
theorem blockRepair_product_sq_dvd
    (M Λ : ℕ → ℕ) (episodes : Finset ℕ)
    (hpay : ∀ i ∈ episodes, M i ^ 2 ∣ Λ i) :
    (∏ i ∈ episodes, M i) ^ 2 ∣ ∏ i ∈ episodes, Λ i := by
  have hprod :
      (∏ i ∈ episodes, M i ^ 2) ∣ ∏ i ∈ episodes, Λ i :=
    Finset.prod_dvd_prod_of_dvd _ _ hpay
  simpa [Finset.prod_pow] using hprod

/-- A finite CRT barrier attached to the primitive numerator/denominator
coordinates at one state. -/
structure CRTBarrier (u v : ℕ → ℕ) where
  start : ℕ
  x : ℕ
  length : ℕ
  length_pos : 0 < length
  start_below : u start < x
  modulus : Fin length → ℕ
  modulus_gt_one : ∀ r, 1 < modulus r
  modulus_dvd_denominator : ∀ r, modulus r ∣ v start
  modulus_dvd_slot : ∀ r, modulus r ∣ x + r.1

/-- A uniform upper bound on positive one-step motion before a crossing. -/
def jumpBound (u : ℕ → ℕ) (s τ J : ℕ) : Prop :=
  0 < J ∧ ∀ n, s ≤ n → n < τ → u (n + 1) ≤ u n + J

/-- The combinatorial core of the repaired-transversal theorem.  At a first
crossing, every complete `J`-block contains a visited slot.  If unrepaired
slots are forbidden, each selected slot is repaired before the crossing. -/
theorem firstCrossing_repairTransversal
    (u v c : ℕ → ℕ) (B : CRTBarrier u v) (τ J K : ℕ)
    (hstart : B.start < τ)
    (hcross : B.x + B.length ≤ u τ)
    (hjump : jumpBound u B.start τ J)
    (hblocks : K * J ≤ B.length)
    (hforbidden : ∀ (r : Fin B.length) t,
      B.start < t → t < τ →
      ¬ repairedAt c B.start (τ - 1) (B.modulus r) →
      u t ≠ B.x + r.1) :
    ∃ r : Fin K → Fin B.length,
      (∀ q, q.1 * J ≤ (r q).1 ∧ (r q).1 < (q.1 + 1) * J) ∧
      ∀ q, repairedAt c B.start (τ - 1) (B.modulus (r q)) := by
  classical
  rcases hjump with ⟨hJ, hjump⟩
  have hslot : ∀ q : Fin K, ∃ r : Fin B.length,
      q.1 * J ≤ r.1 ∧ r.1 < (q.1 + 1) * J ∧
      repairedAt c B.start (τ - 1) (B.modulus r) := by
    intro q
    let P : ℕ → Prop := fun t ↦
      B.start < t ∧ B.x + q.1 * J ≤ u t
    have hcomplete : (q.1 + 1) * J ≤ B.length := by
      have hqK : q.1 + 1 ≤ K := Nat.succ_le_iff.mpr q.2
      exact (Nat.mul_le_mul_right J hqK).trans hblocks
    have hP : ∃ t, P t := by
      refine ⟨τ, hstart, ?_⟩
      have hqJ : q.1 * J ≤ B.length :=
        (Nat.mul_le_mul_right J (Nat.le_succ q.1)).trans hcomplete
      exact (Nat.add_le_add_left hqJ B.x).trans hcross
    let t := Nat.find hP
    let rNat := u t - B.x
    have htP : P t := Nat.find_spec hP
    have htLe : t ≤ τ := Nat.find_min' hP ⟨hstart, by
      have hqJ : q.1 * J ≤ B.length :=
        (Nat.mul_le_mul_right J (Nat.le_succ q.1)).trans hcomplete
      exact (Nat.add_le_add_left hqJ B.x).trans hcross⟩
    have htPrev : B.start ≤ t - 1 := by
      dsimp [P] at htP
      omega
    have htSucc : t - 1 + 1 = t := by
      dsimp [P] at htP
      omega
    have huPrev : u (t - 1) < B.x + q.1 * J := by
      by_contra hnot
      have hge : B.x + q.1 * J ≤ u (t - 1) := by omega
      by_cases heq : t - 1 = B.start
      · rw [heq] at hge
        have hbelow := B.start_below
        omega
      · have hlt : B.start < t - 1 := by omega
        have hmin : t ≤ t - 1 :=
          Nat.find_min' hP ⟨hlt, hge⟩
        omega
    have htPrevLt : t - 1 < τ := by omega
    have hmove : u t ≤ u (t - 1) + J := by
      simpa [htSucc] using hjump (t - 1) htPrev htPrevLt
    have huUpper : u t < B.x + (q.1 + 1) * J := by
      calc
        u t ≤ u (t - 1) + J := hmove
        _ < (B.x + q.1 * J) + J := Nat.add_lt_add_right huPrev J
        _ = B.x + (q.1 + 1) * J := by ring
    have hrLt : rNat < B.length := by
      dsimp [rNat]
      omega
    let r : Fin B.length := ⟨rNat, hrLt⟩
    have htLt : t < τ := by
      by_contra hnot
      have htEq : t = τ := by omega
      rw [htEq] at huUpper
      omega
    have hrBlock : q.1 * J ≤ r.1 ∧ r.1 < (q.1 + 1) * J := by
      dsimp [r, rNat]
      constructor <;> omega
    have hrepair : repairedAt c B.start (τ - 1) (B.modulus r) := by
      apply Classical.byContradiction
      intro hnotRepair
      apply hforbidden r t htP.1 htLt hnotRepair
      dsimp [r, rNat]
      omega
    exact ⟨r, hrBlock.1, hrBlock.2, hrepair⟩
  let r : Fin K → Fin B.length := fun q ↦ Classical.choose (hslot q)
  refine ⟨r, ?_, ?_⟩
  · intro q
    exact ⟨(Classical.choose_spec (hslot q)).1,
      (Classical.choose_spec (hslot q)).2.1⟩
  · intro q
    exact (Classical.choose_spec (hslot q)).2.2

/-- Floor-count form of `firstCrossing_repairTransversal`: the complete
blocks are exactly the first `length / J` jump-width blocks. -/
theorem firstCrossing_repairTransversal_floor
    (u v c : ℕ → ℕ) (B : CRTBarrier u v) (τ J : ℕ)
    (hstart : B.start < τ)
    (hcross : B.x + B.length ≤ u τ)
    (hjump : jumpBound u B.start τ J)
    (hforbidden : ∀ (r : Fin B.length) t,
      B.start < t → t < τ →
      ¬ repairedAt c B.start (τ - 1) (B.modulus r) →
      u t ≠ B.x + r.1) :
    ∃ r : Fin (B.length / J) → Fin B.length,
      (∀ q, q.1 * J ≤ (r q).1 ∧ (r q).1 < (q.1 + 1) * J) ∧
      ∀ q, repairedAt c B.start (τ - 1) (B.modulus (r q)) := by
  exact firstCrossing_repairTransversal u v c B τ J (B.length / J)
    hstart hcross hjump (Nat.div_mul_le_self B.length J) hforbidden

/-- Whole-multiplier lacunarity bounds the product of every initial segment
by the cube of its final multiplier. -/
theorem prefixMultiplierProduct_le_cube
    (a : ℕ → ℕ) (N : ℕ)
    (hpos : ∀ n, N ≤ n → 0 < a n)
    (hgrowth : ∀ n, N ≤ n → a n ^ 3 ≤ a (n + 1) ^ 2) :
    ∀ k, (∏ i ∈ Finset.range (k + 1), a (N + i)) ≤
      a (N + k) ^ 3 := by
  intro k
  induction k with
  | zero =>
      simp only [Nat.zero_add, Finset.range_one, Finset.prod_singleton]
      have ha : 1 ≤ a N := hpos N (le_refl N)
      calc
        a N = a N * 1 := by simp
        _ ≤ a N * (a N * a N) := by
          exact Nat.mul_le_mul_left _
            (one_le_mul_of_one_le_of_one_le ha ha)
        _ = a N ^ 3 := by ring
  | succ k ih =>
      rw [Finset.prod_range_succ]
      calc
        (∏ i ∈ Finset.range (k + 1), a (N + i)) * a (N + (k + 1)) ≤
            a (N + k) ^ 3 * a (N + (k + 1)) :=
          Nat.mul_le_mul_right _ ih
        _ ≤ a (N + (k + 1)) ^ 2 * a (N + (k + 1)) := by
          exact Nat.mul_le_mul_right _ (by
            simpa [Nat.add_assoc] using hgrowth (N + k) (by omega))
        _ = a (N + (k + 1)) ^ 3 := by ring

/-- Exact normal-form data imply the square deletion inequality. -/
theorem trueDeletion_sq_mul_next_lt_two_mul_current
    {b c uNext u paid : ℕ}
    (hb : 0 < b)
    (hstep : b * c ^ 2 * uNext = paid)
    (hcenter : paid < 2 * u) :
    c ^ 2 * uNext < 2 * u := by
  have hle : c ^ 2 * uNext ≤ b * c ^ 2 * uNext := by
    nlinarith
  rw [hstep] at hle
  exact hle.trans_lt hcenter

/-- Every genuine deletion more than halves the primitive numerator. -/
theorem trueDeletion_halves_primitiveNumerator
    {c uNext u : ℕ}
    (hc : 2 ≤ c)
    (hdelete : c ^ 2 * uNext < 2 * u) :
    2 * uNext < u := by
  have hcSq : 4 ≤ c ^ 2 := by nlinarith
  have hfour : 4 * uNext < 2 * u := by
    exact (Nat.mul_le_mul_right uNext hcSq).trans_lt (by
      simpa [Nat.mul_comm] using hdelete)
  omega

end ErdosProblems.Erdos243
