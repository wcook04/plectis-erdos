import ErdosProblems.Erdos243.WeightedCRTRepair
import ErdosProblems.Erdos243.SparseResetRecovery
import ErdosProblems.Erdos243.PrimitivePrefixRigidity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős #243: the repair-entropy conservation law

Two already-checked facts about a recovery interval `[r, r+L)` are here
composed for the first time.

* `recovery_payment_bound_divisionFree` : inside a division-free relative
  error budget `K`, a recovery pays `K ^ L * ∏ h < (K+1) ^ L`.
* `repairedFamily_lcm_sq_dvd_scaleGrowth` : a repaired family pays the
  **square** of its transversal lcm into that same scale growth.

Composing them charges an arbitrary reset by *how much independent
arithmetic information it deletes*, not by how often it happens:

`K ^ L * (lcm of the repaired family) ^ 2 < (K + 1) ^ L`.

Counting resets cannot control a single enormous reset that repairs many CRT
obstructions at once; the lcm-squared form can.  Consequences: independent
repairs have vanishing density (`repaired_card_bound_of_independent`), and on
every fixed horizon, sufficiently late recoveries are cancellation-free
(`eventually_recoveryPayment_eq_one_of_fixedLength`).

Nothing here proves that the unrestricted Erdős 243 orbit terminates.  The
missing producer is a positive lower bound on repair-lcm entropy per unit
recovery time.
-/

namespace ErdosProblems.Erdos243

open scoped BigOperators

/-- The interval scale product is the range product used by the payment
bound. -/
theorem scaleProduct_eq_range_prod (h : ℕ → ℕ) (r L : ℕ) :
    scaleProduct h r (r + L) = ∏ i ∈ Finset.range L, h (r + i) := by
  unfold scaleProduct
  rw [Finset.prod_Ico_eq_prod_range]
  simp

/-- **Repair-entropy conservation law.**  A repaired family on a recovery
interval pays the square of its transversal lcm inside the same division-free
relative-error budget that bounds the whole reset payment. -/
theorem repairedFamily_recovery_energy_divisionFree
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ)
    (u h c : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (herr : ∀ i, i < L → K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L)
    (hrecover : u r ≤ u (r + L))
    (hrepair : ∀ q ∈ R, repairedAt c r (r + L) (m q))
    (hsq : ∀ n ∈ Finset.Ico r (r + L), c n ^ 2 ∣ h n) :
    K ^ L * (R.lcm m) ^ 2 < (K + 1) ^ L := by
  have hdiv : (R.lcm m) ^ 2 ∣ scaleProduct h r (r + L) :=
    repairedFamily_lcm_sq_dvd_scaleGrowth R m c h r (r + L) hrepair hsq
  have hscalePos : 0 < scaleProduct h r (r + L) := by
    unfold scaleProduct
    exact Finset.prod_pos fun n _ => hhpos n
  have hle : (R.lcm m) ^ 2 ≤ scaleProduct h r (r + L) := Nat.le_of_dvd hscalePos hdiv
  have hpay := recovery_payment_bound_divisionFree u h e K r L hK hupos hhpos hstep herr hL
    hrecover
  rw [← scaleProduct_eq_range_prod] at hpay
  calc K ^ L * (R.lcm m) ^ 2 ≤ K ^ L * scaleProduct h r (r + L) :=
        Nat.mul_le_mul_left _ hle
    _ < (K + 1) ^ L := hpay

/-- **Independent repairs have vanishing density.**  A repaired family whose
lcm is at least `2 ^ card` — for instance a pairwise coprime family of moduli
exceeding one — has cardinality bounded through the same budget. -/
theorem repaired_card_bound_of_independent
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ)
    (u h c : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (herr : ∀ i, i < L → K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L)
    (hrecover : u r ≤ u (r + L))
    (hrepair : ∀ q ∈ R, repairedAt c r (r + L) (m q))
    (hsq : ∀ n ∈ Finset.Ico r (r + L), c n ^ 2 ∣ h n)
    (hindep : 2 ^ R.card ≤ R.lcm m) :
    K ^ L * 4 ^ R.card < (K + 1) ^ L := by
  have hmain := repairedFamily_recovery_energy_divisionFree R m u h c e K r L hK hupos hhpos
    hstep herr hL hrecover hrepair hsq
  have hsq2 : (4 : ℕ) ^ R.card ≤ (R.lcm m) ^ 2 := by
    have hstep : ((2 : ℕ) ^ R.card) ^ 2 ≤ (R.lcm m) ^ 2 := Nat.pow_le_pow_left hindep 2
    have h4 : (4 : ℕ) ^ R.card = ((2 : ℕ) ^ R.card) ^ 2 := by
      rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul, Nat.mul_comm]
    rw [h4]
    exact hstep
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hsq2) hmain

/-- **Fixed-horizon resets eventually disappear.**  Under normalised
vanishing of the centred error, every sufficiently late recovery of a fixed
length is cancellation-free.  Recovery times of surviving resets must
therefore escape to infinity. -/
theorem eventually_recoveryPayment_eq_one_of_fixedLength
    (u h : ℕ → ℕ) (e : ℕ → ℤ)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (hvanish : ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K * Int.natAbs (e n) < u n)
    (L : ℕ) (hL : 0 < L) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → u r ≤ u (r + L) →
      (∏ i ∈ Finset.range L, h (r + i)) = 1 := by
  obtain ⟨q, hq, hrate⟩ := exists_nearUnitPower_rate L
  obtain ⟨N, hN⟩ := hvanish q
  refine ⟨N, fun r hr hrecover => ?_⟩
  have herr : ∀ i, i < L → q * Int.natAbs (e (r + i)) < u (r + i) := by
    intro i _
    exact hN (r + i) (by omega)
  have hpay := recovery_payment_bound_divisionFree u h e q r L hq hupos hhpos hstep herr hL
    hrecover
  have hprodPos : 0 < ∏ i ∈ Finset.range L, h (r + i) :=
    Finset.prod_pos fun i _ => hhpos (r + i)
  by_contra hne
  have hge2 : 2 ≤ ∏ i ∈ Finset.range L, h (r + i) := by omega
  have hlow : 2 * q ^ L ≤ q ^ L * ∏ i ∈ Finset.range L, h (r + i) := by
    calc 2 * q ^ L = q ^ L * 2 := by ring
      _ ≤ q ^ L * ∏ i ∈ Finset.range L, h (r + i) := Nat.mul_le_mul_left _ hge2
  omega

/-- **No third category for an old prime-power.**  A modulus surviving exact
denominator deletion still divides the later primitive denominator, so any
overlap between the survivor and the later Sylvester factor `a - 1` is forced
into the later centred error.  Either an old factor is deleted — and paid for
quadratically by the conservation law above — or it stays visible. -/
theorem survivor_overlap_dvd_centeredError
    (c α v : ℕ → ℕ) (a u Q : ℕ → ℕ) (e : ℕ → ℤ)
    (hcdvd : ∀ n, c n ∣ v n)
    (hden : ∀ n, v (n + 1) = α n * (v n / c n))
    (hcenter : ∀ n, (Q n : ℤ) * (v n : ℤ) = ((a n : ℤ) - 1) * (u n : ℤ) + e n) :
    ∀ {s k m : ℕ}, m ∣ v s →
      (Int.gcd ((survivorSteps c s k m : ℕ) : ℤ) ((a (s + k) : ℤ) - 1) : ℤ) ∣ e (s + k) := by
  intro s k m hm
  have hsurvivor : survivorSteps c s k m ∣ v (s + k) :=
    survivor_interval_dvd_denominator c α v hcdvd hden hm
  exact primitiveDigit_gcd_dvd_error (Q := Q (s + k)) (A := v (s + k))
    (a := a (s + k)) (u := u (s + k)) (digit := survivorSteps c s k m)
    hsurvivor (hcenter (s + k))

/-! ## Logarithmic form -/

/-- **Repair entropy in logarithmic form.**  Two units of logarithmic payment
are charged per unit of repaired lcm. -/
theorem repairedFamily_log_energy
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (m : ι → ℕ)
    (u h c : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep : ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - e n)
    (herr : ∀ i, i < L → K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L)
    (hrecover : u r ≤ u (r + L))
    (hrepair : ∀ q ∈ R, repairedAt c r (r + L) (m q))
    (hsq : ∀ n ∈ Finset.Ico r (r + L), c n ^ 2 ∣ h n)
    (hlcm : 0 < R.lcm m) :
    2 * Real.log ((R.lcm m : ℕ) : ℝ) <
      (L : ℝ) * (Real.log ((K : ℝ) + 1) - Real.log (K : ℝ)) := by
  have hmain := repairedFamily_recovery_energy_divisionFree R m u h c e K r L hK hupos hhpos
    hstep herr hL hrecover hrepair hsq
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hlcmR : (0 : ℝ) < ((R.lcm m : ℕ) : ℝ) := by exact_mod_cast hlcm
  have hR : ((K : ℝ)) ^ L * ((R.lcm m : ℕ) : ℝ) ^ 2 < ((K : ℝ) + 1) ^ L := by
    have hcast : ((K ^ L * (R.lcm m) ^ 2 : ℕ) : ℝ) < (((K + 1) ^ L : ℕ) : ℝ) := by
      exact_mod_cast hmain
    push_cast at hcast
    linarith
  have hposL : (0 : ℝ) < ((K : ℝ)) ^ L * ((R.lcm m : ℕ) : ℝ) ^ 2 := by positivity
  have hlog := Real.log_lt_log hposL hR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  push_cast at hlog
  nlinarith [hlog]

end ErdosProblems.Erdos243
