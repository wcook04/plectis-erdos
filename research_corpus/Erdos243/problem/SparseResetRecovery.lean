import ErdosProblems.Erdos243.ReciprocalTailRigidity
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős #243: sparse reset recovery

This module isolates the order-theoretic recovery forest behind dynamically
reduced reciprocal-tail orbits.  It also gives a division-free finite-product
bound for the full reset payment on a recovery interval.

The declarations do not exclude the unrestricted divergent-negative-mass
branch and therefore do not prove Erdős #243.
-/

namespace ErdosProblems.Erdos243

open scoped BigOperators

/-! ## Recovery intervals -/

/-- A reset is a nontrivial reduction factor. -/
def ResetAt (h : ℕ → ℕ) (n : ℕ) : Prop :=
  1 < h n

/-- `t` is the first later index whose height returns to at least `u r`. -/
def FirstRecoveryAt (u : ℕ → ℕ) (r t : ℕ) : Prop :=
  r < t ∧
  u r ≤ u t ∧
  ∀ k, r < k → k < t → u k < u r

/-- A recovery whose interior contains no further reset. -/
def CleanRecoveryAt
    (u h : ℕ → ℕ) (r t : ℕ) : Prop :=
  ResetAt h r ∧
  FirstRecoveryAt u r t ∧
  ∀ k, r < k → k < t → h k = 1

/-- A recovery containing a later reset before its endpoint. -/
def InterruptedRecoveryAt
    (u h : ℕ → ℕ) (r t : ℕ) : Prop :=
  FirstRecoveryAt u r t ∧
  ∃ s, r < s ∧ s < t ∧ ResetAt h s

/-- A first-recovery endpoint is unique. -/
theorem firstRecovery_unique
    {u : ℕ → ℕ} {r t₁ t₂ : ℕ}
    (h₁ : FirstRecoveryAt u r t₁)
    (h₂ : FirstRecoveryAt u r t₂) :
    t₁ = t₂ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := h₂.2.2 t₁ h₁.1 hlt
    exact (not_lt_of_ge h₁.2.1) this
  · have := h₁.2.2 t₂ h₂.1 hgt
    exact (not_lt_of_ge h₂.2.1) this

/-- First-return intervals are laminar: a reset starting inside another
recovery must recover no later than the outer endpoint. -/
theorem firstRecovery_nested
    {u : ℕ → ℕ} {r s tr ts : ℕ}
    (hr : FirstRecoveryAt u r tr)
    (hs : FirstRecoveryAt u s ts)
    (hrs : r < s)
    (hst : s < tr) :
    ts ≤ tr := by
  have husr : u s < u r := hr.2.2 s hrs hst
  by_contra hnot
  have htrts : tr < ts := by omega
  have hinner : u tr < u s := hs.2.2 tr hst htrts
  exact (not_lt_of_ge hr.2.1) (hinner.trans husr)

/-- A specified last reset in a recovery starts a clean sub-recovery. -/
theorem lastReset_starts_cleanRecovery
    {u h : ℕ → ℕ} {r tr ell tell : ℕ}
    (hhpos : ∀ n, 0 < h n)
    (hr : FirstRecoveryAt u r tr)
    (hellReset : ResetAt h ell)
    (hrell : r ≤ ell)
    (helltr : ell < tr)
    (htell : FirstRecoveryAt u ell tell)
    (hmax :
      ∀ k, r ≤ k → k < tr → ResetAt h k → k ≤ ell) :
    tell ≤ tr ∧ CleanRecoveryAt u h ell tell := by
  have htelltr : tell ≤ tr := by
    rcases hrell.eq_or_lt with rfl | hrlt
    · exact (firstRecovery_unique htell hr).le
    · exact firstRecovery_nested hr htell hrlt helltr
  refine ⟨htelltr, hellReset, htell, ?_⟩
  intro k hellk hktell
  have hklt : k < tr := lt_of_lt_of_le hktell htelltr
  by_contra hk
  have hkReset : ResetAt h k := by
    simp only [ResetAt]
    have := hhpos k
    omega
  have hkle := hmax k (hrell.trans (Nat.le_of_lt hellk)) hklt hkReset
  exact (not_lt_of_ge hkle) hellk

/-- Every reset recovery contains a reset-aligned clean recovery.  The proof
chooses the last reset in the finite outer interval and automatically handles
arbitrarily nested interruptions. -/
theorem exists_cleanRecovery_inside
    {u h : ℕ → ℕ} {r tr : ℕ}
    (hhpos : ∀ n, 0 < h n)
    (hrReset : ResetAt h r)
    (hr : FirstRecoveryAt u r tr)
    (hexists :
      ∀ s, ResetAt h s →
        ∃ ts, FirstRecoveryAt u s ts) :
    ∃ ell tell,
      r ≤ ell ∧
      tell ≤ tr ∧
      CleanRecoveryAt u h ell tell := by
  classical
  let resets := (Finset.Ico r tr).filter (ResetAt h)
  have hrmem : r ∈ resets := by
    simp [resets, hr.1, hrReset]
  let ell := resets.max' ⟨r, hrmem⟩
  have hellmem : ell ∈ resets := Finset.max'_mem resets _
  have hrell : r ≤ ell := Finset.le_max' resets r hrmem
  have helltr : ell < tr := by
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hellmem).1).2
  have hellReset : ResetAt h ell := (Finset.mem_filter.mp hellmem).2
  obtain ⟨tell, htell⟩ := hexists ell hellReset
  have hmax :
      ∀ k, r ≤ k → k < tr → ResetAt h k → k ≤ ell := by
    intro k hrk hktr hkReset
    apply Finset.le_max' resets k
    simp [resets, hrk, hktr, hkReset]
  obtain ⟨htelltr, hclean⟩ :=
    lastReset_starts_cleanRecovery
      hhpos hr hellReset hrell helltr htell hmax
  exact ⟨ell, tell, hrell, htelltr, hclean⟩

/-- Distinct clean recoveries are ordered and disjoint. -/
theorem cleanRecovery_disjoint
    {u h : ℕ → ℕ} {r s tr ts : ℕ}
    (hr : CleanRecoveryAt u h r tr)
    (hs : CleanRecoveryAt u h s ts)
    (hrs : r < s) :
    tr ≤ s := by
  by_contra hnot
  have hstr : s < tr := by omega
  have hone : h s = 1 := hr.2.2 s hrs hstr
  have hreset : 1 < h s := hs.1
  omega

/-! ## Division-free payment bounds -/

/-- One exact reduced step plus a division-free relative-error bound controls
the reset payment at that step. -/
theorem recovery_step_bound
    (u h : ℕ → ℕ) (e : ℕ → ℤ) (K n : ℕ)
    (hstep :
      (h n : ℤ) * (u (n + 1) : ℤ) =
        (u n : ℤ) - e n)
    (herr : K * Int.natAbs (e n) < u n) :
    K * h n * u (n + 1) < (K + 1) * u n := by
  have herrZ :
      (K : ℤ) * Int.natAbs (e n) < (u n : ℤ) := by
    exact_mod_cast herr
  have habs : -(Int.natAbs (e n) : ℤ) ≤ e n := by
    by_cases he : 0 ≤ e n
    · rw [Int.natAbs_of_nonneg he]
      omega
    · have he' : e n ≤ 0 := by omega
      have habscast :
          (Int.natAbs (e n) : ℤ) = -e n :=
        Int.ofNat_natAbs_of_nonpos he'
      rw [habscast]
      simp
  have heBound :
      (u n : ℤ) - e n ≤
        (u n : ℤ) + Int.natAbs (e n) := by
    omega
  have hboundZ :
      (K : ℤ) * (h n : ℤ) * (u (n + 1) : ℤ) <
        ((K + 1 : ℕ) : ℤ) * (u n : ℤ) := by
    calc
      (K : ℤ) * (h n : ℤ) * (u (n + 1) : ℤ) =
          (K : ℤ) * ((u n : ℤ) - e n) := by
            rw [mul_assoc, hstep]
      _ ≤ (K : ℤ) *
          ((u n : ℤ) + Int.natAbs (e n)) :=
            mul_le_mul_of_nonneg_left heBound (by positivity)
      _ < (K : ℤ) * (u n : ℤ) + (u n : ℤ) := by
            rw [mul_add]
            simpa [add_comm, add_left_comm, add_assoc] using
              (add_lt_add_left herrZ ((K : ℤ) * (u n : ℤ)))
      _ = ((K + 1 : ℕ) : ℤ) * (u n : ℤ) := by
            push_cast
            ring
  exact_mod_cast hboundZ

/-- Iterating the one-step estimate controls the complete reset payment and
the endpoint height. -/
theorem recovery_payment_with_endpoint_bound
    (u h : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hhpos : ∀ n, 0 < h n)
    (hstep :
      ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) =
        (u n : ℤ) - e n)
    (herr :
      ∀ i, i < L →
        K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L) :
    K ^ L *
        (∏ i ∈ Finset.range L, h (r + i)) *
        u (r + L) <
      (K + 1) ^ L * u r := by
  have hle : ∀ m, m ≤ L →
      K ^ m *
          (∏ i ∈ Finset.range m, h (r + i)) *
          u (r + m) ≤
        (K + 1) ^ m * u r := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
        have hmL : m < L := by omega
        have hsingle :=
          (recovery_step_bound u h e K (r + m)
            (hstep (r + m)) (herr m hmL)).le
        calc
          K ^ (m + 1) *
                (∏ i ∈ Finset.range (m + 1), h (r + i)) *
                u (r + (m + 1)) =
              (K ^ m *
                (∏ i ∈ Finset.range m, h (r + i))) *
              (K * h (r + m) * u (r + m + 1)) := by
                rw [pow_succ, Finset.prod_range_succ]
                ring_nf
          _ ≤ (K ^ m *
                (∏ i ∈ Finset.range m, h (r + i))) *
              ((K + 1) * u (r + m)) :=
                Nat.mul_le_mul_left _ hsingle
          _ = (K + 1) *
              (K ^ m *
                (∏ i ∈ Finset.range m, h (r + i)) *
                u (r + m)) := by ring
          _ ≤ (K + 1) * ((K + 1) ^ m * u r) :=
                Nat.mul_le_mul_left _ (ih (by omega))
          _ = (K + 1) ^ (m + 1) * u r := by
                rw [pow_succ]
                ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  have hmL : m < m + 1 := Nat.lt_succ_self m
  have hsingle :=
    recovery_step_bound u h e K (r + m)
      (hstep (r + m)) (herr m hmL)
  have hprefixPos :
      0 < K ^ m * (∏ i ∈ Finset.range m, h (r + i)) := by
    exact Nat.mul_pos (pow_pos hK m)
      (Finset.prod_pos fun i _hi ↦ hhpos (r + i))
  calc
    K ^ (m + 1) *
          (∏ i ∈ Finset.range (m + 1), h (r + i)) *
          u (r + (m + 1)) =
        (K ^ m *
          (∏ i ∈ Finset.range m, h (r + i))) *
        (K * h (r + m) * u (r + m + 1)) := by
          rw [pow_succ, Finset.prod_range_succ]
          ring_nf
    _ < (K ^ m *
          (∏ i ∈ Finset.range m, h (r + i))) *
        ((K + 1) * u (r + m)) :=
          Nat.mul_lt_mul_of_pos_left hsingle hprefixPos
    _ = (K + 1) *
        (K ^ m *
          (∏ i ∈ Finset.range m, h (r + i)) *
          u (r + m)) := by ring
    _ ≤ (K + 1) * ((K + 1) ^ m * u r) :=
          Nat.mul_le_mul_left _ (hle m (by omega))
    _ = (K + 1) ^ (m + 1) * u r := by
          rw [pow_succ]
          ring

/-- At a genuine recovery, endpoint height cancels from the preceding bound,
leaving a pure inequality for the total reset payment. -/
theorem recovery_payment_bound_divisionFree
    (u h : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep :
      ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) =
        (u n : ℤ) - e n)
    (herr :
      ∀ i, i < L →
        K * Int.natAbs (e (r + i)) < u (r + i))
    (hL : 0 < L)
    (hrecover : u r ≤ u (r + L)) :
    K ^ L *
        (∏ i ∈ Finset.range L, h (r + i)) <
      (K + 1) ^ L := by
  have hbound :=
    recovery_payment_with_endpoint_bound
      u h e K r L hK hhpos hstep herr hL
  apply (Nat.mul_lt_mul_right (hupos r)).mp
  calc
    (K ^ L *
        (∏ i ∈ Finset.range L, h (r + i))) * u r ≤
      (K ^ L *
        (∏ i ∈ Finset.range L, h (r + i))) * u (r + L) :=
          Nat.mul_le_mul_left _ hrecover
    _ < (K + 1) ^ L * u r := hbound

/-- On a clean recovery, the full payment product is just the initial reset
factor. -/
theorem cleanRecovery_payment_eq
    {u h : ℕ → ℕ} {r L : ℕ}
    (hclean : CleanRecoveryAt u h r (r + L)) :
    (∏ i ∈ Finset.range L, h (r + i)) = h r := by
  classical
  have hL : 0 < L := by
    have := hclean.2.1.1
    omega
  apply Finset.prod_eq_single_of_mem 0
  · simp [hL]
  · intro i hi hi0
    apply hclean.2.2 (r + i)
    · omega
    · have hiL := Finset.mem_range.mp hi
      omega

/-- Clean recoveries therefore pay for their initial reset entirely through
the available relative-error budget. -/
theorem cleanRecovery_payment_bound_divisionFree
    (u h : ℕ → ℕ) (e : ℕ → ℤ) (K r L : ℕ)
    (hK : 0 < K)
    (hupos : ∀ n, 0 < u n)
    (hhpos : ∀ n, 0 < h n)
    (hstep :
      ∀ n, (h n : ℤ) * (u (n + 1) : ℤ) =
        (u n : ℤ) - e n)
    (herr :
      ∀ i, i < L →
        K * Int.natAbs (e (r + i)) < u (r + i))
    (hclean : CleanRecoveryAt u h r (r + L)) :
    K ^ L * h r < (K + 1) ^ L := by
  have hL : 0 < L := by
    have := hclean.2.1.1
    omega
  have hbound :=
    recovery_payment_bound_divisionFree
      u h e K r L hK hupos hhpos hstep herr hL hclean.2.1.2.1
  simpa [cleanRecovery_payment_eq hclean] using hbound

/-! ## A checked endpoint consumer -/

/-- A uniformly bounded positive tail and division-free normalized vanishing
force the integral centered state to vanish eventually. -/
theorem eventually_zero_of_bounded_tail_normalizedVanishes
    (C : ℕ → ℕ) (E : ℕ → ℤ) (M : ℕ)
    (hbound : ∀ n, C n ≤ M)
    (hvanish :
      ∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  obtain ⟨N, hN⟩ := hvanish (M + 1)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hsmall := hN n hn
  have habs : Int.natAbs (E n) = 0 := by
    by_contra hne
    have : 0 < Int.natAbs (E n) := Nat.pos_of_ne_zero hne
    have := hbound n
    nlinarith
  exact Int.natAbs_eq_zero.mp habs

/-- The normalized negative mass of an integral tail step. -/
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n

/-- The exact update `Cₙ₊₁ = Cₙ - Eₙ` is bounded above by multiplication by
`1 + negativeRelativeMass`. -/
theorem tail_growth_le_one_add_negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hstep :
      ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) :
    ∀ n,
      (C (n + 1) : ℝ) ≤
        C n * (1 + negativeRelativeMass C E n) := by
  intro n
  have hCne : (C n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hCpos n))
  by_cases he : E n ≤ 0
  · have hmin : min (E n) 0 = E n := min_eq_left he
    have habscast :
        (Int.natAbs (E n) : ℤ) = -E n :=
      Int.ofNat_natAbs_of_nonpos he
    have hstepR :
        (C (n + 1) : ℝ) =
          (C n : ℝ) - (E n : ℝ) := by
      exact_mod_cast hstep n
    rw [negativeRelativeMass, hmin]
    have habsR :
        (Int.natAbs (E n) : ℝ) = -(E n : ℝ) := by
      calc
        (Int.natAbs (E n) : ℝ) =
            (((Int.natAbs (E n) : ℕ) : ℤ) : ℝ) := by norm_num
        _ = ((-E n : ℤ) : ℝ) := by rw [habscast]
        _ = -(E n : ℝ) := by norm_num
    rw [habsR, hstepR]
    apply le_of_eq
    field_simp [hCne]
    ring
  · have hepos : 0 ≤ E n := by omega
    have hmin : min (E n) 0 = 0 := min_eq_right hepos
    have hstepR :
        (C (n + 1) : ℝ) =
          (C n : ℝ) - (E n : ℝ) := by
      exact_mod_cast hstep n
    rw [negativeRelativeMass, hmin]
    simp only [Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, mul_one]
    rw [hstepR]
    exact sub_le_self _ (by exact_mod_cast hepos)

/-- Summable nonnegative relative growth makes the integral tail eventually
bounded; division-free normalized vanishing then forces eventual zero. -/
theorem eventually_zero_of_summable_relativeGrowth
    (C : ℕ → ℕ) (E : ℕ → ℤ) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 ≤ δ n)
    (hsum : Summable δ)
    (hgrowth :
      ∀ n, (C (n + 1) : ℝ) ≤ C n * (1 + δ n))
    (hvanish :
      ∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  have hCprod : ∀ N,
      (C N : ℝ) ≤
        C 0 * (∏ i ∈ Finset.range N, (1 + δ i)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        calc
          (C (N + 1) : ℝ) ≤ C N * (1 + δ N) := hgrowth N
          _ ≤ (C 0 *
                (∏ i ∈ Finset.range N, (1 + δ i))) *
              (1 + δ N) :=
                mul_le_mul_of_nonneg_right ih (by linarith [hδ N])
          _ = C 0 *
              (∏ i ∈ Finset.range (N + 1), (1 + δ i)) := by
                rw [Finset.prod_range_succ]
                ring
  have hmulti : Multipliable (fun n ↦ 1 + δ n) :=
    Real.multipliable_one_add_of_summable hsum
  obtain ⟨R, hRpos, s, hs⟩ :=
    hmulti.eventually_bounded_finset_prod
  obtain ⟨N₀, hsRange⟩ := Finset.exists_nat_subset_range s
  obtain ⟨M, hM⟩ :=
    exists_nat_gt ((C 0 : ℝ) * R)
  have hMpos : 0 < M := by
    have hnonneg : 0 ≤ (C 0 : ℝ) * R := mul_nonneg (by positivity) hRpos.le
    exact_mod_cast hnonneg.trans_lt hM
  obtain ⟨N₁, hN₁⟩ := hvanish M
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  have hn₀ : N₀ ≤ n := (Nat.le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (Nat.le_max_right _ _).trans hn
  have hprod :
      (∏ i ∈ Finset.range n, (1 + δ i)) ≤ R := by
    apply hs
    exact hsRange.trans (Finset.range_mono hn₀)
  have hCnReal : (C n : ℝ) < M := by
    calc
      (C n : ℝ) ≤
          C 0 * (∏ i ∈ Finset.range n, (1 + δ i)) :=
            hCprod n
      _ ≤ C 0 * R :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
      _ < M := hM
  have hCn : C n < M := by exact_mod_cast hCnReal
  have herr := hN₁ n hn₁
  have habs : Int.natAbs (E n) = 0 := by
    by_contra hne
    have habspos : 0 < Int.natAbs (E n) :=
      Nat.pos_of_ne_zero hne
    nlinarith
  exact Int.natAbs_eq_zero.mp habs

/-- Main conditional termination theorem from the sparse-reset return:
finite normalized negative mass forces the integral centered state to vanish
eventually. -/
theorem eventually_zero_of_summable_negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hstep :
      ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n)
    (hvanish :
      ∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (E n) < C n)
    (hsum : Summable (negativeRelativeMass C E)) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  apply eventually_zero_of_summable_relativeGrowth
    C E (negativeRelativeMass C E)
  · intro n
    exact div_nonneg (by positivity) (by positivity)
  · exact hsum
  · exact tail_growth_le_one_add_negativeRelativeMass C E hCpos hstep
  · exact hvanish

/-- Paper-facing endpoint for the finite-negative-mass branch.  Along the
exact product-cleared reciprocal-tail orbit, division-free normalized
vanishing and summable normalized negative centered mass force the original
denominators to satisfy the Sylvester recurrence eventually. -/
theorem sylvesterNext_eventually_of_summable_negativeRelativeMass
    (a D : ℕ → ℤ) (C : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC :
      ∀ n, (C (n + 1) : ℤ) =
        nextTailState (a n) (D n) (C n))
    (hCpos : ∀ n, 0 < C n)
    (hstep :
      ∀ n, (C (n + 1) : ℤ) =
        (C n : ℤ) - centeredState (a n) (D n) (C n))
    (hvanish :
      ∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (centeredState (a n) (D n) (C n)) < C n)
    (hsum :
      Summable
        (negativeRelativeMass C
          (fun n ↦ centeredState (a n) (D n) (C n)))) :
    ∃ N, ∀ n, N ≤ n →
      a (n + 1) = sylvesterNext (a n) := by
  have hzero :
      ∃ N, ∀ n, N ≤ n →
        centeredState (a n) (D n) (C n) = 0 :=
    eventually_zero_of_summable_negativeRelativeMass
      C (fun n ↦ centeredState (a n) (D n) (C n))
      hCpos hstep hvanish hsum
  apply sylvesterNext_eventually_of_centered_zero
    a D (fun n ↦ (C n : ℤ)) hD
  · intro n
    exact hC n
  · exact hzero
  · refine ⟨0, fun n _hn ↦ ?_⟩
    exact_mod_cast (Nat.ne_of_gt (hCpos (n + 1)))

end ErdosProblems.Erdos243
