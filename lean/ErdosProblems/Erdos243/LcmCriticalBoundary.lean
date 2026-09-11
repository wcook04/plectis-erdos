import ErdosProblems.Erdos243.ReciprocalTailRigidity

open scoped BigOperators

/-!
# Erdős 243: the LCM critical boundary

This module formalizes the strict-rise CRT consumer and weighted block
telescope arising from the LCM-cleared tail state.
-/

namespace ErdosProblems.Erdos243

/-- The shifted-CRT obstruction only needs old-modulus avoidance at an
upward step.  The stronger theorem in `ReciprocalTailRigidity` assumes
avoidance at every later state; this is the exact variant used by the
LCM-cleared state. -/
theorem no_boundedRise_of_strictRiseAvoidance
    (u m : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (hm : ∀ n, N ≤ n → 1 < m n)
    (hpair : ∀ {i j : ℕ}, N ≤ i → N ≤ j → i ≠ j →
      Nat.Coprime (m i) (m j))
    (havoid : ∀ {i t : ℕ}, N ≤ i → i < t →
      u t < u (t + 1) → Nat.Coprime (m i) (u t))
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  let selected : Fin B → ℕ := fun i ↦ m (N + i.1)
  have hselected : ∀ i, 1 < selected i := by
    intro i
    exact hm (N + i.1) (by omega)
  have hselectedPair : ∀ i j, i ≠ j →
      Nat.Coprime (selected i) (selected j) := by
    intro i j hij
    apply hpair (by omega) (by omega)
    intro hindex
    apply hij
    apply Fin.ext
    omega
  let T := N + B
  obtain ⟨x, hxT, hxDiv⟩ :=
    exists_shifted_consecutiveMultiples selected hselected hselectedPair (u T)
  obtain ⟨K, hK⟩ := (Filter.tendsto_atTop_atTop.mp huTop) (x + B)
  let t0 := max K (T + 1)
  have ht0T : T < t0 := by
    dsimp [t0]
    exact lt_of_lt_of_le (Nat.lt_succ_self T) (le_max_right K (T + 1))
  have hu0 : x + B ≤ u t0 := hK t0 (le_max_left K (T + 1))
  let P : ℕ → Prop := fun t ↦ T < t ∧ x + B ≤ u t
  have hP : ∃ t, P t := ⟨t0, ht0T, hu0⟩
  let t := Nat.find hP
  have htP : P t := Nat.find_spec hP
  have htPrev : T ≤ t - 1 := by
    dsimp [P] at htP
    omega
  have htSucc : t - 1 + 1 = t := by
    dsimp [P] at htP
    omega
  have huPrevTop : u (t - 1) < x + B := by
    by_contra hnot
    have hge : x + B ≤ u (t - 1) := by omega
    by_cases heq : t - 1 = T
    · rw [heq] at hge
      omega
    · have hTlt : T < t - 1 := by omega
      have hmin : t ≤ t - 1 := Nat.find_min' hP ⟨hTlt, hge⟩
      omega
  have hRiseBound := hrise (t - 1) (le_trans (by omega) htPrev)
  rw [htSucc] at hRiseBound
  have huPrevBottom : x ≤ u (t - 1) := by
    dsimp [P] at htP
    omega
  have hStrictRise : u (t - 1) < u ((t - 1) + 1) := by
    rw [htSucc]
    dsimp [P] at htP
    omega
  let rNat := u (t - 1) - x
  have hrLt : rNat < B := by
    dsimp [rNat]
    omega
  let r : Fin B := ⟨rNat, hrLt⟩
  have hxr : x + r.1 = u (t - 1) := by
    dsimp [r, rNat]
    omega
  have hmodDvd : m (N + r.1) ∣ u (t - 1) := by
    rw [← hxr]
    exact hxDiv r
  have hindexLt : N + r.1 < t - 1 := by
    dsimp [T] at htPrev
    have hr := r.2
    omega
  have hcop : Nat.Coprime (m (N + r.1)) (u (t - 1)) :=
    havoid (by omega) hindexLt hStrictRise
  have hone : m (N + r.1) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hmodDvd
  have hmgt := hm (N + r.1) (by omega)
  omega

/-- Every common divisor of the LCM denominator state and the numerator
state divides the absolute centered digit.  This is the exact arithmetic
payment used at strict rises. -/
theorem centeredLcm_commonDivisor_dvd_digit
    {p D a u : ℕ} {V : ℤ}
    (hpD : p ∣ D)
    (hpu : p ∣ u)
    (hcenter :
      V = (D : ℤ) - (((a - 1) * u : ℕ) : ℤ)) :
    p ∣ V.natAbs := by
  rw [← Int.natCast_dvd]
  rw [hcenter]
  apply dvd_sub
  · exact Int.natCast_dvd_natCast.mpr hpD
  · simp only [Nat.cast_mul]
    exact dvd_mul_of_dvd_right
      (Int.natCast_dvd_natCast.mpr hpu) ((a - 1 : ℕ) : ℤ)

/-- The LCM recurrence and a lower bound `V ≥ -B` give the bounded-rise
inequality required by the CRT consumer. -/
theorem lcmState_rise_le
    (u g : ℕ → ℕ) (V : ℕ → ℤ) (N B n : ℕ)
    (hn : N ≤ n)
    (hgpos : ∀ k, N ≤ k → 0 < g k)
    (hstep : ∀ k, N ≤ k →
      (g k : ℤ) * (u (k + 1) : ℤ) = (u k : ℤ) - V k)
    (hlower : ∀ k, N ≤ k → -(B : ℤ) ≤ V k) :
    u (n + 1) ≤ u n + B := by
  have hg : (1 : ℤ) ≤ g n := by
    exact_mod_cast hgpos n hn
  have hu : (0 : ℤ) ≤ u (n + 1) := by positivity
  have hmul :
      (u (n + 1) : ℤ) ≤ (g n : ℤ) * (u (n + 1) : ℤ) := by
    nlinarith
  rw [hstep n hn] at hmul
  have hlow := hlower n hn
  exact_mod_cast (show (u (n + 1) : ℤ) ≤ u n + B by omega)

/-- At a strict rise the centered LCM digit is negative. -/
theorem lcmState_digit_neg_of_strictRise
    (u g : ℕ → ℕ) (V : ℕ → ℤ) (N n : ℕ)
    (hn : N ≤ n)
    (hgpos : ∀ k, N ≤ k → 0 < g k)
    (hstep : ∀ k, N ≤ k →
      (g k : ℤ) * (u (k + 1) : ℤ) = (u k : ℤ) - V k)
    (hrise : u n < u (n + 1)) :
    V n < 0 := by
  have hg : (1 : ℤ) ≤ g n := by
    exact_mod_cast hgpos n hn
  have hu : (0 : ℤ) ≤ u (n + 1) := by positivity
  have hmul :
      (u (n + 1) : ℤ) ≤ (g n : ℤ) * (u (n + 1) : ℤ) := by
    nlinarith
  rw [hstep n hn] at hmul
  have hriseZ : (u n : ℤ) < u (n + 1) := by
    exact_mod_cast hrise
  omega

/-- A prime larger than the negative-digit bound cannot divide the state at
a strict rise once it has entered the accumulated LCM denominator. -/
theorem lcmState_strictRise_primeAvoidance
    (u g D a : ℕ → ℕ) (V : ℕ → ℤ) (N B p n : ℕ)
    (hn : N ≤ n)
    (hp : Nat.Prime p)
    (hpLarge : B < p)
    (hpD : p ∣ D n)
    (hgpos : ∀ k, N ≤ k → 0 < g k)
    (hstep : ∀ k, N ≤ k →
      (g k : ℤ) * (u (k + 1) : ℤ) = (u k : ℤ) - V k)
    (hcenter : ∀ k, N ≤ k →
      V k = (D k : ℤ) - (((a k - 1) * u k : ℕ) : ℤ))
    (hlower : ∀ k, N ≤ k → -(B : ℤ) ≤ V k)
    (hrise : u n < u (n + 1)) :
    Nat.Coprime p (u n) := by
  rw [hp.coprime_iff_not_dvd]
  intro hpu
  have hneg :=
    lcmState_digit_neg_of_strictRise u g V N n hn hgpos hstep hrise
  have hpAbs : p ∣ (V n).natAbs :=
    centeredLcm_commonDivisor_dvd_digit hpD hpu (hcenter n hn)
  have habsPos : 0 < (V n).natAbs := by
    exact Int.natAbs_pos.mpr (ne_of_lt hneg)
  have hpLe : p ≤ (V n).natAbs := Nat.le_of_dvd habsPos hpAbs
  have habsLe : (V n).natAbs ≤ B := by
    have hrepr' :
        ((V n).natAbs : ℤ) = -V n :=
      Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)
    have hrepr :
        V n = -((V n).natAbs : ℤ) :=
      by omega
    have hlow := hlower n hn
    rw [hrepr] at hlow
    exact_mod_cast (show ((V n).natAbs : ℤ) ≤ B by omega)
  omega

/-- Kernel-checked arithmetic core of the bounded LCM-negative-part
argument.  Once infinitely many old large primes are supplied, the exact
LCM recurrence, centered-digit identity, bounded negative part, and
unbounded state are inconsistent. -/
theorem no_boundedNegative_lcmState_of_oldPrimeSupply
    (u g D a m : ℕ → ℕ) (V : ℕ → ℤ) (N B : ℕ)
    (hB : 0 < B)
    (hmPrime : ∀ i, N ≤ i → Nat.Prime (m i))
    (hmLarge : ∀ i, N ≤ i → B < m i)
    (hmPair : ∀ {i j}, N ≤ i → N ≤ j → i ≠ j →
      Nat.Coprime (m i) (m j))
    (hmOld : ∀ {i t}, N ≤ i → i < t → m i ∣ D t)
    (hgpos : ∀ n, N ≤ n → 0 < g n)
    (hstep : ∀ n, N ≤ n →
      (g n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - V n)
    (hcenter : ∀ n, N ≤ n →
      V n = (D n : ℤ) - (((a n - 1) * u n : ℕ) : ℤ))
    (hlower : ∀ n, N ≤ n → -(B : ℤ) ≤ V n)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False := by
  apply no_boundedRise_of_strictRiseAvoidance u m N B hB
  · intro n hn
    have := (hmPrime n hn).two_le
    omega
  · exact hmPair
  · intro i t hi hit hrise
    exact lcmState_strictRise_primeAvoidance
      u g D a V N B (m i) t (hi.trans (Nat.le_of_lt hit))
      (hmPrime i hi) (hmLarge i hi) (hmOld hi hit)
      hgpos hstep hcenter hlower hrise
  · intro n hn
    exact lcmState_rise_le u g V N B n hn hgpos hstep hlower
  · exact huTop

/-- Multiplicative LCM weight on the first `k` steps after `r`. -/
def lcmBlockWeight (g : ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => lcmBlockWeight g r k * g (r + k)

@[simp]
theorem lcmBlockWeight_zero (g : ℕ → ℕ) (r : ℕ) :
    lcmBlockWeight g r 0 = 1 := rfl

@[simp]
theorem lcmBlockWeight_succ (g : ℕ → ℕ) (r k : ℕ) :
    lcmBlockWeight g r (k + 1) =
      lcmBlockWeight g r k * g (r + k) := rfl

/-- Exact multiplicatively weighted telescope for the LCM state recurrence. -/
theorem lcmState_weightedBlock_telescope
    (u g : ℕ → ℕ) (V : ℕ → ℤ)
    (hstep : ∀ n,
      (g n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - V n) :
    ∀ r k,
      (lcmBlockWeight g r k : ℤ) * (u (r + k) : ℤ) =
        (u r : ℤ) -
          ∑ i ∈ Finset.range k,
            (lcmBlockWeight g r i : ℤ) * V (r + i) := by
  intro r k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      simp only [lcmBlockWeight_succ]
      have hs := hstep (r + k)
      have hindex : r + (k + 1) = (r + k) + 1 := by omega
      rw [hindex]
      push_cast
      rw [mul_assoc, hs, mul_sub, ih]
      ring

/-- Positive local multipliers give a positive block weight. -/
theorem lcmBlockWeight_pos
    (g : ℕ → ℕ) (hgpos : ∀ n, 0 < g n) (r k : ℕ) :
    0 < lcmBlockWeight g r k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [lcmBlockWeight_succ]
      exact Nat.mul_pos ih (hgpos (r + k))

/-- Nonnegative weighted debt over one complete block makes its endpoint
state no larger than its initial state. -/
theorem lcmState_blockEndpoint_le
    (u g : ℕ → ℕ) (V : ℕ → ℤ) (r k : ℕ)
    (hgpos : ∀ n, 0 < g n)
    (hstep : ∀ n,
      (g n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - V n)
    (hdebt :
      0 ≤ ∑ i ∈ Finset.range k,
        (lcmBlockWeight g r i : ℤ) * V (r + i)) :
    u (r + k) ≤ u r := by
  have htelescope := lcmState_weightedBlock_telescope u g V hstep r k
  have hGpos : (0 : ℤ) < lcmBlockWeight g r k := by
    exact_mod_cast lcmBlockWeight_pos g hgpos r k
  have huNonneg : (0 : ℤ) ≤ u (r + k) := by positivity
  have hunit :
      (u (r + k) : ℤ) ≤
        (lcmBlockWeight g r k : ℤ) * u (r + k) := by
    nlinarith
  exact_mod_cast
    (show (u (r + k) : ℤ) ≤ u r by
      rw [htelescope] at hunit
      omega)

/-- A uniform bound on the negative weighted debt inside a block bounds
every state in that block by the initial state plus the same constant. -/
theorem lcmState_insideBlock_le
    (u g : ℕ → ℕ) (V : ℕ → ℤ) (r k B : ℕ)
    (hgpos : ∀ n, 0 < g n)
    (hstep : ∀ n,
      (g n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - V n)
    (hdebt :
      -(∑ i ∈ Finset.range k,
          (lcmBlockWeight g r i : ℤ) * V (r + i)) ≤
        (B : ℤ) * lcmBlockWeight g r k) :
    u (r + k) ≤ u r + B := by
  have htelescope := lcmState_weightedBlock_telescope u g V hstep r k
  have hGpos : (0 : ℤ) < lcmBlockWeight g r k := by
    exact_mod_cast lcmBlockWeight_pos g hgpos r k
  have huStart : (0 : ℤ) ≤ u r := by positivity
  have huEnd : (0 : ℤ) ≤ u (r + k) := by positivity
  have hscaleStart :
      (u r : ℤ) ≤ (lcmBlockWeight g r k : ℤ) * u r := by
    nlinarith
  have hweighted :
      (lcmBlockWeight g r k : ℤ) * u (r + k) ≤
        (lcmBlockWeight g r k : ℤ) * (u r + B) := by
    rw [htelescope]
    nlinarith
  have hresult : (u (r + k) : ℤ) ≤ u r + B := by
    nlinarith
  exact_mod_cast hresult

/-- An integral state which is globally bounded and whose normalized
absolute digits vanish must itself have eventually zero digits. -/
theorem eventually_zero_of_bounded_lcmState
    (u : ℕ → ℕ) (V : ℕ → ℤ) (M : ℕ)
    (hbound : ∀ n, u n ≤ M)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * (V n).natAbs < u n) :
    ∃ N, ∀ n, N ≤ n → V n = 0 := by
  obtain ⟨N, hN⟩ := hvanish (M + 1)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hsmall := hN n hn
  have habs : (V n).natAbs = 0 := by
    by_contra hne
    have hpos : 0 < (V n).natAbs := Nat.pos_of_ne_zero hne
    have hM := hbound n
    nlinarith
  exact Int.natAbs_eq_zero.mp habs

/-- Exact block-debt stabilisation theorem.  The coverage hypothesis is the
proof-relevant statement that the cut points partition all indices; it
avoids hiding an Archimedean selection argument inside the arithmetic core. -/
theorem eventually_zero_of_weightedBlockDebt
    (u g cuts : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ)
    (hcuts : ∀ j, cuts j ≤ cuts (j + 1))
    (hcover : ∀ n, ∃ j k,
      k ≤ cuts (j + 1) - cuts j ∧ n = cuts j + k)
    (hgpos : ∀ n, 0 < g n)
    (hstep : ∀ n,
      (g n : ℤ) * (u (n + 1) : ℤ) = (u n : ℤ) - V n)
    (hend : ∀ j,
      0 ≤ ∑ i ∈ Finset.range (cuts (j + 1) - cuts j),
        (lcmBlockWeight g (cuts j) i : ℤ) * V (cuts j + i))
    (hinside : ∀ j k, k ≤ cuts (j + 1) - cuts j →
      -(∑ i ∈ Finset.range k,
          (lcmBlockWeight g (cuts j) i : ℤ) * V (cuts j + i)) ≤
        (B : ℤ) * lcmBlockWeight g (cuts j) k)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * (V n).natAbs < u n) :
    ∃ N, ∀ n, N ≤ n → V n = 0 := by
  have hendpoint : ∀ j, u (cuts (j + 1)) ≤ u (cuts j) := by
    intro j
    have hlocal := lcmState_blockEndpoint_le u g V (cuts j)
      (cuts (j + 1) - cuts j) hgpos hstep (hend j)
    rw [Nat.add_sub_of_le (hcuts j)] at hlocal
    exact hlocal
  have hendpointZero : ∀ j, u (cuts j) ≤ u (cuts 0) := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (hendpoint j).trans ih
  have hglobal : ∀ n, u n ≤ u (cuts 0) + B := by
    intro n
    obtain ⟨j, k, hk, rfl⟩ := hcover n
    exact (lcmState_insideBlock_le u g V (cuts j) k B
      hgpos hstep (hinside j k hk)).trans
        (Nat.add_le_add_right (hendpointZero j) B)
  exact eventually_zero_of_bounded_lcmState
    u V (u (cuts 0) + B) hglobal hvanish

end ErdosProblems.Erdos243
