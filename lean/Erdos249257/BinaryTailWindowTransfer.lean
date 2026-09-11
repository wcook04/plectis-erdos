import Erdos249257.GenericTailOrbitRigidity
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Binary-tail window transfer

This module isolates the support-free analytic boundary behind the T11
zero-window argument.  Arithmetic owners need only produce two certificates:

* a lower bound `2^h ≤ scale * binaryCoeffTail f (start + h)`;
* an upper envelope for `binaryCoeffTail f`.

The transfer layer composes those certificates, builds the standard subpower
envelope, absorbs the self-referential window length, and performs logarithmic
inversion.  It deliberately knows nothing about support coefficients, divisor
bounds, rational-support states, or the concrete T11/T12 theorem names.

This is an interface refactor only.  It does not strengthen the theorem
frontier of either Erdős problem.
-/

namespace Erdos249257

/-! ## Certificate boundary -/

/-- `f` vanishes at the `h` positive offsets after `N`, namely
`N + 1, ..., N + h`. -/
def CoeffZeroWindow (f : ℕ → ℕ) (N h : ℕ) : Prop :=
  ∀ j : ℕ, j < h → f (N + j + 1) = 0

/-- An empty coefficient window is vacuous. -/
@[simp] theorem coeffZeroWindow_zero (f : ℕ → ℕ) (N : ℕ) :
    CoeffZeroWindow f N 0 := by
  intro j hj
  omega

/-- A length-one window consumes exactly the coefficient at `N + 1`. -/
@[simp] theorem coeffZeroWindow_one_iff (f : ℕ → ℕ) (N : ℕ) :
    CoeffZeroWindow f N 1 ↔ f (N + 1) = 0 := by
  constructor
  · intro hzero
    simpa using hzero 0 (by omega)
  · intro hzero j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa using hzero

/-- A domain-produced lower certificate for a binary coefficient tail. -/
def BinaryTailWindowLowerBound
    (f : ℕ → ℕ) (scale : ℝ) (start h : ℕ) : Prop :=
  (2 : ℝ) ^ h ≤ scale * binaryCoeffTail f (start + h)

/-- A global real-valued upper envelope for a binary coefficient tail. -/
def BinaryCoeffTailEnvelope
    (f : ℕ → ℕ) (envelope : ℕ → ℝ) : Prop :=
  ∀ M : ℕ, binaryCoeffTail f M ≤ envelope M

/-- A natural state doubles exactly across a coefficient-zero window. -/
theorem state_eq_pow_mul_of_coeffZeroWindow
    (f : ℕ → ℕ) (offset v N h : ℕ) (u : ℕ → ℕ)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * f (offset + n + 1) = 2 * u n)
    (hzero : CoeffZeroWindow f (offset + N) h) :
    u (N + h) = 2 ^ h * u N := by
  have hiter : ∀ m : ℕ, m ≤ h → u (N + m) = 2 ^ m * u N := by
    intro m
    induction m with
    | zero =>
        intro _
        simp
    | succ m ih =>
        intro hm
        have hm_lt : m < h := Nat.lt_of_succ_le hm
        have hz0 : f ((offset + N) + m + 1) = 0 := hzero m hm_lt
        have hz : f (offset + (N + m) + 1) = 0 := by
          simpa [Nat.add_assoc] using hz0
        have hstep : u ((N + m) + 1) = 2 * u (N + m) := by
          have := hrec (N + m)
          simpa [hz] using this
        calc
          u (N + (m + 1)) = u ((N + m) + 1) := by
            simp [Nat.add_assoc]
          _ = 2 * u (N + m) := hstep
          _ = 2 * (2 ^ m * u N) := by rw [ih (Nat.le_of_lt hm_lt)]
          _ = 2 ^ (m + 1) * u N := by rw [pow_succ]; ring
  exact hiter h le_rfl

/-- A positive natural state realizing a scaled tail produces the reusable
lower-tail certificate.  Only positivity at the start of the window is used. -/
theorem binaryTailWindowLowerBound_of_natState
    (f : ℕ → ℕ) (offset v N h : ℕ) (u : ℕ → ℕ)
    (huN : 0 < u N)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * f (offset + n + 1) = 2 * u n)
    (htail : ∀ n : ℕ,
      (u n : ℝ) = (v : ℝ) * binaryCoeffTail f (offset + n))
    (hzero : CoeffZeroWindow f (offset + N) h) :
    BinaryTailWindowLowerBound f (v : ℝ) (offset + N) h := by
  have hstate : u (N + h) = 2 ^ h * u N :=
    state_eq_pow_mul_of_coeffZeroWindow f offset v N h u hrec hzero
  have hpowNat : 2 ^ h ≤ u (N + h) := by
    rw [hstate]
    exact Nat.le_mul_of_pos_right (2 ^ h) huN
  have hpowReal : (2 : ℝ) ^ h ≤ (u (N + h) : ℝ) := by
    exact_mod_cast hpowNat
  unfold BinaryTailWindowLowerBound
  calc
    (2 : ℝ) ^ h ≤ (u (N + h) : ℝ) := hpowReal
    _ = (v : ℝ) * binaryCoeffTail f (offset + (N + h)) := htail (N + h)
    _ = (v : ℝ) * binaryCoeffTail f (offset + N + h) := by
      simp [Nat.add_assoc]

/-! ## Generic subpower tail envelope -/

/-- The weighted geometric majorant used by every subpower tail envelope is
summable. -/
theorem summable_succ_div_two_pow :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
  have h :=
    (summable_const_add_mul_geometric 1
      (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)).mul_left (1 / 2 : ℝ)
  refine h.congr fun j => ?_
  push_cast
  rw [pow_succ, div_pow, one_pow]
  ring

/-- Exact value of the weighted geometric majorant. -/
theorem tsum_succ_div_two_pow :
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) = 2 := by
  have hgeom : Summable (fun j : ℕ => ((1 : ℝ) / 2) ^ j) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hlin : Summable (fun j : ℕ => (j : ℝ) * ((1 : ℝ) / 2) ^ j) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one 1
        (by norm_num : ‖(1 : ℝ) / 2‖ < 1))
  calc
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1))
        = (1 / 2 : ℝ) *
            ((∑' j : ℕ, (j : ℝ) * ((1 : ℝ) / 2) ^ j) +
              ∑' j : ℕ, ((1 : ℝ) / 2) ^ j) := by
          rw [← hlin.tsum_add hgeom, ← tsum_mul_left]
          apply tsum_congr
          intro j
          push_cast
          rw [pow_succ, div_pow, one_pow]
          ring
    _ = 2 := by
      rw [tsum_coe_mul_geometric_of_norm_lt_one
          (by norm_num : ‖(1 : ℝ) / 2‖ < 1),
        tsum_geometric_of_norm_lt_one
          (by norm_num : ‖(1 : ℝ) / 2‖ < 1)]
      norm_num

/-- A coefficient bound `f(n) ≤ C n^δ`, with `0 ≤ δ ≤ 1`, gives the
explicit binary-tail bound `2 C (M+1)^δ`. -/
theorem binaryCoeffTail_le_two_mul_rpow
    (f : ℕ → ℕ) (C δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hf : ∀ n : ℕ, (f n : ℝ) ≤ C * (n : ℝ) ^ δ)
    (M : ℕ) :
    binaryCoeffTail f M ≤
      2 * C * (((M + 1 : ℕ) : ℝ) ^ δ) := by
  have hC : 0 ≤ C := by
    have h := hf 1
    have h0 : (0 : ℝ) ≤ (f 1 : ℝ) := Nat.cast_nonneg _
    have := h0.trans h
    simpa using this
  let K : ℝ := C * (((M + 1 : ℕ) : ℝ) ^ δ)
  have hK : 0 ≤ K := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  have hmaj : Summable
      (fun j : ℕ => K * (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1))) :=
    summable_succ_div_two_pow.mul_left K
  have hterm : ∀ j : ℕ,
      (f (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) ≤
        K * (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) := by
    intro j
    have hindexNat : M + j + 1 ≤ (M + 1) * (j + 1) := by
      nlinarith
    have hindex : ((M + j + 1 : ℕ) : ℝ) ≤
        ((M + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast hindexNat
    have hbase : ((M + j + 1 : ℕ) : ℝ) ^ δ ≤
        ((((M + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ δ) :=
      Real.rpow_le_rpow (by positivity) hindex hδ0
    have hjpow : (((j + 1 : ℕ) : ℝ) ^ δ) ≤ ((j + 1 : ℕ) : ℝ) :=
      Real.rpow_le_self_of_one_le (by norm_num) hδ1
    have hcoeff : (f (M + j + 1) : ℝ) ≤
        K * ((j + 1 : ℕ) : ℝ) := by
      calc
        (f (M + j + 1) : ℝ)
            ≤ C * (((M + j + 1 : ℕ) : ℝ) ^ δ) := hf _
        _ ≤ C *
            ((((M + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) ^ δ) := by
              gcongr
        _ = K * (((j + 1 : ℕ) : ℝ) ^ δ) := by
              dsimp [K]
              rw [Real.mul_rpow (by positivity) (by positivity)]
              ring
        _ ≤ K * ((j + 1 : ℕ) : ℝ) := by gcongr
    calc
      (f (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
          ≤ (K * ((j + 1 : ℕ) : ℝ)) / (2 : ℝ) ^ (j + 1) := by
            gcongr
      _ = K * (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) := by ring
  have hsource : Summable
      (fun j : ℕ => (f (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hterm hmaj
  unfold binaryCoeffTail
  calc
    (∑' j : ℕ, (f (M + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1))
        ≤ ∑' j : ℕ, K *
            (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 1)) :=
          Summable.tsum_le_tsum hterm hsource hmaj
    _ = K * 2 := by rw [tsum_mul_left, tsum_succ_div_two_pow]
    _ = 2 * C * (((M + 1 : ℕ) : ℝ) ^ δ) := by
      dsimp [K]
      ring

/-- Predicate-shaped constructor for the standard subpower envelope. -/
theorem binaryCoeffTailEnvelope_two_mul_rpow
    (f : ℕ → ℕ) (C δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hf : ∀ n : ℕ, (f n : ℝ) ≤ C * (n : ℝ) ^ δ) :
    BinaryCoeffTailEnvelope f
      (fun M : ℕ => 2 * C * (((M + 1 : ℕ) : ℝ) ^ δ)) := by
  intro M
  exact binaryCoeffTail_le_two_mul_rpow f C δ hδ0 hδ1 hf M

/-- Compose a lower-tail certificate with an independent upper envelope. -/
theorem binaryTailWindowLowerBound_le_mul_envelope
    {f : ℕ → ℕ} {scale : ℝ} {start h : ℕ}
    {envelope : ℕ → ℝ}
    (hlower : BinaryTailWindowLowerBound f scale start h)
    (hscale : 0 ≤ scale)
    (henvelope : BinaryCoeffTailEnvelope f envelope) :
    (2 : ℝ) ^ h ≤ scale * envelope (start + h) := by
  exact hlower.trans
    (mul_le_mul_of_nonneg_left (henvelope (start + h)) hscale)

/-! ## Self-reference absorption and logarithmic inversion -/

/-- The elementary exponential bound used in the absorption step. -/
theorem nat_add_one_le_two_pow (a : ℕ) :
    a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      calc
        a + 2 ≤ 2 * (a + 1) := by omega
        _ ≤ 2 * 2 ^ a := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (a + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Raising the self-referential inequality to the `k`-th power and using
`Y+h ≤ Y*2^h` consumes exactly one of the `k` binary factors. -/
theorem pow_sub_one_mul_le_of_pow_le_mul_add_invNat_rpow
    (k Y h : ℕ) (hk : 2 ≤ k) (hY : 1 ≤ Y)
    (L : ℝ) (hL : 1 ≤ L)
    (hpow :
      (2 : ℝ) ^ h ≤
        L * (((Y + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) :
    (2 : ℝ) ^ ((k - 1) * h) ≤ L ^ k * (Y : ℝ) := by
  have hk0 : k ≠ 0 := by omega
  have hraised :
      (2 : ℝ) ^ (h * k) ≤ L ^ k * ((Y + h : ℕ) : ℝ) := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ h) hpow k
    calc
      (2 : ℝ) ^ (h * k) = ((2 : ℝ) ^ h) ^ k := by rw [pow_mul]
      _ ≤ (L * (((Y + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) ^ k := hp
      _ = L ^ k * ((Y + h : ℕ) : ℝ) := by
        rw [mul_pow, Real.rpow_inv_natCast_pow (by positivity) hk0]
  have hYh : Y + h ≤ Y * (h + 1) := by
    have hh : h ≤ Y * h := by
      have ht := Nat.mul_le_mul_right h hY
      simpa [Nat.mul_comm] using ht
    calc
      Y + h ≤ Y + Y * h := Nat.add_le_add_left hh Y
      _ = Y * (h + 1) := by simp [Nat.mul_add, Nat.add_comm]
  have hhpow : h + 1 ≤ 2 ^ h := nat_add_one_le_two_pow h
  have hX : Y + h ≤ Y * 2 ^ h :=
    hYh.trans (Nat.mul_le_mul_left Y hhpow)
  have hXreal : ((Y + h : ℕ) : ℝ) ≤ (Y : ℝ) * (2 : ℝ) ^ h := by
    exact_mod_cast hX
  have hwith :
      (2 : ℝ) ^ (h * k) ≤
        L ^ k * (Y : ℝ) * (2 : ℝ) ^ h := by
    calc
      (2 : ℝ) ^ (h * k) ≤ L ^ k * ((Y + h : ℕ) : ℝ) := hraised
      _ ≤ L ^ k * ((Y : ℝ) * (2 : ℝ) ^ h) := by
        gcongr
      _ = L ^ k * (Y : ℝ) * (2 : ℝ) ^ h := by ring
  have hexp : h * k = (k - 1) * h + h := by
    have hsplit : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    calc
      h * k = h * ((k - 1) + 1) := by rw [hsplit]
      _ = (k - 1) * h + h := by ring
  have hmul :
      (2 : ℝ) ^ ((k - 1) * h) * (2 : ℝ) ^ h ≤
        (L ^ k * (Y : ℝ)) * (2 : ℝ) ^ h := by
    simpa [hexp, pow_add, mul_assoc] using hwith
  exact le_of_mul_le_mul_right hmul (by positivity)

/-- Logarithmic form of the absorption theorem. -/
theorem length_le_logb_of_pow_le_mul_add_invNat_rpow
    (k Y h : ℕ) (hk : 2 ≤ k) (hY : 1 ≤ Y)
    (L : ℝ) (hL : 1 ≤ L)
    (hpow :
      (2 : ℝ) ^ h ≤
        L * (((Y + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) :
    (h : ℝ) ≤
      (Real.logb 2 (Y : ℝ) + Real.logb 2 (L ^ k)) /
        ((k - 1 : ℕ) : ℝ) := by
  have hcancel :
      (2 : ℝ) ^ ((k - 1) * h) ≤ L ^ k * (Y : ℝ) :=
    pow_sub_one_mul_le_of_pow_le_mul_add_invNat_rpow
      k Y h hk hY L hL hpow
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hprodpos : 0 < L ^ k * (Y : ℝ) :=
    mul_pos (pow_pos hLpos k) hYpos
  have hlog :
      (((k - 1) * h : ℕ) : ℝ) ≤
        Real.logb 2 (L ^ k * (Y : ℝ)) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hprodpos]
    rw [Real.rpow_natCast]
    exact hcancel
  rw [Real.logb_mul (pow_ne_zero k hLpos.ne') hYpos.ne'] at hlog
  have hkden : 0 < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  rw [le_div_iff₀ hkden]
  norm_num [Nat.cast_mul] at hlog ⊢
  linarith

/-- Fixed-`k` analytic elimination from the certificate-first boundary. -/
theorem length_le_logb_of_binaryTailWindowLowerBound
    (f : ℕ → ℕ) (scale C : ℝ)
    (start h k : ℕ)
    (hlower : BinaryTailWindowLowerBound f scale start h)
    (hscale : 0 ≤ scale)
    (henvelope :
      BinaryCoeffTailEnvelope f
        (fun M : ℕ => C * (((M + 1 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))))
    (hk : 2 ≤ k)
    (hLC : 1 ≤ scale * C) :
    (h : ℝ) ≤
      (Real.logb 2 (((start + 1 : ℕ) : ℝ)) +
        Real.logb 2 ((scale * C) ^ k)) /
      ((k - 1 : ℕ) : ℝ) := by
  have hraw :=
    binaryTailWindowLowerBound_le_mul_envelope hlower hscale henvelope
  have hpow :
      (2 : ℝ) ^ h ≤
        (scale * C) *
          ((((start + 1) + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) := by
    calc
      (2 : ℝ) ^ h ≤
          scale *
            (C * (((start + h + 1 : ℕ) : ℝ) ^ ((k : ℝ)⁻¹))) := hraw
      _ = (scale * C) *
          ((((start + 1) + h : ℕ) : ℝ) ^ ((k : ℝ)⁻¹)) := by
        rw [show start + h + 1 = start + 1 + h by omega]
        ring
  simpa using
    length_le_logb_of_pow_le_mul_add_invNat_rpow
      k (start + 1) h hk (by omega) (scale * C) hLC hpow

/-- Archimedean selector in exactly the exponent produced by absorption. -/
theorem exists_nat_two_le_inv_sub_one_le {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 2 ≤ k ∧ (((k - 1 : ℕ) : ℝ))⁻¹ ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hε
  refine ⟨n + 2, by omega, ?_⟩
  simpa [one_div] using hn.le

/-- Separate a fixed affine shift from the growing index inside `log₂`. -/
theorem logb_nat_affine_le_add (c N : ℕ) :
    Real.logb 2 (c + N + 1 : ℝ) ≤
      Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ) := by
  have hle : (c + N + 1 : ℝ) ≤ (c + 1 : ℝ) * (N + 1 : ℝ) := by
    nlinarith [Nat.zero_le c, Nat.zero_le N]
  calc
    Real.logb 2 (c + N + 1 : ℝ) ≤
        Real.logb 2 ((c + 1 : ℝ) * (N + 1 : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hle
    _ = Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ) := by
      rw [Real.logb_mul (by positivity) (by positivity)]

/-- Convert a parameterized `1/(k-1)` affine-log estimate to an
`ε * log₂(N+1)` estimate while keeping the remaining term explicit. -/
theorem le_epsilon_mul_logb_add_constant_div_of_affine_log_bound
    {ε D x : ℝ} {c N k : ℕ}
    (hbound : x ≤
      (Real.logb 2 (c + N + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ))
    (hinv : (((k - 1 : ℕ) : ℝ))⁻¹ ≤ ε) :
    x ≤ ε * Real.logb 2 (N + 1 : ℝ) +
      (Real.logb 2 (c + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ) := by
  have hnum :
      Real.logb 2 (c + N + 1 : ℝ) + D ≤
        (Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ)) + D :=
    add_le_add (logb_nat_affine_le_add c N) le_rfl
  have hdiv :
      (Real.logb 2 (c + N + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ) ≤
        ((Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ)) + D) /
          ((k - 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have hlog : 0 ≤ Real.logb 2 (N + 1 : ℝ) :=
    Real.logb_nonneg (by norm_num) (by norm_num)
  have hscale :
      Real.logb 2 (N + 1 : ℝ) / ((k - 1 : ℕ) : ℝ) ≤
        ε * Real.logb 2 (N + 1 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hinv hlog
  calc
    x ≤ (Real.logb 2 (c + N + 1 : ℝ) + D) /
        ((k - 1 : ℕ) : ℝ) := hbound
    _ ≤ ((Real.logb 2 (c + 1 : ℝ) + Real.logb 2 (N + 1 : ℝ)) + D) /
        ((k - 1 : ℕ) : ℝ) := hdiv
    _ = Real.logb 2 (N + 1 : ℝ) / ((k - 1 : ℕ) : ℝ) +
        (Real.logb 2 (c + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ) := by ring
    _ ≤ ε * Real.logb 2 (N + 1 : ℝ) +
        (Real.logb 2 (c + 1 : ℝ) + D) / ((k - 1 : ℕ) : ℝ) :=
      add_le_add hscale le_rfl

/-- For positive `N`, replace `log₂(N+1)` by `1 + log₂ N`. -/
theorem logb_nat_succ_le_one_add (N : ℕ) (hN : 1 ≤ N) :
    Real.logb 2 (N + 1 : ℝ) ≤ 1 + Real.logb 2 (N : ℝ) := by
  have hle : (N + 1 : ℝ) ≤ (2 : ℝ) * (N : ℝ) := by
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  calc
    Real.logb 2 (N + 1 : ℝ) ≤ Real.logb 2 ((2 : ℝ) * (N : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hle
    _ = Real.logb 2 (2 : ℝ) + Real.logb 2 (N : ℝ) := by
      rw [Real.logb_mul (by norm_num) (by positivity)]
    _ = 1 + Real.logb 2 (N : ℝ) := by
      rw [Real.logb_self_eq_one (by norm_num)]

#print axioms state_eq_pow_mul_of_coeffZeroWindow
#print axioms binaryTailWindowLowerBound_of_natState
#print axioms binaryCoeffTailEnvelope_two_mul_rpow
#print axioms length_le_logb_of_binaryTailWindowLowerBound

end Erdos249257
