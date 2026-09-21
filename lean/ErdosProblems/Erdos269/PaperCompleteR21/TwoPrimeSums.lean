import ErdosProblems.Erdos269.PaperR7AnalyticInterfaces
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

/-!
# Erdős #269: both two-prime running-LCM sums

This file transcribes the two-prime objects of the short paper's
`res:two-prime-transcendence` and of the long paper's `long269:res:lead-two-prime`
and proves everything those statements assert except one external value theorem.

* `runningLcm p q x` is the literal least common multiple of the `{p,q}`-smooth
  numbers not exceeding `x`; `runningLcm_eq_twoPrimeHeight` identifies it with the
  product of the two maximal pure prime powers.
* `repeatedSum p q` is `R_{p,q}`: the reciprocal running LCM summed at every
  positive `{p,q}`-smooth integer.  `distinctSum p q` is `D_{p,q}`: each distinct
  running LCM counted once.
* `two_prime_affine_and_quadratic` proves the paper's displayed identities
  `eq:two-prime-affine`, with `A` the paper's boundary value
  `ErdosProblems.Erdos269.PaperR7.twoPrimeHeckeValue`.
* `two_prime_sums_transcendental` and `two_prime_transcendence` conclude that both
  values are transcendental.

The only undischarged input is `BugeaudLaurentTranscendence`, the theorem of
Bugeaud and Laurent (Theorem 1.1) in the case `ρ = 0` due to Loxton and van der
Poorten (Theorem 8, p. 40), that the Hecke--Mahler series takes transcendental
values.  It is carried as one explicit named hypothesis, stated in the generality
in which the paper cites it; all of its side conditions for the pair `(1/p, 1/q)`,
including irrationality of the slope `θ = log p / log q`, are proved here.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR21

open Polynomial
open scoped BigOperators

noncomputable section

/-! ## The `{p,q}`-smooth numbers and their running least common multiple -/

/-- The positive `{p,q}`-smooth integers. -/
def SmoothSet (p q : ℕ) : Set ℕ := {n : ℕ | 0 < n ∧ ∃ i j : ℕ, n = p ^ i * q ^ j}

/-- The product of the two maximal pure prime powers not exceeding `x`. -/
def twoPrimeHeight (p q x : ℕ) : ℕ := p ^ Nat.log p x * q ^ Nat.log q x

/-- The exponent pairs of the actual `{p,q}`-smooth prefix up to `x`. -/
def smoothPrefixPairs (p q x : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (Nat.log p x + 1)) ×ˢ (Finset.range (Nat.log q x + 1))).filter
    fun e => p ^ e.1 * q ^ e.2 ≤ x)

/-- The literal running least common multiple of the `{p,q}`-smooth numbers `≤ x`. -/
def runningLcm (p q x : ℕ) : ℕ :=
  (smoothPrefixPairs p q x).lcm fun e => p ^ e.1 * q ^ e.2

private theorem pow_le_of_smooth_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {i j x : ℕ}
    (h : p ^ i * q ^ j ≤ x) : p ^ i ≤ x ∧ q ^ j ≤ x := by
  have h1 : (1 : ℕ) ≤ p ^ i := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne')
  have h2 : (1 : ℕ) ≤ q ^ j := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hq.ne')
  constructor
  · calc p ^ i = p ^ i * 1 := (mul_one _).symm
      _ ≤ p ^ i * q ^ j := Nat.mul_le_mul le_rfl h2
      _ ≤ x := h
  · calc q ^ j = 1 * q ^ j := (one_mul _).symm
      _ ≤ p ^ i * q ^ j := Nat.mul_le_mul h1 le_rfl
      _ ≤ x := h

theorem mem_smoothPrefixPairs {p q x : ℕ} (hp : 1 < p) (hq : 1 < q) {e : ℕ × ℕ} :
    e ∈ smoothPrefixPairs p q x ↔ p ^ e.1 * q ^ e.2 ≤ x := by
  constructor
  · intro he
    exact (Finset.mem_filter.mp he).2
  · intro hle
    obtain ⟨h1, h2⟩ := pow_le_of_smooth_le (by omega : 0 < p) (by omega : 0 < q) hle
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hle⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp h1))
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_log_of_pow_le hq h2))

/-- The paper's running-LCM identity in the two-prime case: the running least
common multiple of the smooth prefix is the product of the two maximal pure
prime powers. -/
theorem runningLcm_eq_twoPrimeHeight {p q x : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hx : x ≠ 0) :
    runningLcm p q x = twoPrimeHeight p q x := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  refine Nat.dvd_antisymm ?_ ?_
  · apply Finset.lcm_dvd
    intro e he
    have hle := (mem_smoothPrefixPairs hp1 hq1).mp he
    obtain ⟨h1, h2⟩ := pow_le_of_smooth_le (by omega : 0 < p) (by omega : 0 < q) hle
    exact mul_dvd_mul (pow_dvd_pow p (Nat.le_log_of_pow_le hp1 h1))
      (pow_dvd_pow q (Nat.le_log_of_pow_le hq1 h2))
  · have hpmem : (Nat.log p x, 0) ∈ smoothPrefixPairs p q x := by
      rw [mem_smoothPrefixPairs hp1 hq1]
      simpa using Nat.pow_log_le_self p hx
    have hqmem : (0, Nat.log q x) ∈ smoothPrefixPairs p q x := by
      rw [mem_smoothPrefixPairs hp1 hq1]
      simpa using Nat.pow_log_le_self q hx
    have hpd : p ^ Nat.log p x ∣ runningLcm p q x := by
      simpa [runningLcm] using
        Finset.dvd_lcm (f := fun e : ℕ × ℕ => p ^ e.1 * q ^ e.2) hpmem
    have hqd : q ^ Nat.log q x ∣ runningLcm p q x := by
      simpa [runningLcm] using
        Finset.dvd_lcm (f := fun e : ℕ × ℕ => p ^ e.1 * q ^ e.2) hqmem
    exact (Nat.coprime_pow_primes _ _ hp hq hpq).mul_dvd_of_dvd_of_dvd hpd hqd

/-! ## Integer logarithms at smooth points -/

theorem log_mul_pow {b : ℕ} (hb : 1 < b) {m : ℕ} (hm : m ≠ 0) (i : ℕ) :
    Nat.log b (m * b ^ i) = Nat.log b m + i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hmi : m * b ^ i ≠ 0 := Nat.mul_ne_zero hm (pow_ne_zero _ (by omega))
    calc Nat.log b (m * b ^ (i + 1)) = Nat.log b (m * b ^ i * b) := by
          congr 1
          ring
      _ = Nat.log b (m * b ^ i) + 1 := Nat.log_mul_base hb hmi
      _ = Nat.log b m + i + 1 := by rw [ih]
      _ = Nat.log b m + (i + 1) := by omega

theorem log_left_smooth {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (i j : ℕ) :
    Nat.log p (p ^ i * q ^ j) = i + Nat.log p (q ^ j) := by
  have h : p ^ i * q ^ j = q ^ j * p ^ i := by ring
  rw [h, log_mul_pow hp (pow_ne_zero _ (by omega : q ≠ 0)) i]
  omega

theorem log_right_smooth {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (i j : ℕ) :
    Nat.log q (p ^ i * q ^ j) = Nat.log q (p ^ i) + j :=
  log_mul_pow hq (pow_ne_zero _ (by omega : p ≠ 0)) j

/-- `m_n = ⌊n θ⌋`: the exponent of the largest power of `q` not exceeding `p ^ n`. -/
def qExp (p q n : ℕ) : ℕ := Nat.log q (p ^ n)

/-- `⌊j / θ⌋`: the exponent of the largest power of `p` not exceeding `q ^ j`. -/
def pExp (p q j : ℕ) : ℕ := Nat.log p (q ^ j)

@[simp] theorem qExp_zero (p q : ℕ) : qExp p q 0 = 0 := by simp [qExp]

@[simp] theorem pExp_zero (p q : ℕ) : pExp p q 0 = 0 := by simp [pExp]

theorem qExp_mono {p q : ℕ} (hp : 0 < p) {m n : ℕ} (h : m ≤ n) :
    qExp p q m ≤ qExp p q n :=
  Nat.log_mono_right (Nat.pow_le_pow_right hp h)

theorem pExp_mono {q : ℕ} (hq : 0 < q) {p m n : ℕ} (h : m ≤ n) :
    pExp p q m ≤ pExp p q n :=
  Nat.log_mono_right (Nat.pow_le_pow_right hq h)

/-- The outer-product form of the two-prime kernel: the reciprocal running value
at `p ^ i q ^ j` splits into a factor depending on `i` and one depending on `j`. -/
theorem twoPrimeHeight_smooth {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (i j : ℕ) :
    twoPrimeHeight p q (p ^ i * q ^ j)
      = (p ^ i * q ^ qExp p q i) * (p ^ pExp p q j * q ^ j) := by
  simp only [twoPrimeHeight, qExp, pExp, log_left_smooth hp hq, log_right_smooth hp hq,
    pow_add]
  ring

theorem twoPrimeHeight_pow_left {p q : ℕ} (hp : 1 < p) (a : ℕ) :
    twoPrimeHeight p q (p ^ a) = p ^ a * q ^ qExp p q a := by
  simp [twoPrimeHeight, qExp, Nat.log_pow hp]

theorem twoPrimeHeight_pow_right {p q : ℕ} (hq : 1 < q) (b : ℕ) :
    twoPrimeHeight p q (q ^ b) = p ^ pExp p q b * q ^ b := by
  simp [twoPrimeHeight, pExp, Nat.log_pow hq]

/-! ## The exact combinatorics of the jump indices -/

private theorem mul_lt_mul_nat {a b c d : ℕ} (h1 : a < c) (h2 : b < d) : a * b < c * d := by
  nlinarith

private theorem mul_lt_mul_nat' {a b c d : ℕ} (h1 : a < c) (h2 : b ≤ d) (hb : 0 < b) :
    a * b < c * d := by
  nlinarith

theorem pow_ne_pow_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) : p ^ a ≠ q ^ b := fun h =>
  hpq (Nat.Prime.pow_inj' hp hq ha hb h).1

/-- Both halves of the paper's statement that exactly one power of `q` lies
strictly between `p ^ n` and `p ^ (n+1)` when `n = ⌊j/θ⌋`: with `j = b + 1`,
`m_n = b` and `δ_n = 1`. -/
theorem qExp_pExp_succ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (b : ℕ) :
    qExp p q (pExp p q (b + 1)) = b ∧ qExp p q (pExp p q (b + 1) + 1) = b + 1 := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hne : p ≠ q := Nat.ne_of_lt hpq
  simp only [qExp, pExp]
  set n := Nat.log p (q ^ (b + 1)) with hn
  have hqpow : q ^ (b + 1) ≠ 0 := pow_ne_zero _ (by omega)
  have hle : p ^ n ≤ q ^ (b + 1) := by
    rw [hn]
    exact Nat.pow_log_le_self p hqpow
  have hlt : q ^ (b + 1) < p ^ (n + 1) := by
    rw [hn]
    exact Nat.lt_pow_succ_log_self hp1 _
  have hppos : 0 < p ^ n := pow_pos (by omega) _
  have hstrict : p ^ n < q ^ (b + 1) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero]
      calc (1 : ℕ) < q := hq1
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ (b + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    · exact lt_of_le_of_ne hle (pow_ne_pow_of_ne hp hq hne (by omega) (by omega))
  have hlow : q ^ b ≤ p ^ n := by
    by_contra hcon
    push_neg at hcon
    have hkey : p ^ (n + 1) < q ^ (b + 1) := by
      calc p ^ (n + 1) = p * p ^ n := by ring
        _ < q * q ^ b := mul_lt_mul_nat hpq hcon
        _ = q ^ (b + 1) := by ring
    omega
  refine ⟨Nat.log_eq_of_pow_le_of_lt_pow hlow hstrict, ?_⟩
  refine Nat.log_eq_of_pow_le_of_lt_pow (le_of_lt hlt) ?_
  calc p ^ (n + 1) = p * p ^ n := by ring
    _ < q * q ^ (b + 1) := mul_lt_mul_nat' hpq (le_of_lt hstrict) hppos
    _ = q ^ (b + 1 + 1) := by ring

/-- The converse selection: whenever the `q`-exponent jumps between `p ^ n` and
`p ^ (n+1)`, the power `q ^ (m_n + 1)` is the one lying in that gap. -/
theorem pExp_qExp_succ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) {n : ℕ}
    (hjump : qExp p q (n + 1) ≠ qExp p q n) :
    pExp p q (qExp p q n + 1) = n := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hne : p ≠ q := Nat.ne_of_lt hpq
  simp only [qExp, pExp] at hjump ⊢
  set b := Nat.log q (p ^ n) with hb
  have hppow : p ^ n ≠ 0 := pow_ne_zero _ (by omega)
  have hppow' : p ^ (n + 1) ≠ 0 := pow_ne_zero _ (by omega)
  have hple : q ^ b ≤ p ^ n := by
    rw [hb]
    exact Nat.pow_log_le_self q hppow
  have hplt : p ^ n < q ^ (b + 1) := by
    rw [hb]
    exact Nat.lt_pow_succ_log_self hq1 _
  have hmono : b ≤ Nat.log q (p ^ (n + 1)) := by
    rw [hb]
    exact Nat.log_mono_right (Nat.pow_le_pow_right (by omega) (by omega))
  have hge : b + 1 ≤ Nat.log q (p ^ (n + 1)) := by omega
  have hqle : q ^ (b + 1) ≤ p ^ (n + 1) :=
    le_trans (Nat.pow_le_pow_right (by omega) hge) (Nat.pow_log_le_self q hppow')
  have hqlt : q ^ (b + 1) < p ^ (n + 1) :=
    lt_of_le_of_ne hqle (pow_ne_pow_of_ne hq hp (Ne.symm hne) (by omega) (by omega))
  exact Nat.log_eq_of_pow_le_of_lt_pow (le_of_lt hplt) hqlt

/-! ## Unique factorisation of the smooth monoid -/

theorem smoothVal_injective {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (fun e : ℕ × ℕ => p ^ e.1 * q ^ e.2) := by
  have hexp : ∀ i i' j j' : ℕ, p ^ i * q ^ j = p ^ i' * q ^ j' → i ≤ i' → i = i' := by
    intro i i' j j' h hle
    by_contra hne
    have hlt : i < i' := lt_of_le_of_ne hle hne
    have hdvd : p ^ i * p ∣ p ^ i * q ^ j := by
      rw [h]
      calc p ^ i * p = p ^ (i + 1) := by ring
        _ ∣ p ^ i' := pow_dvd_pow p hlt
        _ ∣ p ^ i' * q ^ j' := Dvd.intro _ rfl
    have hpi : (0 : ℕ) < p ^ i := pow_pos hp.pos i
    have hpdvd : p ∣ q ^ j := (mul_dvd_mul_iff_left (a := p ^ i) (by omega)).mp hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpdvd))
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only at h
  have hii : i = i' := by
    rcases le_total i i' with hle | hle
    · exact hexp i i' j j' h hle
    · exact (hexp i' i j' j h.symm hle).symm
  subst hii
  have hqq : q ^ j = q ^ j' := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos i) h
  have hjj := Nat.pow_right_injective hq.two_le hqq
  simp [hjj]

theorem smoothSet_eq_range {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    SmoothSet p q = Set.range (fun e : ℕ × ℕ => p ^ e.1 * q ^ e.2) := by
  ext n
  constructor
  · rintro ⟨-, i, j, rfl⟩
    exact ⟨(i, j), rfl⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨Nat.mul_pos (pow_pos hp i) (pow_pos hq j), i, j, rfl⟩

theorem smoothSet_comm (p q : ℕ) : SmoothSet p q = SmoothSet q p := by
  ext n
  constructor
  · rintro ⟨hn, i, j, rfl⟩
    exact ⟨hn, j, i, by ring⟩
  · rintro ⟨hn, i, j, rfl⟩
    exact ⟨hn, j, i, by ring⟩

/-! ## The two sums of the paper -/

/-- `R_{p,q}`: the reciprocal running LCM summed at every positive
`{p,q}`-smooth integer. -/
def repeatedSum (p q : ℕ) : ℝ :=
  ∑' n : SmoothSet p q, ((runningLcm p q (n : ℕ) : ℝ))⁻¹

/-- The distinct values taken by the running LCM on the positive smooth integers. -/
def runningLcmValues (p q : ℕ) : Set ℕ := (runningLcm p q) '' SmoothSet p q

/-- `D_{p,q}`: each distinct running LCM counted once. -/
def distinctSum (p q : ℕ) : ℝ :=
  ∑' H : runningLcmValues p q, (((H : ℕ) : ℝ))⁻¹

/-! ## The two component series -/

/-- The reciprocal running value at the pure power `p ^ n`, that is `x^n y^{m_n}`. -/
def aTerm (p q n : ℕ) : ℝ := ((p : ℝ)⁻¹) ^ n * ((q : ℝ)⁻¹) ^ qExp p q n

/-- The reciprocal running value at the pure power `q ^ j`, that is
`x^{⌊j/θ⌋} y^j`. -/
def cTerm (p q j : ℕ) : ℝ := ((p : ℝ)⁻¹) ^ pExp p q j * ((q : ℝ)⁻¹) ^ j

theorem aTerm_nonneg (p q n : ℕ) : 0 ≤ aTerm p q n := by
  unfold aTerm
  positivity

theorem cTerm_nonneg (p q j : ℕ) : 0 ≤ cTerm p q j := by
  unfold cTerm
  positivity

@[simp] theorem aTerm_zero (p q : ℕ) : aTerm p q 0 = 1 := by simp [aTerm]

@[simp] theorem cTerm_zero (p q : ℕ) : cTerm p q 0 = 1 := by simp [cTerm]

theorem aTerm_eq_inv {p q : ℕ} (n : ℕ) :
    aTerm p q n = (((p : ℝ) ^ n * (q : ℝ) ^ qExp p q n))⁻¹ := by
  rw [aTerm, mul_inv, inv_pow, inv_pow]

theorem cTerm_eq_inv {p q : ℕ} (j : ℕ) :
    cTerm p q j = (((p : ℝ) ^ pExp p q j * (q : ℝ) ^ j))⁻¹ := by
  rw [cTerm, mul_inv, inv_pow, inv_pow]

private theorem inv_lt_one_nat {p : ℕ} (hp : 1 < p) : ((p : ℝ))⁻¹ < 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h : (1 : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact hp1
  simpa [one_div] using h

private theorem inv_nonneg_nat (p : ℕ) : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := by positivity

theorem summable_aTerm {p q : ℕ} (hp : 1 < p) (hq : 1 < q) : Summable (aTerm p q) := by
  refine Summable.of_nonneg_of_le (fun n => aTerm_nonneg p q n) (fun n => ?_)
    (summable_geometric_of_lt_one (inv_nonneg_nat p) (inv_lt_one_nat hp))
  have hle : ((q : ℝ)⁻¹) ^ qExp p q n ≤ 1 :=
    pow_le_one₀ (inv_nonneg_nat q) (le_of_lt (inv_lt_one_nat hq))
  calc aTerm p q n = ((p : ℝ)⁻¹) ^ n * ((q : ℝ)⁻¹) ^ qExp p q n := rfl
    _ ≤ ((p : ℝ)⁻¹) ^ n * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ((p : ℝ)⁻¹) ^ n := mul_one _

theorem summable_cTerm {p q : ℕ} (hp : 1 < p) (hq : 1 < q) : Summable (cTerm p q) := by
  refine Summable.of_nonneg_of_le (fun j => cTerm_nonneg p q j) (fun j => ?_)
    (summable_geometric_of_lt_one (inv_nonneg_nat q) (inv_lt_one_nat hq))
  have hle : ((p : ℝ)⁻¹) ^ pExp p q j ≤ 1 :=
    pow_le_one₀ (inv_nonneg_nat p) (le_of_lt (inv_lt_one_nat hp))
  calc cTerm p q j = ((p : ℝ)⁻¹) ^ pExp p q j * ((q : ℝ)⁻¹) ^ j := rfl
    _ ≤ 1 * ((q : ℝ)⁻¹) ^ j := mul_le_mul_of_nonneg_right hle (by positivity)
    _ = ((q : ℝ)⁻¹) ^ j := one_mul _

theorem summable_cTerm_succ {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    Summable (fun b : ℕ => cTerm p q (b + 1)) :=
  (summable_nat_add_iff 1).mpr (summable_cTerm hp hq)

/-! ## `R = A (1 + B)` -/

theorem repeatedSum_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    repeatedSum p q = (∑' n : ℕ, aTerm p q n) * (∑' j : ℕ, cTerm p q j) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hset := smoothSet_eq_range (p := p) (q := q) (by omega) (by omega)
  have hinj := smoothVal_injective hp hq hpq
  have hstep : repeatedSum p q = ∑' e : ℕ × ℕ, aTerm p q e.1 * cTerm p q e.2 := by
    unfold repeatedSum
    rw [hset, tsum_range (fun n : ℕ => ((runningLcm p q n : ℝ))⁻¹) hinj]
    refine tsum_congr fun e => ?_
    show ((runningLcm p q (p ^ e.1 * q ^ e.2) : ℝ))⁻¹ = aTerm p q e.1 * cTerm p q e.2
    have hne : p ^ e.1 * q ^ e.2 ≠ 0 :=
      (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)).ne'
    rw [runningLcm_eq_twoPrimeHeight hp hq hpq hne, twoPrimeHeight_smooth hp1 hq1,
      aTerm_eq_inv, cTerm_eq_inv]
    push_cast
    rw [← mul_inv]
  rw [hstep]
  exact (Summable.tsum_mul_tsum (summable_aTerm hp1 hq1) (summable_cTerm hp1 hq1)
    (Summable.mul_of_nonneg (summable_aTerm hp1 hq1) (summable_cTerm hp1 hq1)
      (fun n => aTerm_nonneg p q n) (fun j => cTerm_nonneg p q j))).symm

theorem cSum_eq_one_add {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    (∑' j : ℕ, cTerm p q j) = 1 + ∑' b : ℕ, cTerm p q (b + 1) := by
  rw [(summable_cTerm hp hq).tsum_eq_zero_add, cTerm_zero]

/-! ## `D = A + B` -/

/-- The running value at the `a`-th pure power of `p`. -/
def jumpLeft (p q a : ℕ) : ℕ := twoPrimeHeight p q (p ^ a)

/-- The running value at the `(b+1)`-st pure power of `q`. -/
def jumpRight (p q b : ℕ) : ℕ := twoPrimeHeight p q (q ^ (b + 1))

theorem jumpLeft_injective {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    Function.Injective (jumpLeft p q) := by
  have hmono : StrictMono (jumpLeft p q) := by
    apply strictMono_nat_of_lt_succ
    intro a
    simp only [jumpLeft, twoPrimeHeight_pow_left hp]
    have h1 : p ^ a < p ^ (a + 1) := Nat.pow_lt_pow_right hp (by omega)
    have h2 : q ^ qExp p q a ≤ q ^ qExp p q (a + 1) :=
      Nat.pow_le_pow_right (by omega) (qExp_mono (by omega) (by omega))
    have h3 : 0 < q ^ qExp p q a := pow_pos (by omega) _
    exact mul_lt_mul_nat' h1 h2 h3
  exact hmono.injective

theorem jumpRight_injective {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    Function.Injective (jumpRight p q) := by
  have hmono : StrictMono (jumpRight p q) := by
    apply strictMono_nat_of_lt_succ
    intro b
    simp only [jumpRight, twoPrimeHeight_pow_right hq]
    have h1 : q ^ (b + 1) < q ^ (b + 1 + 1) := Nat.pow_lt_pow_right hq (by omega)
    have h2 : p ^ pExp p q (b + 1) ≤ p ^ pExp p q (b + 1 + 1) :=
      Nat.pow_le_pow_right (by omega) (pExp_mono (by omega) (by omega))
    have h3 : 0 < p ^ pExp p q (b + 1) := pow_pos (by omega) _
    calc p ^ pExp p q (b + 1) * q ^ (b + 1)
        = q ^ (b + 1) * p ^ pExp p q (b + 1) := by ring
      _ < q ^ (b + 1 + 1) * p ^ pExp p q (b + 1 + 1) := mul_lt_mul_nat' h1 h2 h3
      _ = p ^ pExp p q (b + 1 + 1) * q ^ (b + 1 + 1) := by ring
  exact hmono.injective

/-- The paper's identification of the distinct running values: they are exactly
the values at `1` and the positive powers of the two primes. -/
theorem runningLcmValues_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    runningLcmValues p q =
      Set.range (jumpLeft p q) ∪ Set.range (jumpRight p q) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  ext H
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hnpos : 0 < n := hn.1
    have hne : n ≠ 0 := by omega
    rw [runningLcm_eq_twoPrimeHeight hp hq hpq hne]
    have hpa : p ^ Nat.log p n ≤ n := Nat.pow_log_le_self p hne
    have hqb : q ^ Nat.log q n ≤ n := Nat.pow_log_le_self q hne
    rcases Nat.lt_or_ge (p ^ Nat.log p n) (q ^ Nat.log q n) with hcase | hcase
    · right
      have hbpos : 0 < Nat.log q n := by
        by_contra hb0
        have hb : Nat.log q n = 0 := by omega
        rw [hb, pow_zero] at hcase
        have h1 : (1 : ℕ) ≤ p ^ Nat.log p n :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
        omega
      refine ⟨Nat.log q n - 1, ?_⟩
      have hbb : Nat.log q n - 1 + 1 = Nat.log q n := by omega
      have hlog : Nat.log p (q ^ Nat.log q n) = Nat.log p n :=
        le_antisymm (Nat.log_mono_right hqb) (Nat.le_log_of_pow_le hp1 (le_of_lt hcase))
      simp only [jumpRight, hbb, twoPrimeHeight, Nat.log_pow hq1, hlog]
    · left
      refine ⟨Nat.log p n, ?_⟩
      have hlog : Nat.log q (p ^ Nat.log p n) = Nat.log q n :=
        le_antisymm (Nat.log_mono_right hpa) (Nat.le_log_of_pow_le hq1 hcase)
      simp only [jumpLeft, twoPrimeHeight, Nat.log_pow hp1, hlog]
  · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨p ^ a, ⟨pow_pos (by omega) a, a, 0, by ring⟩,
        runningLcm_eq_twoPrimeHeight hp hq hpq (pow_ne_zero _ (by omega))⟩
    · exact ⟨q ^ (b + 1), ⟨pow_pos (by omega) _, 0, b + 1, by ring⟩,
        runningLcm_eq_twoPrimeHeight hp hq hpq (pow_ne_zero _ (by omega))⟩

private theorem summable_on_range {g : ℕ → ℕ} (hg : Function.Injective g)
    (h : Summable fun a : ℕ => ((g a : ℝ))⁻¹) :
    Summable ((fun n : ℕ => ((n : ℝ))⁻¹) ∘ ((↑) : Set.range g → ℕ)) := by
  refine ((Equiv.ofInjective g hg).summable_iff
    (f := (fun n : ℕ => ((n : ℝ))⁻¹) ∘ ((↑) : Set.range g → ℕ))).mp ?_
  simpa [Function.comp_def] using h

theorem jumpLeft_inv {p q : ℕ} (hp : 1 < p) (a : ℕ) :
    ((jumpLeft p q a : ℝ))⁻¹ = aTerm p q a := by
  rw [jumpLeft, twoPrimeHeight_pow_left hp, aTerm_eq_inv]
  push_cast
  ring

theorem jumpRight_inv {p q : ℕ} (hq : 1 < q) (b : ℕ) :
    ((jumpRight p q b : ℝ))⁻¹ = cTerm p q (b + 1) := by
  rw [jumpRight, twoPrimeHeight_pow_right hq, cTerm_eq_inv]
  push_cast
  ring

theorem distinctSum_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    distinctSum p q = (∑' n : ℕ, aTerm p q n) + ∑' b : ℕ, cTerm p q (b + 1) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hne : p ≠ q := Nat.ne_of_lt hpq
  have hLinj : Function.Injective (jumpLeft p q) := jumpLeft_injective hp1 hq1
  have hRinj : Function.Injective (jumpRight p q) := jumpRight_injective hp1 hq1
  have hdisj : Disjoint (Set.range (jumpLeft p q)) (Set.range (jumpRight p q)) := by
    rw [Set.disjoint_left]
    rintro H ⟨a, rfl⟩ ⟨b, hb⟩
    rw [jumpLeft, jumpRight, twoPrimeHeight_pow_left hp1,
      twoPrimeHeight_pow_right hq1] at hb
    have hpair := smoothVal_injective hp hq hne (a₁ := (pExp p q (b + 1), b + 1))
      (a₂ := (a, qExp p q a)) (by simpa using hb)
    have h2 : b + 1 = qExp p q a := congrArg Prod.snd hpair
    have h1 : pExp p q (b + 1) = a := congrArg Prod.fst hpair
    have h3 := (qExp_pExp_succ hp hq hpq b).1
    rw [h1] at h3
    omega
  have hsA : Summable ((fun n : ℕ => ((n : ℝ))⁻¹) ∘
      ((↑) : Set.range (jumpLeft p q) → ℕ)) := by
    refine summable_on_range hLinj ?_
    exact (summable_aTerm hp1 hq1).congr fun a => (jumpLeft_inv hp1 a).symm
  have hsB : Summable ((fun n : ℕ => ((n : ℝ))⁻¹) ∘
      ((↑) : Set.range (jumpRight p q) → ℕ)) := by
    refine summable_on_range hRinj ?_
    exact (summable_cTerm_succ hp1 hq1).congr fun b => (jumpRight_inv hq1 b).symm
  unfold distinctSum
  rw [runningLcmValues_eq hp hq hne, Summable.tsum_union_disjoint hdisj hsA hsB,
    tsum_range (fun n : ℕ => ((n : ℝ))⁻¹) hLinj,
    tsum_range (fun n : ℕ => ((n : ℝ))⁻¹) hRinj]
  congr 1
  · exact tsum_congr fun a => jumpLeft_inv hp1 a
  · exact tsum_congr fun b => jumpRight_inv hq1 b

/-! ## The telescoping identity `A - 1 - x A = x (y-1) B / y` -/

/-- The shifted series `x^n y^{m_{n+1}}`. -/
def sTerm (p q n : ℕ) : ℝ := ((p : ℝ)⁻¹) ^ n * ((q : ℝ)⁻¹) ^ qExp p q (n + 1)

/-- The telescoping difference `x^n (y^{m_n} - y^{m_{n+1}})`. -/
def dTerm (p q n : ℕ) : ℝ := aTerm p q n - sTerm p q n

theorem summable_sTerm {p q : ℕ} (hp : 1 < p) (hq : 1 < q) : Summable (sTerm p q) := by
  refine Summable.of_nonneg_of_le (fun n => by unfold sTerm; positivity) (fun n => ?_)
    (summable_geometric_of_lt_one (inv_nonneg_nat p) (inv_lt_one_nat hp))
  have hle : ((q : ℝ)⁻¹) ^ qExp p q (n + 1) ≤ 1 :=
    pow_le_one₀ (inv_nonneg_nat q) (le_of_lt (inv_lt_one_nat hq))
  calc sTerm p q n = ((p : ℝ)⁻¹) ^ n * ((q : ℝ)⁻¹) ^ qExp p q (n + 1) := rfl
    _ ≤ ((p : ℝ)⁻¹) ^ n * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ((p : ℝ)⁻¹) ^ n := mul_one _

theorem sSum_eq {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    (∑' n : ℕ, sTerm p q n) = (p : ℝ) * ((∑' n : ℕ, aTerm p q n) - 1) := by
  have hp0 : ((p : ℝ)) ≠ 0 := by
    have h : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    exact ne_of_gt h
  have hshift : (∑' n : ℕ, aTerm p q (n + 1))
      = ((p : ℝ)⁻¹) * ∑' n : ℕ, sTerm p q n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    unfold aTerm sTerm
    ring
  have hsplit : (∑' n : ℕ, aTerm p q n)
      = 1 + ((p : ℝ)⁻¹) * ∑' n : ℕ, sTerm p q n := by
    rw [(summable_aTerm hp hq).tsum_eq_zero_add, aTerm_zero, hshift]
  rw [hsplit, add_sub_cancel_left, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]

theorem dTerm_support {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Function.support (dTerm p q) ⊆ Set.range (fun b : ℕ => pExp p q (b + 1)) := by
  intro n hn
  simp only [Function.mem_support] at hn
  have hjump : qExp p q (n + 1) ≠ qExp p q n := by
    intro heq
    apply hn
    unfold dTerm aTerm sTerm
    rw [heq]
    ring
  exact ⟨qExp p q n, pExp_qExp_succ hp hq hpq hjump⟩

theorem dSum_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (∑' n : ℕ, dTerm p q n) = ((q : ℝ) - 1) * ∑' b : ℕ, cTerm p q (b + 1) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hq0 : ((q : ℝ)) ≠ 0 := by
    have h : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    exact ne_of_gt h
  have hginj : Function.Injective (fun b : ℕ => pExp p q (b + 1)) := by
    intro a b hab
    have ha := (qExp_pExp_succ hp hq hpq a).1
    have hb := (qExp_pExp_succ hp hq hpq b).1
    simp only at hab
    rw [hab] at ha
    omega
  have hreindex := hginj.tsum_eq (f := dTerm p q) (dTerm_support hp hq hpq)
  rw [← hreindex, ← tsum_mul_left]
  refine tsum_congr fun b => ?_
  have h1 := (qExp_pExp_succ hp hq hpq b).1
  have h2 := (qExp_pExp_succ hp hq hpq b).2
  show dTerm p q (pExp p q (b + 1)) = ((q : ℝ) - 1) * cTerm p q (b + 1)
  unfold dTerm aTerm sTerm cTerm
  rw [h1, h2, pow_succ]
  generalize ((q : ℝ))⁻¹ ^ b = Y
  generalize ((p : ℝ))⁻¹ ^ pExp p q (b + 1) = X
  field_simp

theorem bSum_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (∑' b : ℕ, cTerm p q (b + 1))
      = ((p : ℝ) - ((p : ℝ) - 1) * (∑' n : ℕ, aTerm p q n)) / ((q : ℝ) - 1) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq1' : ((q : ℝ) - 1) ≠ 0 := by linarith
  have hsub : (∑' n : ℕ, dTerm p q n)
      = (∑' n : ℕ, aTerm p q n) - ∑' n : ℕ, sTerm p q n := by
    have h := (summable_aTerm hp1 hq1).tsum_sub (summable_sTerm hp1 hq1)
    simpa [dTerm] using h
  have hd := dSum_eq hp hq hpq
  rw [hsub, sSum_eq hp1 hq1] at hd
  field_simp
  linarith

/-! ## The Hecke--Mahler boundary value -/

/-- The Hecke--Mahler series `F_θ(β,α) = ∑_{n≥1} ∑_{k=1}^{⌊nθ⌋} β^n α^k`.  The
outer index runs over all `n ≥ 0`; the inner sum is empty at `n = 0`. -/
def heckeMahlerSeries (θ β α : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ) * θ⌋₊, β ^ n * α ^ k

/-- Bugeaud and Laurent, Theorem 1.1, in the case `ρ = 0` due to Loxton and van der
Poorten, Theorem 8, p. 40: the Hecke--Mahler series takes transcendental values at
nonzero algebraic arguments inside the stated region.  This is the one external
input of the two-prime theorem. -/
def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)

theorem sum_Icc_pow {y : ℝ} (hy : y ≠ 1) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, y ^ k = (y - y ^ (m + 1)) / (1 - y) := by
  have h1y : (1 : ℝ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
    field_simp
    ring

theorem qExp_eq_floor {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (n : ℕ) :
    qExp p q n = ⌊(n : ℝ) * Real.logb q p⌋₊ := by
  rw [qExp, ← Real.natFloor_logb_natCast q (p ^ n)]
  congr 1
  rw [Nat.cast_pow, Real.logb_pow]

/-- The paper's `A`: the series over the pure powers of `p` is the boundary value
already recorded in the tree. -/
theorem aSum_eq_heckeValue {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    (∑' n : ℕ, aTerm p q n) = PaperR7.twoPrimeHeckeValue p q := by
  refine tsum_congr fun n => ?_
  simp only [aTerm]
  rw [qExp_eq_floor hp hq]

/-- The paper's boundary identity `A = 1/(1-x) - ((1-y)/y) F_θ(x,y)`, in the
normalised form `A = p/(p-1) - (q-1) F`. -/
theorem heckeValue_boundary {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    (∑' n : ℕ, aTerm p q n)
      = (p : ℝ) / ((p : ℝ) - 1)
        - ((q : ℝ) - 1) *
          heckeMahlerSeries (Real.logb q p) ((p : ℝ)⁻¹) ((q : ℝ)⁻¹) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hp0 : ((p : ℝ)) ≠ 0 := by
    intro h
    rw [h] at hpR
    linarith
  have hq0 : ((q : ℝ)) ≠ 0 := by
    intro h
    rw [h] at hqR
    linarith
  have hp1ne : ((p : ℝ) - 1) ≠ 0 := by
    intro h
    have : (p : ℝ) = 1 := by linarith
    linarith [this]
  have hq1ne : ((q : ℝ) - 1) ≠ 0 := by
    intro h
    have : (q : ℝ) = 1 := by linarith
    linarith [this]
  have hxlt : ((p : ℝ))⁻¹ < 1 := inv_lt_one_nat hp
  have hylt : ((q : ℝ))⁻¹ < 1 := inv_lt_one_nat hq
  have hxnn : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := inv_nonneg_nat p
  have hyne : ((q : ℝ))⁻¹ ≠ 1 := ne_of_lt hylt
  have hgeoS : Summable (fun n : ℕ => ((p : ℝ))⁻¹ ^ n) :=
    summable_geometric_of_lt_one hxnn hxlt
  have hgeo : (∑' n : ℕ, ((p : ℝ))⁻¹ ^ n) = (1 - ((p : ℝ))⁻¹)⁻¹ :=
    tsum_geometric_of_lt_one hxnn hxlt
  have hinner : ∀ n : ℕ,
      (∑ k ∈ Finset.Icc 1 ⌊(n : ℝ) * Real.logb q p⌋₊,
        ((p : ℝ))⁻¹ ^ n * ((q : ℝ))⁻¹ ^ k)
        = ((q : ℝ) - 1)⁻¹ * (((p : ℝ))⁻¹ ^ n - aTerm p q n) := by
    intro n
    rw [← Finset.mul_sum, ← qExp_eq_floor hp hq, sum_Icc_pow hyne]
    unfold aTerm
    rw [pow_succ]
    generalize ((q : ℝ))⁻¹ ^ qExp p q n = Y
    generalize ((p : ℝ))⁻¹ ^ n = X
    have h1y : (1 : ℝ) - ((q : ℝ))⁻¹ ≠ 0 := by
      intro h
      have : ((q : ℝ))⁻¹ = 1 := by linarith
      exact hyne this
    field_simp
  have hF : heckeMahlerSeries (Real.logb q p) ((p : ℝ))⁻¹ ((q : ℝ))⁻¹
      = ((q : ℝ) - 1)⁻¹ * ((1 - ((p : ℝ))⁻¹)⁻¹ - ∑' n : ℕ, aTerm p q n) := by
    unfold heckeMahlerSeries
    rw [tsum_congr hinner, tsum_mul_left]
    congr 1
    rw [hgeoS.tsum_sub (summable_aTerm hp hq), hgeo]
  have hxv : (1 - ((p : ℝ))⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
    field_simp
  rw [hF, ← mul_assoc, mul_inv_cancel₀ hq1ne, one_mul, hxv]
  ring

/-! ## Irrationality of the slope -/

theorem irrational_logb_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational (Real.logb q p) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  rintro ⟨r, hr⟩
  have hrv : Real.log (p : ℝ) = (r : ℝ) * Real.log (q : ℝ) := by
    have hrl : (r : ℝ) = Real.log (p : ℝ) / Real.log (q : ℝ) := by
      rw [hr, Real.logb]
    rw [hrl]
    field_simp
  have hrpos : 0 < r := by
    have h : (0 : ℝ) < (r : ℝ) := by nlinarith
    exact_mod_cast h
  have hnumpos : 0 < r.num := Rat.num_pos.mpr hrpos
  have hane : r.num.toNat ≠ 0 := by omega
  have hbne : r.den ≠ 0 := r.den_nz
  have hrq : (r : ℝ) = ((r.num.toNat : ℕ) : ℝ) / ((r.den : ℕ) : ℝ) := by
    rw [show ((r.num.toNat : ℕ) : ℝ) = ((r.num : ℤ) : ℝ) by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnumpos.le)]
    rw [← Rat.cast_def]
  have hbR : (0 : ℝ) < ((r.den : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hbne
  have hlogeq : Real.log ((p : ℝ) ^ r.den) = Real.log ((q : ℝ) ^ r.num.toNat) := by
    rw [Real.log_pow, Real.log_pow, hrv, hrq]
    field_simp
  have hppos : (0 : ℝ) < (p : ℝ) ^ r.den := by positivity
  have hqpos : (0 : ℝ) < (q : ℝ) ^ r.num.toNat := by positivity
  have hpow : ((p : ℝ)) ^ r.den = ((q : ℝ)) ^ r.num.toNat := by
    calc ((p : ℝ)) ^ r.den = Real.exp (Real.log ((p : ℝ) ^ r.den)) := (Real.exp_log hppos).symm
      _ = Real.exp (Real.log ((q : ℝ) ^ r.num.toNat)) := by rw [hlogeq]
      _ = ((q : ℝ)) ^ r.num.toNat := Real.exp_log hqpos
  have hnat : p ^ r.den = q ^ r.num.toNat := by exact_mod_cast hpow
  exact hpq (Nat.Prime.pow_inj' hp hq hbne hane hnat).1

/-! ## Transcendence -/

private theorem isAlgebraic_ratCast (r : ℚ) : IsAlgebraic ℚ ((r : ℝ)) := by
  refine ⟨Polynomial.X - Polynomial.C r, Polynomial.X_sub_C_ne_zero r, ?_⟩
  simp

private theorem transcendental_affine {F : ℝ} (hF : Transcendental ℚ F) (c d : ℚ)
    (hd : d ≠ 0) : Transcendental ℚ ((d : ℝ) * F + (c : ℝ)) := by
  have h := hF.aeval (Polynomial.C d * Polynomial.X + Polynomial.C c)
    (by rw [Polynomial.natDegree_linear hd]; omega)
    (by
      rw [Polynomial.leadingCoeff_linear hd]
      exact mem_nonZeroDivisors_of_ne_zero hd)
  simpa using h

/-- Transcendence of the paper's `A`, granted the cited value theorem. -/
theorem transcendental_heckeValue (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (PaperR7.twoPrimeHeckeValue p q) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hne : p ≠ q := Nat.ne_of_lt hpq
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hpqR : ((p : ℝ)) < (q : ℝ) := by exact_mod_cast hpq
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hirr : Irrational (Real.logb q p) := irrational_logb_of_primes hp hq hne
  have hθpos : 0 < Real.logb q p := by
    rw [Real.logb]
    exact div_pos (Real.log_pos hpR) (Real.log_pos hqR)
  have hθlt : Real.logb q p < 1 := by
    rw [Real.logb, div_lt_one (Real.log_pos hqR)]
    exact Real.log_lt_log hp0 hpqR
  have halgβ : IsAlgebraic ℚ ((p : ℝ))⁻¹ := by
    have h : ((p : ℝ))⁻¹ = (((p : ℚ))⁻¹ : ℚ) := by push_cast; ring
    rw [h]
    exact isAlgebraic_ratCast _
  have halgα : IsAlgebraic ℚ ((q : ℝ))⁻¹ := by
    have h : ((q : ℝ))⁻¹ = (((q : ℚ))⁻¹ : ℚ) := by push_cast; ring
    rw [h]
    exact isAlgebraic_ratCast _
  have hβne : ((p : ℝ))⁻¹ ≠ 0 := by positivity
  have hαne : ((q : ℝ))⁻¹ ≠ 0 := by positivity
  have hβabs : |((p : ℝ))⁻¹| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact inv_lt_one_nat hp1
  have hrpow : |((q : ℝ))⁻¹| ^ (Real.logb q p) = ((p : ℝ))⁻¹ := by
    rw [abs_of_pos (by positivity), Real.inv_rpow (le_of_lt hq0),
      Real.rpow_logb hq0 (by linarith) hp0]
  have hsize : |((p : ℝ))⁻¹| * |((q : ℝ))⁻¹| ^ (Real.logb q p) < 1 := by
    rw [hrpow, abs_of_pos (by positivity)]
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hmul : ((p : ℝ))⁻¹ * ((p : ℝ))⁻¹ = ((p : ℝ) * (p : ℝ))⁻¹ := by
      rw [mul_inv]
    rw [hmul, inv_lt_one_iff₀]
    right
    nlinarith
  have hFtr := hBL (Real.logb q p) ((p : ℝ))⁻¹ ((q : ℝ))⁻¹ hirr hθpos hθlt halgβ halgα
    hβne hαne hβabs hsize
  have hbd := heckeValue_boundary (p := p) (q := q) hp1 hq1
  rw [← aSum_eq_heckeValue hp1 hq1]
  have hkey : (∑' n : ℕ, aTerm p q n)
      = ((-(((q : ℚ)) - 1) : ℚ) : ℝ) *
          heckeMahlerSeries (Real.logb q p) ((p : ℝ))⁻¹ ((q : ℝ))⁻¹
        + ((((p : ℚ)) / (((p : ℚ)) - 1) : ℚ) : ℝ) := by
    rw [hbd]
    push_cast
    ring
  rw [hkey]
  refine transcendental_affine hFtr _ _ ?_
  have hqQ : (1 : ℚ) < (q : ℚ) := by exact_mod_cast hq1
  intro hcon
  have hzero : ((q : ℚ)) - 1 = 0 := by
    have := neg_eq_zero.mp hcon
    linarith
  linarith

/-! ## The paper's theorems -/

/-- The short paper's displayed identities `eq:two-prime-affine`: both two-prime
sums are explicit polynomials over `ℚ` in the single boundary value `A`. -/
theorem two_prime_affine_and_quadratic {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    distinctSum p q
        = (((q : ℝ) - (p : ℝ)) * PaperR7.twoPrimeHeckeValue p q + (p : ℝ))
          / ((q : ℝ) - 1) ∧
      repeatedSum p q
        = (((p : ℝ) + (q : ℝ) - 1) * PaperR7.twoPrimeHeckeValue p q
            - ((p : ℝ) - 1) * (PaperR7.twoPrimeHeckeValue p q) ^ 2)
          / ((q : ℝ) - 1) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hne : p ≠ q := Nat.ne_of_lt hpq
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq1' : ((q : ℝ) - 1) ≠ 0 := by linarith
  have hA := aSum_eq_heckeValue (p := p) (q := q) hp1 hq1
  have hB := bSum_eq hp hq hpq
  have hD := distinctSum_eq hp hq hpq
  have hR := repeatedSum_eq hp hq hne
  rw [cSum_eq_one_add hp1 hq1] at hR
  rw [hB] at hD hR
  rw [hA] at hD hR
  constructor
  · rw [hD]
    field_simp
    ring
  · rw [hR]
    field_simp
    ring

/-- The short paper's theorem: for `p < q` both two-prime sums are transcendental,
granted the cited Hecke--Mahler value theorem. -/
theorem two_prime_sums_transcendental (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (distinctSum p q) ∧ Transcendental ℚ (repeatedSum p q) := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hne : p ≠ q := Nat.ne_of_lt hpq
  obtain ⟨hD, hR⟩ := two_prime_affine_and_quadratic hp hq hpq
  have hA := transcendental_heckeValue hBL hp hq hpq
  have hpQ : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp1
  have hqQ : (1 : ℚ) < (q : ℚ) := by exact_mod_cast hq1
  have hpqQ : ((p : ℚ)) ≠ (q : ℚ) := by exact_mod_cast hne
  refine PaperR7.two_prime_transcendence_from_analytic_inputs (p : ℚ) (q : ℚ)
    hpQ hqQ hpqQ (PaperR7.twoPrimeHeckeValue p q) (distinctSum p q) (repeatedSum p q)
    hA ?_ ?_
  · rw [hD]
    push_cast
    ring
  · rw [hR]
    push_cast
    ring

theorem repeatedSum_comm {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    repeatedSum p q = repeatedSum q p := by
  unfold repeatedSum
  rw [smoothSet_comm p q]
  refine tsum_congr fun n => ?_
  have hnpos : 0 < (n : ℕ) := n.2.1
  have hne : (n : ℕ) ≠ 0 := by omega
  rw [runningLcm_eq_twoPrimeHeight hp hq hpq hne,
    runningLcm_eq_twoPrimeHeight hq hp (Ne.symm hpq) hne]
  unfold twoPrimeHeight
  push_cast
  ring

theorem distinctSum_comm {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    distinctSum p q = distinctSum q p := by
  have hset : runningLcmValues p q = runningLcmValues q p := by
    unfold runningLcmValues
    rw [smoothSet_comm p q]
    apply Set.image_congr
    intro n hn
    have hnpos : 0 < n := hn.1
    have hne : n ≠ 0 := by omega
    rw [runningLcm_eq_twoPrimeHeight hp hq hpq hne,
      runningLcm_eq_twoPrimeHeight hq hp (Ne.symm hpq) hne]
    unfold twoPrimeHeight
    ring
  unfold distinctSum
  rw [hset]

/-- The long paper's lead theorem: for distinct primes `p` and `q`, both
`R_{p,q}` and `D_{p,q}` are transcendental, granted the cited value theorem. -/
theorem two_prime_transcendence (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Transcendental ℚ (repeatedSum p q) ∧ Transcendental ℚ (distinctSum p q) := by
  rcases lt_or_gt_of_ne hpq with h | h
  · obtain ⟨hD, hR⟩ := two_prime_sums_transcendental hBL hp hq h
    exact ⟨hR, hD⟩
  · obtain ⟨hD, hR⟩ := two_prime_sums_transcendental hBL hq hp h
    rw [repeatedSum_comm hp hq hpq, distinctSum_comm hp hq hpq]
    exact ⟨hR, hD⟩

#print axioms runningLcm_eq_twoPrimeHeight
#print axioms qExp_pExp_succ
#print axioms pExp_qExp_succ
#print axioms twoPrimeHeight_smooth
#print axioms runningLcmValues_eq
#print axioms repeatedSum_eq
#print axioms distinctSum_eq
#print axioms bSum_eq
#print axioms heckeValue_boundary
#print axioms irrational_logb_of_primes
#print axioms transcendental_heckeValue
#print axioms two_prime_affine_and_quadratic
#print axioms two_prime_sums_transcendental
#print axioms two_prime_transcendence

end

end ErdosProblems.Erdos269.PaperCompleteR21
