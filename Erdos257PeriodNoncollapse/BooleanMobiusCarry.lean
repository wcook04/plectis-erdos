import Erdos257PeriodNoncollapse.GenericTailOrbitRigidity
import Erdos257PeriodNoncollapse.GreedyAchievementSet
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Boolean–Möbius carry coordinates for Erdős #257

For a support `A ⊆ ℕ`, the binary Lambert expansion has positive-index
coefficient

`f_A(n) = #{a ∈ A : a ∣ n}`.

This file makes two exact coordinate changes kernel-visible.

* Dirichlet/Möbius: `f_A = 1_A * ζ` and `μ * f_A = 1_A` on positive
  integers.  Conversely, every arithmetic function whose Möbius transform
  is Boolean is the divisor-count coefficient of the support selected by
  that Boolean transform.
* Binary carry: rationality of the support series is equivalent to a
  tempered integer orbit for `f_A`; for a displayed fraction `p/q`, the
  orbit has multiplier `q`, initial value `p`, and its carry quotient is
  exactly `f_A`.

Exponent zero is analytically invisible because the existing support series
uses real division-by-zero conventions at `2^0 - 1`.  Accordingly, set-level
recovery is stated either on positive indices or under `0 ∉ A`.  Omitting
that guard would be false.

The worked support `{2,3}` gives `10/21` and the pure period-six orbit
`10,20,19,17,13,26`.  These coordinate theorems do **not** prove Erdős
#257: they neither exclude infinite Boolean carry paths nor turn finite
search into a completeness argument.  Both Erdős #249 and #257 remain open.

No novelty or priority claim is made for the new theorems in this file.
-/

namespace Erdos257PeriodNoncollapse

open ArithmeticFunction Filter Set
open scoped ArithmeticFunction.Moebius

/-! ## Arithmetic-function packaging -/

/-- The positive-index integer indicator of a support.  Arithmetic functions
must vanish at zero, which is also the correct normalization for the Lambert
coefficient calculus. -/
noncomputable def positiveSupportBit (A : Set ℕ) (n : ℕ) : ℤ :=
  letI := Classical.propDecidable (0 < n ∧ n ∈ A)
  if 0 < n ∧ n ∈ A then 1 else 0

/-- `positiveSupportBit` packaged as an integer-valued arithmetic function. -/
noncomputable def positiveSupportBitAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨positiveSupportBit A, by simp [positiveSupportBit]⟩

/-- The support divisor-count coefficient, cast to an integer-valued
arithmetic function. -/
noncomputable def supportCoeffAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ (supportCoeff A n : ℤ), by simp [supportCoeff]⟩

@[simp] theorem positiveSupportBit_zero (A : Set ℕ) :
    positiveSupportBit A 0 = 0 := by
  simp [positiveSupportBit]

theorem positiveSupportBit_eq_one_iff {A : Set ℕ} {n : ℕ} (hn : 0 < n) :
    positiveSupportBit A n = 1 ↔ n ∈ A := by
  classical
  simp [positiveSupportBit, hn]

@[simp] theorem positiveSupportBitAF_apply (A : Set ℕ) (n : ℕ) :
    positiveSupportBitAF A n = positiveSupportBit A n := rfl

@[simp] theorem supportCoeffAF_apply (A : Set ℕ) (n : ℕ) :
    supportCoeffAF A n = (supportCoeff A n : ℤ) := rfl

/-- The divisor-count coefficient is exactly `1_A * ζ`, with the support
indicator normalized at zero. -/
theorem positiveSupportBitAF_mul_zeta (A : Set ℕ) :
    positiveSupportBitAF A *
        (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)
      = supportCoeffAF A := by
  classical
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [positiveSupportBitAF_apply, supportCoeffAF_apply]
  change
    (∑ d ∈ n.divisors, positiveSupportBit A d) =
      (supportCoeff A n : ℤ)
  rw [supportCoeff_eq_card_filter A n, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  by_cases hA : d ∈ A <;> simp [positiveSupportBit, hdpos, hA]

/-- Exact Möbius recovery: `μ * f_A = 1_A` as arithmetic functions. -/
theorem moebius_mul_supportCoeffAF (A : Set ℕ) :
    ArithmeticFunction.moebius * supportCoeffAF A = positiveSupportBitAF A := by
  calc
    ArithmeticFunction.moebius * supportCoeffAF A =
        ArithmeticFunction.moebius *
          (positiveSupportBitAF A *
            (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
              ArithmeticFunction ℤ)) := by
          rw [positiveSupportBitAF_mul_zeta]
    _ = (ArithmeticFunction.moebius *
          (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℤ)) * positiveSupportBitAF A := by
          ac_rfl
    _ = positiveSupportBitAF A := by
          rw [ArithmeticFunction.moebius_mul_coe_zeta, one_mul]

/-- Pointwise positive-index form of Möbius recovery. -/
theorem mobius_supportCoeff_eq_one_iff (A : Set ℕ) {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 ↔ n ∈ A := by
  rw [moebius_mul_supportCoeffAF]
  exact positiveSupportBit_eq_one_iff hn

/-- The Möbius transform of every support coefficient is Boolean. -/
theorem mobius_supportCoeff_boolean (A : Set ℕ) (n : ℕ) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 0 ∨
      (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 := by
  rw [moebius_mul_supportCoeffAF]
  change positiveSupportBit A n = 0 ∨ positiveSupportBit A n = 1
  classical
  by_cases h : 0 < n ∧ n ∈ A <;> simp [positiveSupportBit, h]

/-- Under the honest zero normalization, the Boolean Möbius transform
recovers the entire support set, not merely its positive part. -/
theorem mobius_supportCoeff_recovers_support (A : Set ℕ) (hzero : 0 ∉ A) :
    {n : ℕ | (ArithmeticFunction.moebius * supportCoeffAF A) n = 1} = A := by
  ext n
  rw [moebius_mul_supportCoeffAF]
  change positiveSupportBit A n = 1 ↔ n ∈ A
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hzero]
  · simp [positiveSupportBit, hn]

/-! ## Converse Boolean inversion -/

/-- The positive support selected by the Boolean Möbius transform of `f`. -/
noncomputable def booleanMobiusSupport (f : ArithmeticFunction ℤ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ (ArithmeticFunction.moebius * f) n = 1}

@[simp] theorem zero_not_mem_booleanMobiusSupport (f : ArithmeticFunction ℤ) :
    0 ∉ booleanMobiusSupport f := by
  simp [booleanMobiusSupport]

/-- A Boolean Möbius transform is exactly the normalized indicator of the
support that it selects. -/
theorem moebius_mul_eq_positiveSupportBitAF_of_boolean
    (f : ArithmeticFunction ℤ)
    (hbool : ∀ n : ℕ, 0 < n →
      (ArithmeticFunction.moebius * f) n = 0 ∨
        (ArithmeticFunction.moebius * f) n = 1) :
    ArithmeticFunction.moebius * f =
      positiveSupportBitAF (booleanMobiusSupport f) := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rcases hbool n hn with hzero | hone
    · change (ArithmeticFunction.moebius * f) n =
          positiveSupportBit (booleanMobiusSupport f) n
      rw [hzero]
      classical
      unfold positiveSupportBit
      rw [if_neg]
      rintro ⟨_, hmem⟩
      change 0 < n ∧ (ArithmeticFunction.moebius * f) n = 1 at hmem
      omega
    · change (ArithmeticFunction.moebius * f) n =
          positiveSupportBit (booleanMobiusSupport f) n
      rw [hone]
      classical
      unfold positiveSupportBit
      rw [if_pos]
      exact ⟨hn, ⟨hn, hone⟩⟩

/-- **Boolean Möbius inversion, converse direction.**  Every integer-valued
arithmetic function with Boolean Möbius transform is the support coefficient
of the positive set selected by that transform.  No search or finiteness
hypothesis appears. -/
theorem eq_supportCoeffAF_booleanMobiusSupport_of_boolean
    (f : ArithmeticFunction ℤ)
    (hbool : ∀ n : ℕ, 0 < n →
      (ArithmeticFunction.moebius * f) n = 0 ∨
        (ArithmeticFunction.moebius * f) n = 1) :
    f = supportCoeffAF (booleanMobiusSupport f) := by
  have hbit := moebius_mul_eq_positiveSupportBitAF_of_boolean f hbool
  calc
    f = ((↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℤ) * ArithmeticFunction.moebius) * f := by
        rw [ArithmeticFunction.coe_zeta_mul_moebius, one_mul]
    _ = (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℤ) * (ArithmeticFunction.moebius * f) := by
        rw [mul_assoc]
    _ = (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
          ArithmeticFunction ℤ) *
            positiveSupportBitAF (booleanMobiusSupport f) := by rw [hbit]
    _ = positiveSupportBitAF (booleanMobiusSupport f) *
          (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
            ArithmeticFunction ℤ) := by rw [mul_comm]
    _ = supportCoeffAF (booleanMobiusSupport f) :=
          positiveSupportBitAF_mul_zeta _

/-! ## Sharp divisor and support-coefficient growth -/

/-- Elementary divisor-pair estimate `τ(n) ≤ 2⌊√n⌋`.  Mathlib currently
supplies only the coarser `τ(n) ≤ n`; the partition below pairs every
divisor above the square root with its complementary divisor below it. -/
theorem card_divisors_le_two_mul_sqrt (n : ℕ) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let small := n.divisors.filter fun d => d ≤ Nat.sqrt n
  let large := n.divisors.filter fun d => ¬ d ≤ Nat.sqrt n
  have hsplit : small.card + large.card = n.divisors.card := by
    simpa [small, large] using
      (Finset.card_filter_add_card_filter_not (s := n.divisors)
        (fun d => d ≤ Nat.sqrt n))
  have hsmallsub : small ⊆ Finset.Icc 1 (Nat.sqrt n) := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hddiv, hdle⟩
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hddiv, hdle⟩
  have hsmall : small.card ≤ Nat.sqrt n := by
    calc
      small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card :=
        Finset.card_le_card hsmallsub
      _ = Nat.sqrt n := by simp [Nat.card_Icc]
  have hcomplement : ∀ {d : ℕ}, d ∈ n.divisors → n / (n / d) = d := by
    intro d hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdle : d ≤ n := Nat.le_of_dvd hnpos hdvd
    have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
    have hqdvd : n / d ∣ n := Nat.div_dvd_of_dvd hdvd
    apply (Nat.div_eq_iff_eq_mul_left hqpos hqdvd).2
    exact (Nat.mul_div_cancel' hdvd).symm
  have hlargeinj : Set.InjOn (fun d : ℕ => n / d) (↑large : Set ℕ) := by
    intro a ha b hb hab
    have hadiv : a ∈ n.divisors := (Finset.mem_filter.mp ha).1
    have hbdiv : b ∈ n.divisors := (Finset.mem_filter.mp hb).1
    change n / a = n / b at hab
    calc
      a = n / (n / a) := (hcomplement hadiv).symm
      _ = n / (n / b) := by rw [hab]
      _ = b := hcomplement hbdiv
  have himagesub :
      large.image (fun d : ℕ => n / d) ⊆ Finset.Icc 1 (Nat.sqrt n) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨d, hdlarge, rfl⟩
    rcases Finset.mem_filter.mp hdlarge with ⟨hddiv, hdnot⟩
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hddiv).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hddiv
    have hdle : d ≤ n := Nat.le_of_dvd hnpos hdvd
    have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
    have hfactor : n = (n / d) * d := (Nat.div_mul_cancel hdvd).symm
    rcases Nat.le_sqrt_of_eq_mul hfactor with hqle | hdleS
    · exact Finset.mem_Icc.mpr ⟨hqpos, hqle⟩
    · exact False.elim (hdnot hdleS)
  have hlarge : large.card ≤ Nat.sqrt n := by
    calc
      large.card = (large.image (fun d : ℕ => n / d)).card :=
        (Finset.card_image_iff.mpr hlargeinj).symm
      _ ≤ (Finset.Icc 1 (Nat.sqrt n)).card := Finset.card_le_card himagesub
      _ = Nat.sqrt n := by simp [Nat.card_Icc]
  omega

/-- The support coefficient inherits the sharp divisor-pair envelope. -/
theorem supportCoeff_le_two_mul_sqrt (A : Set ℕ) (n : ℕ) :
    supportCoeff A n ≤ 2 * Nat.sqrt n :=
  le_trans (supportCoeff_le_card_divisors A n)
    (card_divisors_le_two_mul_sqrt n)

/-- The floor-square-root of a shifted index is controlled by the fixed
root plus the shift. -/
theorem sqrt_shift_le_sqrt_add_index (N j : ℕ) :
    Nat.sqrt (N + j + 1) ≤ Nat.sqrt N + j + 1 := by
  have hN := Nat.sqrt_le_add N
  have hsq : N + j + 1 ≤
      (Nat.sqrt N + j + 1) * (Nat.sqrt N + j + 1) := by
    nlinarith
  have h := Nat.sqrt_le_sqrt hsq
  simpa using h

/-- **Sharp support-tail strip.**  The scaled binary support-coefficient
tail grows at most like `2√N + 4`, exactly the envelope used by the T8
Boolean-carry formulation. -/
theorem binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    (A : Set ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff A) N ≤
      2 * Real.sqrt (N : ℝ) + 4 := by
  have hsum : Summable
      (fun j : ℕ ↦
        ((supportCoeff A (N + j + 1) : ℝ)) /
          (2 : ℝ) ^ (j + 1)) :=
    summable_coeff_shift_tail 2 N (supportCoeff A)
      (by norm_num) (supportCoeff_le_self A)
  have hcmp : Summable
      (fun j : ℕ ↦
        (((Nat.sqrt N + 1 : ℕ) : ℝ) + (j : ℝ)) *
          ((1 : ℝ) / 2) ^ j) :=
    summable_const_add_mul_geometric (Nat.sqrt N + 1)
      (by norm_num) (by norm_num)
  have hterm : ∀ j : ℕ,
      ((supportCoeff A (N + j + 1) : ℝ)) /
          (2 : ℝ) ^ (j + 1) ≤
        (((Nat.sqrt N + 1 : ℕ) : ℝ) + (j : ℝ)) *
          ((1 : ℝ) / 2) ^ j := by
    intro j
    have hcoeff : supportCoeff A (N + j + 1) ≤
        2 * (Nat.sqrt N + j + 1) :=
      (supportCoeff_le_two_mul_sqrt A (N + j + 1)).trans
        (Nat.mul_le_mul_left 2 (sqrt_shift_le_sqrt_add_index N j))
    have hcoeffR : (supportCoeff A (N + j + 1) : ℝ) ≤
        2 * ((Nat.sqrt N + j + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcoeff
    calc
      ((supportCoeff A (N + j + 1) : ℝ)) /
          (2 : ℝ) ^ (j + 1)
          ≤ (2 * ((Nat.sqrt N + j + 1 : ℕ) : ℝ)) /
              (2 : ℝ) ^ (j + 1) := by gcongr
      _ = (((Nat.sqrt N + 1 : ℕ) : ℝ) + (j : ℝ)) *
            ((1 : ℝ) / 2) ^ j := by
          push_cast
          rw [pow_succ, div_pow, one_pow]
          field_simp
          ring
  unfold binaryCoeffTail
  calc
    (∑' j : ℕ, ((supportCoeff A (N + j + 1) : ℝ)) /
        (2 : ℝ) ^ (j + 1))
        ≤ ∑' j : ℕ,
            (((Nat.sqrt N + 1 : ℕ) : ℝ) + (j : ℝ)) *
              ((1 : ℝ) / 2) ^ j :=
          Summable.tsum_le_tsum hterm hsum hcmp
    _ ≤ 2 * (((Nat.sqrt N + 1 : ℕ) : ℝ)) + 2 :=
      tsum_const_add_mul_geometric_le (Nat.sqrt N + 1)
        (by norm_num) (by norm_num)
    _ ≤ 2 * Real.sqrt (N : ℝ) + 4 := by
      have hsqrt : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      push_cast
      linarith

/-- A single positive support element forces every scaled coefficient tail
to be strictly positive. -/
theorem binaryCoeffTail_supportCoeff_pos_of_exists_pos_mem
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A) (N : ℕ) :
    0 < binaryCoeffTail (supportCoeff A) N := by
  obtain ⟨a, ha, haA⟩ := hA
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  let j : ℕ := k * (N + 1)
  have hidx : N + j + 1 = (k + 1) * (N + 1) := by
    dsimp [j]
    ring
  have hcoeff : 0 < supportCoeff A (N + j + 1) := by
    apply supportCoeff_pos_of_mem_dvd A haA
    · rw [hidx]
      exact dvd_mul_right (k + 1) (N + 1)
    · rw [hidx]
      positivity
  have hterm :
      (0 : ℝ) <
        (supportCoeff A (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) := by
    positivity
  have hsum := summable_coeff_shift_tail 2 N (supportCoeff A)
    (by norm_num) (supportCoeff_le_self A)
  unfold binaryCoeffTail
  exact lt_of_lt_of_le hterm (hsum.le_tsum j (fun i _ ↦ by positivity))

/-! ## Lambert-series and tail-orbit bridge -/

/-- At base two, the support Lambert series is literally the generic binary
coefficient series of `supportCoeff A`. -/
theorem erdosSupportSeries_two_eq_binaryCoeffSeries (A : Set ℕ) :
    erdosSupportSeries 2 A = binaryCoeffSeries (supportCoeff A) := by
  rw [erdosSupportSeries_eq_tsum_supportCoeff 2 A (by norm_num)]
  rfl

/-- Rationality of the support series is exactly existence of a tempered
integer carry orbit for its support coefficient. -/
theorem erdosSupportSeries_rational_iff_exists_temperedCarry (A : Set ℕ) :
    HasRationalValue (erdosSupportSeries 2 A) ↔
      ∃ q : ℕ, 0 < q ∧ ∃ U : ℕ → ℤ,
        IsTemperedBinaryOrbit (supportCoeff A) q U := by
  rw [erdosSupportSeries_two_eq_binaryCoeffSeries]
  exact binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (supportCoeff A) (supportCoeff_le_self A)

/-- A displayed fraction produces an orbit with that exact denominator.
The proof constructs the integer prefix orbit and identifies it with the
scaled analytic tail. -/
theorem exists_temperedCarry_of_support_fraction
    (A : Set ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) :
    ∃ U : ℕ → ℤ, U 0 = p ∧
      IsTemperedBinaryOrbit (supportCoeff A) q U := by
  let z : ℕ → ℤ := fun N ↦
    Classical.choose
      (bpow_mul_coeff_series_eq_int_add_tail 2 N (supportCoeff A)
        (by norm_num) (supportCoeff_le_self A))
  have hz : ∀ N : ℕ,
      (2 : ℝ) ^ N * binaryCoeffSeries (supportCoeff A) =
        (z N : ℝ) + binaryCoeffTail (supportCoeff A) N := by
    intro N
    exact Classical.choose_spec
      (bpow_mul_coeff_series_eq_int_add_tail 2 N (supportCoeff A)
        (by norm_num) (supportCoeff_le_self A))
  let U : ℕ → ℤ := fun N ↦ (2 : ℤ) ^ N * p - (q : ℤ) * z N
  have htail : ∀ N : ℕ,
      (U N : ℝ) = (q : ℝ) * binaryCoeffTail (supportCoeff A) N := by
    intro N
    have hN := hz N
    rw [← erdosSupportSeries_two_eq_binaryCoeffSeries A, hvalue] at hN
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hmul := congrArg (fun x : ℝ ↦ (q : ℝ) * x) hN
    change
      (q : ℝ) * ((2 : ℝ) ^ N * ((p : ℝ) / (q : ℝ))) =
        (q : ℝ) * ((z N : ℝ) + binaryCoeffTail (supportCoeff A) N) at hmul
    have hcancel :
        (q : ℝ) * ((2 : ℝ) ^ N * ((p : ℝ) / (q : ℝ))) =
          (2 : ℝ) ^ N * (p : ℝ) := by
      field_simp
    rw [hcancel] at hmul
    unfold U
    push_cast
    linarith
  refine ⟨U, ?_, ?_, ?_⟩
  · apply Int.cast_injective (α := ℝ)
    rw [htail 0, binaryCoeffTail_zero,
      ← erdosSupportSeries_two_eq_binaryCoeffSeries A, hvalue]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    field_simp
  · intro N
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [htail (N + 1), htail N,
      binaryCoeffTail_succ (supportCoeff A) (supportCoeff_le_self A) N]
    ring
  · have hlim :=
      (binaryCoeffTail_div_pow_tendsto_zero
        (supportCoeff A) (supportCoeff_le_self A)).const_mul (q : ℝ)
    convert hlim using 1
    · funext N
      rw [htail N]
      ring
    · simp

/-- Every tempered carry orbit with initial numerator `p` certifies the
displayed fraction `p/q`. -/
theorem support_fraction_of_temperedCarry
    (A : Set ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (hU0 : U 0 = p)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) :
    erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  have htail := temperedBinaryOrbit_eq_scaledTail
    (supportCoeff A) (supportCoeff_le_self A) horbit 0
  rw [binaryCoeffTail_zero, ← erdosSupportSeries_two_eq_binaryCoeffSeries A,
    hU0] at htail
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hq0).2
  nlinarith

/-- Fixed-fraction equivalence form of the Boolean carry trunk. -/
theorem support_fraction_iff_exists_temperedCarry
    (A : Set ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q) :
    erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) ↔
      ∃ U : ℕ → ℤ, U 0 = p ∧
        IsTemperedBinaryOrbit (supportCoeff A) q U := by
  constructor
  · exact exists_temperedCarry_of_support_fraction A p q hq
  · rintro ⟨U, hU0, hU⟩
    exact support_fraction_of_temperedCarry A p q hq U hU0 hU

/-! ## The exact half-residual carry bridge

The bridge below does not introduce a second carry model.  It uses the
existing `affineBinaryOrbit` twice: with doubled support coefficients it is
the denominator-two orbit for the displayed fraction `1/2`; after the
forced first digit it factors as twice the same affine orbit with undoubled
coefficients.  For a finite prefix, the remaining `binaryCoeffTail` is the
future-multiple tail of that finite support, not the tail of a hypothetical
completed representation.
-/

/-- Adding one to the correction recurrence turns its affine input
`1 - f_A` into the existing unit support-carry input `f_A`. -/
theorem correctionCarry_add_one_recurrence_iff
    (A : Set ℕ) (K : ℕ → ℤ) (N : ℕ) :
    K (N + 1) = 2 * K N + 1 - (supportCoeff A (N + 1) : ℤ) ↔
      K (N + 1) + 1 =
        2 * (K N + 1) - (supportCoeff A (N + 1) : ℤ) := by
  constructor <;> intro h <;> omega

/-- Doubling the add-one correction state gives exactly the denominator-two
support-carry recurrence. -/
theorem correctionCarry_two_mul_add_one_recurrence_iff
    (A : Set ℕ) (K : ℕ → ℤ) (N : ℕ) :
    K (N + 1) = 2 * K N + 1 - (supportCoeff A (N + 1) : ℤ) ↔
      2 * (K (N + 1) + 1) =
        2 * (2 * (K N + 1)) -
          ((2 * supportCoeff A (N + 1) : ℕ) : ℤ) := by
  push_cast
  constructor <;> intro h <;> omega

/-- The initial value and recurrence determine the denominator-two support
carry uniquely, and identify it with the existing affine orbit. -/
theorem halfCarry_eq_affineBinaryOrbit
    (A : Set ℕ) (U : ℕ → ℤ) (hU0 : U 0 = 1)
    (hrec : ∀ N : ℕ,
      U (N + 1) = 2 * U N -
        ((2 * supportCoeff A (N + 1) : ℕ) : ℤ)) :
    ∀ N : ℕ,
      U N = affineBinaryOrbit
        (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1 N := by
  intro N
  induction N with
  | zero => simpa using hU0
  | succ N ih =>
      rw [hrec N, affineBinaryOrbit_succ, ih]

/-- A support has displayed value `1/2` exactly when its canonical affine
denominator-two carry is tempered.  This is the fixed-fraction carry theorem
with the existential orbit removed by recurrence uniqueness. -/
theorem support_half_iff_affineBinaryOrbit_tempered (A : Set ℕ) :
    erdosSupportSeries 2 A = (1 : ℝ) / 2 ↔
      IsTemperedBinaryOrbit (supportCoeff A) 2
        (affineBinaryOrbit
          (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1) := by
  constructor
  · intro hhalf
    obtain ⟨U, hU0, horbit⟩ :=
      exists_temperedCarry_of_support_fraction A 1 2 (by norm_num)
        (by rw [hhalf]; norm_num)
    have hU : U = affineBinaryOrbit
        (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1 :=
      funext (halfCarry_eq_affineBinaryOrbit A U hU0 horbit.1)
    rw [← hU]
    exact horbit
  · intro horbit
    have hfrac := support_fraction_of_temperedCarry A 1 2 (by norm_num) _ rfl horbit
    rw [hfrac]; norm_num

/-- Exact residual identity for the canonical half carry.  It is the
prefix-plus-scaled-tail decomposition expressed directly in the existing
affine-orbit coordinate. -/
theorem halfSupportSeries_residual_scaled_eq_affineCarry_sub_tail
    (A : Set ℕ) (N : ℕ) :
    (2 : ℝ) ^ N * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) =
      (affineBinaryOrbit
          (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1 N : ℤ) / 2 -
        binaryCoeffTail (supportCoeff A) N := by
  have hdiff :
      (affineBinaryOrbit
          (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1 N : ℤ) -
          2 * binaryCoeffTail (supportCoeff A) N =
        (2 : ℝ) ^ N * (1 - 2 * erdosSupportSeries 2 A) := by
    induction N with
    | zero =>
        rw [affineBinaryOrbit_zero, binaryCoeffTail_zero,
          erdosSupportSeries_two_eq_binaryCoeffSeries]
        norm_num
    | succ N ih =>
        simp only [affineBinaryOrbit_succ,
          binaryCoeffTail_succ (supportCoeff A) (supportCoeff_le_self A) N]
        push_cast [pow_succ] at ih ⊢
        linarith [ih]
  calc
    (2 : ℝ) ^ N * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) =
        ((2 : ℝ) ^ N * (1 - 2 * erdosSupportSeries 2 A)) / 2 := by ring
    _ = ((affineBinaryOrbit
          (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1 N : ℤ) -
          2 * binaryCoeffTail (supportCoeff A) N) / 2 := by rw [← hdiff]
    _ = (affineBinaryOrbit
          (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1 N : ℤ) / 2 -
        binaryCoeffTail (supportCoeff A) N := by ring

/-- Truncating a support above `M` does not change its divisor-count
coefficient through level `M`. -/
theorem supportCoeff_inter_Iic_eq_of_le
    (A : Set ℕ) {n M : ℕ} (hnM : n ≤ M) :
    supportCoeff (A ∩ Set.Iic M) n = supportCoeff A n := by
  classical
  unfold supportCoeff
  congr 1
  ext d
  simp only [Finset.mem_filter, Set.mem_inter_iff, Set.mem_Iic]
  constructor
  · rintro ⟨hd, hA, _⟩
    exact ⟨hd, hA⟩
  · rintro ⟨hd, hA⟩
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hnpos : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2
    exact ⟨hd, hA, (Nat.le_of_dvd hnpos hdvd).trans hnM⟩

/-- Consequently, the canonical half carry at depth `M` can be computed
from the full support or from its finite prefix through `M`. -/
theorem affineHalfCarry_inter_Iic_eq
    (A : Set ℕ) (M : ℕ) :
    affineBinaryOrbit
        (fun n : ℕ ↦
          ((2 * supportCoeff (A ∩ Set.Iic M) n : ℕ) : ℤ)) 1 M =
      affineBinaryOrbit
        (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1 M := by
  have haux : ∀ n ≤ M,
      affineBinaryOrbit
          (fun k : ℕ ↦
            ((2 * supportCoeff (A ∩ Set.Iic M) k : ℕ) : ℤ)) 1 n =
        affineBinaryOrbit
          (fun k : ℕ ↦ ((2 * supportCoeff A k : ℕ) : ℤ)) 1 n := by
    intro n hnM
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [affineBinaryOrbit_succ]
        rw [ih (by omega), supportCoeff_inter_Iic_eq_of_le A hnM]
  exact haux M le_rfl

/-- If exponent one is absent, the denominator-two carry factors after its
first step as twice an integer affine carry with unit coefficient input.
This is the precise `U = 2V` identification from the corrected development. -/
theorem halfDenominatorCarry_eq_two_mul_integerCarry
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    affineBinaryOrbit
        (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1 (N + 1) =
      2 * affineBinaryOrbit
        (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1 N := by
  have hcoeffOne : supportCoeff A 1 = 0 := by
    classical
    unfold supportCoeff
    simp [hone]
  induction N with
  | zero => simp [hcoeffOne]
  | succ N ih =>
      rw [affineBinaryOrbit_succ, ih, affineBinaryOrbit_succ]
      push_cast
      ring

/-- **Finite-prefix carry-tail residual formula (the formal development.s
equation (18)).**  The integer term is the existing affine support carry,
while the analytic term is the future-multiple tail generated only by the
finite support `A ∩ Iic (N+1)`. -/
theorem halfFinitePrefix_residual_eq_pow_mul_integerCarry_sub_finiteTail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (1 : ℝ) / 2 - erdosSupportSeries 2 (A ∩ Set.Iic (N + 1)) =
      ((affineBinaryOrbit
          (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1 N : ℤ) -
        binaryCoeffTail (supportCoeff (A ∩ Set.Iic (N + 1))) (N + 1)) /
          (2 : ℝ) ^ (N + 1) := by
  have hscaled :=
    halfSupportSeries_residual_scaled_eq_affineCarry_sub_tail
      (A ∩ Set.Iic (N + 1)) (N + 1)
  rw [affineHalfCarry_inter_Iic_eq A (N + 1),
    halfDenominatorCarry_eq_two_mul_integerCarry A hone N] at hscaled
  push_cast at hscaled
  have hpow : (2 : ℝ) ^ (N + 1) ≠ 0 := by positivity
  apply (eq_div_iff hpow).2
  simpa [mul_comm] using hscaled

/-- The exact carry difference in a support orbit. -/
theorem temperedCarry_difference
    (A : Set ℕ) (q : ℕ) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    2 * U N - U (N + 1) =
      (q : ℤ) * (supportCoeff A (N + 1) : ℤ) := by
  have hrec := horbit.1 N
  push_cast at hrec
  omega

/-- Divisibility of every carry difference by the displayed denominator. -/
theorem denominator_dvd_temperedCarry_difference
    (A : Set ℕ) (q : ℕ) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    (q : ℤ) ∣ 2 * U N - U (N + 1) := by
  rw [temperedCarry_difference A q U horbit N]
  exact dvd_mul_right _ _

/-- After exact division, the carry quotient is precisely `f_A(N+1)`. -/
theorem temperedCarry_quotient_eq_supportCoeff
    (A : Set ℕ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    (2 * U N - U (N + 1)) / (q : ℤ) =
      (supportCoeff A (N + 1) : ℤ) := by
  rw [temperedCarry_difference A q U horbit N]
  exact Int.mul_ediv_cancel_left _ (Int.ofNat_ne_zero.mpr hq.ne')

/-- A positive support and positive multiplier force every state of a
tempered support carry to be a positive integer. -/
theorem temperedCarry_pos_of_exists_pos_mem
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    0 < U N := by
  have htail := binaryCoeffTail_supportCoeff_pos_of_exists_pos_mem A hA N
  have hid := temperedBinaryOrbit_eq_scaledTail
    (supportCoeff A) (supportCoeff_le_self A) horbit N
  have hreal : (0 : ℝ) < (U N : ℝ) := by
    rw [hid]
    positivity
  exact_mod_cast hreal

/-- Every tempered support carry lies in the formal development.s sharp square-root
strip. -/
theorem temperedCarry_le_denominator_mul_two_sqrt_add_four
    (A : Set ℕ) (q : ℕ) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (N : ℕ) :
    (U N : ℝ) ≤
      (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4) := by
  rw [temperedBinaryOrbit_eq_scaledTail
    (supportCoeff A) (supportCoeff_le_self A) horbit N]
  exact mul_le_mul_of_nonneg_left
    (binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A N)
    (Nat.cast_nonneg q)

/-- The square-root strip is strong enough to enforce the tempered boundary;
the proof deliberately relaxes `√N` to `N+1` and uses the already checked
linear-over-exponential limit. -/
theorem tendsto_div_pow_zero_of_nonnegative_sqrt_bound
    (q : ℕ) (U : ℕ → ℤ)
    (hnonneg : ∀ N : ℕ, 0 ≤ U N)
    (hbound : ∀ N : ℕ, (U N : ℝ) ≤
      (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4)) :
    Tendsto (fun N : ℕ ↦ (U N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0) := by
  have hsqrt : ∀ N : ℕ, Real.sqrt (N : ℝ) ≤ (N : ℝ) + 1 := by
    intro N
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith
  have hNlim : Tendsto (fun N : ℕ ↦ (N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have h1lim : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have huplim : Tendsto
      (fun N : ℕ ↦ (q : ℝ) * (2 * (N : ℝ) + 6) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    have h := (hNlim.const_mul (2 * (q : ℝ))).add
      (h1lim.const_mul (6 * (q : ℝ)))
    convert h using 1
    · funext N
      ring
    · simp
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N ↦
      div_nonneg (by exact_mod_cast hnonneg N) (by positivity))
    (Filter.Eventually.of_forall fun N ↦ ?_)
    huplim
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    (U N : ℝ) ≤ (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4) := hbound N
    _ ≤ (q : ℝ) * (2 * ((N : ℝ) + 1) + 4) := by
      gcongr
      exact hsqrt N
    _ = (q : ℝ) * (2 * (N : ℝ) + 6) := by ring

/-! ## The quotient-facing interface -/

/-- The normalized integer carry quotient.  Index zero is forced to zero;
at positive index `n` this is `(2U(n-1)-U(n))/q`. -/
def carryQuotient (q : ℕ) (U : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else (2 * U (n - 1) - U n) / (q : ℤ)

/-- The carry quotient packaged as an arithmetic function. -/
def carryQuotientAF (q : ℕ) (U : ℕ → ℤ) : ArithmeticFunction ℤ :=
  ⟨carryQuotient q U, by simp [carryQuotient]⟩

/-- The quotient-only T8 certificate.  It mentions no support set: Boolean
Möbius inversion reconstructs the unique normalized support afterwards. -/
structure BooleanMobiusCarryCertificate (p : ℤ) (q : ℕ) (U : ℕ → ℤ) : Prop where
  initial : U 0 = p
  positive : ∀ N : ℕ, 0 < U N
  sqrtBound : ∀ N : ℕ, (U N : ℝ) ≤
    (q : ℝ) * (2 * Real.sqrt (N : ℝ) + 4)
  divisible : ∀ N : ℕ, (q : ℤ) ∣ 2 * U N - U (N + 1)
  mobiusBoolean : ∀ n : ℕ, 0 < n →
    (ArithmeticFunction.moebius * carryQuotientAF q U) n = 0 ∨
      (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1

@[simp] theorem carryQuotient_zero (q : ℕ) (U : ℕ → ℤ) :
    carryQuotient q U 0 = 0 := by simp [carryQuotient]

/-- A tempered support carry recovers the whole divisor-count coefficient
through exact quotient extraction. -/
theorem carryQuotientAF_eq_supportCoeffAF
    (A : Set ℕ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) :
    carryQuotientAF q U = supportCoeffAF A := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [carryQuotientAF]
  · obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    change carryQuotient q U (N + 1) = (supportCoeff A (N + 1) : ℤ)
    rw [carryQuotient, if_neg (by omega)]
    simpa using temperedCarry_quotient_eq_supportCoeff A q hq U horbit N

/-- The Möbius transform of the carry quotient is the normalized support
bit.  This is the inversion formula `μ * f_U = 1_A`. -/
theorem moebius_mul_carryQuotientAF
    (A : Set ℕ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) :
    ArithmeticFunction.moebius * carryQuotientAF q U =
      positiveSupportBitAF A := by
  rw [carryQuotientAF_eq_supportCoeffAF A q hq U horbit,
    moebius_mul_supportCoeffAF]

/-- Hence the Möbius transform of every exact carry quotient is Boolean. -/
theorem mobius_carryQuotient_boolean
    (A : Set ℕ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) (n : ℕ) :
    (ArithmeticFunction.moebius * carryQuotientAF q U) n = 0 ∨
      (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1 := by
  rw [carryQuotientAF_eq_supportCoeffAF A q hq U horbit]
  exact mobius_supportCoeff_boolean A n

/-- With `0 ∉ A`, the carry quotient's Boolean Möbius transform recovers
the support literally as a set. -/
theorem mobius_carryQuotient_recovers_support
    (A : Set ℕ) (hzero : 0 ∉ A)
    (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (horbit : IsTemperedBinaryOrbit (supportCoeff A) q U) :
    {n : ℕ | (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A := by
  rw [carryQuotientAF_eq_supportCoeffAF A q hq U horbit]
  exact mobius_supportCoeff_recovers_support A hzero

/-- **Forward T8 direction.**  A normalized nonempty support with value `p/q`
produces a positive square-root-bounded integer orbit whose differences are
divisible by `q`, whose carry quotient has Boolean Möbius transform, and
whose selected support is exactly the original `A`. -/
theorem exists_booleanMobiusCarry_of_support_fraction
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) :
    ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A := by
  obtain ⟨U, hU0, horbit⟩ :=
    exists_temperedCarry_of_support_fraction A p q hq hvalue
  refine ⟨U, ?_, ?_⟩
  · refine ⟨hU0, ?_, ?_, ?_, ?_⟩
    · exact fun N ↦ temperedCarry_pos_of_exists_pos_mem A hpos q hq U horbit N
    · exact fun N ↦
        temperedCarry_le_denominator_mul_two_sqrt_add_four A q U horbit N
    · exact fun N ↦
        denominator_dvd_temperedCarry_difference A q U horbit N
    · exact fun n _ ↦ mobius_carryQuotient_boolean A q hq U horbit n
  · exact mobius_carryQuotient_recovers_support A hzero q hq U horbit

/-- **Converse T8 direction.**  A quotient-only Boolean carry certificate
reconstructs a normalized support `A`, becomes a tempered support orbit for
that `A`, and certifies the exact value `p/q`. -/
theorem support_fraction_of_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) (U : ℕ → ℤ)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧ erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  let A := booleanMobiusSupport (carryQuotientAF q U)
  have hcoeff : carryQuotientAF q U = supportCoeffAF A :=
    eq_supportCoeffAF_booleanMobiusSupport_of_boolean
      (carryQuotientAF q U) cert.mobiusBoolean
  have hrec : ∀ N : ℕ,
      U (N + 1) = 2 * U N -
        ((q * supportCoeff A (N + 1) : ℕ) : ℤ) := by
    intro N
    have hquot :
        (2 * U N - U (N + 1)) / (q : ℤ) =
          (supportCoeff A (N + 1) : ℤ) := by
      have happ := congrArg
        (fun f : ArithmeticFunction ℤ ↦ f (N + 1)) hcoeff
      change carryQuotient q U (N + 1) =
        (supportCoeff A (N + 1) : ℤ) at happ
      rw [carryQuotient, if_neg (by omega)] at happ
      simpa using happ
    have hmul := Int.mul_ediv_cancel' (cert.divisible N)
    rw [hquot] at hmul
    push_cast
    omega
  have htemp : Tendsto (fun N : ℕ ↦ (U N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_div_pow_zero_of_nonnegative_sqrt_bound q U
      (fun N ↦ (cert.positive N).le) cert.sqrtBound
  have horbit : IsTemperedBinaryOrbit (supportCoeff A) q U := ⟨hrec, htemp⟩
  refine ⟨zero_not_mem_booleanMobiusSupport _, ?_⟩
  exact support_fraction_of_temperedCarry A p q hq U cert.initial horbit

/-- A quotient-only Boolean carry certificate exposes every reconstructed
object used by the converse, not only the final scalar identity. -/
theorem BooleanMobiusCarryCertificate.reconstructsSupport
    {p : ℤ} {q : ℕ} {U : ℕ → ℤ} (hq : 0 < q)
    (cert : BooleanMobiusCarryCertificate p q U) :
    let A := booleanMobiusSupport (carryQuotientAF q U)
    0 ∉ A ∧
      carryQuotientAF q U = supportCoeffAF A ∧
      IsTemperedBinaryOrbit (supportCoeff A) q U ∧
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A ∧
      erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
  let A := booleanMobiusSupport (carryQuotientAF q U)
  have hzero : 0 ∉ A :=
    zero_not_mem_booleanMobiusSupport (carryQuotientAF q U)
  have hcoeff : carryQuotientAF q U = supportCoeffAF A := by
    simpa [A] using
      eq_supportCoeffAF_booleanMobiusSupport_of_boolean
        (carryQuotientAF q U) cert.mobiusBoolean
  have hrec : ∀ N : ℕ,
      U (N + 1) =
        2 * U N - ((q * supportCoeff A (N + 1) : ℕ) : ℤ) := by
    intro N
    have hquot := congrArg
      (fun f : ArithmeticFunction ℤ ↦ f (N + 1)) hcoeff
    change carryQuotient q U (N + 1) =
      (supportCoeff A (N + 1) : ℤ) at hquot
    rw [carryQuotient, if_neg (by omega)] at hquot
    have hqZ : (q : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hq.ne'
    have hdifference :
        2 * U N - U (N + 1) =
          (supportCoeff A (N + 1) : ℤ) * (q : ℤ) :=
      (Int.ediv_eq_iff_eq_mul_left hqZ (cert.divisible N)).mp hquot
    have hdifference' :
        2 * U N - U (N + 1) =
          (q : ℤ) * (supportCoeff A (N + 1) : ℤ) := by
      simpa [mul_comm] using hdifference
    push_cast
    omega
  have htemp := tendsto_div_pow_zero_of_nonnegative_sqrt_bound q U
    (fun N ↦ (cert.positive N).le) cert.sqrtBound
  have horbit : IsTemperedBinaryOrbit (supportCoeff A) q U :=
    ⟨hrec, htemp⟩
  have hrecovery :
      {n : ℕ |
        (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1} = A :=
    mobius_carryQuotient_recovers_support A hzero q hq U horbit
  have hvalue : erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) :=
    support_fraction_of_temperedCarry A p q hq U cert.initial horbit
  exact ⟨hzero, hcoeff, horbit, hrecovery, hvalue⟩

/-- **Certificate T8 equivalence.**  Positive normalized supports with
value `p/q` are in exact correspondence at the existence level with
quotient-only Boolean Möbius carry certificates.  The converse support is
not guessed: it is reconstructed as `booleanMobiusSupport` of the carry
quotient. -/
theorem exists_normalized_support_fraction_iff_exists_booleanMobiusCarry
    (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U := by
  constructor
  · rintro ⟨A, hzero, hpos, hvalue⟩
    obtain ⟨U, cert, _⟩ :=
      exists_booleanMobiusCarry_of_support_fraction
        A hzero hpos p q hq hvalue
    exact ⟨U, cert⟩
  · rintro ⟨U, cert⟩
    let A := booleanMobiusSupport (carryQuotientAF q U)
    have hpair : 0 ∉ A ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ) := by
      simpa [A] using support_fraction_of_booleanMobiusCarry p q hq U cert
    have hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A := by
      by_contra hnone
      have hnone' : ∀ a : ℕ, 0 < a → a ∉ A := by
        intro a ha haA
        exact hnone ⟨a, ha, haA⟩
      have hAempty : A = ∅ := by
        ext n
        constructor
        · intro hnA
          have hnpos : 0 < n := by
            change 0 < n ∧
              (ArithmeticFunction.moebius * carryQuotientAF q U) n = 1 at hnA
            exact hnA.1
          exact False.elim (hnone' n hnpos hnA)
        · simp
      have hvalue := hpair.2
      rw [hAempty] at hvalue
      have hzeroValue : (0 : ℝ) = (p : ℝ) / (q : ℝ) := by
        simpa [erdosSupportSeries] using hvalue
      have hq0 : (q : ℝ) ≠ 0 := by positivity
      have hpcast : (p : ℝ) = 0 := by
        field_simp [hq0] at hzeroValue
        linarith
      have hpzero : p = 0 := by exact_mod_cast hpcast
      have hppos : 0 < p := by
        rw [← cert.initial]
        exact cert.positive 0
      omega
    exact ⟨A, hpair.1, hpos, hpair.2⟩

/-! ## Exact regression fixture: `A = {2,3}` -/

/-- The two-point support used in the formal development.s explicit orbit check. -/
def support23 : Set ℕ := {2, 3}

/-- The positive-index coefficient `f_{\{2,3\}}`, represented by its six
residue values.  Its value at zero is a table convenience and is never used
as an arithmetic-function value. -/
def supportCoeff23Residue (n : ℕ) : ℕ :=
  match n % 6 with
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | _ => 0

/-- The formal development.s pure period-six numerator orbit. -/
def carryOrbit23 (N : ℕ) : ℤ :=
  match N % 6 with
  | 0 => 10
  | 1 => 20
  | 2 => 19
  | 3 => 17
  | 4 => 13
  | _ => 26

private theorem mod_six_cases (n : ℕ) :
    n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨
      n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
  have h := Nat.mod_lt n (by norm_num : 0 < 6)
  omega

/-- Residue form equals the expected pair of divisibility indicators. -/
theorem supportCoeff23Residue_eq_divisibility (n : ℕ) :
    supportCoeff23Residue n =
      (if 2 ∣ n then 1 else 0) + (if 3 ∣ n then 1 else 0) := by
  rcases mod_six_cases n with h | h | h | h | h | h <;>
    simp [supportCoeff23Residue, h, Nat.dvd_iff_mod_eq_zero] <;>
    split_ifs <;> omega

/-- The residue table is not an auxiliary model: on positive integers it
is exactly the kernel's `supportCoeff` for `{2,3}`. -/
theorem supportCoeff_support23_eq_residue {n : ℕ} (hn : 0 < n) :
    supportCoeff support23 n = supportCoeff23Residue n := by
  classical
  unfold supportCoeff
  rw [Finset.card_filter]
  have hpoint : ∀ d : ℕ,
      (if d ∈ support23 then 1 else 0) =
        (if d = 2 then 1 else 0) + (if d = 3 then 1 else 0) := by
    intro d
    simp only [support23, Set.mem_insert_iff, Set.mem_singleton_iff]
    split_ifs <;> omega
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq',
    supportCoeff23Residue_eq_divisibility n]
  simp [Nat.mem_divisors, hn.ne']

/-- Exact value of the support series: `1/3 + 1/7 = 10/21`. -/
theorem erdosSupportSeries_support23_eq_ten_div_twenty_one :
    erdosSupportSeries 2 support23 = (10 : ℝ) / 21 := by
  unfold erdosSupportSeries
  rw [tsum_eq_sum (s := {2, 3})]
  · norm_num [support23, Set.indicator]
  · intro b hb
    rw [Set.indicator_of_notMem]
    simpa [support23] using hb

/-- The six listed orbit values, in their unambiguous order `U₀,...,U₅`. -/
theorem carryOrbit23_initial_cycle :
    carryOrbit23 0 = 10 ∧ carryOrbit23 1 = 20 ∧
      carryOrbit23 2 = 19 ∧ carryOrbit23 3 = 17 ∧
      carryOrbit23 4 = 13 ∧ carryOrbit23 5 = 26 := by
  norm_num [carryOrbit23]

/-- The orbit is purely periodic with period six. -/
theorem carryOrbit23_periodic (N : ℕ) :
    carryOrbit23 (N + 6) = carryOrbit23 N := by
  simp [carryOrbit23]

/-- Uniform positive bounds for the explicit orbit. -/
theorem carryOrbit23_bounds (N : ℕ) :
    10 ≤ carryOrbit23 N ∧ carryOrbit23 N ≤ 26 := by
  rcases mod_six_cases N with h | h | h | h | h | h <;>
    simp [carryOrbit23, h]

/-- Exact carry recurrence for the explicit orbit. -/
theorem carryOrbit23_recurrence (N : ℕ) :
    carryOrbit23 (N + 1) =
      2 * carryOrbit23 N -
        ((21 * supportCoeff support23 (N + 1) : ℕ) : ℤ) := by
  rw [supportCoeff_support23_eq_residue (by omega : 0 < N + 1)]
  rcases mod_six_cases N with h | h | h | h | h | h
  · have hs : (N + 1) % 6 = 1 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 2 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 3 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 4 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 5 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]
  · have hs : (N + 1) % 6 = 0 := by omega
    simp [carryOrbit23, supportCoeff23Residue, h, hs]

/-- The explicit six-cycle is a genuine tempered integer carry orbit, not
merely a finite recurrence check. -/
theorem carryOrbit23_isTempered :
    IsTemperedBinaryOrbit (supportCoeff support23) 21 carryOrbit23 := by
  refine ⟨carryOrbit23_recurrence, ?_⟩
  have hlim : Tendsto (fun N : ℕ ↦ (26 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N ↦ ?_)
    (Filter.Eventually.of_forall fun N ↦ ?_)
    hlim
  · apply div_nonneg
    · have h : (0 : ℤ) ≤ carryOrbit23 N :=
        le_trans (by norm_num) (carryOrbit23_bounds N).1
      exact_mod_cast h
    · positivity
  · apply div_le_div_of_nonneg_right
    · exact_mod_cast (carryOrbit23_bounds N).2
    · positivity

/-- The displayed fraction is reduced. -/
theorem ten_coprime_twenty_one : Nat.Coprime 10 21 := by norm_num

/-- Exact divisibility of every difference in the explicit six-cycle. -/
theorem twenty_one_dvd_carryOrbit23_difference (N : ℕ) :
    (21 : ℤ) ∣ 2 * carryOrbit23 N - carryOrbit23 (N + 1) :=
  denominator_dvd_temperedCarry_difference
    support23 21 carryOrbit23 carryOrbit23_isTempered N

/-- Exact quotient recovery in the explicit six-cycle. -/
theorem carryOrbit23_quotient_eq_supportCoeff (N : ℕ) :
    (2 * carryOrbit23 N - carryOrbit23 (N + 1)) / (21 : ℤ) =
      (supportCoeff support23 (N + 1) : ℤ) :=
  temperedCarry_quotient_eq_supportCoeff
    support23 21 (by norm_num) carryOrbit23 carryOrbit23_isTempered N

/-- The explicit quotient's Möbius transform recovers exactly `{2,3}`. -/
theorem mobius_carryOrbit23_recovers_support :
    {n : ℕ |
      (ArithmeticFunction.moebius * carryQuotientAF 21 carryOrbit23) n = 1} =
        support23 := by
  apply mobius_carryQuotient_recovers_support
    support23 (by norm_num [support23]) 21 (by norm_num)
      carryOrbit23 carryOrbit23_isTempered

/-- The analytic scaled-tail identity behind the six-cycle. -/
theorem carryOrbit23_eq_twenty_one_mul_tail (N : ℕ) :
    (carryOrbit23 N : ℝ) =
      21 * binaryCoeffTail (supportCoeff support23) N :=
  temperedBinaryOrbit_eq_scaledTail
    (supportCoeff support23) (supportCoeff_le_self support23)
      carryOrbit23_isTempered N

/-- The explicit orbit satisfies the sharp positive square-root strip. -/
theorem carryOrbit23_positive_and_sqrt_bounded (N : ℕ) :
    0 < carryOrbit23 N ∧
      (carryOrbit23 N : ℝ) ≤ 21 * (2 * Real.sqrt (N : ℝ) + 4) := by
  constructor
  · have h := (carryOrbit23_bounds N).1
    omega
  · exact temperedCarry_le_denominator_mul_two_sqrt_add_four
      support23 21 carryOrbit23 carryOrbit23_isTempered N

/-! ## The prescribed point `1/21`

The visible-lattice identity supplies `1/21` with non-Boolean primitive
multiplicities.  The definitions below instead attach the existing affine
Lambert carry directly to the Boolean greedy support.  This exposes the exact
remaining endpoint: the carry is nonnegative at every depth, and any
subexponential upper bound makes it tempered and therefore proves that the
greedy support has value `1/21`.

This section does not assume that the greedy orbit survives.  In particular,
the nonnegativity theorem is an unconditional one-sided carry estimate, while
the subexponential bound remains the open arithmetic obligation.
-/

/-- The first `N` binary Lambert coefficients, before carrying. -/
noncomputable def binaryCoeffPrefix (c : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | N + 1 =>
      binaryCoeffPrefix c N + (c (N + 1) : ℝ) / (2 : ℝ) ^ (N + 1)

/-- Integer numerator of the same dyadic prefix at denominator `2^N`. -/
def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)

/-- Natural-valued membership bit of a support.  Unlike `supportCoeff`, this
is the actual binary word used by the dyadic-correction fixed point. -/
noncomputable def supportMembershipBit (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact if n ∈ A then 1 else 0

theorem supportMembershipBit_le_one (A : Set ℕ) (n : ℕ) :
    supportMembershipBit A n ≤ 1 := by
  classical
  unfold supportMembershipBit
  split <;> omega

theorem supportMembershipBit_eq_zero_iff (A : Set ℕ) (n : ℕ) :
    supportMembershipBit A n = 0 ↔ n ∉ A := by
  classical
  simp [supportMembershipBit]

theorem supportMembershipBit_eq_one_iff (A : Set ℕ) (n : ℕ) :
    supportMembershipBit A n = 1 ↔ n ∈ A := by
  classical
  simp [supportMembershipBit]

/-- Dyadic numerator of the actual support word through depth `N`. -/
noncomputable def supportDyadicPrefixNumerator (A : Set ℕ) (N : ℕ) : ℕ :=
  binaryCoeffPrefixNumerator (supportMembershipBit A) N

/-- The recursive numerator really represents `binaryCoeffPrefix` at the
common dyadic denominator. -/
theorem binaryCoeffPrefixNumerator_div_pow
    (c : ℕ → ℕ) :
    ∀ N : ℕ,
      (binaryCoeffPrefixNumerator c N : ℝ) / (2 : ℝ) ^ N =
        binaryCoeffPrefix c N := by
  intro N
  induction N with
  | zero => simp [binaryCoeffPrefixNumerator, binaryCoeffPrefix]
  | succ N ih =>
      rw [binaryCoeffPrefixNumerator, binaryCoeffPrefix, pow_succ]
      push_cast
      have hpow : (2 : ℝ) ^ N ≠ 0 := by positivity
      field_simp [hpow] at ih ⊢
      linarith

/-- If a binary prefix numerator has `r` trailing zero bits, then its final
`r` coefficients vanish.  This is the exact arithmetic bridge from a large
two-adic boundary valuation in the correction iteration to a long skipped
block in the underlying support word. -/
theorem binaryCoeffPrefixNumerator_terminal_zero_of_pow_two_dvd
    (c : ℕ → ℕ) (hbit : ∀ n : ℕ, c n ≤ 1) :
    ∀ {N r : ℕ}, r ≤ N →
      2 ^ r ∣ binaryCoeffPrefixNumerator c N →
      ∀ n : ℕ, N - r < n → n ≤ N → c n = 0 := by
  intro N r hr hdiv
  induction r generalizing N with
  | zero =>
      intro n hn
      omega
  | succ r ih =>
      have hNpos : 0 < N := by omega
      have htwo : 2 ∣ binaryCoeffPrefixNumerator c N := by
        exact dvd_trans (pow_dvd_pow 2 (by omega : 1 ≤ r + 1)) hdiv
      have hcNmod :
          c N % 2 = 0 := by
        rw [show N = (N - 1) + 1 by omega,
          binaryCoeffPrefixNumerator, Nat.dvd_iff_mod_eq_zero] at htwo
        simpa [show N - 1 + 1 = N by omega, Nat.add_mod] using htwo
      have hcN : c N = 0 := by
        have hcNle := hbit N
        omega
      have hprev :
          2 ^ r ∣ binaryCoeffPrefixNumerator c (N - 1) := by
        have hdiv' :
            2 ^ (r + 1) ∣
              2 * binaryCoeffPrefixNumerator c (N - 1) := by
          rw [show N = (N - 1) + 1 by omega,
            binaryCoeffPrefixNumerator,
            show N - 1 + 1 = N by omega, hcN, add_zero] at hdiv
          exact hdiv
        have hcancel :
            2 * 2 ^ r ∣
              2 * binaryCoeffPrefixNumerator c (N - 1) := by
          simpa only [pow_succ, Nat.mul_comm] using hdiv'
        exact
          (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hcancel
      intro n hnlo hnhi
      by_cases hnN : n = N
      · simpa [hnN] using hcN
      · apply ih (N := N - 1) (by omega) hprev n
        · omega
        · omega

/-- If `2^r` divides one plus a binary prefix numerator, its final `r`
coefficients are all one.  This is the right-boundary companion to
`binaryCoeffPrefixNumerator_terminal_zero_of_pow_two_dvd`. -/
theorem binaryCoeffPrefixNumerator_terminal_one_of_pow_two_dvd_succ
    (c : ℕ → ℕ) (hbit : ∀ n : ℕ, c n ≤ 1) :
    ∀ {N r : ℕ}, r ≤ N →
      2 ^ r ∣ binaryCoeffPrefixNumerator c N + 1 →
      ∀ n : ℕ, N - r < n → n ≤ N → c n = 1 := by
  intro N r hr hdiv
  induction r generalizing N with
  | zero =>
      intro n hn
      omega
  | succ r ih =>
      have hNpos : 0 < N := by omega
      have htwo :
          2 ∣ binaryCoeffPrefixNumerator c N + 1 := by
        exact dvd_trans (pow_dvd_pow 2 (by omega : 1 ≤ r + 1)) hdiv
      have hcNmod :
          (c N + 1) % 2 = 0 := by
        rw [show N = (N - 1) + 1 by omega,
          binaryCoeffPrefixNumerator, Nat.dvd_iff_mod_eq_zero] at htwo
        simpa [show N - 1 + 1 = N by omega, Nat.add_mod] using htwo
      have hcN : c N = 1 := by
        have hcNle := hbit N
        omega
      have hprev :
          2 ^ r ∣ binaryCoeffPrefixNumerator c (N - 1) + 1 := by
        have hdiv' :
            2 ^ (r + 1) ∣
              2 * (binaryCoeffPrefixNumerator c (N - 1) + 1) := by
          rw [show N = (N - 1) + 1 by omega,
            binaryCoeffPrefixNumerator,
            show N - 1 + 1 = N by omega, hcN] at hdiv
          convert hdiv using 1 <;> omega
        have hcancel :
            2 * 2 ^ r ∣
              2 * (binaryCoeffPrefixNumerator c (N - 1) + 1) := by
          simpa only [pow_succ, Nat.mul_comm] using hdiv'
        exact
          (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hcancel
      intro n hnlo hnhi
      by_cases hnN : n = N
      · simpa [hnN] using hcN
      · apply ih (N := N - 1) (by omega) hprev n
        · omega
        · omega

/-- Conversely, a zero terminal block contributes an explicit power of two
to the binary prefix numerator. -/
theorem binaryCoeffPrefixNumerator_pow_two_dvd_of_terminal_zero
    (c : ℕ → ℕ) :
    ∀ {N r : ℕ}, r ≤ N →
      (∀ n : ℕ, N - r < n → n ≤ N → c n = 0) →
      2 ^ r ∣ binaryCoeffPrefixNumerator c N := by
  intro N r hr hzero
  induction r generalizing N with
  | zero =>
      simp
  | succ r ih =>
      have hNpos : 0 < N := by omega
      have hcN : c N = 0 := hzero N (by omega) le_rfl
      have hprevZero :
          ∀ n : ℕ, (N - 1) - r < n → n ≤ N - 1 → c n = 0 := by
        intro n hnlo hnhi
        exact hzero n (by omega) (by omega)
      have hprev :
          2 ^ r ∣ binaryCoeffPrefixNumerator c (N - 1) :=
        ih (N := N - 1) (by omega) hprevZero
      rcases hprev with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [show N = (N - 1) + 1 by omega,
        binaryCoeffPrefixNumerator,
        show N - 1 + 1 = N by omega, hcN, add_zero, ht, pow_succ]
      ring

/-- Divisibility of a support-word numerator by `2^r` means that the final
`r` membership bits are all zero. -/
theorem supportDyadicPrefixNumerator_terminal_gap_of_pow_two_dvd
    (A : Set ℕ) {N r : ℕ} (hr : r ≤ N)
    (hdiv : 2 ^ r ∣ supportDyadicPrefixNumerator A N) :
    ∀ n : ℕ, N - r < n → n ≤ N → n ∉ A := by
  intro n hnlo hnhi
  rw [← supportMembershipBit_eq_zero_iff]
  exact binaryCoeffPrefixNumerator_terminal_zero_of_pow_two_dvd
    (supportMembershipBit A) (supportMembershipBit_le_one A)
    hr hdiv n hnlo hnhi

/-- Divisibility of one plus a support-word numerator by `2^r` means that
the final `r` membership bits are all selected. -/
theorem supportDyadicPrefixNumerator_terminal_full_of_pow_two_dvd_succ
    (A : Set ℕ) {N r : ℕ} (hr : r ≤ N)
    (hdiv : 2 ^ r ∣ supportDyadicPrefixNumerator A N + 1) :
    ∀ n : ℕ, N - r < n → n ≤ N → n ∈ A := by
  intro n hnlo hnhi
  rw [← supportMembershipBit_eq_one_iff]
  exact binaryCoeffPrefixNumerator_terminal_one_of_pow_two_dvd_succ
    (supportMembershipBit A) (supportMembershipBit_le_one A)
    hr hdiv n hnlo hnhi

/-- Exact support-word form: an empty doubling block is equivalent to `K`
trailing zero bits in the depth-`2*K` dyadic numerator. -/
theorem supportDyadicPrefixNumerator_empty_doublingBlock_iff
    (A : Set ℕ) (K : ℕ) :
    (∀ n : ℕ, K < n → n ≤ 2 * K → n ∉ A) ↔
      2 ^ K ∣ supportDyadicPrefixNumerator A (2 * K) := by
  constructor
  · intro hgap
    apply binaryCoeffPrefixNumerator_pow_two_dvd_of_terminal_zero
      (supportMembershipBit A) (by omega)
    intro n hnlo hnhi
    rw [supportMembershipBit_eq_zero_iff]
    exact hgap n (by omega) hnhi
  · intro hdiv n hKn hn2K
    exact
      supportDyadicPrefixNumerator_terminal_gap_of_pow_two_dvd
        A (N := 2 * K) (r := K) (by omega) hdiv n (by omega) hn2K

/-- Exact prefix/tail decomposition of the binary Lambert series. -/
theorem binaryCoeffSeries_eq_prefix_add_tail
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ∀ N : ℕ,
      binaryCoeffSeries c =
        binaryCoeffPrefix c N + binaryCoeffTail c N / (2 : ℝ) ^ N := by
  intro N
  induction N with
  | zero => simp [binaryCoeffPrefix]
  | succ N ih =>
      rw [binaryCoeffPrefix, binaryCoeffTail_succ c hgrowth N, ih]
      simp only [pow_succ]
      ring

/-- Restricting a support above `M` leaves its binary prefix through `N ≤ M`
unchanged. -/
theorem binaryCoeffPrefix_supportCoeff_inter_Iic_eq
    (A : Set ℕ) {N M : ℕ} (hNM : N ≤ M) :
    binaryCoeffPrefix (supportCoeff (A ∩ Set.Iic M)) N =
      binaryCoeffPrefix (supportCoeff A) N := by
  induction N with
  | zero => simp [binaryCoeffPrefix]
  | succ N ih =>
      rw [binaryCoeffPrefix, binaryCoeffPrefix, ih (by omega),
        supportCoeff_inter_Iic_eq_of_le A hNM]

/-- The support value cut off at exponent `N` is exactly its displayed
finite prefix. -/
theorem positiveMersenneSupportValue_inter_Iic_eq_prefix
    (A : Set ℕ) (N : ℕ) :
    positiveMersenneSupportValue (A ∩ Set.Iic N) =
      ∑ k ∈ Finset.range N, Set.indicator A mersenneWeight (k + 1) := by
  rw [positiveMersenneSupportValue_eq_prefix_add_suffix
    (A ∩ Set.Iic N) N]
  have hsuffix :
      positiveMersenneSupportSuffix (A ∩ Set.Iic N) N = 0 := by
    unfold positiveMersenneSupportSuffix
    have hzero :
        (fun k : ℕ =>
          Set.indicator (A ∩ Set.Iic N) mersenneWeight (N + k + 1)) =
            fun _ => 0 := by
      funext k
      rw [Set.indicator_of_notMem]
      simp
    rw [hzero]
    simp
  rw [hsuffix, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k + 1 ≤ N := by
    simpa using Finset.mem_range.mp hk
  by_cases hA : k + 1 ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem
        (show k + 1 ∈ A ∩ Set.Iic N from ⟨hA, hkN⟩)]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem]
    simp [hA]

/-- The binary Lambert prefix generated by the first `N` greedy choices is
bounded by the target.  This is the analytic source of the unconditional
one-sided carry estimate. -/
theorem binaryCoeffPrefix_greedySupport_le
    {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    binaryCoeffPrefix (supportCoeff (greedyMersenneSupport x)) N ≤ x := by
  let A := greedyMersenneSupport x
  let AN := A ∩ Set.Iic N
  have hprefix :
      binaryCoeffPrefix (supportCoeff A) N =
        binaryCoeffPrefix (supportCoeff AN) N := by
    symm
    exact binaryCoeffPrefix_supportCoeff_inter_Iic_eq A le_rfl
  have htail := binaryCoeffTail_nonneg (supportCoeff AN) N
  have hprefix_le_series :
      binaryCoeffPrefix (supportCoeff AN) N ≤
        binaryCoeffSeries (supportCoeff AN) := by
    rw [binaryCoeffSeries_eq_prefix_add_tail
      (supportCoeff AN) (supportCoeff_le_self AN) N]
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
    exact le_add_of_nonneg_right (div_nonneg htail hpow)
  have hseries :
      binaryCoeffSeries (supportCoeff AN) =
        ∑ k ∈ Finset.range N,
          Set.indicator A mersenneWeight (k + 1) := by
    rw [← erdosSupportSeries_two_eq_binaryCoeffSeries AN,
      ← positiveMersenneSupportValue_eq_erdosSupportSeries AN,
      positiveMersenneSupportValue_inter_Iic_eq_prefix A N]
  have hgreedy := greedyMersenne_prefix_add_remainder x N
  have hrem := greedyMersenneRemainder_nonneg hx N
  change x =
      (∑ k ∈ Finset.range N,
        Set.indicator A mersenneWeight (k + 1)) +
          greedyMersenneRemainder x N at hgreedy
  change binaryCoeffPrefix (supportCoeff A) N ≤ x
  rw [hprefix]
  rw [hseries] at hprefix_le_series
  linarith

/-- The scaled future-multiple tail generated by the first `N` choices of
the denominator-`21` greedy support.  Truncating the support is essential:
this quantity is determined at depth `N`, without assuming any future
greedy decisions or achievement-set membership. -/
noncomputable def twentyOneGreedyFinitePrefixTail (N : ℕ) : ℝ :=
  binaryCoeffTail
    (supportCoeff
      (greedyMersenneSupport (1 / 21 : ℝ) ∩ Set.Iic N)) N

/-- The canonical denominator-`21` carry driven by the greedy support of
`1/21`. -/
noncomputable def twentyOneGreedyCarry (N : ℕ) : ℤ :=
  affineBinaryOrbit
    (fun n : ℕ =>
      ((21 * supportCoeff
        (greedyMersenneSupport (1 / 21 : ℝ)) n : ℕ) : ℤ))
    1 N

@[simp] theorem twentyOneGreedyCarry_zero :
    twentyOneGreedyCarry 0 = 1 := rfl

/-- Exact carry recurrence. -/
theorem twentyOneGreedyCarry_succ (N : ℕ) :
    twentyOneGreedyCarry (N + 1) =
      2 * twentyOneGreedyCarry N -
        ((21 * supportCoeff
          (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) : ℕ) : ℤ) := rfl

/-- The denominator-`21` carry divided by its binary place value is
antitone.  This is the mechanism which turns cofinally many small returns
into a global limit theorem. -/
theorem scaled_twentyOneGreedyCarry_antitone :
    Antitone (fun N : ℕ =>
      (twentyOneGreedyCarry N : ℝ) / (2 : ℝ) ^ N) := by
  apply antitone_nat_of_succ_le
  intro N
  rw [twentyOneGreedyCarry_succ, pow_succ]
  push_cast
  calc
    (2 * (twentyOneGreedyCarry N : ℝ) -
          (21 * supportCoeff
            (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) : ℝ)) /
        ((2 : ℝ) ^ N * 2) =
      (twentyOneGreedyCarry N : ℝ) / (2 : ℝ) ^ N -
        (21 * supportCoeff
          (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) : ℝ) /
            ((2 : ℝ) ^ N * 2) := by ring
    _ ≤ (twentyOneGreedyCarry N : ℝ) / (2 : ℝ) ^ N :=
      sub_le_self _ (by positivity)

/-- Closed finite-prefix formula for an affine support carry. -/
theorem affineSupportCarry_eq_pow_mul_prefixResidual
    (A : Set ℕ) (p : ℤ) (q N : ℕ) :
    (affineBinaryOrbit
        (fun n : ℕ => ((q * supportCoeff A n : ℕ) : ℤ)) p N : ℝ) =
      (2 : ℝ) ^ N *
        ((p : ℝ) - (q : ℝ) *
          binaryCoeffPrefix (supportCoeff A) N) := by
  induction N with
  | zero => simp [binaryCoeffPrefix]
  | succ N ih =>
      rw [affineBinaryOrbit_succ, Int.cast_sub, Int.cast_mul,
        Int.cast_ofNat, ih, binaryCoeffPrefix]
      push_cast
      simp only [pow_succ]
      field_simp
      ring

/-- **Exact defect/remainder bridge before taking a limit.**  The
denominator-`21` carry is the sum of two nonnegative depth-`N` quantities:
the actual greedy remainder scaled by `2^N`, and the future-multiple tail
generated by the already selected finite prefix.  No survival, tempering,
or future-support hypothesis is used. -/
theorem twentyOneGreedyCarry_eq_scaled_remainder_add_finitePrefixTail
    (N : ℕ) :
    (twentyOneGreedyCarry N : ℝ) =
      21 * ((2 : ℝ) ^ N *
          greedyMersenneRemainder (1 / 21 : ℝ) N +
        twentyOneGreedyFinitePrefixTail N) := by
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  let AN := A ∩ Set.Iic N
  have hprefixValue :
      (∑ k ∈ Finset.range N,
          Set.indicator A mersenneWeight (k + 1)) =
        binaryCoeffPrefix (supportCoeff A) N +
          binaryCoeffTail (supportCoeff AN) N / (2 : ℝ) ^ N := by
    calc
      (∑ k ∈ Finset.range N,
          Set.indicator A mersenneWeight (k + 1)) =
          positiveMersenneSupportValue AN := by
            exact
              (positiveMersenneSupportValue_inter_Iic_eq_prefix A N).symm
      _ = erdosSupportSeries 2 AN :=
            positiveMersenneSupportValue_eq_erdosSupportSeries AN
      _ = binaryCoeffSeries (supportCoeff AN) :=
            erdosSupportSeries_two_eq_binaryCoeffSeries AN
      _ = binaryCoeffPrefix (supportCoeff AN) N +
            binaryCoeffTail (supportCoeff AN) N / (2 : ℝ) ^ N :=
              binaryCoeffSeries_eq_prefix_add_tail
                (supportCoeff AN) (supportCoeff_le_self AN) N
      _ = binaryCoeffPrefix (supportCoeff A) N +
            binaryCoeffTail (supportCoeff AN) N / (2 : ℝ) ^ N := by
              rw [binaryCoeffPrefix_supportCoeff_inter_Iic_eq A le_rfl]
  have hgreedy :=
    greedyMersenne_prefix_add_remainder (1 / 21 : ℝ) N
  change
    (1 / 21 : ℝ) =
      (∑ k ∈ Finset.range N,
        Set.indicator A mersenneWeight (k + 1)) +
          greedyMersenneRemainder (1 / 21 : ℝ) N at hgreedy
  rw [hprefixValue] at hgreedy
  have hcarry :=
    affineSupportCarry_eq_pow_mul_prefixResidual A 1 21 N
  have hcarry' :
      (twentyOneGreedyCarry N : ℝ) =
        (2 : ℝ) ^ N *
          ((1 : ℝ) - 21 * binaryCoeffPrefix (supportCoeff A) N) := by
    simpa [twentyOneGreedyCarry, A] using hcarry
  rw [hcarry']
  change
    (2 : ℝ) ^ N *
        ((1 : ℝ) - 21 * binaryCoeffPrefix (supportCoeff A) N) =
      21 * ((2 : ℝ) ^ N *
          greedyMersenneRemainder (1 / 21 : ℝ) N +
        binaryCoeffTail (supportCoeff AN) N)
  have hpow : (2 : ℝ) ^ N ≠ 0 := by positivity
  field_simp [hpow] at hgreedy
  nlinarith

/-- The finite-prefix divisor tail is nonnegative at every depth. -/
theorem twentyOneGreedyFinitePrefixTail_nonneg (N : ℕ) :
    0 ≤ twentyOneGreedyFinitePrefixTail N :=
  binaryCoeffTail_nonneg _ N

/-- The universal divisor-pair estimate applies to the finite-prefix tail
without any information about future greedy choices. -/
theorem twentyOneGreedyFinitePrefixTail_le_two_sqrt_add_four (N : ℕ) :
    twentyOneGreedyFinitePrefixTail N ≤
      2 * Real.sqrt (N : ℝ) + 4 :=
  binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    (greedyMersenneSupport (1 / 21 : ℝ) ∩ Set.Iic N) N

/-- Exact integer form of the affine-prefix identity. -/
theorem affineSupportCarry_eq_pow_sub_prefixNumerator
    (A : Set ℕ) (p : ℤ) (q N : ℕ) :
    affineBinaryOrbit
        (fun n : ℕ => ((q * supportCoeff A n : ℕ) : ℤ)) p N =
      (2 : ℤ) ^ N * p -
        (q : ℤ) * (binaryCoeffPrefixNumerator (supportCoeff A) N : ℤ) := by
  induction N with
  | zero => simp [binaryCoeffPrefixNumerator]
  | succ N ih =>
      rw [affineBinaryOrbit_succ, ih, binaryCoeffPrefixNumerator, pow_succ]
      push_cast
      ring

/-- **Unconditional all-depth estimate.**  The denominator-`21` greedy carry
is nonnegative at every depth.  Equivalently, the signed periodic-bit carry
used in the Booleanisation search is nonpositive at every depth. -/
theorem twentyOneGreedyCarry_nonneg (N : ℕ) :
    0 ≤ twentyOneGreedyCarry N := by
  have hprefix :=
    binaryCoeffPrefix_greedySupport_le
      (x := (1 / 21 : ℝ)) (by norm_num) N
  have hid := affineSupportCarry_eq_pow_mul_prefixResidual
    (greedyMersenneSupport (1 / 21 : ℝ)) 1 21 N
  have hid' :
      (twentyOneGreedyCarry N : ℝ) =
      (2 : ℝ) ^ N *
        ((1 : ℝ) - 21 *
          binaryCoeffPrefix
            (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))) N) := by
    simpa [twentyOneGreedyCarry] using hid
  have hfactor :
      (0 : ℝ) ≤ 1 - 21 *
        binaryCoeffPrefix
          (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))) N := by
    linarith
  have hreal : (0 : ℝ) ≤ twentyOneGreedyCarry N := by
    rw [hid']
    exact mul_nonneg (by positivity) hfactor
  exact_mod_cast hreal

/-- The displayed greedy Lambert numerator lies below the integral quotient
`⌊2^N / 21⌋`.  This isolates the exact natural-number subtraction hidden in
the denominator-`21` carry. -/
theorem twentyOneGreedyPrefixNumerator_le_div (N : ℕ) :
    binaryCoeffPrefixNumerator
        (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))) N
      ≤ 2 ^ N / 21 := by
  let c := supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))
  let P := binaryCoeffPrefixNumerator c N
  have hprefix :=
    binaryCoeffPrefix_greedySupport_le
      (x := (1 / 21 : ℝ)) (by norm_num) N
  have hnum := binaryCoeffPrefixNumerator_div_pow c N
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hnum_le : 21 * P ≤ 2 ^ N := by
    have hreal : (21 : ℝ) * (P : ℝ) ≤ (2 : ℝ) ^ N := by
      change
        (21 : ℝ) *
            (binaryCoeffPrefixNumerator
              (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))) N : ℝ)
          ≤ (2 : ℝ) ^ N
      change
        (binaryCoeffPrefixNumerator c N : ℝ) / (2 : ℝ) ^ N =
          binaryCoeffPrefix c N at hnum
      change binaryCoeffPrefix c N ≤ (1 / 21 : ℝ) at hprefix
      have hnum_eq :
          (binaryCoeffPrefixNumerator c N : ℝ) =
            (2 : ℝ) ^ N * binaryCoeffPrefix c N := by
        simpa [mul_comm] using
          (div_eq_iff (ne_of_gt hpowpos)).mp hnum
      rw [hnum_eq]
      nlinarith
    exact_mod_cast hreal
  change P ≤ 2 ^ N / 21
  omega

/-- The genuinely dynamical part of the denominator-`21` carry, after
removing the six-periodic residue of `2^N mod 21`.  Unlike the raw carry,
this coordinate starts at zero and is an ordinary natural number. -/
noncomputable def twentyOneGreedyDefect (N : ℕ) : ℕ :=
  2 ^ N / 21 -
    binaryCoeffPrefixNumerator
      (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))) N

/-- The next binary digit of the periodic rational baseline
`⌊2^N / 21⌋`, represented in an integer form that makes the defect
recurrence division-free. -/
def twentyOneFloorBit (N : ℕ) : ℤ :=
  ((2 ^ (N + 1) / 21 : ℕ) : ℤ) -
    2 * ((2 ^ N / 21 : ℕ) : ℤ)

/-- Cast form of the defect definition, with the natural subtraction
certified by the greedy prefix bound. -/
theorem twentyOneGreedyDefect_cast_eq (N : ℕ) :
    (twentyOneGreedyDefect N : ℤ) =
      ((2 ^ N / 21 : ℕ) : ℤ) -
        (binaryCoeffPrefixNumerator
          (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))) N : ℤ) := by
  have hle := twentyOneGreedyPrefixNumerator_le_div N
  change
    (((2 ^ N / 21 -
      binaryCoeffPrefixNumerator
        (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))) N : ℕ) : ℕ) : ℤ) =
      ((2 ^ N / 21 : ℕ) : ℤ) -
        (binaryCoeffPrefixNumerator
          (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))) N : ℤ)
  exact Nat.cast_sub hle

/-- The exact one-dimensional recurrence behind the certified computation.
The only nonperiodic input is the actual greedy divisor-count coefficient. -/
theorem twentyOneGreedyDefect_succ (N : ℕ) :
    (twentyOneGreedyDefect (N + 1) : ℤ) =
      2 * (twentyOneGreedyDefect N : ℤ) +
        twentyOneFloorBit N -
          (supportCoeff
            (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) : ℤ) := by
  rw [twentyOneGreedyDefect_cast_eq, twentyOneGreedyDefect_cast_eq,
    binaryCoeffPrefixNumerator]
  unfold twentyOneFloorBit
  push_cast
  ring

/-- The next denominator-`21` floor bit is the quotient of twice the
current period residue.  In particular it is a genuine binary digit. -/
theorem twentyOneFloorBit_eq_two_mul_mod_div (N : ℕ) :
    twentyOneFloorBit N =
      ((2 * (2 ^ N % 21) / 21 : ℕ) : ℤ) := by
  have hpow : 2 ^ (N + 1) = 2 * 2 ^ N := by
    rw [pow_succ]
    ring
  have hdecomp := Nat.mod_add_div (2 ^ N) 21
  have hquot :
      2 * 2 ^ N / 21 =
        2 * (2 ^ N / 21) + 2 * (2 ^ N % 21) / 21 := by
    omega
  unfold twentyOneFloorBit
  rw [hpow, hquot]
  push_cast
  ring

/-- The periodic denominator-`21` baseline contributes at most one unit in
each one-step defect transition. -/
theorem twentyOneFloorBit_le_one (N : ℕ) :
    twentyOneFloorBit N ≤ 1 := by
  rw [twentyOneFloorBit_eq_two_mul_mod_div]
  have hmod : 2 ^ N % 21 < 21 := Nat.mod_lt _ (by omega)
  have hbit : 2 * (2 ^ N % 21) / 21 ≤ 1 := by omega
  exact_mod_cast hbit

/-- Dropping the nonnegative divisor load from the exact recurrence gives
the universal one-step growth envelope for the natural defect. -/
theorem twentyOneGreedyDefect_succ_le (N : ℕ) :
    twentyOneGreedyDefect (N + 1) ≤
      2 * twentyOneGreedyDefect N + 1 := by
  have hrec := twentyOneGreedyDefect_succ N
  have hbit := twentyOneFloorBit_le_one N
  have hcoeff :
      (0 : ℤ) ≤
        (supportCoeff
          (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) : ℤ) := by
    positivity
  have hz :
      (twentyOneGreedyDefect (N + 1) : ℤ) ≤
        2 * (twentyOneGreedyDefect N : ℤ) + 1 := by
    omega
  exact_mod_cast hz

/-- Iterated one-step growth in a subtraction-free form.  The added unit
turns `Q ↦ 2Q+1` into pure dyadic multiplication. -/
theorem twentyOneGreedyDefect_add_one_le_pow_mul (N L : ℕ) :
    twentyOneGreedyDefect (N + L) + 1 ≤
      2 ^ L * (twentyOneGreedyDefect N + 1) := by
  induction L with
  | zero =>
      simp
  | succ L ih =>
      calc
        twentyOneGreedyDefect (N + (L + 1)) + 1 =
            twentyOneGreedyDefect ((N + L) + 1) + 1 := by
              congr 2
        _ ≤ 2 * twentyOneGreedyDefect (N + L) + 2 := by
              have hstep := twentyOneGreedyDefect_succ_le (N + L)
              omega
        _ = 2 * (twentyOneGreedyDefect (N + L) + 1) := by ring
        _ ≤ 2 * (2 ^ L * (twentyOneGreedyDefect N + 1)) :=
              Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (L + 1) * (twentyOneGreedyDefect N + 1) := by
              rw [pow_succ]
              ring

/-- The divisor load removed from the defect during the six ranks after
`N`.  The weights are the exact binary propagation weights in the iterated
defect recurrence. -/
noncomputable def twentyOneSixStepRepairLoad (N : ℕ) : ℕ :=
  32 * supportCoeff
      (greedyMersenneSupport (1 / 21 : ℝ)) (N + 1) +
    16 * supportCoeff
      (greedyMersenneSupport (1 / 21 : ℝ)) (N + 2) +
    8 * supportCoeff
      (greedyMersenneSupport (1 / 21 : ℝ)) (N + 3) +
    4 * supportCoeff
      (greedyMersenneSupport (1 / 21 : ℝ)) (N + 4) +
    2 * supportCoeff
      (greedyMersenneSupport (1 / 21 : ℝ)) (N + 5) +
    supportCoeff
      (greedyMersenneSupport (1 / 21 : ℝ)) (N + 6)

/-- Six periodic baseline bits telescope to three times the current
remainder modulo `21`.  This is the arithmetic reason that blocks of six
are the natural scale for the denominator-`21` defect. -/
theorem twentyOneFloorBit_six_weighted (N : ℕ) :
    32 * twentyOneFloorBit N +
        16 * twentyOneFloorBit (N + 1) +
        8 * twentyOneFloorBit (N + 2) +
        4 * twentyOneFloorBit (N + 3) +
        2 * twentyOneFloorBit (N + 4) +
        twentyOneFloorBit (N + 5) =
      3 * ((2 ^ N % 21 : ℕ) : ℤ) := by
  have hpow : 2 ^ (N + 6) = 64 * 2 ^ N := by
    rw [pow_add]
    norm_num
    omega
  have hmod :
      2 ^ (N + 6) % 21 = 2 ^ N % 21 := by
    rw [hpow, Nat.mul_mod]
    norm_num
  have hdecomp := Nat.mod_add_div (2 ^ N) 21
  have hdecompSix := Nat.mod_add_div (2 ^ (N + 6)) 21
  have hquot :
      2 ^ (N + 6) / 21 =
        64 * (2 ^ N / 21) + 3 * (2 ^ N % 21) := by
    omega
  have hquotZ :
      ((2 ^ (N + 6) / 21 : ℕ) : ℤ) =
        64 * ((2 ^ N / 21 : ℕ) : ℤ) +
          3 * ((2 ^ N % 21 : ℕ) : ℤ) := by
    exact_mod_cast hquot
  unfold twentyOneFloorBit
  rw [show N + 1 + 1 = N + 2 by omega,
    show N + 2 + 1 = N + 3 by omega,
    show N + 3 + 1 = N + 4 by omega,
    show N + 4 + 1 = N + 5 by omega,
    show N + 5 + 1 = N + 6 by omega]
  rw [hquotZ]
  push_cast
  ring

/-- Exact six-step defect dynamics.  The exponentially magnified old defect
is opposed by the actual weighted divisor load accumulated over the next
six greedy ranks. -/
theorem twentyOneGreedyDefect_add_six (N : ℕ) :
    (twentyOneGreedyDefect (N + 6) : ℤ) =
      64 * (twentyOneGreedyDefect N : ℤ) +
        3 * ((2 ^ N % 21 : ℕ) : ℤ) -
          (twentyOneSixStepRepairLoad N : ℤ) := by
  have h0 := twentyOneGreedyDefect_succ N
  have h1 := twentyOneGreedyDefect_succ (N + 1)
  have h2 := twentyOneGreedyDefect_succ (N + 2)
  have h3 := twentyOneGreedyDefect_succ (N + 3)
  have h4 := twentyOneGreedyDefect_succ (N + 4)
  have h5 := twentyOneGreedyDefect_succ (N + 5)
  have hbits := twentyOneFloorBit_six_weighted N
  norm_num [Nat.add_assoc] at h0 h1 h2 h3 h4 h5
  rw [h5, h4, h3, h2, h1, h0]
  unfold twentyOneSixStepRepairLoad
  push_cast at hbits ⊢
  linear_combination hbits

/-- A six-rank block contracts the defect to `Q_N + 1` exactly when its
weighted divisor load pays the full `63 Q_N` amplification plus the
periodic residue charge.  This is an iff, so the remaining frontier is a
finite-window load inequality rather than an opaque real approximation. -/
theorem twentyOneGreedyDefect_add_six_le_iff_repairLoad (N : ℕ) :
    twentyOneGreedyDefect (N + 6) ≤ twentyOneGreedyDefect N + 1 ↔
      63 * twentyOneGreedyDefect N +
          3 * (2 ^ N % 21) ≤
        twentyOneSixStepRepairLoad N + 1 := by
  have hrec := twentyOneGreedyDefect_add_six N
  constructor <;> intro h <;> omega

/-- The exact slope-aware form of the six-step recurrence.  Unlike the
translation-invariant contraction above, this spends all slack already
accumulated below `⌊N/6⌋`; exact computation shows that this distinction is
essential, since the translation-invariant contraction first fails at
`N = 73` while the slope envelope survives. -/
theorem twentyOneGreedyDefect_add_six_le_div_six_iff_repairLoad (N : ℕ) :
    twentyOneGreedyDefect (N + 6) ≤ (N + 6) / 6 ↔
      64 * twentyOneGreedyDefect N +
          3 * (2 ^ N % 21) ≤
        twentyOneSixStepRepairLoad N + N / 6 + 1 := by
  have hrec := twentyOneGreedyDefect_add_six N
  constructor <;> intro h <;> omega

/-- A rank is slope-dangerous precisely when the old defect and periodic
charge already exceed the next `⌊N/6⌋` allowance before any of the six
new divisor loads are credited.  At every other rank the desired slope
step is automatic. -/
def TwentyOneGreedyDefectSlopeDanger (N : ℕ) : Prop :=
  N / 6 + 1 <
    64 * twentyOneGreedyDefect N + 3 * (2 ^ N % 21)

/-- Outside the slope-danger region, nonnegativity of the repair load alone
closes the next six-rank slope step. -/
theorem twentyOneGreedyDefect_add_six_le_div_six_of_not_slopeDanger
    (N : ℕ) (hsafe : ¬ TwentyOneGreedyDefectSlopeDanger N) :
    twentyOneGreedyDefect (N + 6) ≤ (N + 6) / 6 := by
  apply
    (twentyOneGreedyDefect_add_six_le_div_six_iff_repairLoad N).2
  unfold TwentyOneGreedyDefectSlopeDanger at hsafe
  omega

/-- Every slope-dangerous rank is genuinely a high-defect rank.  Thus the
repair-load frontier is confined to `N < 384 Q_N + 354`; the vast
low-defect region needs no divisor arithmetic at all. -/
theorem twentyOneGreedyDefectSlopeDanger_rank_lt
    (N : ℕ) (hdanger : TwentyOneGreedyDefectSlopeDanger N) :
    N < 384 * twentyOneGreedyDefect N + 354 := by
  have hmod : 2 ^ N % 21 < 21 := Nat.mod_lt _ (by omega)
  have hrem : N % 6 < 6 := Nat.mod_lt _ (by omega)
  have hdecomp := Nat.mod_add_div N 6
  unfold TwentyOneGreedyDefectSlopeDanger at hdanger
  omega

/-- The sharp slope envelope now asks for repair load only at exact
slope-danger ranks.  This is strictly weaker than a false uniform block
contraction: safe ranks close from accumulated slack, while dangerous ranks
pay only the load actually needed to remain below `⌊(N+6)/6⌋`. -/
theorem twentyOneGreedyDefect_le_div_six_of_dangerRepairLoad
    (hbase : ∀ N : ℕ, N < 6 → twentyOneGreedyDefect N = 0)
    (hdanger : ∀ N : ℕ, TwentyOneGreedyDefectSlopeDanger N →
      64 * twentyOneGreedyDefect N +
          3 * (2 ^ N % 21) ≤
        twentyOneSixStepRepairLoad N + N / 6 + 1) :
    ∀ N : ℕ, twentyOneGreedyDefect N ≤ N / 6 := by
  intro N
  by_cases hN : N < 6
  · rw [hbase N hN]
    exact Nat.zero_le _
  · obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 6 := by
      exact ⟨N - 6, by omega⟩
    by_cases hK : TwentyOneGreedyDefectSlopeDanger K
    · exact
        (twentyOneGreedyDefect_add_six_le_div_six_iff_repairLoad K).2
          (hdanger K hK)
    · exact
        twentyOneGreedyDefect_add_six_le_div_six_of_not_slopeDanger K hK

/-- A slightly coarser but simpler producer may discharge the load inequality
only under the explicit high-defect condition `N < 384 Q_N + 354`. -/
theorem twentyOneGreedyDefect_le_div_six_of_highDefectRepairLoad
    (hbase : ∀ N : ℕ, N < 6 → twentyOneGreedyDefect N = 0)
    (hload : ∀ N : ℕ,
      N < 384 * twentyOneGreedyDefect N + 354 →
      64 * twentyOneGreedyDefect N +
          3 * (2 ^ N % 21) ≤
        twentyOneSixStepRepairLoad N + N / 6 + 1) :
    ∀ N : ℕ, twentyOneGreedyDefect N ≤ N / 6 := by
  apply twentyOneGreedyDefect_le_div_six_of_dangerRepairLoad hbase
  intro N hdanger
  exact hload N (twentyOneGreedyDefectSlopeDanger_rank_lt N hdanger)

/-- The block contraction plus the six initial rows implies the observed
global bound `Q_N ≤ ⌊N/6⌋`.  This separates the finite base certificate
from the repeating arithmetic obligation. -/
theorem twentyOneGreedyDefect_le_div_six_of_blockContraction
    (hbase : ∀ N : ℕ, N < 6 → twentyOneGreedyDefect N = 0)
    (hblock : ∀ N : ℕ,
      twentyOneGreedyDefect (N + 6) ≤ twentyOneGreedyDefect N + 1) :
    ∀ N : ℕ, twentyOneGreedyDefect N ≤ N / 6 := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hN : N < 6
      · rw [hbase N hN]
        omega
      · obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 6 := by
          exact ⟨N - 6, by omega⟩
        have hK := ih K (by omega)
        exact (hblock K).trans (by omega)

/-- A floor-slope contraction over a configurable block.  Exact
falsification shows that the smallest surviving block grows with the tested
horizon, so the block length is deliberately not hardcoded. -/
def TwentyOneGreedyDefectFloorSlopeBlockContraction (B : ℕ) : Prop :=
  ∀ N : ℕ,
    twentyOneGreedyDefect (N + B) ≤
      twentyOneGreedyDefect N + B / 6

/-- Any positive block divisible by six gives a valid induction scheme.
The finite base strip and the translation-invariant block contraction imply
the sharp all-depth `⌊N/6⌋` envelope. -/
theorem twentyOneGreedyDefect_le_div_six_of_floorSlopeBlockContraction
    {B : ℕ} (hBpos : 0 < B) (hBdiv : 6 ∣ B)
    (hbase : ∀ N : ℕ, N < B →
      twentyOneGreedyDefect N ≤ N / 6)
    (hblock : TwentyOneGreedyDefectFloorSlopeBlockContraction B) :
    ∀ N : ℕ, twentyOneGreedyDefect N ≤ N / 6 := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hN : N < B
      · exact hbase N hN
      · obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + B := by
          exact ⟨N - B, by omega⟩
        have hK := ih K (by omega)
        calc
          twentyOneGreedyDefect (K + B)
              ≤ twentyOneGreedyDefect K + B / 6 := hblock K
          _ ≤ K / 6 + B / 6 := by omega
          _ = (K + B) / 6 := (Nat.add_div_of_dvd_left hBdiv).symm

/-- The carry is at least the ordinary period-six remainder `2^N mod 21`.
This is the precise all-depth form of nonnegativity for the signed periodic
Lambert defect. -/
theorem twentyOneGreedyCarry_ge_pow_mod (N : ℕ) :
    ((2 ^ N % 21 : ℕ) : ℤ) ≤ twentyOneGreedyCarry N := by
  let c := supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))
  let P := binaryCoeffPrefixNumerator c N
  have hPdiv : P ≤ 2 ^ N / 21 := by
    simpa [P, c] using twentyOneGreedyPrefixNumerator_le_div N
  have hdecomp := Nat.mod_add_div (2 ^ N) 21
  have hid := affineSupportCarry_eq_pow_sub_prefixNumerator
    (greedyMersenneSupport (1 / 21 : ℝ)) 1 21 N
  have hid' :
    twentyOneGreedyCarry N =
      (2 : ℤ) ^ N -
        21 * (binaryCoeffPrefixNumerator c N : ℤ) := by
    simpa [twentyOneGreedyCarry, c] using hid
  have hPdivZ :
      (P : ℤ) ≤ ((2 ^ N / 21 : ℕ) : ℤ) := by
    exact_mod_cast hPdiv
  have hdecompZ :
      ((2 ^ N % 21 : ℕ) : ℤ) +
          21 * ((2 ^ N / 21 : ℕ) : ℤ) =
        (2 : ℤ) ^ N := by
    exact_mod_cast hdecomp
  rw [hid']
  omega

/-- Exact periodic-baseline decomposition.  All unboundedness questions are
therefore concentrated in the natural-valued defect `Q_N`; the residue term
is uniformly below `21`. -/
theorem twentyOneGreedyCarry_eq_mod_add_defect (N : ℕ) :
    twentyOneGreedyCarry N =
      ((2 ^ N % 21 : ℕ) : ℤ) +
        21 * (twentyOneGreedyDefect N : ℤ) := by
  let c := supportCoeff (greedyMersenneSupport (1 / 21 : ℝ))
  let P := binaryCoeffPrefixNumerator c N
  have hPdiv : P ≤ 2 ^ N / 21 := by
    simpa [P, c] using twentyOneGreedyPrefixNumerator_le_div N
  have hdef :
      (twentyOneGreedyDefect N : ℤ) =
        ((2 ^ N / 21 : ℕ) : ℤ) - (P : ℤ) := by
    change
      (((2 ^ N / 21 - P : ℕ) : ℕ) : ℤ) =
        ((2 ^ N / 21 : ℕ) : ℤ) - (P : ℤ)
    exact Nat.cast_sub hPdiv
  have hdecomp := Nat.mod_add_div (2 ^ N) 21
  have hdecompZ :
      ((2 ^ N % 21 : ℕ) : ℤ) +
          21 * ((2 ^ N / 21 : ℕ) : ℤ) =
        (2 : ℤ) ^ N := by
    exact_mod_cast hdecomp
  have hid := affineSupportCarry_eq_pow_sub_prefixNumerator
    (greedyMersenneSupport (1 / 21 : ℝ)) 1 21 N
  have hid' :
      twentyOneGreedyCarry N =
        (2 : ℤ) ^ N - 21 * (P : ℤ) := by
    simpa [twentyOneGreedyCarry, P, c] using hid
  rw [hid', hdef]
  omega

/-- Exact real decomposition of the defect coordinate.  The periodic
remainder fraction, the scaled actual greedy remainder, and the
finite-prefix divisor tail are now separated with no limiting argument. -/
theorem twentyOneGreedyDefect_add_mod_div_eq_scaled_remainder_add_tail
    (N : ℕ) :
    (twentyOneGreedyDefect N : ℝ) +
        ((2 ^ N % 21 : ℕ) : ℝ) / 21 =
      (2 : ℝ) ^ N *
          greedyMersenneRemainder (1 / 21 : ℝ) N +
        twentyOneGreedyFinitePrefixTail N := by
  have hcarry :=
    twentyOneGreedyCarry_eq_scaled_remainder_add_finitePrefixTail N
  have hdecomp := twentyOneGreedyCarry_eq_mod_add_defect N
  apply_fun (fun z : ℤ => (z : ℝ)) at hdecomp
  push_cast at hdecomp
  rw [hcarry] at hdecomp
  calc
    (twentyOneGreedyDefect N : ℝ) +
          ((2 ^ N % 21 : ℕ) : ℝ) / 21 =
        (((2 ^ N % 21 : ℕ) : ℝ) +
          21 * (twentyOneGreedyDefect N : ℝ)) / 21 := by ring
    _ = (21 * ((2 : ℝ) ^ N *
          greedyMersenneRemainder (1 / 21 : ℝ) N +
        twentyOneGreedyFinitePrefixTail N)) / 21 :=
      congrArg (fun x : ℝ => x / 21) hdecomp.symm
    _ = (2 : ℝ) ^ N *
          greedyMersenneRemainder (1 / 21 : ℝ) N +
        twentyOneGreedyFinitePrefixTail N := by ring

/-- A positive-index Mersenne weight occupies at most two units after
dyadic rescaling.  This deliberately keeps the sharp endpoint at rank one:
`2^N / (2^N - 1) ≤ 2`. -/
theorem two_pow_mul_mersenneWeight_le_two
    {N : ℕ} (hN : 0 < N) :
    (2 : ℝ) ^ N * mersenneWeight N ≤ 2 := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ N - 1 := by
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) hN.ne')
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
  rw [mersenneWeight, mul_one_div, div_le_iff₀ hden]
  linarith

/-- At every omitted greedy exponent, the denominator-`21` defect is only
square-root sized.  A skip leaves the remainder unchanged and strictly below
the omitted Mersenne weight; after dyadic rescaling this costs fewer than two
units.  The remaining defect is therefore confined to the universal
finite-prefix divisor tail. -/
theorem twentyOneGreedyDefect_lt_two_sqrt_add_six_of_skip
    {N : ℕ}
    (hskip :
      N ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ)) :
    (twentyOneGreedyDefect N : ℝ) <
      2 * Real.sqrt (N : ℝ) + 6 := by
  have hN : 0 < N := by
    exact Nat.pos_of_ne_zero
      (fun hzero => by
        subst N
        exact zero_not_mem_greedyMersenneSkippedSupport _ hskip)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hnot :
      ¬ mersenneWeight (n + 1) ≤
        greedyMersenneRemainder (1 / 21 : ℝ) n :=
    (succ_mem_greedyMersenneSkippedSupport_iff
      (1 / 21 : ℝ) n).1 hskip
  have hrem :
      greedyMersenneRemainder (1 / 21 : ℝ) (n + 1) =
        greedyMersenneRemainder (1 / 21 : ℝ) n := by
    rw [greedyMersenneRemainder_succ, if_neg hnot]
  have hremLt :
      greedyMersenneRemainder (1 / 21 : ℝ) (n + 1) <
        mersenneWeight (n + 1) := by
    rw [hrem]
    exact lt_of_not_ge hnot
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  have hscaledLtWeight :
      (2 : ℝ) ^ (n + 1) *
          greedyMersenneRemainder (1 / 21 : ℝ) (n + 1) <
        (2 : ℝ) ^ (n + 1) * mersenneWeight (n + 1) :=
    mul_lt_mul_of_pos_left hremLt hpowPos
  have hweightBound :=
    two_pow_mul_mersenneWeight_le_two (N := n + 1) (by omega)
  have hscaledLt :
      (2 : ℝ) ^ (n + 1) *
          greedyMersenneRemainder (1 / 21 : ℝ) (n + 1) < 2 :=
    hscaledLtWeight.trans_le hweightBound
  have hid :=
    twentyOneGreedyDefect_add_mod_div_eq_scaled_remainder_add_tail (n + 1)
  have htail :=
    twentyOneGreedyFinitePrefixTail_le_two_sqrt_add_four (n + 1)
  have hmod :
      (0 : ℝ) ≤ ((2 ^ (n + 1) % 21 : ℕ) : ℝ) / 21 := by positivity
  nlinarith

/-- A skip at rank `N` constrains the defect at every later rank `N+L`.
Consequently, a violation of this explicit dyadic-square-root envelope is a
certificate that the earlier rank was selected. -/
theorem twentyOneGreedyDefect_add_one_lt_pow_mul_sqrt_of_skip
    {N : ℕ} (L : ℕ)
    (hskip :
      N ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ)) :
    (twentyOneGreedyDefect (N + L) : ℝ) + 1 <
      (2 : ℝ) ^ L * (2 * Real.sqrt (N : ℝ) + 7) := by
  have hgrowth := twentyOneGreedyDefect_add_one_le_pow_mul N L
  have hgrowthR :
      (twentyOneGreedyDefect (N + L) : ℝ) + 1 ≤
        (2 : ℝ) ^ L * ((twentyOneGreedyDefect N : ℝ) + 1) := by
    exact_mod_cast hgrowth
  have hskipBound :=
    twentyOneGreedyDefect_lt_two_sqrt_add_six_of_skip hskip
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hscaled :
      (2 : ℝ) ^ L * ((twentyOneGreedyDefect N : ℝ) + 1) <
        (2 : ℝ) ^ L * (2 * Real.sqrt (N : ℝ) + 7) :=
    mul_lt_mul_of_pos_left (by linarith) hpowPos
  exact hgrowthR.trans_lt hscaled

/-- Large later defect forces selection at the earlier rank.  This is the
contrapositive interface used to turn defect growth into a certified long
selected run. -/
theorem mem_greedyMersenneSupport_of_defect_growth_threshold
    {N L : ℕ} (hN : 0 < N)
    (hlarge :
      (2 : ℝ) ^ L * (2 * Real.sqrt (N : ℝ) + 7) ≤
        (twentyOneGreedyDefect (N + L) : ℝ) + 1) :
    N ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
  by_contra hnot
  have hskip :
      N ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ) := by
    exact ⟨hN.ne', hnot⟩
  have hbound :=
    twentyOneGreedyDefect_add_one_lt_pow_mul_sqrt_of_skip L hskip
  linarith

/-- The scaled actual remainder is at most `Q_N + 1`.  This is the
non-circular direction of the defect bridge: the finite divisor tail is
nonnegative and the periodic residue is strictly below the denominator. -/
theorem twentyOne_scaled_greedyRemainder_le_defect_add_one (N : ℕ) :
    (2 : ℝ) ^ N * greedyMersenneRemainder (1 / 21 : ℝ) N ≤
      (twentyOneGreedyDefect N : ℝ) + 1 := by
  have hid :=
    twentyOneGreedyDefect_add_mod_div_eq_scaled_remainder_add_tail N
  have htail := twentyOneGreedyFinitePrefixTail_nonneg N
  have hmod : 2 ^ N % 21 < 21 := Nat.mod_lt _ (by omega)
  have hmodR : ((2 ^ N % 21 : ℕ) : ℝ) < 21 := by
    exact_mod_cast hmod
  nlinarith

/-- Conversely, after subtracting the universal `O(√N)` finite-tail
allowance, every remaining unit of defect is forced into the actual scaled
greedy remainder.  Thus a linearly large danger defect cannot be hidden in
old divisor corrections. -/
theorem twentyOne_defect_sub_two_sqrt_sub_four_le_scaled_greedyRemainder
    (N : ℕ) :
    (twentyOneGreedyDefect N : ℝ) -
          (2 * Real.sqrt (N : ℝ) + 4) ≤
      (2 : ℝ) ^ N * greedyMersenneRemainder (1 / 21 : ℝ) N := by
  have hid :=
    twentyOneGreedyDefect_add_mod_div_eq_scaled_remainder_add_tail N
  have htail :=
    twentyOneGreedyFinitePrefixTail_le_two_sqrt_add_four N
  have hmod : (0 : ℝ) ≤ ((2 ^ N % 21 : ℕ) : ℝ) := by positivity
  nlinarith

/-- Beyond every requested depth, the carry returns below a linear envelope.
This is strictly weaker than a uniform all-depth square-root estimate. -/
def TwentyOneGreedyCarryCofinalLinearReturn : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    twentyOneGreedyCarry M ≤ ((21 * (M + 1) : ℕ) : ℤ)

/-- Cofinal linear returns force the whole scaled carry to zero.  The
antitone scaled orbit propagates each late return to every later depth. -/
theorem twentyOneGreedyCarry_scaled_tendsto_zero_of_cofinalLinearReturn
    (hreturn : TwentyOneGreedyCarryCofinalLinearReturn) :
    Tendsto
      (fun N : ℕ =>
        (twentyOneGreedyCarry N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
  let f : ℕ → ℝ := fun N =>
    (twentyOneGreedyCarry N : ℝ) / (2 : ℝ) ^ N
  let b : ℕ → ℝ := fun N =>
    21 * ((N : ℝ) + 1) / (2 : ℝ) ^ N
  have hanti : Antitone f := by
    simpa [f] using scaled_twentyOneGreedyCarry_antitone
  have hN : Tendsto (fun N : ℕ => (N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    simpa using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have hOne : Tendsto (fun N : ℕ => (1 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hb : Tendsto b atTop (nhds 0) := by
    have h := (hN.const_mul 21).add (hOne.const_mul 21)
    convert h using 1
    · funext N
      simp only [b]
      ring
    · simp
  have hnonneg : ∀ N : ℕ, 0 ≤ f N := by
    intro N
    exact div_nonneg (by exact_mod_cast twentyOneGreedyCarry_nonneg N)
      (by positivity)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 hb ε hε
  obtain ⟨M, hN₀M, hM⟩ := hreturn N₀
  have hMf : f M ≤ b M := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    change (twentyOneGreedyCarry M : ℝ) ≤ 21 * ((M : ℝ) + 1)
    exact_mod_cast hM
  have hbM : b M < ε := by
    have hdist := hN₀ M hN₀M
    have hbnonneg : 0 ≤ b M := by
      dsimp [b]
      positivity
    simpa [Real.dist_eq, abs_of_nonneg hbnonneg] using hdist
  refine ⟨M, ?_⟩
  intro N hMN
  have hfN : f N < ε :=
    lt_of_le_of_lt ((hanti hMN).trans hMf) hbM
  have hfnonneg := hnonneg N
  change dist (f N) 0 < ε
  simpa [Real.dist_eq, abs_of_nonneg hfnonneg] using hfN

/-- Any subexponential upper bound closes the prescribed-point problem.  The
lower squeeze bound is supplied by `twentyOneGreedyCarry_nonneg`, so the only
remaining mathematical burden is an upper estimate. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_carry_tendsto
    (hcarry : Tendsto
      (fun N : ℕ =>
        (twentyOneGreedyCarry N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0)) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  have horbit : IsTemperedBinaryOrbit (supportCoeff A) 21
      twentyOneGreedyCarry := by
    refine ⟨?_, hcarry⟩
    intro N
    exact twentyOneGreedyCarry_succ N
  have hvalue :=
    support_fraction_of_temperedCarry A 1 21 (by norm_num)
      twentyOneGreedyCarry rfl horbit
  have hpositive :
      positiveMersenneSupportValue A = (1 / 21 : ℝ) := by
    rw [positiveMersenneSupportValue_eq_erdosSupportSeries, hvalue]
    norm_num
  exact ⟨A, zero_not_mem_greedyMersenneSupport _, hpositive.symm⟩

/-- A cofinal sequence of merely linear returns already closes the
prescribed-point endpoint. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalLinearReturn
    (hreturn : TwentyOneGreedyCarryCofinalLinearReturn) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_carry_tendsto
  exact
    twentyOneGreedyCarry_scaled_tendsto_zero_of_cofinalLinearReturn hreturn

/-- It is enough for the sharp floor-slope estimate to hold after one
six-step block at cofinally many starting ranks.  No estimate is required
between those ranks. -/
def TwentyOneGreedyDefectSlopeStepCofinally : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    twentyOneGreedyDefect (N + 6) ≤ (N + 6) / 6

/-- Cofinal floor-slope steps already give the cofinal linear carry returns
needed for membership.  This discards both a global defect bound and any
bound on the gaps between successful steps. -/
theorem
    one_div_twenty_one_mem_mersenneAchievementSet_of_slopeStepCofinally
    (hstep : TwentyOneGreedyDefectSlopeStepCofinally) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalLinearReturn
  intro K
  obtain ⟨N, hKN, hQ⟩ := hstep K
  refine ⟨N + 6, by omega, ?_⟩
  rw [twentyOneGreedyCarry_eq_mod_add_defect]
  have hmodNat : 2 ^ (N + 6) % 21 < 21 :=
    Nat.mod_lt _ (by omega)
  have hmodNat' : 2 ^ (N + 6) % 21 ≤ 20 := by omega
  have hmodZ :
      ((2 ^ (N + 6) % 21 : ℕ) : ℤ) ≤ 20 := by
    exact_mod_cast hmodNat'
  have hQZ :
      (twentyOneGreedyDefect (N + 6) : ℤ) ≤
        (((N + 6) / 6 : ℕ) : ℤ) := by
    exact_mod_cast hQ
  have hdiv : (N + 6) / 6 ≤ N + 6 := Nat.div_le_self _ _
  have hdivZ : (((N + 6) / 6 : ℕ) : ℤ) ≤ (N + 6 : ℤ) := by
    exact_mod_cast hdiv
  push_cast
  omega

/-- The experimentally dominant route: it suffices that slope-safe ranks
occur cofinally.  At each such rank the six-step floor bound is automatic,
so no repair-load estimate is needed there. -/
def TwentyOneGreedyDefectSlopeSafeCofinally : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    ¬ TwentyOneGreedyDefectSlopeDanger N

theorem
    one_div_twenty_one_mem_mersenneAchievementSet_of_slopeSafeCofinally
    (hsafe : TwentyOneGreedyDefectSlopeSafeCofinally) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply
    one_div_twenty_one_mem_mersenneAchievementSet_of_slopeStepCofinally
  intro K
  obtain ⟨N, hKN, hsafeN⟩ := hsafe K
  exact
    ⟨N, hKN,
      twentyOneGreedyDefect_add_six_le_div_six_of_not_slopeDanger
        N hsafeN⟩

/-- A concrete cofinal sublinear-return target.  It asks only for
arbitrarily late ranks at which the defect lies below the very weak affine
threshold `(N - 354) / 384`; neither boundedness nor an all-depth estimate
is required. -/
def TwentyOneGreedyDefectCofinalLinearSeparation : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    384 * twentyOneGreedyDefect N + 354 ≤ N

theorem
    one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalLinearSeparation
    (hsep : TwentyOneGreedyDefectCofinalLinearSeparation) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply
    one_div_twenty_one_mem_mersenneAchievementSet_of_slopeSafeCofinally
  intro K
  obtain ⟨N, hKN, hsepN⟩ := hsep K
  refine ⟨N, hKN, ?_⟩
  intro hdanger
  have hlt := twentyOneGreedyDefectSlopeDanger_rank_lt N hdanger
  omega

/-- Contrapositive classification: non-membership cannot merely produce
occasional large defects.  It forces every sufficiently late rank to be
slope-dangerous. -/
theorem twentyOneGreedyDefect_eventually_slopeDanger_of_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
      TwentyOneGreedyDefectSlopeDanger N := by
  by_contra hcontra
  apply hnot
  apply
    one_div_twenty_one_mem_mersenneAchievementSet_of_slopeSafeCofinally
  intro K
  by_contra hK
  push Not at hK
  exact hcontra ⟨K, hK⟩

/-- Hence the sole non-membership branch has an eventual explicit linear
lower bound on the defect.  One arbitrarily late violation of this bound
already proves membership. -/
theorem twentyOneGreedyDefect_eventually_linearLower_of_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
      N < 384 * twentyOneGreedyDefect N + 354 := by
  obtain ⟨K, hK⟩ :=
    twentyOneGreedyDefect_eventually_slopeDanger_of_not_mem hnot
  exact
    ⟨K, fun N hKN =>
      twentyOneGreedyDefectSlopeDanger_rank_lt N (hK N hKN)⟩

/-- Once a greedy state is fatal, its excess over the complete remaining
Mersenne tail is conserved exactly.  Both quantities lose the same selected
weight at every later step. -/
theorem greedyMersenneRemainder_sub_tail_eq_of_fatalAt_add
    {x : ℝ} {n : ℕ} (hfatal : GreedyMersenneFatalAt x n) (k : ℕ) :
    greedyMersenneRemainder x (n + k) - mersenneTail (n + k) =
      greedyMersenneRemainder x n - mersenneTail n := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hfatalK := greedyMersenneFatalAt_add hfatal k
      have htake := (greedyMersenneFatalAt_succ hfatalK).1
      have htail := mersenneTail_eq_weight_add (n + k)
      rw [show n + (k + 1) = (n + k) + 1 by omega,
        greedyMersenneRemainder_succ, if_pos htake]
      linarith

/-- A fatal denominator-`21` state forces a geometric lower bound on the
defect.  The fixed positive tail excess is multiplied by `2^(n+k)`; the
exact defect/remainder bridge loses only the harmless additive unit. -/
theorem twentyOneGreedyDefect_add_one_ge_geometric_fatalExcess
    {n : ℕ}
    (hfatal : GreedyMersenneFatalAt (1 / 21 : ℝ) n) (k : ℕ) :
    (2 : ℝ) ^ (n + k) *
          (greedyMersenneRemainder (1 / 21 : ℝ) n - mersenneTail n) ≤
      (twentyOneGreedyDefect (n + k) : ℝ) + 1 := by
  have heq :=
    greedyMersenneRemainder_sub_tail_eq_of_fatalAt_add hfatal k
  have htail := mersenneTail_nonneg (n + k)
  have hrem :
      greedyMersenneRemainder (1 / 21 : ℝ) n - mersenneTail n ≤
        greedyMersenneRemainder (1 / 21 : ℝ) (n + k) := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hrem
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (n + k))
  exact hscaled.trans
    (twentyOne_scaled_greedyRemainder_le_defect_add_one (n + k))

/-- Non-membership is therefore exponentially rigid: it supplies one
positive constant `δ` such that `2^(n+k) δ ≤ Q_(n+k)+1` at every later
rank.  The earlier eventual linear lower bound is only a coarse shadow of
this fatal-tail alternative. -/
theorem twentyOneGreedyDefect_geometricLower_of_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ∃ n : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ k : ℕ,
        (2 : ℝ) ^ (n + k) * δ ≤
          (twentyOneGreedyDefect (n + k) : ℝ) + 1 := by
  have hnotSurvive :
      ¬ ∀ n : ℕ,
        greedyMersenneRemainder (1 / 21 : ℝ) n ≤ mersenneTail n := by
    intro hsurvive
    exact hnot
      ((mem_mersenneAchievementSet_iff_greedy_survival
        (1 / 21 : ℝ)).2 ⟨by norm_num, hsurvive⟩)
  push Not at hnotSurvive
  obtain ⟨n, hn⟩ := hnotSurvive
  let δ :=
    greedyMersenneRemainder (1 / 21 : ℝ) n - mersenneTail n
  have hfatal : GreedyMersenneFatalAt (1 / 21 : ℝ) n := hn
  refine ⟨n, δ, ?_, ?_⟩
  · exact sub_pos.mpr hn
  · intro k
    simpa [δ] using
      twentyOneGreedyDefect_add_one_ge_geometric_fatalExcess hfatal k

/-- Direct defect-coordinate version of subexponentiality.  Unlike a global
polynomial bound, it asks only that `Q_N+1` eventually lie below every fixed
positive multiple of `2^N`. -/
def TwentyOneGreedyDefectSubexponential : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
      (twentyOneGreedyDefect N : ℝ) + 1 < (2 : ℝ) ^ N * δ

/-- Any subexponential estimate in the natural-valued defect coordinate
rules out the geometrically growing fatal branch and proves membership. -/
theorem
    one_div_twenty_one_mem_mersenneAchievementSet_of_defectSubexponential
    (hsubexp : TwentyOneGreedyDefectSubexponential) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  by_contra hnot
  obtain ⟨n, δ, hδ, hlower⟩ :=
    twentyOneGreedyDefect_geometricLower_of_not_mem hnot
  obtain ⟨K, hK⟩ := hsubexp δ hδ
  have hupper := hK (n + K) (by omega)
  have hlowerK := hlower K
  exact (not_lt_of_ge hlowerK) hupper

/-- Membership supplies the missing tempered boundary for the *canonical*
denominator-`21` greedy carry.  The support code witnessing membership is
necessarily the greedy code; the displayed-fraction carry it produces has
the same initial state and recurrence as `twentyOneGreedyCarry`, hence is
that carry by induction. -/
theorem twentyOneGreedyCarry_scaled_tendsto_zero_of_mem
    (hmem : (1 / 21 : ℝ) ∈ mersenneAchievementSet) :
    Tendsto
      (fun N : ℕ =>
        (twentyOneGreedyCarry N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
  rcases hmem with ⟨A, hA0, hvalue⟩
  have hsupport :
      greedyMersenneSupport (1 / 21 : ℝ) = A := by
    rw [hvalue]
    exact greedySupport_supportValue_eq A hA0
  have hseries :
      erdosSupportSeries 2
          (greedyMersenneSupport (1 / 21 : ℝ)) =
        (1 : ℝ) / (21 : ℝ) := by
    rw [hsupport, ← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  obtain ⟨U, hU0, hU⟩ :=
    exists_temperedCarry_of_support_fraction
      (greedyMersenneSupport (1 / 21 : ℝ)) 1 21 (by omega)
        (by simpa using hseries)
  have hUeq : U = twentyOneGreedyCarry := by
    funext N
    induction N with
    | zero => simpa using hU0
    | succ N ih =>
        rw [hU.1 N, twentyOneGreedyCarry_succ, ih]
  rw [hUeq] at hU
  exact hU.2

/-- Conversely, actual membership forces the natural defect to be
subexponential.  The periodic-baseline decomposition bounds `Q_N + 1` by
the nonnegative carry plus one, so the tempered carry limit transfers
directly to the defect coordinate. -/
theorem twentyOneGreedyDefectSubexponential_of_mem
    (hmem : (1 / 21 : ℝ) ∈ mersenneAchievementSet) :
    TwentyOneGreedyDefectSubexponential := by
  have hcarry :=
    twentyOneGreedyCarry_scaled_tendsto_zero_of_mem hmem
  have hOne :
      Tendsto (fun N : ℕ => (1 : ℝ) / (2 : ℝ) ^ N)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hupper :
      Tendsto
        (fun N : ℕ =>
          ((twentyOneGreedyCarry N : ℝ) + 1) / (2 : ℝ) ^ N)
        atTop (nhds 0) := by
    have h := hcarry.add hOne
    convert h using 1
    · funext N
      ring
    · simp
  have hdefect :
      Tendsto
        (fun N : ℕ =>
          ((twentyOneGreedyDefect N : ℝ) + 1) / (2 : ℝ) ^ N)
        atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun N => by positivity)
      (Filter.Eventually.of_forall fun N => ?_)
      hupper
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hdecomp := twentyOneGreedyCarry_eq_mod_add_defect N
    have hmod : (0 : ℤ) ≤ (2 ^ N % 21 : ℕ) := by omega
    push_cast at hdecomp
    exact_mod_cast (show
      (twentyOneGreedyDefect N : ℤ) + 1 ≤
        twentyOneGreedyCarry N + 1 by omega)
  intro δ hδ
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hdefect) δ hδ
  refine ⟨K, fun N hKN => ?_⟩
  have hdist := hK N hKN
  have hnonneg :
      0 ≤ ((twentyOneGreedyDefect N : ℝ) + 1) /
        (2 : ℝ) ^ N := by positivity
  have hratio :
      ((twentyOneGreedyDefect N : ℝ) + 1) /
          (2 : ℝ) ^ N < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hdist
    exact hdist
  have hpow : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have := (div_lt_iff₀ hpow).1 hratio
  nlinarith

/-- **Exact normalized-defect characterization.**  The prescribed point is
represented if and only if the canonical denominator-`21` defect is
subexponential relative to `2^N`.  Thus the subexponential producer is not
an arbitrary sufficient bound: it is precisely the remaining asymptotic
content of the problem in this coordinate. -/
theorem one_div_twenty_one_mem_iff_greedyDefectSubexponential :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      TwentyOneGreedyDefectSubexponential := by
  exact ⟨twentyOneGreedyDefectSubexponential_of_mem,
    one_div_twenty_one_mem_mersenneAchievementSet_of_defectSubexponential⟩

/-- Weakest normalized-return producer exposed by the fatal/subexponential
dichotomy: after every cutoff, `Q_N + 1` falls below any prescribed positive
multiple of `2^N` at some later rank.  Unlike subexponentiality, this imposes
no eventual bound at all; a single sufficiently small normalized return
beyond each cutoff is enough. -/
def TwentyOneGreedyDefectNormalizedSmallCofinally : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    (twentyOneGreedyDefect N : ℝ) + 1 < (2 : ℝ) ^ N * δ

/-- **Exact cofinal normalized-return characterization.**  Membership at
`1/21` is equivalent to arbitrarily small normalized defect returns occurring
cofinally.  The reverse implication uses only the fatal geometric lower
bound: a single cofinal return below its fixed positive excess contradicts
non-membership. -/
theorem one_div_twenty_one_mem_iff_defectNormalizedSmallCofinally :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      TwentyOneGreedyDefectNormalizedSmallCofinally := by
  constructor
  · intro hmem δ hδ K
    obtain ⟨K₀, hK₀⟩ :=
      twentyOneGreedyDefectSubexponential_of_mem hmem δ hδ
    refine ⟨max K K₀, le_max_left K K₀, ?_⟩
    exact hK₀ (max K K₀) (le_max_right K K₀)
  · intro hsmall
    by_contra hnot
    obtain ⟨n, δ, hδ, hlower⟩ :=
      twentyOneGreedyDefect_geometricLower_of_not_mem hnot
    obtain ⟨N, hnN, hupper⟩ := hsmall δ hδ n
    have hlowerN := hlower (N - n)
    have hsum : n + (N - n) = N := by omega
    rw [hsum] at hlowerN
    exact (not_lt_of_ge hlowerN) hupper

/-- Weakest bounded-return formulation in the native greedy coordinate:
there is one fixed ceiling hit by the scaled remainder beyond every cutoff.
No convergence, return frequency, or prescribed ceiling is required. -/
def TwentyOneScaledGreedyRemainderCofinallyBounded : Prop :=
  ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    (2 : ℝ) ^ N *
        greedyMersenneRemainder (1 / 21 : ℝ) N ≤ B

/-- **Exact cofinal scaled-remainder characterization.**  Membership at
`1/21` is equivalent to the scaled greedy remainder returning cofinally to
one fixed bounded interval.  On the surviving branch the scaled remainder
is bounded by the scaled complete tail, which tends to `1`.  On the fatal
branch one fixed positive tail excess is conserved, so multiplication by
`2^N` eventually exceeds every proposed ceiling. -/
theorem
    one_div_twenty_one_mem_iff_scaledGreedyRemainderCofinallyBounded :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      TwentyOneScaledGreedyRemainderCofinallyBounded := by
  constructor
  · intro hmem
    obtain ⟨_, hsurvive⟩ :=
      (mem_mersenneAchievementSet_iff_greedy_survival
        (1 / 21 : ℝ)).1 hmem
    obtain ⟨K₀, hK₀⟩ :=
      (Metric.tendsto_atTop.1 tendsto_two_pow_mul_mersenneTail_one)
        1 (by norm_num)
    refine ⟨2, fun K => ⟨max K K₀, le_max_left K K₀, ?_⟩⟩
    have hdist := hK₀ (max K K₀) (le_max_right K K₀)
    have htailUpper :
        (2 : ℝ) ^ (max K K₀) * mersenneTail (max K K₀) < 2 := by
      rw [Real.dist_eq] at hdist
      have := (abs_lt.mp hdist).2
      linarith
    have hscaled :=
      mul_le_mul_of_nonneg_left (hsurvive (max K K₀))
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (max K K₀))
    exact hscaled.trans htailUpper.le
  · rintro ⟨B, hbounded⟩
    by_contra hnot
    have hnotSurvive :
        ¬ ∀ n : ℕ,
          greedyMersenneRemainder (1 / 21 : ℝ) n ≤ mersenneTail n := by
      intro hsurvive
      exact hnot
        ((mem_mersenneAchievementSet_iff_greedy_survival
          (1 / 21 : ℝ)).2 ⟨by norm_num, hsurvive⟩)
    push Not at hnotSurvive
    obtain ⟨n, hn⟩ := hnotSurvive
    let δ :=
      greedyMersenneRemainder (1 / 21 : ℝ) n - mersenneTail n
    have hδ : 0 < δ := sub_pos.mpr hn
    have hfatal : GreedyMersenneFatalAt (1 / 21 : ℝ) n := hn
    have hpow :
        Tendsto (fun N : ℕ => (2 : ℝ) ^ N) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    obtain ⟨K₀, hK₀⟩ :=
      (Filter.tendsto_atTop_atTop.1 hpow) (B / δ + 1)
    obtain ⟨N, hcut, hupper⟩ := hbounded (max n K₀)
    have hnN : n ≤ N := le_max_left n K₀ |>.trans hcut
    have hK₀N : K₀ ≤ N := le_max_right n K₀ |>.trans hcut
    have hpowN : B / δ < (2 : ℝ) ^ N := by
      have := hK₀ N hK₀N
      linarith
    have hstrict : B < (2 : ℝ) ^ N * δ :=
      (div_lt_iff₀ hδ).1 hpowN
    have heq :=
      greedyMersenneRemainder_sub_tail_eq_of_fatalAt_add
        hfatal (N - n)
    have hsum : n + (N - n) = N := by omega
    rw [hsum] at heq
    have hδle :
        δ ≤ greedyMersenneRemainder (1 / 21 : ℝ) N := by
      have htail := mersenneTail_nonneg N
      dsimp [δ]
      linarith
    have hscaled :=
      mul_le_mul_of_nonneg_left hδle
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ N)
    exact (not_lt_of_ge hupper) (hstrict.trans_le hscaled)

/-- Most generally, at cofinally many ranks either floor slack closes the
block automatically or the exact repair-load inequality pays for it. -/
def TwentyOneGreedyDangerRepairSucceedsCofinally : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    (TwentyOneGreedyDefectSlopeDanger N →
      64 * twentyOneGreedyDefect N +
          3 * (2 ^ N % 21) ≤
        twentyOneSixStepRepairLoad N + N / 6 + 1)

theorem
    one_div_twenty_one_mem_mersenneAchievementSet_of_dangerRepairCofinally
    (hrepair : TwentyOneGreedyDangerRepairSucceedsCofinally) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply
    one_div_twenty_one_mem_mersenneAchievementSet_of_slopeStepCofinally
  intro K
  obtain ⟨N, hKN, hrepairN⟩ := hrepair K
  refine ⟨N, hKN, ?_⟩
  by_cases hdanger : TwentyOneGreedyDefectSlopeDanger N
  · exact
      (twentyOneGreedyDefect_add_six_le_div_six_iff_repairLoad N).2
        (hrepairN hdanger)
  · exact
      twentyOneGreedyDefect_add_six_le_div_six_of_not_slopeDanger
        N hdanger

/-- The denominator-`21` defect need not obey a uniform slope bound.
It suffices that some fixed bounded defect band is visited beyond every
cutoff.  This concrete interface matches the certified repeated returns to
`Q_N ≤ 1`; the slope-safe cofinal interface above is weaker still and also
allows the defect to grow sublinearly. -/
def TwentyOneGreedyDefectCofinallyBounded : Prop :=
  ∃ B : ℕ, ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ twentyOneGreedyDefect M ≤ B

/-- Cofinal returns to any fixed defect band force cofinal linear carry
returns and hence membership of the prescribed rational point. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_defectCofinallyBounded
    (hbounded : TwentyOneGreedyDefectCofinallyBounded) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalLinearReturn
  obtain ⟨B, hB⟩ := hbounded
  intro N
  obtain ⟨M, hmaxM, hdefect⟩ := hB (max N B)
  refine ⟨M, (Nat.le_max_left N B).trans hmaxM, ?_⟩
  rw [twentyOneGreedyCarry_eq_mod_add_defect]
  have hmodNat : 2 ^ M % 21 < 21 := Nat.mod_lt _ (by omega)
  have hmodNat' : 2 ^ M % 21 ≤ 20 := by omega
  have hmodZ : ((2 ^ M % 21 : ℕ) : ℤ) ≤ 20 := by
    exact_mod_cast hmodNat'
  have hdefectZ :
      (twentyOneGreedyDefect M : ℤ) ≤ (B : ℤ) := by
    exact_mod_cast hdefect
  have hBM : B ≤ M := (Nat.le_max_right N B).trans hmaxM
  have hBMZ : (B : ℤ) ≤ (M : ℤ) := by
    exact_mod_cast hBM
  push_cast
  omega

/-- The concrete band seen by exact computation is `Q_N ≤ 1`.
Proving that it recurs cofinally is already enough; no global bound on the
defect or on the gaps between returns is required. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_defect_le_one_cofinally
    (hreturn : ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ twentyOneGreedyDefect M ≤ 1) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply
    one_div_twenty_one_mem_mersenneAchievementSet_of_defectCofinallyBounded
  exact ⟨1, hreturn⟩

/-- Exact one-dimensional arithmetic target suggested by the certified
greedy computation.  Proving `Q_N ≤ ⌊N/6⌋` at every depth would solve the
prescribed-point problem outright. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_defect_le_div_six
    (hdefect : ∀ N : ℕ, twentyOneGreedyDefect N ≤ N / 6) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalLinearReturn
  intro N
  refine ⟨N, le_rfl, ?_⟩
  rw [twentyOneGreedyCarry_eq_mod_add_defect]
  have hmodNat : 2 ^ N % 21 < 21 := Nat.mod_lt _ (by omega)
  have hmodNat' : 2 ^ N % 21 ≤ 20 := by omega
  have hmodZ : ((2 ^ N % 21 : ℕ) : ℤ) ≤ 20 := by
    exact_mod_cast hmodNat'
  have hdefectZ :
      (twentyOneGreedyDefect N : ℤ) ≤ ((N / 6 : ℕ) : ℤ) := by
    exact_mod_cast hdefect N
  have hdiv : N / 6 ≤ N := Nat.div_le_self N 6
  have hdivZ : ((N / 6 : ℕ) : ℤ) ≤ (N : ℤ) := by
    exact_mod_cast hdiv
  push_cast
  omega

/-- A finite six-row base check and the exact repair-load inequality solve
the prescribed point `1/21`.  No asymptotic estimate remains in this
interface. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_sixStepRepairLoad
    (hbase : ∀ N : ℕ, N < 6 → twentyOneGreedyDefect N = 0)
    (hload : ∀ N : ℕ,
      63 * twentyOneGreedyDefect N +
          3 * (2 ^ N % 21) ≤
        twentyOneSixStepRepairLoad N + 1) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_defect_le_div_six
  apply twentyOneGreedyDefect_le_div_six_of_blockContraction hbase
  intro N
  exact
    (twentyOneGreedyDefect_add_six_le_iff_repairLoad N).2
      (hload N)

/-- Slope-aware repair-load endpoint.  It is enough to pay the exact
six-step load only when accumulated floor slack cannot close the block
automatically. -/
theorem
    one_div_twenty_one_mem_mersenneAchievementSet_of_dangerRepairLoad
    (hbase : ∀ N : ℕ, N < 6 → twentyOneGreedyDefect N = 0)
    (hdanger : ∀ N : ℕ, TwentyOneGreedyDefectSlopeDanger N →
      64 * twentyOneGreedyDefect N +
          3 * (2 ^ N % 21) ≤
        twentyOneSixStepRepairLoad N + N / 6 + 1) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_defect_le_div_six
  exact
    twentyOneGreedyDefect_le_div_six_of_dangerRepairLoad hbase hdanger

/-- Explicit high-defect version of the slope-aware endpoint.  Repair-load
arithmetic is required only while `N < 384 Q_N + 354`; low-defect ranks are
closed for free by the floor slack. -/
theorem
    one_div_twenty_one_mem_mersenneAchievementSet_of_highDefectRepairLoad
    (hbase : ∀ N : ℕ, N < 6 → twentyOneGreedyDefect N = 0)
    (hload : ∀ N : ℕ,
      N < 384 * twentyOneGreedyDefect N + 354 →
      64 * twentyOneGreedyDefect N +
          3 * (2 ^ N % 21) ≤
        twentyOneSixStepRepairLoad N + N / 6 + 1) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_defect_le_div_six
  exact
    twentyOneGreedyDefect_le_div_six_of_highDefectRepairLoad hbase hload

/-- Configurable finite-window producer: certify one positive block length
divisible by six, its initial strip, and its translation-invariant
floor-slope contraction, and the prescribed point follows. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_floorSlopeBlock
    {B : ℕ} (hBpos : 0 < B) (hBdiv : 6 ∣ B)
    (hbase : ∀ N : ℕ, N < B →
      twentyOneGreedyDefect N ≤ N / 6)
    (hblock : TwentyOneGreedyDefectFloorSlopeBlockContraction B) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_defect_le_div_six
  exact
    twentyOneGreedyDefect_le_div_six_of_floorSlopeBlockContraction
      hBpos hBdiv hbase hblock

#print axioms twentyOneGreedyDefect_add_six
#print axioms twentyOneGreedyDefect_add_six_le_iff_repairLoad
#print axioms twentyOneGreedyDefect_add_one_le_pow_mul
#print axioms two_pow_mul_mersenneWeight_le_two
#print axioms twentyOneGreedyDefect_lt_two_sqrt_add_six_of_skip
#print axioms mem_greedyMersenneSupport_of_defect_growth_threshold
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_floorSlopeBlock

/-- A concrete square-root carry strip is already enough to solve the
prescribed-point endpoint.  This is deliberately stated without assuming
that the carry is tempered: tempering is derived from the strip and the
unconditional nonnegativity theorem. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_carry_sqrt_bound
    (hupper : ∀ N : ℕ,
      (twentyOneGreedyCarry N : ℝ) ≤
        21 * (2 * Real.sqrt (N : ℝ) + 4)) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_carry_tendsto
  exact tendsto_div_pow_zero_of_nonnegative_sqrt_bound
    21 twentyOneGreedyCarry twentyOneGreedyCarry_nonneg hupper

/-- The most economical dynamical producer currently visible at the
prescribed point: skipped exponents occur beyond every cutoff.  A fatal
greedy state would select every later exponent, so this condition alone
rules out fatality; it asks for neither a carry bound nor a remainder cap. -/
def TwentyOneGreedySkipsCofinally : Prop :=
  ∀ N : ℕ, ∃ m : ℕ,
    m ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ) ∧ N < m

/-- A uniform bound on selected runs is a stronger, finite-window producer
for cofinal skipping.  The exact checker currently sees very short runs, but
the theorem deliberately leaves the bound existential. -/
def TwentyOneGreedySelectedRunsBounded : Prop :=
  ∃ B : ℕ, ∀ N : ℕ, ∃ m : ℕ,
    m ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ) ∧
      N < m ∧ m ≤ N + B

/-- Cofinal skipped exponents solve the prescribed-point endpoint directly
through the absorbing-fatal-state theorem. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinal_skips
    (hskips : TwentyOneGreedySkipsCofinally) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply mem_mersenneAchievementSet_of_greedySkippedSupport_infinite
    (by norm_num)
  exact Set.infinite_of_forall_exists_gt hskips

/-- Any finite uniform selected-run bound therefore solves the endpoint. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_bounded_selectedRuns
    (hbounded : TwentyOneGreedySelectedRunsBounded) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_cofinal_skips
  rcases hbounded with ⟨B, hB⟩
  intro N
  obtain ⟨m, hm, hNm, _⟩ := hB N
  exact ⟨m, hm, hNm⟩

/-- Target-generic two-channel transport.  Selected branches preserve the cap
automatically; the only arithmetic burden is the omitted correction tail on
the skipped branches. -/
theorem target_mem_mersenneAchievementSet_of_skipped_twoChannelCap
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n →
      greedyMersenneRemainder x n ≤ halfTwoChannelCap (n + 1)) :
    x ∈ mersenneAchievementSet := by
  have hall :
      ∀ n : ℕ, greedyMersenneRemainder x n ≤ halfTwoChannelCap n := by
    intro n
    induction n with
    | zero =>
        exact hx1.trans (by norm_num [halfTwoChannelCap])
    | succ n ih =>
        rw [greedyMersenneRemainder_succ]
        by_cases htake :
            mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n
        · rw [if_pos htake]
          exact (sub_le_sub_right ih _).trans (halfTwoChannelCap_selected n)
        · rw [if_neg htake]
          exact hskip n htake
  apply mem_mersenneAchievementSet_of_greedy_survival hx0
  intro n
  exact (hall n).trans (halfTwoChannelCap_le_mersenneTail n)

/-- Prescribed-point form of the skipped two-channel endpoint.  Relative to
the dyadic cap, this admits the complete first correction channel and leaves
only the higher-channel tail to exclude. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_skipped_twoChannelCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (1 / 21 : ℝ) n →
      greedyMersenneRemainder (1 / 21 : ℝ) n ≤
        halfTwoChannelCap (n + 1)) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  exact target_mem_mersenneAchievementSet_of_skipped_twoChannelCap
    (1 / 21 : ℝ) (by norm_num) (by norm_num) hskip

/-- Target-generic dyadic-cap transport.  Selected branches preserve the cap
automatically; only skipped branches can enter the narrow unsafe sliver
between `2^-(n+1)` and `1/(2^(n+1)-1)`. -/
theorem target_mem_mersenneAchievementSet_of_skipped_dyadicCap
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n →
      greedyMersenneRemainder x n ≤ halfDyadicCap (n + 1)) :
    x ∈ mersenneAchievementSet := by
  apply target_mem_mersenneAchievementSet_of_skipped_twoChannelCap x hx0 hx1
  intro n hskipped
  exact
    (hskip n hskipped).trans
      (halfDyadicCap_le_halfTwoChannelCap (n + 1))

/-- Local skipped-branch endpoint for the prescribed rational.  This is
strictly weaker than asking for the dyadic cap at every depth, because
selected steps are discharged by the universal transport inequality. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_skipped_dyadicCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (1 / 21 : ℝ) n →
      greedyMersenneRemainder (1 / 21 : ℝ) n ≤
        halfDyadicCap (n + 1)) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  exact target_mem_mersenneAchievementSet_of_skipped_dyadicCap
    (1 / 21 : ℝ) (by norm_num) (by norm_num) hskip

/-- The correction made when the binary skeleton `2⁻ⁿ` is replaced by the
Mersenne weight `(2ⁿ - 1)⁻¹`.  Although the original half argument called
this `halfCorrectionValue`, the quantity itself is target-independent. -/
noncomputable def supportDyadicCorrectionValue (A : Set ℕ) : ℝ :=
  positiveMersenneSupportValue A - positiveDyadicSupportValue A

/-- The binary value demanded by the fixed-point equation at target `x`. -/
noncomputable def targetDyadicComplementValue (x : ℝ) (A : Set ℕ) : ℝ :=
  x - positiveDyadicSupportValue A

/-- Exact target-independent form of the correction fixed-point equation. -/
theorem positiveMersenneSupportValue_eq_target_iff_correction_eq_complement
    (x : ℝ) (A : Set ℕ) :
    positiveMersenneSupportValue A = x ↔
      supportDyadicCorrectionValue A =
        targetDyadicComplementValue x A := by
  unfold supportDyadicCorrectionValue targetDyadicComplementValue
  constructor <;> intro h <;> linarith

/-- A shifted coarse-cell boundary has a concrete combinatorial
consequence.  If its odd coarse numerator is `q`, the lower coarse word has
depth-`2*K` numerator `2^v * (q - 1)`.  A valuation `v ≥ K - 1` therefore
makes that word divisible by `2^K`, forcing every support bit in the
doubling block `(K,2*K]` to vanish.

This lemma is intentionally only about the displayed shifted-word equation.
An actual left boundary has prefix `2^v*q`; an actual right boundary has
`prefix + 1 = 2^v*q`.  Those orientations require separate classifiers. -/
theorem correctionBoundary_large_valuation_forces_empty_doublingBlock
    (A : Set ℕ) (K v q : ℕ)
    (hv : K - 1 ≤ v) (hq : Odd q)
    (hprefix :
      supportDyadicPrefixNumerator A (2 * K) =
        2 ^ v * (q - 1)) :
    ∀ n : ℕ, K < n → n ≤ 2 * K → n ∉ A := by
  rcases hq with ⟨t, rfl⟩
  have hvdiv :
      2 ^ (v + 1) ∣ supportDyadicPrefixNumerator A (2 * K) := by
    refine ⟨t, ?_⟩
    rw [hprefix]
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  have hKdiv :
      2 ^ K ∣ supportDyadicPrefixNumerator A (2 * K) := by
    exact dvd_trans (pow_dvd_pow 2 (by omega)) hvdiv
  have hgap :=
    supportDyadicPrefixNumerator_terminal_gap_of_pow_two_dvd
      A (N := 2 * K) (r := K) (by omega) hKdiv
  intro n hKn hn2K
  exact hgap n (by omega) hn2K

/-- Contrapositive for the shifted coarse-word equation: one selected
exponent in `(K,2*K]` excludes its non-amplifying valuation range. -/
theorem correctionBoundary_valuation_lt_of_mem_doublingBlock
    (A : Set ℕ) (K v q : ℕ)
    (hq : Odd q)
    (hprefix :
      supportDyadicPrefixNumerator A (2 * K) =
        2 ^ v * (q - 1))
    (hhit : ∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧ n ∈ A) :
    v < K - 1 := by
  by_contra hv
  have hlarge : K - 1 ≤ v := by omega
  obtain ⟨n, hKn, hn2K, hnA⟩ := hhit
  exact
    (correctionBoundary_large_valuation_forces_empty_doublingBlock
      A K v q hlarge hq hprefix n hKn hn2K) hnA

/-- Combining a support hit with the shifted coarse-word equation gives its
strict-amplification inequality. -/
theorem correctionBoundary_forceDepth_gt_of_mem_doublingBlock
    (A : Set ℕ) (K v q : ℕ) (hK : 1 < K)
    (hq : Odd q)
    (hprefix :
      supportDyadicPrefixNumerator A (2 * K) =
        2 ^ v * (q - 1))
    (hhit : ∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧ n ∈ A) :
    K < 2 * K - v - 1 := by
  rw [crossedBoundary_forceDepth_gt_iff hK]
  exact correctionBoundary_valuation_lt_of_mem_doublingBlock
    A K v q hq hprefix hhit

/-- Orientation-correct form for a boundary met at the *left* edge of the
actual depth-`2*K` support cell.  If that boundary has numerator
`2^v * q`, a hit in `(K,2*K]` rules out `v ≥ K`.  The only case not already
giving strict depth amplification is therefore `v = K-1`; in that case the
whole doubling block is forced to be the singleton word `10...0`.

This is deliberately separate from
`correctionBoundary_valuation_lt_of_mem_doublingBlock`: an actual left
boundary supplies `prefix = 2^v*q`, not `2^v*(q-1)`. -/
theorem correctionBoundary_left_valuation_lt_or_singleton_doublingBlock
    (A : Set ℕ) (K v q : ℕ) (hK : 2 ≤ K)
    (_hq : Odd q)
    (hprefix :
      supportDyadicPrefixNumerator A (2 * K) = 2 ^ v * q)
    (hhit : ∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧ n ∈ A) :
    v < K - 1 ∨
      (v = K - 1 ∧
        K + 1 ∈ A ∧
        ∀ n : ℕ, K + 1 < n → n ≤ 2 * K → n ∉ A) := by
  by_cases hvsmall : v < K - 1
  · exact Or.inl hvsmall
  · right
    have hKminusOneLe : K - 1 ≤ v := by omega
    have hvK : v < K := by
      by_contra hvK
      have hKv : K ≤ v := by omega
      have hvdiv :
          2 ^ v ∣ supportDyadicPrefixNumerator A (2 * K) := by
        exact ⟨q, hprefix⟩
      have hKdiv :
          2 ^ K ∣ supportDyadicPrefixNumerator A (2 * K) :=
        dvd_trans (pow_dvd_pow 2 hKv) hvdiv
      obtain ⟨n, hKn, hn2K, hnA⟩ := hhit
      exact
        (supportDyadicPrefixNumerator_terminal_gap_of_pow_two_dvd
          A (N := 2 * K) (r := K) (by omega) hKdiv
          n (by omega) hn2K) hnA
    have hveq : v = K - 1 := by omega
    have hvdiv :
        2 ^ v ∣ supportDyadicPrefixNumerator A (2 * K) := by
      exact ⟨q, hprefix⟩
    have hgap :
        ∀ n : ℕ, K + 1 < n → n ≤ 2 * K → n ∉ A := by
      have hterminal :=
        supportDyadicPrefixNumerator_terminal_gap_of_pow_two_dvd
          A (N := 2 * K) (r := K - 1) (by omega)
          (by simpa [hveq] using hvdiv)
      intro n hnlo hnhi
      exact hterminal n (by omega) hnhi
    obtain ⟨n, hKn, hn2K, hnA⟩ := hhit
    have hn : n = K + 1 := by
      by_contra hne
      exact (hgap n (by omega) hn2K) hnA
    exact ⟨hveq, by simpa [hn] using hnA, hgap⟩

/-- Orientation-correct form for a boundary met at the *right* edge of the
actual depth-`2*K` support cell.  Here `prefix + 1 = 2^v*q`.  Either the
common parent is strictly deeper than `K`, or every bit from `K+2` through
`2*K` is selected.  Thus right-boundary non-amplification is exactly a long
terminal selected run, rather than an untyped valuation obstruction. -/
theorem correctionBoundary_right_amplifies_or_longSelectedRun
    (A : Set ℕ) (K v q : ℕ) (hK : 3 ≤ K)
    (_hq : Odd q)
    (hboundary :
      supportDyadicPrefixNumerator A (2 * K) + 1 = 2 ^ v * q) :
    K < 2 * K - v - 1 ∨
      ∀ n : ℕ, K + 1 < n → n ≤ 2 * K → n ∈ A := by
  by_cases hvsmall : v < K - 1
  · exact Or.inl ((crossedBoundary_forceDepth_gt_iff (by omega)).2 hvsmall)
  · right
    have hKminusOneLe : K - 1 ≤ v := by omega
    have hvdiv :
        2 ^ v ∣ supportDyadicPrefixNumerator A (2 * K) + 1 := by
      exact ⟨q, hboundary⟩
    have hdiv :
        2 ^ (K - 1) ∣ supportDyadicPrefixNumerator A (2 * K) + 1 :=
      dvd_trans (pow_dvd_pow 2 hKminusOneLe) hvdiv
    have hfull :=
      supportDyadicPrefixNumerator_terminal_full_of_pow_two_dvd_succ
        A (N := 2 * K) (r := K - 1) (by omega) hdiv
    intro n hnlo hnhi
    exact hfull n (by omega) hnhi

/-- Greedy residuals can only decrease. -/
theorem greedyMersenneRemainder_antitone (x : ℝ) :
    Antitone (greedyMersenneRemainder x) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [greedyMersenneRemainder_succ]
  by_cases htake :
      mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n
  · rw [if_pos htake]
    exact sub_le_self _ (mersenneWeight_pos (by omega)).le
  · rw [if_neg htake]

/-- If the greedy support has no selected exponent in the next `L` ranks,
the residual is unchanged across that whole block. -/
theorem greedyMersenneRemainder_add_eq_of_support_gap
    (x : ℝ) (K : ℕ) :
    ∀ L : ℕ,
      (∀ n : ℕ, K < n → n ≤ K + L →
        n ∉ greedyMersenneSupport x) →
      greedyMersenneRemainder x (K + L) =
        greedyMersenneRemainder x K := by
  intro L
  induction L with
  | zero =>
      simp
  | succ L ih =>
      intro hgap
      have hprevGap :
          ∀ n : ℕ, K < n → n ≤ K + L →
            n ∉ greedyMersenneSupport x := by
        intro n hKn hnKL
        exact hgap n hKn (by omega)
      have hprev := ih hprevGap
      have hnot :
          K + L + 1 ∉ greedyMersenneSupport x :=
        hgap (K + L + 1) (by omega) (by omega)
      have hskip :
          ¬ mersenneWeight (K + L + 1) ≤
            greedyMersenneRemainder x (K + L) := by
        simpa only [succ_mem_greedyMersenneSupport_iff] using hnot
      rw [show K + (L + 1) = K + L + 1 by omega,
        greedyMersenneRemainder_succ, if_neg hskip, hprev]

/-- The exceptional left-boundary word isolated above has an exact residual
meaning.  If `(K,2*K]` is `10...0`, the rank-`K+1` weight is taken and the
post-take residual stays fixed until rank `2*K`; the final zero then places
the old residual in the narrow interval
`[w_(K+1), w_(K+1)+w_(2K))`. -/
theorem greedyRemainder_sandwich_of_singleton_doublingBlock
    (x : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hfirst : K + 1 ∈ greedyMersenneSupport x)
    (hrest : ∀ n : ℕ, K + 1 < n → n ≤ 2 * K →
      n ∉ greedyMersenneSupport x) :
    mersenneWeight (K + 1) ≤ greedyMersenneRemainder x K ∧
      greedyMersenneRemainder x (2 * K - 1) =
        greedyMersenneRemainder x K - mersenneWeight (K + 1) ∧
      greedyMersenneRemainder x K <
        mersenneWeight (K + 1) + mersenneWeight (2 * K) := by
  have htake :
      mersenneWeight (K + 1) ≤ greedyMersenneRemainder x K := by
    exact
      (succ_mem_greedyMersenneSupport_iff x K).1
        (by simpa using hfirst)
  have htakeStep :
      greedyMersenneRemainder x (K + 1) =
        greedyMersenneRemainder x K - mersenneWeight (K + 1) := by
    rw [greedyMersenneRemainder_succ, if_pos htake]
  have hgap :
      ∀ n : ℕ, K + 1 < n → n ≤ (K + 1) + (K - 2) →
        n ∉ greedyMersenneSupport x := by
    intro n hnlo hnhi
    exact hrest n hnlo (by omega)
  have hconstant :
      greedyMersenneRemainder x ((K + 1) + (K - 2)) =
        greedyMersenneRemainder x (K + 1) :=
    greedyMersenneRemainder_add_eq_of_support_gap
      x (K + 1) (K - 2) hgap
  have hbefore :
      greedyMersenneRemainder x (2 * K - 1) =
        greedyMersenneRemainder x K - mersenneWeight (K + 1) := by
    rw [show 2 * K - 1 = (K + 1) + (K - 2) by omega,
      hconstant, htakeStep]
  have hnotLast :
      2 * K ∉ greedyMersenneSupport x :=
    hrest (2 * K) (by omega) le_rfl
  have hskipLast :
      ¬ mersenneWeight (2 * K) ≤
        greedyMersenneRemainder x (2 * K - 1) := by
    intro htakeLast
    apply hnotLast
    have htakeLast' :
        mersenneWeight (2 * K - 1 + 1) ≤
          greedyMersenneRemainder x (2 * K - 1) := by
      simpa [show 2 * K - 1 + 1 = 2 * K by omega] using htakeLast
    have hmem :=
      (succ_mem_greedyMersenneSupport_iff x (2 * K - 1)).2
        htakeLast'
    simpa [show 2 * K - 1 + 1 = 2 * K by omega] using hmem
  exact ⟨htake, hbefore, by rw [hbefore] at hskipLast; linarith⟩

/-- Complete arithmetic output for an actual *left*-boundary crossing.
Either its reduced dyadic depth strictly exceeds `K`, or the greedy residual
is forced into the explicit singleton-block sandwich.  Thus the left
orientation no longer hides a generic "valuation obstruction": only one
concrete greedy word and one two-weight interval remain. -/
theorem greedyCorrectionBoundary_left_amplifies_or_singletonSandwich
    (x : ℝ) (K v q : ℕ) (hK : 3 ≤ K)
    (hq : Odd q)
    (hprefix :
      supportDyadicPrefixNumerator (greedyMersenneSupport x) (2 * K) =
        2 ^ v * q)
    (hhit : ∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧
      n ∈ greedyMersenneSupport x) :
    K < 2 * K - v - 1 ∨
      (mersenneWeight (K + 1) ≤ greedyMersenneRemainder x K ∧
        greedyMersenneRemainder x K <
          mersenneWeight (K + 1) + mersenneWeight (2 * K)) := by
  rcases
      correctionBoundary_left_valuation_lt_or_singleton_doublingBlock
        (greedyMersenneSupport x) K v q (by omega) hq hprefix hhit with
    hv | ⟨_, hfirst, hrest⟩
  · exact Or.inl ((crossedBoundary_forceDepth_gt_iff (by omega)).2 hv)
  · have hsand :=
      greedyRemainder_sandwich_of_singleton_doublingBlock
        x K (by omega) hfirst hrest
    exact Or.inr ⟨hsand.1, hsand.2.2⟩

/-- A selected exponent anywhere in `(K,2*K]` forces the residual at `K`
above the smallest weight in that block. -/
theorem mersenneWeight_two_mul_le_remainder_of_mem_doublingBlock
    (x : ℝ) (K n : ℕ) (hKn : K < n) (hn2K : n ≤ 2 * K)
    (hnmem : n ∈ greedyMersenneSupport x) :
    mersenneWeight (2 * K) ≤ greedyMersenneRemainder x K := by
  have hnpos : 0 < n := by omega
  have hweight :=
    mersenneWeight_add_le_geometric n (2 * K - n) hnpos
  have hindex : n + (2 * K - n) = 2 * K := by omega
  have hpow :
      ((1 : ℝ) / 2) ^ (2 * K - n) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hweightLe :
      mersenneWeight (2 * K) ≤ mersenneWeight n := by
    rw [← hindex]
    calc
      mersenneWeight (n + (2 * K - n))
          ≤ mersenneWeight n * ((1 : ℝ) / 2) ^ (2 * K - n) :=
        hweight
      _ ≤ mersenneWeight n := by
        nlinarith [mersenneWeight_pos hnpos]
  have htake :
      mersenneWeight n ≤ greedyMersenneRemainder x (n - 1) := by
    have h :=
      (succ_mem_greedyMersenneSupport_iff x (n - 1)).1
        (by simpa [show n - 1 + 1 = n by omega] using hnmem)
    simpa [show n - 1 + 1 = n by omega] using h
  have hrem :
      greedyMersenneRemainder x (n - 1) ≤
        greedyMersenneRemainder x K :=
    greedyMersenneRemainder_antitone x (by omega)
  exact hweightLe.trans (htake.trans hrem)

/-- Exact scalar form of the doubling-block condition.  Hitting
`(K,2*K]` is equivalent to the single lower bound
`w_(2K) ≤ R_K` on the greedy residual. -/
theorem greedySupport_mem_doublingBlock_iff_weight_le_remainder
    (x : ℝ) (K : ℕ) (hK : 0 < K) :
    (∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧
      n ∈ greedyMersenneSupport x) ↔
      mersenneWeight (2 * K) ≤ greedyMersenneRemainder x K := by
  constructor
  · rintro ⟨n, hKn, hn2K, hnmem⟩
    exact mersenneWeight_two_mul_le_remainder_of_mem_doublingBlock
      x K n hKn hn2K hnmem
  · intro hlower
    by_contra hhit
    have hgap :
        ∀ n : ℕ, K < n → n ≤ 2 * K →
          n ∉ greedyMersenneSupport x := by
      intro n hKn hn2K hnmem
      exact hhit ⟨n, hKn, hn2K, hnmem⟩
    have hprevGap :
        ∀ n : ℕ, K < n → n ≤ K + (K - 1) →
          n ∉ greedyMersenneSupport x := by
      intro n hKn hnupper
      exact hgap n hKn (by omega)
    have hrem :
        greedyMersenneRemainder x (2 * K - 1) =
          greedyMersenneRemainder x K := by
      simpa [show K + (K - 1) = 2 * K - 1 by omega] using
        greedyMersenneRemainder_add_eq_of_support_gap
          x K (K - 1) hprevGap
    have hnot : 2 * K ∉ greedyMersenneSupport x :=
      hgap (2 * K) (by omega) le_rfl
    have hskip :
        ¬ mersenneWeight (2 * K) ≤
          greedyMersenneRemainder x (2 * K - 1) := by
      intro htake
      have hmem :=
        (succ_mem_greedyMersenneSupport_iff x (2 * K - 1)).2
          (by simpa [show 2 * K - 1 + 1 = 2 * K by omega] using htake)
      exact hnot (by simpa [show 2 * K - 1 + 1 = 2 * K by omega] using hmem)
    rw [hrem] at hskip
    exact hskip hlower

/-- The remaining combinatorial throat suggested by the correction
certificate.  The exact run verifies this from `K = 3` through `K = 5000`;
an all-depth proof would rule out every non-amplifying crossed boundary. -/
def TwentyOneGreedyHitsDoublingBlocks : Prop :=
  ∀ K : ℕ, 3 ≤ K →
    ∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧
      n ∈ greedyMersenneSupport (1 / 21 : ℝ)

/-- The eventual form is the actual correction-boundary obligation.  A
finite initial collection of empty doubling blocks cannot affect an
unbounded prefix-forcing construction. -/
def TwentyOneGreedyEventuallyHitsDoublingBlocks : Prop :=
  ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
    ∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧
      n ∈ greedyMersenneSupport (1 / 21 : ℝ)

/-- The complementary asymptotic branch: empty doubling blocks occur beyond
every cutoff.  This branch is already terminal, since each such block
contains a skipped greedy rank arbitrarily far out. -/
def TwentyOneGreedyEmptyDoublingBlocksCofinally : Prop :=
  ∀ N : ℕ, ∃ K : ℕ, N ≤ K ∧
    ∀ n : ℕ, K < n → n ≤ 2 * K →
      n ∉ greedyMersenneSupport (1 / 21 : ℝ)

/-- Cofinal empty doubling blocks solve the prescribed point rather than
obstructing it: their first ranks give cofinally many greedy skips. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinal_emptyDoublingBlocks
    (hempty : TwentyOneGreedyEmptyDoublingBlocksCofinally) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_cofinal_skips
  intro N
  obtain ⟨K, hK, hgap⟩ := hempty (max N 1)
  have hNK : N ≤ K := (le_max_left N 1).trans hK
  have hKone : 1 ≤ K := (le_max_right N 1).trans hK
  refine ⟨K + 1, ?_, by omega⟩
  have hnot :
      K + 1 ∉ greedyMersenneSupport (1 / 21 : ℝ) :=
    hgap (K + 1) (by omega) (by omega)
  change K + 1 ≠ 0 ∧ K + 1 ∉ greedyMersenneSupport (1 / 21 : ℝ)
  exact ⟨by omega, hnot⟩

/-- Exhaustive asymptotic split.  Either the empty-block branch already
proves membership, or every sufficiently large doubling block is hit.  Thus
the correction route never needs the formerly stated all-depth hit
hypothesis. -/
theorem one_div_twenty_one_mem_or_eventually_hits_doublingBlocks :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ∨
      TwentyOneGreedyEventuallyHitsDoublingBlocks := by
  classical
  by_cases hhits : TwentyOneGreedyEventuallyHitsDoublingBlocks
  · exact Or.inr hhits
  · left
    apply
      one_div_twenty_one_mem_mersenneAchievementSet_of_cofinal_emptyDoublingBlocks
    intro N
    unfold TwentyOneGreedyEventuallyHitsDoublingBlocks at hhits
    push_neg at hhits
    obtain ⟨K, hNK, hnohit⟩ := hhits N
    refine ⟨K, hNK, ?_⟩
    intro n hKn hn2K hnmem
    exact hnohit n hKn hn2K hnmem

/-- Conditional shifted-word frontier.  Either the target is already in the
achievement set, or every sufficiently large boundary satisfying the
displayed `2^v*(q-1)` prefix equation has larger forcing depth.  This does
not classify the actual left/right boundary orientations by itself. -/
theorem one_div_twenty_one_mem_or_eventual_correctionBoundary_amplification :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ K₀ : ℕ, ∀ K v q : ℕ, K₀ ≤ K → 3 ≤ K → Odd q →
        supportDyadicPrefixNumerator
            (greedyMersenneSupport (1 / 21 : ℝ)) (2 * K) =
              2 ^ v * (q - 1) →
          K < 2 * K - v - 1 := by
  rcases one_div_twenty_one_mem_or_eventually_hits_doublingBlocks with
    hmem | ⟨K₀, hhits⟩
  · exact Or.inl hmem
  · right
    refine ⟨K₀, ?_⟩
    intro K v q hK₀ hK hq hprefix
    exact correctionBoundary_forceDepth_gt_of_mem_doublingBlock
      (greedyMersenneSupport (1 / 21 : ℝ)) K v q
      (by omega) hq hprefix (hhits K hK₀)

#print axioms one_div_twenty_one_mem_or_eventually_hits_doublingBlocks
#print axioms
  one_div_twenty_one_mem_or_eventual_correctionBoundary_amplification

/-- Scalar residual form of the remaining no-gap throat. -/
theorem twentyOneGreedyHitsDoublingBlocks_iff :
    TwentyOneGreedyHitsDoublingBlocks ↔
      ∀ K : ℕ, 3 ≤ K →
        mersenneWeight (2 * K) ≤
          greedyMersenneRemainder (1 / 21 : ℝ) K := by
  unfold TwentyOneGreedyHitsDoublingBlocks
  constructor <;> intro h K hK
  · exact
      (greedySupport_mem_doublingBlock_iff_weight_le_remainder
        (1 / 21 : ℝ) K (by omega)).1 (h K hK)
  · exact
      (greedySupport_mem_doublingBlock_iff_weight_le_remainder
        (1 / 21 : ℝ) K (by omega)).2 (h K hK)

/-! ## Exact finite correction images

The reference checker does not manipulate the infinite correction value
directly.  At depth `N` it uses the exact identity

`x - correction(prefix N) = dyadic(prefix N) + remainder N`

and subtracts the complete unresolved correction tail.  The definitions and
lemmas below make that exact finite object available to theorem producers.
They are target-generic; only the final specialization fixes `x = 1/21`. -/

/-- The finite Mersenne prefix selected by the greedy itinerary of `x`. -/
noncomputable def targetGreedyMersennePrefix (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Set.indicator (greedyMersenneSupport x) mersenneWeight (k + 1)

/-- The same finite greedy word evaluated in the binary skeleton. -/
noncomputable def targetGreedyDyadicPrefix (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Set.indicator (greedyMersenneSupport x)
      (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 1)

/-- The finite correction carried by the greedy word through depth `N`. -/
noncomputable def targetGreedyCorrectionPrefix (x : ℝ) (N : ℕ) : ℝ :=
  targetGreedyMersennePrefix x N - targetGreedyDyadicPrefix x N

/-- The finite dyadic support sum is the recursive membership-word prefix. -/
theorem binaryCoeffPrefix_supportMembershipBit_eq_dyadicPrefix
    (A : Set ℕ) :
    ∀ N : ℕ,
      binaryCoeffPrefix (supportMembershipBit A) N =
        ∑ k ∈ Finset.range N,
          Set.indicator A (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 1) := by
  classical
  intro N
  induction N with
  | zero =>
      simp [binaryCoeffPrefix]
  | succ N ih =>
      rw [binaryCoeffPrefix, Finset.sum_range_succ, ih]
      by_cases hmem : N + 1 ∈ A
      · simp [supportMembershipBit, hmem]
      · simp [supportMembershipBit, hmem]

/-- Integer numerator form of the actual greedy dyadic prefix. -/
theorem targetGreedyDyadicPrefix_eq_supportNumerator_div_pow
    (x : ℝ) (N : ℕ) :
    targetGreedyDyadicPrefix x N =
      (supportDyadicPrefixNumerator (greedyMersenneSupport x) N : ℝ) /
        (2 : ℝ) ^ N := by
  rw [supportDyadicPrefixNumerator,
    binaryCoeffPrefixNumerator_div_pow,
    binaryCoeffPrefix_supportMembershipBit_eq_dyadicPrefix]
  rfl

/-- Exact finite-stage identity used by the denominator-`21` correction
checker.  No limiting or membership assumption occurs here. -/
theorem target_sub_greedyCorrectionPrefix_eq_dyadicPrefix_add_remainder
    (x : ℝ) (N : ℕ) :
    x - targetGreedyCorrectionPrefix x N =
      targetGreedyDyadicPrefix x N + greedyMersenneRemainder x N := by
  have hprefix := greedyMersenne_prefix_add_remainder x N
  change
    x = targetGreedyMersennePrefix x N +
      greedyMersenneRemainder x N at hprefix
  unfold targetGreedyCorrectionPrefix
  linarith

/-- One positive-index correction digit. -/
noncomputable def mersenneDyadicCorrectionWeight (n : ℕ) : ℝ :=
  mersenneWeight n - ((1 : ℝ) / 2) ^ n

theorem mersenneDyadicCorrectionWeight_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ mersenneDyadicCorrectionWeight n := by
  rw [mersenneDyadicCorrectionWeight,
    mersenneWeight_eq_two_channels_add_remainder hn]
  have hquarter : 0 ≤ ((1 : ℝ) / 4) ^ n := by positivity
  have hrem := mersenneWeightRemainder_nonneg hn
  linarith

/-- The selected correction after depth `N`. -/
noncomputable def supportDyadicCorrectionSuffix
    (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑' k : ℕ,
    Set.indicator A mersenneDyadicCorrectionWeight (N + k + 1)

theorem summable_supportDyadicCorrectionIndicator (A : Set ℕ) :
    Summable (fun k : ℕ =>
      Set.indicator A mersenneDyadicCorrectionWeight (k + 1)) := by
  have hsub :=
    (summable_positiveMersenneSupportIndicator A).sub
      (summable_positiveDyadicSupportIndicator A)
  refine hsub.congr fun k => ?_
  by_cases hk : k + 1 ∈ A
  · simp [mersenneDyadicCorrectionWeight, hk]
  · simp [hk]

theorem summable_supportDyadicCorrectionSuffix
    (A : Set ℕ) (N : ℕ) :
    Summable (fun k : ℕ =>
      Set.indicator A mersenneDyadicCorrectionWeight (N + k + 1)) := by
  have hshift :=
    (summable_nat_add_iff N).mpr
      (summable_supportDyadicCorrectionIndicator A)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift

theorem supportDyadicCorrectionSuffix_nonneg
    (A : Set ℕ) (N : ℕ) :
    0 ≤ supportDyadicCorrectionSuffix A N := by
  unfold supportDyadicCorrectionSuffix
  exact tsum_nonneg fun k => by
    by_cases hk : N + k + 1 ∈ A
    · rw [Set.indicator_of_mem hk]
      exact mersenneDyadicCorrectionWeight_nonneg (by omega)
    · rw [Set.indicator_of_notMem hk]

/-- The selected correction suffix is bounded by the complete correction
tail. -/
theorem supportDyadicCorrectionSuffix_le_tail
    (A : Set ℕ) (N : ℕ) :
    supportDyadicCorrectionSuffix A N ≤ mersenneCorrectionTail N := by
  have hM :
      Summable (fun k : ℕ => mersenneWeight (N + k + 1)) :=
    summable_mersenneTail N
  have hD :
      Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (N + k + 1)) := by
    have hbase : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  calc
    supportDyadicCorrectionSuffix A N
        ≤ ∑' k : ℕ, mersenneDyadicCorrectionWeight (N + k + 1) := by
          unfold supportDyadicCorrectionSuffix
          exact
            (summable_supportDyadicCorrectionSuffix A N).tsum_le_tsum
              (fun k => by
                by_cases hk : N + k + 1 ∈ A
                · rw [Set.indicator_of_mem hk]
                · rw [Set.indicator_of_notMem hk]
                  exact mersenneDyadicCorrectionWeight_nonneg (by omega))
              (hM.sub hD)
    _ = mersenneTail N -
          ∑' k : ℕ, ((1 : ℝ) / 2) ^ (N + k + 1) := by
          unfold mersenneDyadicCorrectionWeight mersenneTail
          rw [hM.tsum_sub hD]
    _ = mersenneCorrectionTail N := by
          rw [tsum_half_nat_add_succ]
          rfl

/-- The full correction splits into its selected finite prefix and selected
suffix. -/
theorem supportDyadicCorrectionValue_eq_prefix_add_suffix
    (A : Set ℕ) (N : ℕ) :
    supportDyadicCorrectionValue A =
      (∑ k ∈ Finset.range N,
        Set.indicator A mersenneDyadicCorrectionWeight (k + 1)) +
          supportDyadicCorrectionSuffix A N := by
  have hsplit :=
    (summable_supportDyadicCorrectionIndicator A).sum_add_tsum_nat_add N
  have hwhole :
      supportDyadicCorrectionValue A =
        ∑' k : ℕ,
          Set.indicator A mersenneDyadicCorrectionWeight (k + 1) := by
    unfold supportDyadicCorrectionValue positiveMersenneSupportValue
      positiveDyadicSupportValue mersenneDyadicCorrectionWeight
    calc
      (∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)) -
            ∑' k : ℕ,
              Set.indicator A (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 1)
          =
        ∑' k : ℕ,
          (Set.indicator A mersenneWeight (k + 1) -
            Set.indicator A (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (k + 1)) :=
        ((summable_positiveMersenneSupportIndicator A).tsum_sub
          (summable_positiveDyadicSupportIndicator A)).symm
      _ = ∑' k : ℕ,
          Set.indicator A
            (fun n : ℕ => mersenneWeight n - ((1 : ℝ) / 2) ^ n)
            (k + 1) := by
        apply tsum_congr
        intro k
        by_cases hk : k + 1 ∈ A <;> simp [hk]
  rw [hwhole]
  simpa [supportDyadicCorrectionSuffix, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hsplit.symm

theorem targetGreedyCorrectionPrefix_eq_indicator_sum
    (x : ℝ) (N : ℕ) :
    targetGreedyCorrectionPrefix x N =
      ∑ k ∈ Finset.range N,
        Set.indicator (greedyMersenneSupport x)
          mersenneDyadicCorrectionWeight (k + 1) := by
  classical
  unfold targetGreedyCorrectionPrefix targetGreedyMersennePrefix
    targetGreedyDyadicPrefix mersenneDyadicCorrectionWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hmem : k + 1 ∈ greedyMersenneSupport x <;> simp [hmem]

/-- The infinite correction image lies in the exact interval computed from
the finite greedy residual. -/
theorem target_sub_supportCorrection_mem_greedyCorrectionImage
    (x : ℝ) (N : ℕ) :
    x -
        supportDyadicCorrectionValue (greedyMersenneSupport x) ∈
      Set.Icc
        (targetGreedyDyadicPrefix x N +
          greedyMersenneRemainder x N - mersenneCorrectionTail N)
        (targetGreedyDyadicPrefix x N +
          greedyMersenneRemainder x N) := by
  have hsplit :=
    supportDyadicCorrectionValue_eq_prefix_add_suffix
      (greedyMersenneSupport x) N
  rw [← targetGreedyCorrectionPrefix_eq_indicator_sum x N] at hsplit
  have hsuffix0 :=
    supportDyadicCorrectionSuffix_nonneg (greedyMersenneSupport x) N
  have hsuffixLe :=
    supportDyadicCorrectionSuffix_le_tail (greedyMersenneSupport x) N
  have hid :=
    target_sub_greedyCorrectionPrefix_eq_dyadicPrefix_add_remainder x N
  constructor <;> linarith

/-- The infinite dyadic word selected by the greedy support lies in the
ordinary cylinder determined by its first `N` bits. -/
theorem positiveDyadicSupportValue_mem_greedyPrefixCell
    (x : ℝ) (N : ℕ) :
    positiveDyadicSupportValue (greedyMersenneSupport x) ∈
      Set.Icc
        (targetGreedyDyadicPrefix x N)
        (targetGreedyDyadicPrefix x N + ((1 : ℝ) / 2) ^ N) := by
  let A := greedyMersenneSupport x
  let tail : ℝ :=
    ∑' k : ℕ,
      Set.indicator A (fun n : ℕ => ((1 : ℝ) / 2) ^ n) (N + k + 1)
  have hsplit :=
    (summable_positiveDyadicSupportIndicator A).sum_add_tsum_nat_add N
  have hdecomp :
      positiveDyadicSupportValue A =
        targetGreedyDyadicPrefix x N + tail := by
    simpa [A, tail, positiveDyadicSupportValue,
      targetGreedyDyadicPrefix, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hsplit.symm
  have htail0 : 0 ≤ tail := by
    unfold tail
    exact tsum_nonneg fun k => by
      by_cases hk : N + k + 1 ∈ A
      · rw [Set.indicator_of_mem hk]
        positivity
      · rw [Set.indicator_of_notMem hk]
  have hbase : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have htailSummable :
      Summable (fun k : ℕ =>
        Set.indicator A (fun n : ℕ => ((1 : ℝ) / 2) ^ n)
          (N + k + 1)) := by
    have hshift :=
      (summable_nat_add_iff N).mpr
        (summable_positiveDyadicSupportIndicator A)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hfullTail :
      Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (N + k + 1)) := by
    have hshift := (summable_nat_add_iff (N + 1)).mpr hbase
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have htailLe : tail ≤ ((1 : ℝ) / 2) ^ N := by
    calc
      tail ≤ ∑' k : ℕ, ((1 : ℝ) / 2) ^ (N + k + 1) := by
        unfold tail
        exact htailSummable.tsum_le_tsum
          (fun k => by
            by_cases hk : N + k + 1 ∈ A
            · rw [Set.indicator_of_mem hk]
            · rw [Set.indicator_of_notMem hk]
              positivity)
          hfullTail
      _ = ((1 : ℝ) / 2) ^ N := tsum_half_nat_add_succ N
  change
    positiveDyadicSupportValue A ∈
      Set.Icc
        (targetGreedyDyadicPrefix x N)
        (targetGreedyDyadicPrefix x N + ((1 : ℝ) / 2) ^ N)
  rw [hdecomp]
  exact
    ⟨le_add_of_nonneg_right htail0,
      by simpa [add_comm] using
        add_le_add_left htailLe (targetGreedyDyadicPrefix x N)⟩

/-- A correction-image forcing chain records exactly the two quantities
computed by the finite checker: `x - correction(A)` and the infinite
dyadic word selected by `A`.  Shrinking common cells identify them. -/
structure TargetCorrectionImageForcingChain (x : ℝ) (A : Set ℕ) where
  depth : ℕ → ℕ
  cellLeft : ℕ → ℝ
  correctionImage_mem : ∀ k : ℕ,
    x - supportDyadicCorrectionValue A ∈
      Set.Icc (cellLeft k)
        (cellLeft k + ((1 : ℝ) / 2) ^ (depth k))
  dyadic_mem : ∀ k : ℕ,
    positiveDyadicSupportValue A ∈
      Set.Icc (cellLeft k)
        (cellLeft k + ((1 : ℝ) / 2) ^ (depth k))
  depth_tendsto : Tendsto depth atTop atTop

theorem TargetCorrectionImageForcingChain.correctionImage_eq_dyadic
    {x : ℝ} {A : Set ℕ}
    (chain : TargetCorrectionImageForcingChain x A) :
    x - supportDyadicCorrectionValue A =
      positiveDyadicSupportValue A := by
  have hdist : ∀ k : ℕ,
      |(x - supportDyadicCorrectionValue A) -
          positiveDyadicSupportValue A|
        ≤ ((1 : ℝ) / 2) ^ (chain.depth k) := by
    intro k
    rcases chain.correctionImage_mem k with ⟨hXL, hXR⟩
    rcases chain.dyadic_mem k with ⟨hDL, hDR⟩
    rw [abs_le]
    constructor <;> linarith
  have hpow :
      Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ (chain.depth k))
        atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      chain.depth_tendsto
  have hconstDist :
      Tendsto
        (fun _ : ℕ =>
          |(x - supportDyadicCorrectionValue A) -
            positiveDyadicSupportValue A|)
        atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
      hpow
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hdist)
  have hzero :
      |(x - supportDyadicCorrectionValue A) -
        positiveDyadicSupportValue A| = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstDist
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- The correction-image chain is already a complete arbitrary-target
achievement-set certificate. -/
theorem target_mem_mersenneAchievementSet_of_correctionImageForcingChain
    (x : ℝ) (A : Set ℕ) (hA0 : 0 ∉ A)
    (chain : TargetCorrectionImageForcingChain x A) :
    x ∈ mersenneAchievementSet := by
  refine ⟨A, hA0, ?_⟩
  have heq := chain.correctionImage_eq_dyadic
  unfold supportDyadicCorrectionValue at heq
  linarith

/-- The finite producer interface used by the exact checker.  At macrostep
`k`, the full correction image coming from `stage k` is trapped in the
ordinary dyadic cylinder of the actual greedy word at `depth k`. -/
structure GreedyCorrectionImageForcingChain (x : ℝ) where
  stage : ℕ → ℕ
  depth : ℕ → ℕ
  interval_trapped : ∀ k : ℕ,
    Set.Icc
        (targetGreedyDyadicPrefix x (stage k) +
          greedyMersenneRemainder x (stage k) -
            mersenneCorrectionTail (stage k))
        (targetGreedyDyadicPrefix x (stage k) +
          greedyMersenneRemainder x (stage k)) ⊆
      Set.Icc
        (targetGreedyDyadicPrefix x (depth k))
        (targetGreedyDyadicPrefix x (depth k) +
          ((1 : ℝ) / 2) ^ (depth k))
  depth_tendsto : Tendsto depth atTop atTop

/-- Exact finite correction traps assemble into the infinite
correction-image certificate without any additional asymptotic estimate. -/
noncomputable def GreedyCorrectionImageForcingChain.toTargetChain
    {x : ℝ} (chain : GreedyCorrectionImageForcingChain x) :
    TargetCorrectionImageForcingChain x (greedyMersenneSupport x) where
  depth := chain.depth
  cellLeft := fun k => targetGreedyDyadicPrefix x (chain.depth k)
  correctionImage_mem := fun k =>
    chain.interval_trapped k
      (target_sub_supportCorrection_mem_greedyCorrectionImage
        x (chain.stage k))
  dyadic_mem := fun k =>
    positiveDyadicSupportValue_mem_greedyPrefixCell x (chain.depth k)
  depth_tendsto := chain.depth_tendsto

/-- Denominator-`21` endpoint in the checker’s native finite-stage
coordinates. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_correctionImageChain
    (chain : GreedyCorrectionImageForcingChain (1 / 21 : ℝ)) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  exact target_mem_mersenneAchievementSet_of_correctionImageForcingChain
    (1 / 21 : ℝ) (greedyMersenneSupport (1 / 21 : ℝ))
    (zero_not_mem_greedyMersenneSupport _) chain.toTargetChain

/-- Local, non-recursive form of the remaining correction obligation.  Every
finite correction image fits in some strictly deeper cylinder of the actual
greedy word.  The cells need not be supplied compatibly: both infinite
quantities are fixed, so independent cofinal traps already suffice. -/
def GreedyCorrectionImageCofinalTrapping (x : ℝ) : Prop :=
  ∀ K : ℕ, ∃ d : ℕ, K < d ∧
    Set.Icc
        (targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K - mersenneCorrectionTail K)
        (targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K) ⊆
      Set.Icc
        (targetGreedyDyadicPrefix x d)
        (targetGreedyDyadicPrefix x d + ((1 : ℝ) / 2) ^ d)

/-- Scalar form of one finite trapping cell.  It is exactly the pair of
endpoint inequalities emitted by an exact interval evaluator. -/
theorem greedyCorrectionImage_subset_prefixCell_iff
    (x : ℝ) (K d : ℕ) :
    Set.Icc
        (targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K - mersenneCorrectionTail K)
        (targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K) ⊆
      Set.Icc
        (targetGreedyDyadicPrefix x d)
        (targetGreedyDyadicPrefix x d + ((1 : ℝ) / 2) ^ d) ↔
      targetGreedyDyadicPrefix x d ≤
        targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K - mersenneCorrectionTail K ∧
      targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K ≤
        targetGreedyDyadicPrefix x d + ((1 : ℝ) / 2) ^ d := by
  have heta := mersenneCorrectionTail_nonneg K
  constructor
  · intro hsubset
    have hlower := hsubset
      (show
        targetGreedyDyadicPrefix x K +
              greedyMersenneRemainder x K - mersenneCorrectionTail K ∈
            Set.Icc
              (targetGreedyDyadicPrefix x K +
                greedyMersenneRemainder x K - mersenneCorrectionTail K)
              (targetGreedyDyadicPrefix x K +
                greedyMersenneRemainder x K) by
        constructor <;> linarith)
    have hupper := hsubset
      (show
        targetGreedyDyadicPrefix x K +
              greedyMersenneRemainder x K ∈
            Set.Icc
              (targetGreedyDyadicPrefix x K +
                greedyMersenneRemainder x K - mersenneCorrectionTail K)
              (targetGreedyDyadicPrefix x K +
                greedyMersenneRemainder x K) by
        constructor <;> linarith)
    exact ⟨hlower.1, hupper.2⟩
  · rintro ⟨hlower, hupper⟩ z hz
    exact ⟨hlower.trans hz.1, hz.2.trans hupper⟩

/-- The correction accumulated by the actual greedy word between two
finite depths. -/
noncomputable def targetGreedyCorrectionBlock
    (x : ℝ) (K d : ℕ) : ℝ :=
  targetGreedyCorrectionPrefix x d -
    targetGreedyCorrectionPrefix x K

/-- Exact change of coordinates from two dyadic prefix cells to the later
greedy residual plus the correction accumulated between them. -/
theorem targetGreedyDyadicPrefix_add_remainder_sub_prefix
    (x : ℝ) (K d : ℕ) :
    targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K -
        targetGreedyDyadicPrefix x d =
      greedyMersenneRemainder x d +
        targetGreedyCorrectionBlock x K d := by
  have hK :=
    target_sub_greedyCorrectionPrefix_eq_dyadicPrefix_add_remainder x K
  have hd :=
    target_sub_greedyCorrectionPrefix_eq_dyadicPrefix_add_remainder x d
  unfold targetGreedyCorrectionBlock
  linarith

/-- **Scalar trapping band.**  A stage-`K` correction image lies in the
actual depth-`d` greedy cylinder exactly when the later residual plus the
intervening selected correction lies between the unresolved correction tail
at `K` and the dyadic cell width at `d`. -/
theorem greedyCorrectionImage_subset_prefixCell_iff_correctionBand
    (x : ℝ) (K d : ℕ) :
    Set.Icc
        (targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K - mersenneCorrectionTail K)
        (targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K) ⊆
      Set.Icc
        (targetGreedyDyadicPrefix x d)
        (targetGreedyDyadicPrefix x d + ((1 : ℝ) / 2) ^ d) ↔
      mersenneCorrectionTail K ≤
          greedyMersenneRemainder x d +
            targetGreedyCorrectionBlock x K d ∧
        greedyMersenneRemainder x d +
            targetGreedyCorrectionBlock x K d ≤
          ((1 : ℝ) / 2) ^ d := by
  rw [greedyCorrectionImage_subset_prefixCell_iff]
  have hdiff :=
    targetGreedyDyadicPrefix_add_remainder_sub_prefix x K d
  constructor <;> rintro ⟨hlower, hupper⟩ <;>
    constructor <;> linarith

#print axioms
  greedyCorrectionImage_subset_prefixCell_iff_correctionBand

/-- Cofinal trapping is just a cofinal family of two exact scalar endpoint
inequalities. -/
theorem greedyCorrectionImageCofinalTrapping_iff :
    GreedyCorrectionImageCofinalTrapping (1 / 21 : ℝ) ↔
      ∀ K : ℕ, ∃ d : ℕ, K < d ∧
        targetGreedyDyadicPrefix (1 / 21 : ℝ) d ≤
          targetGreedyDyadicPrefix (1 / 21 : ℝ) K +
            greedyMersenneRemainder (1 / 21 : ℝ) K -
              mersenneCorrectionTail K ∧
        targetGreedyDyadicPrefix (1 / 21 : ℝ) K +
            greedyMersenneRemainder (1 / 21 : ℝ) K ≤
          targetGreedyDyadicPrefix (1 / 21 : ℝ) d +
            ((1 : ℝ) / 2) ^ d := by
  unfold GreedyCorrectionImageCofinalTrapping
  constructor <;> intro h K
  · obtain ⟨d, hKd, hcell⟩ := h K
    exact
      ⟨d, hKd,
        (greedyCorrectionImage_subset_prefixCell_iff
          (1 / 21 : ℝ) K d).1 hcell⟩
  · obtain ⟨d, hKd, hbounds⟩ := h K
    exact
      ⟨d, hKd,
        (greedyCorrectionImage_subset_prefixCell_iff
          (1 / 21 : ℝ) K d).2 hbounds⟩

/-- Independent cofinal finite traps canonically assemble into the forcing
chain consumed by the analytic endpoint. -/
noncomputable def greedyCorrectionImageForcingChain_of_cofinalTrapping
    {x : ℝ} (htrap : GreedyCorrectionImageCofinalTrapping x) :
    GreedyCorrectionImageForcingChain x := by
  classical
  choose depth hdepth hcell using htrap
  refine
    { stage := fun K => K
      depth := depth
      interval_trapped := ?_
      depth_tendsto := ?_ }
  · intro K
    exact hcell K
  · rw [tendsto_atTop]
    intro B
    filter_upwards [eventually_ge_atTop B] with K hBK
    exact hBK.trans (Nat.le_of_lt (hdepth K))

/-- The entire denominator-`21` correction proof is therefore reduced to
the local cofinal trapping statement, with no compatibility or limit data
left for the producer. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalTrapping
    (htrap :
      GreedyCorrectionImageCofinalTrapping (1 / 21 : ℝ)) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  one_div_twenty_one_mem_mersenneAchievementSet_of_correctionImageChain
    (greedyCorrectionImageForcingChain_of_cofinalTrapping htrap)

/-- The genuinely minimal asymptotic producer only needs trapping stages
beyond every cutoff.  It need not solve the finite image at every depth. -/
def GreedyCorrectionImageTrappingCofinally (x : ℝ) : Prop :=
  ∀ N : ℕ, ∃ K d : ℕ, N ≤ K ∧ K < d ∧
    Set.Icc
        (targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K - mersenneCorrectionTail K)
        (targetGreedyDyadicPrefix x K +
          greedyMersenneRemainder x K) ⊆
      Set.Icc
        (targetGreedyDyadicPrefix x d)
        (targetGreedyDyadicPrefix x d + ((1 : ℝ) / 2) ^ d)

/-- Cofinal trapping stages independently assemble into a forcing chain. -/
noncomputable def greedyCorrectionImageForcingChain_of_trappingCofinally
    {x : ℝ} (htrap : GreedyCorrectionImageTrappingCofinally x) :
    GreedyCorrectionImageForcingChain x := by
  classical
  choose stage depth hstage hdepth hcell using htrap
  refine
    { stage := stage
      depth := depth
      interval_trapped := hcell
      depth_tendsto := ?_ }
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_ge_atTop B] with N hBN
  exact hBN.trans (hstage N) |>.trans (Nat.le_of_lt (hdepth N))

theorem one_div_twenty_one_mem_mersenneAchievementSet_of_trappingCofinally
    (htrap :
      GreedyCorrectionImageTrappingCofinally (1 / 21 : ℝ)) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  one_div_twenty_one_mem_mersenneAchievementSet_of_correctionImageChain
    (greedyCorrectionImageForcingChain_of_trappingCofinally htrap)

/-- The local theorem isolated by the exhaustive doubling-block split.  At a
depth whose next doubling block contains an actual greedy digit, the full
finite correction image fits in a strictly deeper cylinder of that same
greedy word. -/
def TwentyOneCorrectionImageAmplifiesOnDoublingBlockHit : Prop :=
  ∀ K : ℕ, 3 ≤ K →
    (∃ n : ℕ, K < n ∧ n ≤ 2 * K ∧
      n ∈ greedyMersenneSupport (1 / 21 : ℝ)) →
    ∃ d : ℕ, K < d ∧
      Set.Icc
          (targetGreedyDyadicPrefix (1 / 21 : ℝ) K +
            greedyMersenneRemainder (1 / 21 : ℝ) K -
              mersenneCorrectionTail K)
          (targetGreedyDyadicPrefix (1 / 21 : ℝ) K +
            greedyMersenneRemainder (1 / 21 : ℝ) K) ⊆
        Set.Icc
          (targetGreedyDyadicPrefix (1 / 21 : ℝ) d)
          (targetGreedyDyadicPrefix (1 / 21 : ℝ) d +
            ((1 : ℝ) / 2) ^ d)

/-- **Single-local-theorem endpoint.**  Empty doubling blocks cofinally
already force greedy convergence.  Otherwise every sufficiently large block
is hit, and local correction-image amplification supplies cofinally many
shrinking common cylinders.  Hence the local hit-to-cell theorem alone
settles the prescribed rational point. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_amplifiesOnHit
    (hamplify : TwentyOneCorrectionImageAmplifiesOnDoublingBlockHit) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  rcases one_div_twenty_one_mem_or_eventually_hits_doublingBlocks with
    hmem | ⟨K₀, hhits⟩
  · exact hmem
  · apply
      one_div_twenty_one_mem_mersenneAchievementSet_of_trappingCofinally
    intro N
    let K := max (max N K₀) 3
    have hNK : N ≤ K := le_trans (le_max_left N K₀) (le_max_left _ 3)
    have hK₀K : K₀ ≤ K :=
      le_trans (le_max_right N K₀) (le_max_left _ 3)
    have hK : 3 ≤ K := le_max_right _ 3
    obtain ⟨d, hKd, hcell⟩ := hamplify K hK (hhits K hK₀K)
    exact ⟨K, d, hNK, hKd, hcell⟩

#print axioms
  target_sub_supportCorrection_mem_greedyCorrectionImage
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalTrapping
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_amplifiesOnHit

/-- A producer interface for the dyadic-correction route at an arbitrary
target.  At stage `k`, the complete correction enclosure is trapped in one
dyadic cylinder, and the target-minus-binary value is in that same cylinder.
Unbounded cylinder depth then turns finite exact interval arithmetic into an
exact support identity.

For `x = 1/21`, the certified interval iteration starts with the word
`00001` and experimentally amplifies depths
`5, 10, 19, 38, 75, 149, 298, ...`; the remaining theorem-search burden is
to produce these data at every stage, not to reprove the analytic endpoint. -/
structure TargetPrefixForcingChain (x : ℝ) (A : Set ℕ) where
  depth : ℕ → ℕ
  cellLeft : ℕ → ℝ
  correctionLower : ℕ → ℝ
  correctionUpper : ℕ → ℝ
  correction_mem : ∀ k : ℕ,
    supportDyadicCorrectionValue A ∈
      Set.Icc (correctionLower k) (correctionUpper k)
  interval_trapped : ∀ k : ℕ,
    Set.Icc (correctionLower k) (correctionUpper k) ⊆
      Set.Icc (cellLeft k) (cellLeft k + ((1 : ℝ) / 2) ^ (depth k))
  complement_mem : ∀ k : ℕ,
    targetDyadicComplementValue x A ∈
      Set.Icc (cellLeft k) (cellLeft k + ((1 : ℝ) / 2) ^ (depth k))
  depth_tendsto : Tendsto depth atTop atTop

/-- Two sides of the target correction equation trapped in the producer's
unbounded dyadic cylinders are equal. -/
theorem TargetPrefixForcingChain.correction_eq_complement
    {x : ℝ} {A : Set ℕ} (chain : TargetPrefixForcingChain x A) :
    supportDyadicCorrectionValue A =
      targetDyadicComplementValue x A := by
  have hcorrectionCell : ∀ k : ℕ,
      supportDyadicCorrectionValue A ∈
        Set.Icc (chain.cellLeft k)
          (chain.cellLeft k + ((1 : ℝ) / 2) ^ (chain.depth k)) := by
    intro k
    exact chain.interval_trapped k (chain.correction_mem k)
  have hdist : ∀ k : ℕ,
      |supportDyadicCorrectionValue A - targetDyadicComplementValue x A|
        ≤ ((1 : ℝ) / 2) ^ (chain.depth k) := by
    intro k
    rcases hcorrectionCell k with ⟨hBL, hBR⟩
    rcases chain.complement_mem k with ⟨hCL, hCR⟩
    have hpowNonneg : 0 ≤ ((1 : ℝ) / 2) ^ (chain.depth k) := by
      positivity
    rw [abs_le]
    constructor <;> linarith
  have hpow :
      Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ (chain.depth k))
        atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      chain.depth_tendsto
  have hconstZero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hconstDist :
      Tendsto
        (fun _ : ℕ =>
          |supportDyadicCorrectionValue A - targetDyadicComplementValue x A|)
        atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hconstZero hpow
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall hdist)
  have hzero :
      |supportDyadicCorrectionValue A - targetDyadicComplementValue x A| = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstDist
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- The arbitrary-target fixed-point consumer. -/
theorem target_mem_mersenneAchievementSet_of_prefixForcingChain
    (x : ℝ) (A : Set ℕ) (hA0 : 0 ∉ A)
    (chain : TargetPrefixForcingChain x A) :
    x ∈ mersenneAchievementSet := by
  refine ⟨A, hA0, ?_⟩
  exact
    (positiveMersenneSupportValue_eq_target_iff_correction_eq_complement x A).2
      chain.correction_eq_complement |>.symm

/-- Denominator-`21` endpoint for the interval-prefix producer. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_prefixForcingChain
    (A : Set ℕ) (hA0 : 0 ∉ A)
    (chain : TargetPrefixForcingChain (1 / 21 : ℝ) A) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  target_mem_mersenneAchievementSet_of_prefixForcingChain
    (1 / 21 : ℝ) A hA0 chain

end Erdos257PeriodNoncollapse
