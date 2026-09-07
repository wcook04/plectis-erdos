import Erdos257PeriodNoncollapse.FirstHarmonicGap
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Complex first harmonic and the large-prime pivot socket

This module turns the real first-harmonic reduction into an exact complex
interface.  It also records the algebra that a large-prime pivot argument
must actually populate:

* `windowFirstExp` has real part `windowFirstCos` and unit norm;
* removing any proposed pivot phase by division gives an exact factorisation;
* centring a finite fibre is an identity, not a probabilistic heuristic;
* the four actual analytic terms use the weaker one-sided budget
  `14/25 + 1/100 + 1/100 + 8/25 = 9/10` consumed by `FirstHarmonicGap`;
* a cofinal supply of those budget decompositions proves the #249 series
  irrational through the existing certificate theorem.

No prime-distribution or decorrelation estimate is asserted here.  The
predicate `DTWPivotResidualDecorrelation` is the exact analytic socket whose
future proof must provide the four named budget pieces.
-/

namespace Erdos257PeriodNoncollapse
namespace TotientTailPeriodKiller

open Finset

noncomputable section

/-- The residue angle used by the first additive character. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))

/-- The complex first additive character of the endpoint discrepancy. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)

@[simp]
theorem windowFirstExp_re (h N L : ℕ) :
    (windowFirstExp h N L).re = windowFirstCos h N L := by
  rw [windowFirstExp, Complex.exp_ofReal_mul_I_re]
  rfl

@[simp]
theorem norm_windowFirstExp (h N L : ℕ) : ‖windowFirstExp h N L‖ = 1 := by
  simp [windowFirstExp]

/-- A complex first-harmonic saving is stronger than the real-part saving
used by the certificate theorem. -/
theorem exists_certifiedKill_of_first_harmonic_norm_gap
    {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖
        ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L := by
  apply exists_certifiedKill_of_first_harmonic_gap hX hroom
  calc
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L)
        = (∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L).re := by
            simp
    _ ≤ ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ :=
      Complex.re_le_norm _
    _ ≤ (21 / 25 : ℝ) * X := hgap
    _ ≤ (9 / 10 : ℝ) * X := by
      have hXnonneg : (0 : ℝ) ≤ X := by positivity
      nlinarith

/-- Cofinal complex first-harmonic norm saving.  This is a checked direct
analytic interface, stronger than the already-landed real-part interface. -/
def DTWFirstHarmonicNormGap : Prop :=
  ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ, ∃ X L : ℕ,
    max X₀ 1 ≤ X ∧
    16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
    ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖
      ≤ (21 / 25 : ℝ) * X

/-- The complex norm gap composes all the way to irrationality. -/
theorem irrational_totient_series_of_first_harmonic_norm_gap
    (hgap : DTWFirstHarmonicNormGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_certificate_supply
  intro h hh N₀
  obtain ⟨X, L, hX, hroom, hnorm⟩ := hgap h hh N₀
  obtain ⟨N, hNIco, hkill⟩ := exists_certifiedKill_of_first_harmonic_norm_gap
    (lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right _ _) hX)) hroom hnorm
  exact ⟨N, le_trans (le_trans (Nat.le_max_left _ _) hX)
    (Finset.mem_Ico.mp hNIco).1, L, hkill⟩

/-! ## Exact pivot algebra -/

/-- Offset of the pivot argument `N + (L-s+1)`. -/
def pivotOffset (L s : ℕ) : ℕ := L - s + 1

/-- The two occurrences of an overlap totient value have the advertised net
integer weight.  Dividing this identity by `2^L` gives the coefficient
`(2^h-1)/2^(t+1)` from the paper calculation. -/
theorem overlap_weight_identity {h L t : ℕ} (hht : h ≤ t) (htL : t < L) :
    (2 : ℤ) ^ (L - 1 - (t - h)) - (2 : ℤ) ^ (L - 1 - t) =
      ((2 : ℤ) ^ h - 1) * (2 : ℤ) ^ (L - 1 - t) := by
  have hexp : L - 1 - (t - h) = (L - 1 - t) + h := by omega
  rw [hexp, pow_add]
  ring

/-- Real angle of the proposed one-dimensional pivot phase. -/
noncomputable def pivotPrimeAngle (h L s m p : ℕ) : ℝ :=
  2 * Real.pi *
    (((2 : ℝ) ^ h - 1) * (Nat.totient m : ℝ) * ((p : ℝ) - 1) /
      (2 * (2 : ℝ) ^ (L - s)))

/-- The proposed one-dimensional phase after the identity
`φ(mp)=φ(m)(p-1)` has been applied at the overlap pivot. -/
noncomputable def pivotPrimePhase (h L s m p : ℕ) : ℂ :=
  Complex.exp ((pivotPrimeAngle h L s m p : ℂ) * Complex.I)

@[simp]
theorem norm_pivotPrimePhase (h L s m p : ℕ) :
    ‖pivotPrimePhase h L s m p‖ = 1 := by
  simp [pivotPrimePhase]

/-- Removing the pivot by division.  Division rather than an informal
"independence" claim makes the residual definition exact. -/
noncomputable def pivotResidualWeight (h N L s m p : ℕ) : ℂ :=
  windowFirstExp h N L / pivotPrimePhase h L s m p

/-- The pivot and its residual reconstruct the original phase exactly. -/
theorem windowFirstExp_eq_residual_mul_pivot (h N L s m p : ℕ) :
    windowFirstExp h N L =
      pivotResidualWeight h N L s m p * pivotPrimePhase h L s m p := by
  rw [pivotResidualWeight, div_mul_cancel₀]
  exact Complex.exp_ne_zero _

/-- The elementary arithmetic input used at a clean prime pivot. -/
theorem totient_mul_prime_of_not_dvd {m p : ℕ}
    (hp : p.Prime) (hpm : ¬p ∣ m) :
    Nat.totient (m * p) = Nat.totient m * (p - 1) := by
  simpa [Nat.mul_comm] using Nat.totient_mul_of_prime_of_not_dvd hp hpm

/-- A factor larger than a positive cofactor cannot divide that cofactor. -/
theorem not_dvd_of_pos_of_lt {m p : ℕ} (hm : 0 < m) (hmp : m < p) : ¬p ∣ m := by
  intro hdiv
  exact (not_le_of_gt hmp) (Nat.le_of_dvd hm hdiv)

/-- Exact centring identity on one finite supplier fibre. -/
theorem sum_mul_eq_centered_add_mean {α : Type*} [DecidableEq α]
    (P : Finset α) (W z : α → ℂ) (zbar : ℂ) :
    (∑ p ∈ P, W p * z p) =
      (∑ p ∈ P, W p * (z p - zbar)) + zbar * ∑ p ∈ P, W p := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-! ## Concrete supplier fibres and the weaker one-sided budget -/

/-- Actual integer at the selected overlap position. -/
def pivotArgument (N L s : ℕ) : ℕ := N + pivotOffset L s

/-- Canonical large-prime choice: maximum-fold the finite prime-factor set.
The fallback value `1` is rejected by `pivotSupplier`. -/
def pivotPrime (N L s : ℕ) : ℕ :=
  (pivotArgument N L s).primeFactors.toList.foldl Nat.max 1

def pivotCofactor (N L s : ℕ) : ℕ :=
  pivotArgument N L s / pivotPrime N L s

/-- On a prime pivot argument the canonical maximum-prime-factor selector is
the argument itself. -/
theorem pivotPrime_eq_pivotArgument_of_prime {N L s : ℕ}
    (hp : (pivotArgument N L s).Prime) :
    pivotPrime N L s = pivotArgument N L s := by
  rw [pivotPrime, Nat.Prime.primeFactors hp]
  simp [Nat.max_eq_right hp.one_le]

/-- A prime pivot argument has canonical cofactor one. -/
theorem pivotCofactor_eq_one_of_pivotArgument_prime {N L s : ℕ}
    (hp : (pivotArgument N L s).Prime) :
    pivotCofactor N L s = 1 := by
  rw [pivotCofactor, pivotPrime_eq_pivotArgument_of_prime hp,
    Nat.div_self hp.pos]

/-- If `p` is larger than a positive cofactor `m`, then the canonical
maximum-prime-factor selector on the product `m*p` is exactly `p`. -/
theorem pivotPrime_eq_of_argument_eq_mul_prime
    {N L s m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hmp : m < p)
    (harg : pivotArgument N L s = m * p) :
    pivotPrime N L s = p := by
  let factors := (m * p).primeFactors.toList
  have hprod : m * p ≠ 0 := mul_ne_zero hm.ne' hp.ne_zero
  have hpFactors : p ∈ factors := by
    simp only [factors, Finset.mem_toList]
    exact hp.mem_primeFactors (dvd_mul_left p m) hprod
  have hmax : factors.max (List.ne_nil_of_mem hpFactors) = p := by
    apply (List.max_eq_iff (List.ne_nil_of_mem hpFactors)).2
    refine ⟨hpFactors, ?_⟩
    intro q hq
    have hqFactors : q ∈ (m * p).primeFactors := by
      simpa [factors] using hq
    have hqPrime := Nat.prime_of_mem_primeFactors hqFactors
    have hqDvd := Nat.dvd_of_mem_primeFactors hqFactors
    rcases hqPrime.dvd_mul.mp hqDvd with hqm | hqp
    · exact le_trans (Nat.le_of_dvd hm hqm) (Nat.le_of_lt hmp)
    · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hqPrime hp).mp hqp)
  rw [pivotPrime, harg]
  change factors.foldl Nat.max 1 = p
  rw [List.foldl_max_eq_max (List.ne_nil_of_mem hpFactors), hmax,
    Nat.max_eq_right hp.one_le]

/-- The corresponding canonical cofactor is the original `m`. -/
theorem pivotCofactor_eq_of_argument_eq_mul_prime
    {N L s m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hmp : m < p)
    (harg : pivotArgument N L s = m * p) :
    pivotCofactor N L s = m := by
  rw [pivotCofactor, pivotPrime_eq_of_argument_eq_mul_prime hm hp hmp harg,
    harg, Nat.mul_div_cancel _ hp.pos]

/-- Decidable clean-supplier predicate.  The explicit multiplication receipt
avoids relying on division simplification outside this definition. -/
def pivotSupplier (X L s N : ℕ) : Prop :=
  let p := pivotPrime N L s
  let m := pivotCofactor N L s
  p.Prime ∧ m * p = pivotArgument N L s ∧ 0 < m ∧
    m ≤ Nat.sqrt X / 2 ∧ 2 * Nat.sqrt X < p

instance (X L s N : ℕ) : Decidable (pivotSupplier X L s N) := by
  unfold pivotSupplier
  infer_instance

def pivotSupplierBases (X L s : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (pivotSupplier X L s)

def pivotGoodCofactor (L s N : ℕ) (η : ℝ) : Prop :=
  η * pivotCofactor N L s ≤ Nat.totient (pivotCofactor N L s)

noncomputable instance (L s N : ℕ) (η : ℝ) :
    Decidable (pivotGoodCofactor L s N η) := by
  classical exact inferInstance

def pivotGoodBases (X L s : ℕ) (η : ℝ) : Finset ℕ :=
  (pivotSupplierBases X L s).filter fun N => pivotGoodCofactor L s N η

def pivotBadBases (X L s : ℕ) (η : ℝ) : Finset ℕ :=
  (pivotSupplierBases X L s).filter fun N => ¬pivotGoodCofactor L s N η

def pivotNonSupplierBases (X L s : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter fun N => ¬pivotSupplier X L s N

noncomputable def pivotPhaseAt (h N L s : ℕ) : ℂ :=
  pivotPrimePhase h L s (pivotCofactor N L s) (pivotPrime N L s)

noncomputable def pivotResidualAt (h N L s : ℕ) : ℂ :=
  windowFirstExp h N L / pivotPhaseAt h N L s

theorem windowFirstExp_eq_pivotResidualAt_mul_phase (h N L s : ℕ) :
    windowFirstExp h N L = pivotResidualAt h N L s * pivotPhaseAt h N L s := by
  rw [pivotResidualAt, div_mul_cancel₀]
  exact Complex.exp_ne_zero _

/-- The canonical clean supplier really gives the advertised totient
factorisation at the pivot argument. -/
theorem totient_pivotArgument_eq_mul {X L s N : ℕ}
    (hN : N ∈ pivotSupplierBases X L s) :
    Nat.totient (pivotArgument N L s) =
      Nat.totient (pivotCofactor N L s) * (pivotPrime N L s - 1) := by
  have hs := (Finset.mem_filter.mp hN).2
  change (pivotPrime N L s).Prime ∧
    pivotCofactor N L s * pivotPrime N L s = pivotArgument N L s ∧
    0 < pivotCofactor N L s ∧
    pivotCofactor N L s ≤ Nat.sqrt X / 2 ∧
    2 * Nat.sqrt X < pivotPrime N L s at hs
  rcases hs with ⟨hp, hmul, hm, hmroot, hplarge⟩
  have hmp : pivotCofactor N L s < pivotPrime N L s := by omega
  rw [← hmul]
  exact totient_mul_prime_of_not_dvd hp (not_dvd_of_pos_of_lt hm hmp)

def pivotFiber (X L s m : ℕ) : Finset ℕ :=
  (pivotSupplierBases X L s).filter fun N => pivotCofactor N L s = m

/-- The finite prime interval which parametrises one supplier fibre.  The
upper `range` bound is only a finiteness witness; membership is the two exact
product inequalities. -/
def pivotSupplierPrimes (X L s m : ℕ) : Finset ℕ :=
  (Finset.range (2 * X + pivotOffset L s + 1)).filter fun p =>
    p.Prime ∧ X + pivotOffset L s ≤ m * p ∧
      m * p < 2 * X + pivotOffset L s

/-- Convert a prime in the product interval back to its window base. -/
def pivotBaseOfPrime (L s m p : ℕ) : ℕ := m * p - pivotOffset L s

/-- Exact membership form of the supplier-fibre parametrisation.

For a positive cofactor `m ≤ sqrt(X)/2`, a prime `p` in the shifted product
interval maps to `N = m*p - pivotOffset L s`.  Conversely every member of the
canonical largest-prime supplier fibre arises uniquely this way. -/
theorem mem_pivotFiber_iff_exists_supplierPrime
    {X L s m N : ℕ} (hm : 0 < m) (hmsmall : m ≤ Nat.sqrt X / 2) :
    N ∈ pivotFiber X L s m ↔
      ∃ p ∈ pivotSupplierPrimes X L s m,
        pivotBaseOfPrime L s m p = N := by
  let t := pivotOffset L s
  constructor
  · intro hN
    have hfiber := Finset.mem_filter.mp hN
    have hsupplierBase := Finset.mem_filter.mp hfiber.1
    have hIco := Finset.mem_Ico.mp hsupplierBase.1
    have hsupplier := hsupplierBase.2
    change (pivotPrime N L s).Prime ∧
      pivotCofactor N L s * pivotPrime N L s = pivotArgument N L s ∧
      0 < pivotCofactor N L s ∧
      pivotCofactor N L s ≤ Nat.sqrt X / 2 ∧
      2 * Nat.sqrt X < pivotPrime N L s at hsupplier
    let p := pivotPrime N L s
    have hcofactor : pivotCofactor N L s = m := hfiber.2
    have hmul : m * p = N + t := by
      simpa [p, t, pivotArgument, hcofactor] using hsupplier.2.1
    have hpRange : p < 2 * X + t + 1 := by
      have hp_le : p ≤ m * p := by
        calc
          p = 1 * p := by simp
          _ ≤ m * p := Nat.mul_le_mul_right p hm
      omega
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpRange,
      hsupplier.1, ?_, ?_⟩, ?_⟩
    · omega
    · omega
    · simp only [pivotBaseOfPrime]
      omega
  · rintro ⟨p, hpSet, rfl⟩
    have hpData := (Finset.mem_filter.mp hpSet).2
    rcases hpData with ⟨hp, hlower, hupper⟩
    have htpos : 0 < t := by simp [t, pivotOffset]
    have ht_le : t ≤ m * p := by omega
    have hbaseLower : X ≤ m * p - t := by omega
    have hbaseUpper : m * p - t < 2 * X := by omega
    have htwo_m : 2 * m ≤ Nat.sqrt X := by omega
    have hpLarge : 2 * Nat.sqrt X < p := by
      by_contra hnot
      have hp_le : p ≤ 2 * Nat.sqrt X := by omega
      have hprod_le : m * p ≤ X := by
        nlinarith [Nat.sqrt_le X]
      omega
    have hmp : m < p := by omega
    have harg :
        pivotArgument (pivotBaseOfPrime L s m p) L s = m * p := by
      simp only [pivotArgument, pivotBaseOfPrime]
      exact Nat.sub_add_cancel ht_le
    have hpivot := pivotPrime_eq_of_argument_eq_mul_prime hm hp hmp harg
    have hcofactor := pivotCofactor_eq_of_argument_eq_mul_prime hm hp hmp harg
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨hbaseLower, hbaseUpper⟩, ?_⟩, hcofactor⟩
    change (pivotPrime (pivotBaseOfPrime L s m p) L s).Prime ∧
      pivotCofactor (pivotBaseOfPrime L s m p) L s *
          pivotPrime (pivotBaseOfPrime L s m p) L s =
        pivotArgument (pivotBaseOfPrime L s m p) L s ∧
      0 < pivotCofactor (pivotBaseOfPrime L s m p) L s ∧
      pivotCofactor (pivotBaseOfPrime L s m p) L s ≤ Nat.sqrt X / 2 ∧
      2 * Nat.sqrt X < pivotPrime (pivotBaseOfPrime L s m p) L s
    rw [hpivot, hcofactor, harg]
    exact ⟨hp, rfl, hm, hmsmall, hpLarge⟩

/-- The prime-to-base map is injective on the exact supplier interval. -/
theorem pivotBaseOfPrime_injective_on_supplierPrimes
    {X L s m p q : ℕ} (hm : 0 < m)
    (hp : p ∈ pivotSupplierPrimes X L s m)
    (hq : q ∈ pivotSupplierPrimes X L s m)
    (heq : pivotBaseOfPrime L s m p = pivotBaseOfPrime L s m q) :
    p = q := by
  have hpLower := (Finset.mem_filter.mp hp).2.2.1
  have hqLower := (Finset.mem_filter.mp hq).2.2.1
  have hproducts : m * p = m * q := by
    simp only [pivotBaseOfPrime] at heq
    omega
  exact Nat.mul_left_cancel hm hproducts

/-- Set-level form of the exact bijection between supplier primes and one
canonical fibre.  Together with
`pivotBaseOfPrime_injective_on_supplierPrimes`, this is a genuine bijection,
not merely a surjective parametrisation. -/
theorem image_pivotSupplierPrimes_eq_pivotFiber
    {X L s m : ℕ} (hm : 0 < m) (hmsmall : m ≤ Nat.sqrt X / 2) :
    (pivotSupplierPrimes X L s m).image (pivotBaseOfPrime L s m) =
      pivotFiber X L s m := by
  ext N
  rw [Finset.mem_image, mem_pivotFiber_iff_exists_supplierPrime hm hmsmall]

/-- Supplier primes are not automatically isolated from all other arguments
in the same window.  Here the pivot is `38 = 2*19`, while the same prime also
divides the distinct window argument `18+1 = 19`. -/
theorem supplierPrime_not_globally_isolated_counterexample :
    pivotOffset 20 1 = 20 ∧
    18 ∈ pivotFiber 16 20 1 2 ∧
    pivotPrime 18 20 1 = 19 ∧
    19 ∣ pivotArgument 18 20 1 ∧
    19 ∣ 18 + 1 := by
  have hp : Nat.Prime 19 := by native_decide
  have harg : pivotArgument 18 20 1 = 2 * 19 := by
    norm_num [pivotArgument, pivotOffset]
  have hpivot : pivotPrime 18 20 1 = 19 :=
    pivotPrime_eq_of_argument_eq_mul_prime (by norm_num) hp (by norm_num) harg
  have hpSet : 19 ∈ pivotSupplierPrimes 16 20 1 2 := by
    native_decide
  have hfiber : 18 ∈ pivotFiber 16 20 1 2 :=
    (mem_pivotFiber_iff_exists_supplierPrime (by norm_num) (by native_decide)).2
      ⟨19, hpSet, by norm_num [pivotBaseOfPrime, pivotOffset]⟩
  exact ⟨by norm_num [pivotOffset], hfiber, hpivot, by
    rw [harg]
    exact dvd_mul_left 19 2, by norm_num⟩

/-- The canonical natural fibre `m=1, s=L-h` is literally the shifted
dyadic interval of primes.  This is a membership equality for the actual
largest-prime supplier set, not a separately sampled prime surrogate. -/
theorem mem_pivotFiber_one_overlap_iff
    {h X L N : ℕ} (hX : 4 ≤ X) (hL : h ≤ L) :
    N ∈ pivotFiber X L (L - h) 1 ↔
      X ≤ N ∧ N < 2 * X ∧ (N + h + 1).Prime := by
  have hoffset : pivotOffset L (L - h) = h + 1 := by
    simp [pivotOffset]
    omega
  have hargument : pivotArgument N L (L - h) = N + h + 1 := by
    simp [pivotArgument, hoffset]
    omega
  constructor
  · intro hN
    have hfiber := Finset.mem_filter.mp hN
    have hsupplierBase := Finset.mem_filter.mp hfiber.1
    have hIco := Finset.mem_Ico.mp hsupplierBase.1
    have hsupplier := hsupplierBase.2
    change (pivotPrime N L (L - h)).Prime ∧
      pivotCofactor N L (L - h) * pivotPrime N L (L - h) =
        pivotArgument N L (L - h) ∧
      0 < pivotCofactor N L (L - h) ∧
      pivotCofactor N L (L - h) ≤ Nat.sqrt X / 2 ∧
      2 * Nat.sqrt X < pivotPrime N L (L - h) at hsupplier
    have hcofactor : pivotCofactor N L (L - h) = 1 := hfiber.2
    have hprimeArgument :
        pivotPrime N L (L - h) = pivotArgument N L (L - h) := by
      rw [← hsupplier.2.1, hcofactor, one_mul]
    have hpivotArgument : (pivotArgument N L (L - h)).Prime := by
      rw [← hprimeArgument]
      exact hsupplier.1
    exact ⟨hIco.1, hIco.2, by simpa [hargument] using hpivotArgument⟩
  · rintro ⟨hNX, hN2X, hprime⟩
    have hpivotArgument : (pivotArgument N L (L - h)).Prime := by
      simpa [hargument] using hprime
    have hpivotPrime := pivotPrime_eq_pivotArgument_of_prime hpivotArgument
    have hpivotCofactor :=
      pivotCofactor_eq_one_of_pivotArgument_prime hpivotArgument
    have hsqrtTwo : 2 ≤ Nat.sqrt X := by
      rw [Nat.le_sqrt]
      omega
    have htwosqrt : 2 * Nat.sqrt X ≤ X := by
      nlinarith [Nat.sqrt_le X]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hNX, hN2X⟩, ?_⟩,
      hpivotCofactor⟩
    change (pivotPrime N L (L - h)).Prime ∧
      pivotCofactor N L (L - h) * pivotPrime N L (L - h) =
        pivotArgument N L (L - h) ∧
      0 < pivotCofactor N L (L - h) ∧
      pivotCofactor N L (L - h) ≤ Nat.sqrt X / 2 ∧
      2 * Nat.sqrt X < pivotPrime N L (L - h)
    rw [hpivotPrime, hpivotCofactor]
    refine ⟨hpivotArgument, one_mul _, by omega, ?_, ?_⟩
    · omega
    · rw [hargument]
      omega

noncomputable def pivotFiberMean (h X L s m : ℕ) : ℂ :=
  ((pivotFiber X L s m).card : ℂ)⁻¹ *
    ∑ N ∈ pivotFiber X L s m, pivotPhaseAt h N L s

noncomputable def pivotCenteredCorrelation
    (h X L s : ℕ) (η : ℝ) : ℂ :=
  ∑ N ∈ pivotGoodBases X L s η,
    pivotResidualAt h N L s *
      (pivotPhaseAt h N L s - pivotFiberMean h X L s (pivotCofactor N L s))

noncomputable def pivotFiberMeanContribution
    (h X L s : ℕ) (η : ℝ) : ℂ :=
  ∑ N ∈ pivotGoodBases X L s η,
    pivotResidualAt h N L s *
      pivotFiberMean h X L s (pivotCofactor N L s)

noncomputable def pivotBadContribution
    (h X L s : ℕ) (η : ℝ) : ℂ :=
  ∑ N ∈ pivotBadBases X L s η, windowFirstExp h N L

noncomputable def pivotNonSupplierContribution (h X L s : ℕ) : ℂ :=
  ∑ N ∈ pivotNonSupplierBases X L s, windowFirstExp h N L

private theorem pivot_good_split (h X L s : ℕ) (η : ℝ) :
    (∑ N ∈ pivotGoodBases X L s η, windowFirstExp h N L) =
      pivotCenteredCorrelation h X L s η +
        pivotFiberMeanContribution h X L s η := by
  rw [pivotCenteredCorrelation, pivotFiberMeanContribution,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N hN
  rw [windowFirstExp_eq_pivotResidualAt_mul_phase]
  ring

/-- Exact decomposition into the four actual, evaluator-visible terms. -/
theorem windowFirstExp_sum_eq_pivot_decomposition
    (h X L s : ℕ) (η : ℝ) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L) =
      pivotCenteredCorrelation h X L s η +
      pivotFiberMeanContribution h X L s η +
      pivotBadContribution h X L s η +
      pivotNonSupplierContribution h X L s := by
  classical
  have hsupplier :
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L) =
        (∑ N ∈ pivotSupplierBases X L s, windowFirstExp h N L) +
        (∑ N ∈ pivotNonSupplierBases X L s, windowFirstExp h N L) := by
    simpa [pivotSupplierBases, pivotNonSupplierBases] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.Ico X (2 * X)) (pivotSupplier X L s)
        (windowFirstExp h · L)).symm
  have hgoodbad :
      (∑ N ∈ pivotSupplierBases X L s, windowFirstExp h N L) =
        (∑ N ∈ pivotGoodBases X L s η, windowFirstExp h N L) +
        (∑ N ∈ pivotBadBases X L s η, windowFirstExp h N L) := by
    simpa [pivotGoodBases, pivotBadBases] using
      (Finset.sum_filter_add_sum_filter_not
        (pivotSupplierBases X L s) (fun N => pivotGoodCofactor L s N η)
        (windowFirstExp h · L)).symm
  rw [hsupplier, hgoodbad, pivot_good_split]
  simp [pivotBadContribution, pivotNonSupplierContribution]

/-- Unlike the earlier `X/2` complex-norm proposal, the consumer only needs a
one-sided real bound.  With the same other budgets, `14/25` is sufficient. -/
def PivotBudgetAt (h X L s : ℕ) (η : ℝ) : Prop :=
  (pivotCenteredCorrelation h X L s η).re ≤ (14 / 25 : ℝ) * X ∧
  ‖pivotFiberMeanContribution h X L s η‖ ≤ (1 / 100 : ℝ) * X ∧
  ‖pivotBadContribution h X L s η‖ ≤ (1 / 100 : ℝ) * X ∧
  ‖pivotNonSupplierContribution h X L s‖ ≤ (8 / 25 : ℝ) * X

theorem first_harmonic_gap_of_pivotBudgetAt {h X L s : ℕ} {η : ℝ}
    (hbudget : PivotBudgetAt h X L s η) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L)
      ≤ (9 / 10 : ℝ) * X := by
  rcases hbudget with ⟨hcentred, hmean, hbad, hnon⟩
  rw [show (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) =
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L).re by simp,
    windowFirstExp_sum_eq_pivot_decomposition h X L s η]
  have hmeanRe := Complex.re_le_norm (pivotFiberMeanContribution h X L s η)
  have hbadRe := Complex.re_le_norm (pivotBadContribution h X L s η)
  have hnonRe := Complex.re_le_norm (pivotNonSupplierContribution h X L s)
  change (pivotCenteredCorrelation h X L s η).re +
      (pivotFiberMeanContribution h X L s η).re +
      (pivotBadContribution h X L s η).re +
      (pivotNonSupplierContribution h X L s).re ≤ (9 / 10 : ℝ) * X
  linarith

/-- The genuinely narrower cofinal socket: all four terms are fixed finite
sums over canonical largest-prime supplier fibres.  The remaining estimate is only
`Re centred ≤ 14X/25`, not `‖centred‖ ≤ X/2`. -/
def DTWPivotResidualDecorrelation : Prop :=
  ∀ h : ℕ, 0 < h → ∃ s : ℕ, 0 < s ∧ ∃ η : ℝ, 0 < η ∧ η < 1 ∧
    ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 1 ≤ X ∧
      h ≤ L - s ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      PivotBudgetAt h X L s η

theorem irrational_totient_series_of_pivotResidualDecorrelation
    (hmix : DTWPivotResidualDecorrelation) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totient_series_of_certificate_supply
  intro h hh N₀
  obtain ⟨s, hs, η, hη, hη1, hmixh⟩ := hmix h hh
  obtain ⟨X, L, hX, hoverlap, hroom, hbudget⟩ := hmixh N₀
  obtain ⟨N, hNIco, hkill⟩ := exists_certifiedKill_of_first_harmonic_gap
    (lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right _ _) hX)) hroom
    (first_harmonic_gap_of_pivotBudgetAt hbudget)
  exact ⟨N, le_trans (le_trans (Nat.le_max_left _ _) hX)
    (Finset.mem_Ico.mp hNIco).1, L, hkill⟩

#print axioms overlap_weight_identity
#print axioms pivotPrime_eq_pivotArgument_of_prime
#print axioms pivotCofactor_eq_one_of_pivotArgument_prime
#print axioms mem_pivotFiber_one_overlap_iff
#print axioms windowFirstExp_sum_eq_pivot_decomposition
#print axioms irrational_totient_series_of_pivotResidualDecorrelation

end
end TotientTailPeriodKiller
end Erdos257PeriodNoncollapse
