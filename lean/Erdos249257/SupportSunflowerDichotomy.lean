import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.SupportDilationDifferences
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
# Support sunflower and valuation-signature interfaces

This sibling records exact arithmetic needed by the support-sunflower route to
Erdős #257.  It deliberately does not assert the universal conjecture.  For
finite-core orthogonal petal bouquets, the remaining analytic obligation is
isolated exactly as `SunflowerForcedSlotTailSelection`; its conversion to the
finite selector and the existing carry-aware certificate consumer is proved
below.

The proved material here has two roles:

* divisor hits along a progression are counted with the reduced modulus
  `a / gcd a M`, without a false coprimality assumption;
* finite-core bouquets retain their full petal as reduced modulus after every
  finite frame enlargement, and bounded petal rank gives bounded support rank;
* exact prime-power layer differences extract support elements of a prescribed
  `p`-adic valuation, repairing the repeated-prime gap in distinct-prime
  dilation differences.
-/

namespace Erdos249257.SupportSunflowerDichotomy

open Erdos249257.SupportDilationDifferences

/-- A finite-core orthogonal petal bouquet.  Every exceptional element and
every ray core is absorbed by one fixed positive integer `Q`; the residual
petals are nontrivial, coprime to `Q`, globally pairwise coprime, and have
summable reciprocal mass.  The support equation is deliberately set-valued,
so duplicate bookkeeping cannot change the Boolean divisor transform. -/
structure OrthogonalPetalBouquet (A : Set ℕ) where
  Q : ℕ
  Q_pos : 0 < Q
  exceptional : Finset ℕ
  core : ℕ → ℕ
  petal : ℕ → ℕ
  exceptional_pos : ∀ d ∈ exceptional, 0 < d
  exceptional_dvd_Q : ∀ d ∈ exceptional, d ∣ Q
  core_pos : ∀ i, 0 < core i
  core_dvd_Q : ∀ i, core i ∣ Q
  petal_one_lt : ∀ i, 1 < petal i
  petal_coprime_Q : ∀ i, Nat.Coprime (petal i) Q
  petal_pairwise : ∀ i j, i ≠ j → Nat.Coprime (petal i) (petal j)
  support_eq :
    A = (↑exceptional : Set ℕ) ∪ Set.range (fun i => core i * petal i)
  summable_inv_petal : Summable (fun i => (1 : ℝ) / (petal i : ℝ))

namespace OrthogonalPetalBouquet

/-- The support ray attached to an index. -/
def ray {A : Set ℕ} (hB : OrthogonalPetalBouquet A) (i : ℕ) : ℕ :=
  hB.core i * hB.petal i

theorem ray_pos {A : Set ℕ} (hB : OrthogonalPetalBouquet A) (i : ℕ) :
    0 < hB.ray i := by
  exact Nat.mul_pos (hB.core_pos i)
    (Nat.lt_trans zero_lt_one (hB.petal_one_lt i))

theorem ray_mem {A : Set ℕ} (hB : OrthogonalPetalBouquet A) (i : ℕ) :
    hB.ray i ∈ A := by
  change hB.core i * hB.petal i ∈ A
  have hmem : hB.core i * hB.petal i ∈
      (↑hB.exceptional : Set ℕ) ∪
        Set.range (fun j => hB.core j * hB.petal j) :=
    Or.inr ⟨i, rfl⟩
  exact Eq.mpr
    (congrArg (fun S : Set ℕ => hB.core i * hB.petal i ∈ S) hB.support_eq)
    hmem

/-- Exceptional frame elements cannot coincide with a ray.  Thus the support
equation is automatically a disjoint decomposition, rather than requiring a
redundant field in the structure. -/
theorem exceptional_ne_ray {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    {d : ℕ} (hd : d ∈ hB.exceptional) (i : ℕ) :
    d ≠ hB.ray i := by
  intro hdir
  have hpetal_dvd_d : hB.petal i ∣ d := by
    rw [hdir]
    exact dvd_mul_left (hB.petal i) (hB.core i)
  have hpetal_dvd_Q : hB.petal i ∣ hB.Q :=
    hpetal_dvd_d.trans (hB.exceptional_dvd_Q d hd)
  have hone : hB.petal i = 1 :=
    Nat.eq_one_of_dvd_coprimes (hB.petal_coprime_Q i)
      dvd_rfl hpetal_dvd_Q
  exact (Nat.ne_of_gt (hB.petal_one_lt i)) hone

/-- Orthogonal petals force distinct support rays even when their cores can
repeat. -/
theorem ray_injective {A : Set ℕ} (hB : OrthogonalPetalBouquet A) :
    Function.Injective hB.ray := by
  intro i j hij
  by_contra hne
  have hpetal_core : Nat.Coprime (hB.petal i) (hB.core j) :=
    Nat.Coprime.of_dvd_right (hB.core_dvd_Q j) (hB.petal_coprime_Q i)
  have hpetal_dvd : hB.petal i ∣ hB.petal j := by
    apply hpetal_core.dvd_of_dvd_mul_left
    change hB.core i * hB.petal i = hB.core j * hB.petal j at hij
    rw [← hij]
    exact dvd_mul_left (hB.petal i) (hB.core i)
  have hone : hB.petal i = 1 :=
    Nat.eq_one_of_dvd_coprimes (hB.petal_pairwise i j hne)
      dvd_rfl hpetal_dvd
  exact (Nat.ne_of_gt (hB.petal_one_lt i)) hone

theorem petal_injective {A : Set ℕ} (hB : OrthogonalPetalBouquet A) :
    Function.Injective hB.petal := by
  intro i j hij
  by_contra hne
  have hpetal_dvd : hB.petal i ∣ hB.petal j := by rw [hij]
  have hone : hB.petal i = 1 :=
    Nat.eq_one_of_dvd_coprimes (hB.petal_pairwise i j hne)
      dvd_rfl hpetal_dvd
  exact (Nat.ne_of_gt (hB.petal_one_lt i)) hone

/-- Canonical inverse index on the ray range; values away from the range are
irrelevant. -/
noncomputable def rayIndex {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (d : ℕ) : ℕ := by
  classical
  exact if h : ∃ i, hB.ray i = d then Classical.choose h else 0

theorem ray_rayIndex_eq {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    {d : ℕ} (hd : d ∈ Set.range hB.ray) :
    hB.ray (hB.rayIndex d) = d := by
  classical
  rcases hd with ⟨i, rfl⟩
  have hex : ∃ j, hB.ray j = hB.ray i := ⟨i, rfl⟩
  simp only [rayIndex, dif_pos hex]
  exact Classical.choose_spec hex

/-- A foreign ray that appears after dilation by a selected ray pays its own
petal locally: orthogonality removes the selected ray, leaving a divisor of
the undilated argument. -/
theorem petal_dvd_of_ray_dvd {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    {i j x : ℕ} (hji : j ≠ i) (hdiv : hB.ray j ∣ hB.ray i * x) :
    hB.petal j ∣ x := by
  have hpetal_core : Nat.Coprime (hB.petal j) (hB.core i) :=
    Nat.Coprime.of_dvd_right (hB.core_dvd_Q i) (hB.petal_coprime_Q j)
  have hpetal_ray : Nat.Coprime (hB.petal j) (hB.ray i) := by
    exact hpetal_core.mul_right (hB.petal_pairwise j i hji)
  apply hpetal_ray.dvd_of_dvd_mul_left
  exact (dvd_mul_left (hB.petal j) (hB.core j)).trans hdiv

/-- The ray part, hence the whole bouquet support, is infinite. -/
theorem infinite {A : Set ℕ} (hB : OrthogonalPetalBouquet A) : A.Infinite := by
  rw [hB.support_eq]
  exact (Set.infinite_range_of_injective hB.ray_injective).mono
    (Set.subset_union_right)

/-- The selected frame step.  It absorbs the fixed core and the petals at
the finitely many promoted ray indices. -/
def frameStep {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (F : Finset ℕ) : ℕ :=
  hB.Q * ∏ i ∈ F, hB.petal i

theorem core_dvd_frameStep {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (F : Finset ℕ) (i : ℕ) :
    hB.core i ∣ hB.frameStep F := by
  exact (hB.core_dvd_Q i).trans (dvd_mul_right hB.Q _)

/-- An unselected petal stays coprime to the entire enlarged frame. -/
theorem petal_coprime_frameStep {A : Set ℕ}
    (hB : OrthogonalPetalBouquet A) (F : Finset ℕ) {i : ℕ}
    (hi : i ∉ F) :
    Nat.Coprime (hB.petal i) (hB.frameStep F) := by
  apply (hB.petal_coprime_Q i).mul_right
  apply Nat.Coprime.prod_right
  intro j hj
  exact hB.petal_pairwise i j (by
    intro hij
    subst j
    exact hi hj)

/-- Persistent reduced modulus: after any finite frame is assembled, every
unselected ray has gcd exactly its core. -/
theorem gcd_ray_frameStep {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (F : Finset ℕ) {i : ℕ} (hi : i ∉ F) :
    Nat.gcd (hB.ray i) (hB.frameStep F) = hB.core i := by
  simpa [ray, Nat.mul_comm] using
    Nat.gcd_mul_of_coprime_of_dvd (hB.petal_coprime_frameStep F hi)
      (hB.core_dvd_frameStep F i)

/-- Consequently the exact reduced modulus of an unselected ray is its
petal, independently of the size of the selected frame. -/
theorem ray_div_gcd_frameStep {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (F : Finset ℕ) {i : ℕ} (hi : i ∉ F) :
    hB.ray i / Nat.gcd (hB.ray i) (hB.frameStep F) = hB.petal i := by
  rw [hB.gcd_ray_frameStep F hi]
  simpa [ray, Nat.mul_comm] using
    Nat.mul_div_left (hB.petal i) (hB.core_pos i)

/-- Every bouquet contains a positive support element, as needed by the
far-tail positivity clause of the carry consumer. -/
theorem exists_pos_mem {A : Set ℕ} (hB : OrthogonalPetalBouquet A) :
    ∃ a : ℕ, 0 < a ∧ a ∈ A :=
  ⟨hB.ray 0, hB.ray_pos 0, hB.ray_mem 0⟩

private theorem cardFactors_le_of_dvd {a Q : ℕ}
    (ha : 0 < a) (hQ : 0 < Q) (had : a ∣ Q) :
    ArithmeticFunction.cardFactors a ≤ ArithmeticFunction.cardFactors Q := by
  obtain ⟨t, rfl⟩ := had
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp at hQ
  rw [ArithmeticFunction.cardFactors_mul ha.ne' ht]
  omega

/-- A uniform petal-rank ceiling gives a genuine bounded-`Ω` support.  The
fixed contribution is paid once by `Ω(Q)`, while each ray pays only its own
petal rank. -/
theorem cardFactors_le_of_mem {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    {R a : ℕ} (hpetal : ∀ i, ArithmeticFunction.cardFactors (hB.petal i) ≤ R)
    (haA : a ∈ A) :
    ArithmeticFunction.cardFactors a ≤
      ArithmeticFunction.cardFactors hB.Q + R := by
  rw [hB.support_eq] at haA
  rcases haA with haE | ⟨i, rfl⟩
  · have haE' : a ∈ hB.exceptional := by simpa using haE
    exact (cardFactors_le_of_dvd (hB.exceptional_pos a haE') hB.Q_pos
      (hB.exceptional_dvd_Q a haE')).trans (Nat.le_add_right _ _)
  · rw [ArithmeticFunction.cardFactors_mul (hB.core_pos i).ne'
      (Nat.ne_of_gt (Nat.lt_trans zero_lt_one (hB.petal_one_lt i)))]
    have hcore : ArithmeticFunction.cardFactors (hB.core i) ≤
        ArithmeticFunction.cardFactors hB.Q :=
      cardFactors_le_of_dvd (hB.core_pos i) hB.Q_pos (hB.core_dvd_Q i)
    exact Nat.add_le_add hcore (hpetal i)

/-! ## A concrete genuinely two-core bounded-`Ω` bouquet -/

/-- Alternate between the two fixed cores `2` and `3`. -/
def alternatingPrimeCore (i : ℕ) : ℕ :=
  if Even i then 2 else 3

/-- The square of the `(i + 2)`-nd prime.  Starting at index two excludes
both fixed core primes. -/
noncomputable def primeSquarePetal (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime (i + 2) ^ 2

/-- An explicit infinite support with genuinely different fixed cores. -/
def alternatingPrimeSquareSupport : Set ℕ :=
  Set.range (fun i => alternatingPrimeCore i * primeSquarePetal i)

private theorem alternatingPrimeCore_pos (i : ℕ) :
    0 < alternatingPrimeCore i := by
  by_cases hi : Even i <;> simp [alternatingPrimeCore, hi]

private theorem alternatingPrimeCore_dvd_six (i : ℕ) :
    alternatingPrimeCore i ∣ 6 := by
  by_cases hi : Even i <;> norm_num [alternatingPrimeCore, hi]

private theorem primeSquarePetal_one_lt (i : ℕ) :
    1 < primeSquarePetal i := by
  have hp := (Nat.prime_nth_prime (i + 2)).two_le
  simp only [primeSquarePetal]
  nlinarith

private theorem primeSquarePetal_coprime_six (i : ℕ) :
    Nat.Coprime (primeSquarePetal i) 6 := by
  let p := Nat.nth Nat.Prime (i + 2)
  have hp : p.Prime := Nat.prime_nth_prime (i + 2)
  have hp4 : 4 ≤ p := by
    have h := Nat.add_two_le_nth_prime (i + 2)
    simpa [p] using (show 4 ≤ i + 2 + 2 by omega).trans h
  have hpd : ¬p ∣ 6 := by
    intro hp6
    have hp23 : p ∣ 2 * 3 := by simpa using hp6
    rcases hp.dvd_mul.mp hp23 with hp2 | hp3
    · have : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
      omega
    · have : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
      omega
  simpa [primeSquarePetal, p] using
    ((hp.coprime_iff_not_dvd).2 hpd).pow 2 1

private theorem primeSquarePetal_pairwise (i j : ℕ) (hij : i ≠ j) :
    Nat.Coprime (primeSquarePetal i) (primeSquarePetal j) := by
  have hpi := Nat.prime_nth_prime (i + 2)
  have hpj := Nat.prime_nth_prime (j + 2)
  have hbase : Nat.nth Nat.Prime (i + 2) ≠ Nat.nth Nat.Prime (j + 2) := by
    intro heq
    have hidx := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective heq
    exact hij (by omega)
  simpa [primeSquarePetal] using
    Nat.coprime_pow_primes 2 2 hpi hpj hbase

private theorem summable_inv_primeSquarePetal :
    Summable (fun i => (1 : ℝ) / (primeSquarePetal i : ℝ)) := by
  have hseries : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun i : ℕ =>
      (1 : ℝ) / ((i + 2 : ℕ) : ℝ) ^ 2) := by
    have h := hseries.comp_injective
      (show Function.Injective (fun i : ℕ => i + 2) from
        fun _ _ hij => Nat.add_right_cancel hij)
    simpa [Function.comp_def] using h
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hshift
  have hidx : i + 2 ≤ Nat.nth Nat.Prime (i + 2) := by
    have h := Nat.add_two_le_nth_prime (i + 2)
    omega
  have hden : (((i + 2 : ℕ) : ℝ) ^ 2) ≤
      ((Nat.nth Nat.Prime (i + 2) : ℕ) : ℝ) ^ 2 := by
    gcongr
  simpa [primeSquarePetal] using
    one_div_le_one_div_of_le (by positivity) hden

/-- Concrete witness for the orthogonal-petal interface.  It has no
exceptional part, frame `Q = 6`, alternating cores `2,3`, and squared-prime
petals. -/
noncomputable def alternatingPrimeSquareBouquet :
    OrthogonalPetalBouquet alternatingPrimeSquareSupport where
  Q := 6
  Q_pos := by norm_num
  exceptional := ∅
  core := alternatingPrimeCore
  petal := primeSquarePetal
  exceptional_pos := by simp
  exceptional_dvd_Q := by simp
  core_pos := alternatingPrimeCore_pos
  core_dvd_Q := alternatingPrimeCore_dvd_six
  petal_one_lt := primeSquarePetal_one_lt
  petal_coprime_Q := primeSquarePetal_coprime_six
  petal_pairwise := primeSquarePetal_pairwise
  support_eq := by simp [alternatingPrimeSquareSupport]
  summable_inv_petal := summable_inv_primeSquarePetal

/-- The explicit alternating-core support is infinite. -/
theorem alternatingPrimeSquareSupport_infinite :
    alternatingPrimeSquareSupport.Infinite :=
  alternatingPrimeSquareBouquet.infinite

/-- Every member of the explicit support has exactly three prime factors
with multiplicity: one fixed core prime and a squared petal prime. -/
theorem alternatingPrimeSquareSupport_cardFactors_eq_three
    {a : ℕ} (ha : a ∈ alternatingPrimeSquareSupport) :
    ArithmeticFunction.cardFactors a = 3 := by
  rw [alternatingPrimeSquareSupport] at ha
  rcases ha with ⟨i, rfl⟩
  rw [ArithmeticFunction.cardFactors_mul (alternatingPrimeCore_pos i).ne'
    (Nat.ne_of_gt (Nat.lt_trans zero_lt_one (primeSquarePetal_one_lt i)))]
  have hcore : ArithmeticFunction.cardFactors (alternatingPrimeCore i) = 1 := by
    by_cases hi : Even i <;>
      simp [alternatingPrimeCore, hi, Nat.prime_two, Nat.prime_three]
  have hpetal : ArithmeticFunction.cardFactors (primeSquarePetal i) = 2 := by
    change ArithmeticFunction.cardFactors (Nat.nth Nat.Prime (i + 2) ^ 2) = 2
    exact ArithmeticFunction.cardFactors_apply_prime_pow
      (k := 2) (Nat.prime_nth_prime (i + 2))
  omega

/-- A small non-vacuity receipt: both fixed cores actually occur. -/
theorem alternatingPrimeSquareBouquet_uses_two_cores :
    alternatingPrimeSquareBouquet.core 0 = 2 ∧
      alternatingPrimeSquareBouquet.core 1 = 3 := by
  norm_num [alternatingPrimeSquareBouquet, alternatingPrimeCore]

end OrthogonalPetalBouquet

/-- The unresolved analytic supply in the bounded-`Ω`, reciprocal-summable
sunflower route.  Its conclusion is exactly the carry-aware certificate data
consumed by the landed arbitrary-support irrationality theorem. -/
def SunflowerForcedCarrySupply (A : Set ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
    (2 ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
      supportCoeff A (N + r) * 2 ^ (K - r)) ∧
    (∑ r ∈ Finset.Icc (K + 1) L,
      supportCoeff A (N + r) * 2 ^ (L - r) ≤ C) ∧
    (∃ t : ℕ, 0 < supportCoeff A (N + L + 1 + t)) ∧
    q * (C + (N + L + 2)) < 2 ^ L

/-- Closing the named forced-carry socket would prove irrationality for that
support by the existing carry-aware certificate kernel. -/
theorem irrational_erdosSupportSeries_of_sunflower_forcedCarry_supply
    (A : Set ℕ) (hsupply : SunflowerForcedCarrySupply A) :
    Irrational (erdosSupportSeries 2 A) := by
  exact irrational_erdosSupportSeries_of_weighted_coeff_carry_certificates
    2 A (by norm_num) hsupply

/-- The exact finite selector produced by the persistent-reduced-modulus
argument.  The first clause fixes the undamped carry slot.  The second clause
is the finite, natural-number form of a uniform binary-tail bound: every
middle window beginning after that slot has normalized cost at most `16`.

Keeping this predicate separate from `SunflowerForcedCarrySupply` records the
real remaining mathematical seam.  It contains no rationality hypothesis and
refers directly to the genuine Boolean divisor transform `supportCoeff A`. -/
def SunflowerForcedSlotCarrySelection (A : Set ℕ) : Prop :=
  ∀ K : ℕ, 0 < K → ∃ N : ℕ,
    (2 ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
      supportCoeff A (N + r) * 2 ^ (K - r)) ∧
    ∀ L : ℕ, K ≤ L →
      ∑ r ∈ Finset.Icc (K + 1) L,
          supportCoeff A (N + r) * 2 ^ (L - r)
        ≤ 16 * 2 ^ (L - K)

/-- Analytic form of the forced-slot selector.  This is the statement proved
directly by the orthogonal-bouquet averaging argument. -/
def SunflowerForcedSlotTailSelection (A : Set ℕ) : Prop :=
  ∀ K : ℕ, 0 < K → ∃ N : ℕ,
    (2 ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
      supportCoeff A (N + r) * 2 ^ (K - r)) ∧
    binaryCoeffTail (supportCoeff A) (N + K) ≤ 16

/-- A uniform real binary-tail bound pays every finite natural middle-window
budget.  This bridge keeps the analytic bouquet proof and the exact carry
consumer cleanly separated. -/
theorem forcedSlotCarrySelection_of_tailSelection
    (A : Set ℕ) (htail : SunflowerForcedSlotTailSelection A) :
    SunflowerForcedSlotCarrySelection A := by
  intro K hK
  obtain ⟨N, hcarry, htail16⟩ := htail K hK
  refine ⟨N, hcarry, ?_⟩
  intro L hKL
  let H := L - K
  let C := ∑ r ∈ Finset.Icc (K + 1) L,
    supportCoeff A (N + r) * 2 ^ (L - r)
  change C ≤ 16 * 2 ^ H
  have hreidx : C = ∑ j ∈ Finset.range H,
      supportCoeff A (N + K + j + 1) * 2 ^ (H - (j + 1)) := by
    have hIccIco : Finset.Icc (K + 1) L = Finset.Ico (K + 1) (L + 1) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    dsimp [C]
    rw [hIccIco, Finset.sum_Ico_eq_sum_range]
    have hlen : L + 1 - (K + 1) = H := by simp [H]
    rw [hlen]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjH : j < H := Finset.mem_range.mp hj
    congr 2 <;> omega
  have hnorm : (C : ℝ) / (2 : ℝ) ^ H =
      ∑ j ∈ Finset.range H,
        (supportCoeff A (N + K + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) := by
    rw [hreidx]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjH : j < H := Finset.mem_range.mp hj
    have hpow : (2 : ℝ) ^ H =
        (2 : ℝ) ^ (H - (j + 1)) * (2 : ℝ) ^ (j + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    field_simp
  have hsum : Summable (fun j : ℕ =>
      (supportCoeff A (N + K + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) :=
    summable_coeff_shift_tail 2 (N + K) (supportCoeff A)
      (by norm_num) (supportCoeff_le_self A)
  have hpartial :
      (∑ j ∈ Finset.range H,
        (supportCoeff A (N + K + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1))
        ≤ binaryCoeffTail (supportCoeff A) (N + K) := by
    unfold binaryCoeffTail
    exact hsum.sum_le_tsum (Finset.range H) (fun j _ => by positivity)
  have hnormalized : (C : ℝ) / (2 : ℝ) ^ H ≤ 16 := by
    rw [hnorm]
    exact hpartial.trans htail16
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ H := by positivity
  have hcast : (C : ℝ) ≤ ((16 * 2 ^ H : ℕ) : ℝ) := by
    push_cast
    rw [← div_le_iff₀ hpowpos]
    simpa using hnormalized
  exact_mod_cast hcast

/-- A forced-slot selector composes unconditionally into the landed carry
supply as soon as the support has one positive member.  This is the exact
consumer bridge needed by the orthogonal-petal bouquet argument; in
particular, no multiplicative decimation or layer-rationality transport is
used.

The proof chooses an explicit later scale.  `param_linear_le_two_pow` absorbs
the linear far-tail term, while the selector's `16 * 2^(L-K)` budget is paid
by choosing `K = 16*q + 1`. -/
theorem sunflowerForcedCarrySupply_of_forcedSlotCarrySelection
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (hselection : SunflowerForcedSlotCarrySelection A) :
    SunflowerForcedCarrySupply A := by
  intro q hq
  let K := 16 * q + 1
  have hK : 0 < K := by simp [K]
  obtain ⟨N, hcarry, hmiddle⟩ := hselection K hK
  let e := q * (N + K + 2)
  let H := 3 * q + e
  let L := K + H
  let C := ∑ r ∈ Finset.Icc (K + 1) L,
    supportCoeff A (N + r) * 2 ^ (L - r)
  refine ⟨N, K, L, C, ?_, hcarry, le_rfl, ?_, ?_⟩
  · simp [L]
  · obtain ⟨a, ha, haA⟩ := hA
    let n := N + L + 1
    refine ⟨(a - 1) * n, ?_⟩
    apply supportCoeff_pos_of_mem_dvd A haA
    · use n
      have ha_one : a - 1 + 1 = a := by omega
      simp only [n]
      calc
        N + L + 1 + (a - 1) * (N + L + 1) =
            (a - 1 + 1) * (N + L + 1) := by ring
        _ = a * (N + L + 1) := by rw [ha_one]
    · omega
  · have hC : C ≤ 16 * 2 ^ H := by
      simpa [C, L] using hmiddle L (by simp [L])
    have hlinear : q * H + e ≤ 2 ^ H := by
      simpa [H] using param_linear_le_two_pow q e
    have hbudget : q * (C + (N + L + 2)) ≤ K * 2 ^ H := by
      calc
        q * (C + (N + L + 2)) = q * C + (q * H + e) := by
          simp only [L, e]
          ring
        _ ≤ q * (16 * 2 ^ H) + 2 ^ H :=
          Nat.add_le_add (Nat.mul_le_mul_left q hC) hlinear
        _ = K * 2 ^ H := by simp [K]; ring
    have hKpow : K < 2 ^ K := Nat.lt_two_pow_self
    calc
      q * (C + (N + L + 2)) ≤ K * 2 ^ H := hbudget
      _ < 2 ^ K * 2 ^ H := Nat.mul_lt_mul_of_pos_right hKpow (by positivity)
      _ = 2 ^ L := by simp [L, pow_add]

/-- Exact bouquet composition endpoint.  The sole remaining hypothesis is
the analytic selector proved by the persistent-reduced-modulus averaging
argument; all carry arithmetic and support positivity are discharged here. -/
theorem sunflowerForcedCarrySupply_of_orthogonalPetalBouquet
    {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (hselection : SunflowerForcedSlotTailSelection A) :
    SunflowerForcedCarrySupply A :=
  sunflowerForcedCarrySupply_of_forcedSlotCarrySelection A hB.exists_pos_mem
    (forcedSlotCarrySelection_of_tailSelection A hselection)

/-- Conditional headline for the bouquet lane, with the remaining selector
named at exactly its mathematical boundary. -/
theorem irrational_erdosSupportSeries_of_orthogonalPetalBouquet
    {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (hselection : SunflowerForcedSlotTailSelection A) :
    Irrational (erdosSupportSeries 2 A) :=
  irrational_erdosSupportSeries_of_sunflower_forcedCarry_supply A
    (sunflowerForcedCarrySupply_of_orthogonalPetalBouquet hB hselection)

/-- Divisibility along `M * y + c` occupies at most one residue class modulo
the reduced modulus `a / gcd a M`.  This is the valid replacement for applying
the coprime progression bound when support strays share factors with the CRT
frame. -/
theorem card_filter_dvd_progression_le_reduced
    (M c a Y : ℕ) (ha : 0 < a) :
    ((Finset.range Y).filter (fun y => a ∣ M * y + c)).card
      ≤ Y / (a / Nat.gcd a M) + 1 := by
  classical
  let d := a / Nat.gcd a M
  have hgpos : 0 < Nat.gcd a M := Nat.gcd_pos_of_pos_left M ha
  have hdpos : 0 < d := by
    exact Nat.div_pos (Nat.gcd_le_left M ha) hgpos
  have hmono : ∀ y₁ ∈ (Finset.range Y).filter (fun y => a ∣ M * y + c),
      ∀ y₂ ∈ (Finset.range Y).filter (fun y => a ∣ M * y + c),
      y₁ < y₂ → y₁ / d < y₂ / d := by
    intro y₁ h₁ y₂ h₂ hlt
    have hy₁a := (Finset.mem_filter.mp h₁).2
    have hy₂a := (Finset.mem_filter.mp h₂).2
    obtain ⟨k, rfl⟩ : ∃ k, y₂ = y₁ + k := ⟨y₂ - y₁, by omega⟩
    have hk : 0 < k := by omega
    have hsum : M * (y₁ + k) + c = (M * y₁ + c) + M * k := by ring
    rw [hsum] at hy₂a
    have hMk : a ∣ M * k := (Nat.dvd_add_right hy₁a).mp hy₂a
    have hagk : a ∣ Nat.gcd a M * k := dvd_gcd_mul_of_dvd_mul hMk
    have hdk : d ∣ k := by
      exact (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left a M) hgpos).2 hagk
    have hdle : d ≤ k := Nat.le_of_dvd hk hdk
    have hstep : (y₁ + d) / d ≤ (y₁ + k) / d :=
      Nat.div_le_div_right (by omega)
    have hsucc : (y₁ + d) / d = y₁ / d + 1 :=
      Nat.add_div_right y₁ hdpos
    calc
      y₁ / d < y₁ / d + 1 := Nat.lt_succ_self _
      _ = (y₁ + d) / d := hsucc.symm
      _ ≤ (y₁ + k) / d := hstep
  have hmaps : ∀ y ∈ (Finset.range Y).filter (fun y => a ∣ M * y + c),
      y / d ∈ Finset.range (Y / d + 1) := by
    intro y hy
    have hyY : y < Y := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have hle : y / d ≤ Y / d := Nat.div_le_div_right (Nat.le_of_lt hyY)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hinj : Set.InjOn (fun y => y / d)
      ↑((Finset.range Y).filter (fun y => a ∣ M * y + c)) := by
    intro y₁ h₁ y₂ h₂ heq
    replace h₁ := Finset.mem_coe.mp h₁
    replace h₂ := Finset.mem_coe.mp h₂
    by_contra hne
    rcases Nat.lt_or_ge y₁ y₂ with hlt | hge
    · exact absurd heq (Nat.ne_of_lt (hmono y₁ h₁ y₂ h₂ hlt))
    · rcases Nat.lt_or_ge y₂ y₁ with hlt | hge'
      · exact absurd heq.symm (Nat.ne_of_lt (hmono y₂ h₂ y₁ h₁ hlt))
      · exact hne (by omega)
  change ((Finset.range Y).filter (fun y => a ∣ M * y + c)).card
      ≤ Y / d + 1
  calc
    ((Finset.range Y).filter (fun y => a ∣ M * y + c)).card
        ≤ (Finset.range (Y / d + 1)).card :=
      Finset.card_le_card_of_injOn (fun y => y / d) hmaps hinj
    _ = Y / d + 1 := Finset.card_range _

/-- If the frame step divides a distinguished slot, every later hit by a
support divisor is spaced from that slot by `gcd a M`.  This is the exact
arithmetic source of the geometric damping in the repaired middle-window
estimate. -/
theorem gcd_dvd_offset_sub_of_dvd_progression
    (M x a y r s : ℕ) (hframe : M ∣ x + r)
    (hhit : a ∣ x + y * M + s) :
    Nat.gcd a M ∣ s - r := by
  have hg_hit : Nat.gcd a M ∣ x + y * M + s :=
    (Nat.gcd_dvd_left a M).trans hhit
  have hg_yM : Nat.gcd a M ∣ y * M :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_right a M) y
  have hg_xs : Nat.gcd a M ∣ x + s := by
    have hreorder : x + y * M + s = y * M + (x + s) := by omega
    rw [hreorder] at hg_hit
    exact (Nat.dvd_add_right hg_yM).mp hg_hit
  have hg_xr : Nat.gcd a M ∣ x + r :=
    (Nat.gcd_dvd_right a M).trans hframe
  have hsub : Nat.gcd a M ∣ (x + s) - (x + r) :=
    Nat.dvd_sub hg_xs hg_xr
  simpa [Nat.add_sub_add_left] using hsub

/-- A nontrivial later hit cannot occur before the gcd spacing. -/
theorem gcd_le_offset_sub_of_dvd_progression
    (M x a y r s : ℕ) (hframe : M ∣ x + r)
    (hhit : a ∣ x + y * M + s) (hrs : r < s) :
    Nat.gcd a M ≤ s - r := by
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hrs)
    (gcd_dvd_offset_sub_of_dvd_progression M x a y r s hframe hhit)

/-- Support elements with exact `p`-adic exponent `e`, after removing the
prime-power layer. -/
def exactPrimePowerPullback (p e : ℕ) (A : Set ℕ) : Set ℕ :=
  {d | d.Coprime p ∧ p ^ e * d ∈ A}

private theorem filter_range_succ_card
    (P : ℕ → Prop) [DecidablePred P] (e : ℕ) :
    ((Finset.range (e + 1)).filter P).card =
      ((Finset.range e).filter P).card + if P e then 1 else 0 := by
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : P e
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, Nat.add_zero]

/-- The new divisor layer between `p^(e-1) * n` and `p^e * n` is exactly
the prescribed valuation pullback, provided the residual argument is coprime
to `p`. -/
theorem supportCoeff_prime_power_layer
    (A : Set ℕ) {p e n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hnp : n.Coprime p) :
    supportCoeff A (p ^ e * n) =
      supportCoeff A (p ^ (e - 1) * n) +
        supportCoeff (exactPrimePowerPullback p e A) n := by
  change supportCoeff A (p ^ e * n) =
    supportCoeff A (p ^ (e - 1) * n) +
      supportCoeff {d | d.Coprime p ∧ p ^ e * d ∈ A} n
  classical
  have hn0 : n ≠ 0 := by
    intro hn
    subst n
    exact hp.ne_one (by simpa using hnp)
  have hpn : ¬ p ∣ n := hp.coprime_iff_not_dvd.mp hnp.symm
  rw [supportCoeff_eq_card_filter, supportCoeff_eq_card_filter,
    supportCoeff_eq_card_filter,
    card_filter_divisors_prime_pow_mul_eq_sum
      (fun D => D ∈ A) p e n hp hn0 hpn,
    card_filter_divisors_prime_pow_mul_eq_sum
      (fun D => D ∈ A) p (e - 1) n hp hn0 hpn]
  have hepred : e - 1 + 1 = e := by omega
  calc
    (∑ d ∈ n.divisors,
        ((Finset.range (e + 1)).filter fun j => p ^ j * d ∈ A).card) =
        ∑ d ∈ n.divisors,
          (((Finset.range e).filter fun j => p ^ j * d ∈ A).card +
            if p ^ e * d ∈ A then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      exact filter_range_succ_card (fun j => p ^ j * d ∈ A) e
    _ = (∑ d ∈ n.divisors,
          ((Finset.range e).filter fun j => p ^ j * d ∈ A).card) +
        ∑ d ∈ n.divisors, (if p ^ e * d ∈ A then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ d ∈ n.divisors,
          ((Finset.range (e - 1 + 1)).filter fun j => p ^ j * d ∈ A).card) +
        ((n.divisors.filter fun d => d.Coprime p ∧ p ^ e * d ∈ A).card) := by
      rw [hepred, Finset.card_filter]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      have hdp : d.Coprime p :=
        Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_divisors hd) hnp
      exact if_congr (and_iff_right hdp).symm rfl rfl

/-- Integer-difference form consumed by valuation-signature operators. -/
theorem supportCoeffInt_prime_power_layer
    (A : Set ℕ) {p e n : ℕ} (hp : p.Prime) (he : 0 < e)
    (hnp : n.Coprime p) :
    supportCoeffInt A (p ^ e * n) -
        supportCoeffInt A (p ^ (e - 1) * n) =
      supportCoeffInt (exactPrimePowerPullback p e A) n := by
  change (supportCoeff A (p ^ e * n) : ℤ) -
      (supportCoeff A (p ^ (e - 1) * n) : ℤ) =
    (supportCoeff (exactPrimePowerPullback p e A) n : ℤ)
  rw [supportCoeff_prime_power_layer A hp he hnp]
  push_cast
  ring

/-- Moving-prime-power regression: the exact third `2`-adic layer of the
singleton support `{8}` contributes one new divisor at residual argument
`1`. -/
theorem supportCoeffInt_prime_power_layer_fixture :
    supportCoeffInt ({8} : Set ℕ) (2 ^ 3 * 1) -
        supportCoeffInt ({8} : Set ℕ) (2 ^ (3 - 1) * 1) = 1 := by
  rw [supportCoeffInt_prime_power_layer ({8} : Set ℕ)
    (p := 2) (e := 3) (n := 1) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [supportCoeffInt, exactPrimePowerPullback,
    supportCoeff_eq_card_filter]
  decide

#print axioms irrational_erdosSupportSeries_of_sunflower_forcedCarry_supply
#print axioms OrthogonalPetalBouquet.alternatingPrimeSquareSupport_infinite
#print axioms OrthogonalPetalBouquet.alternatingPrimeSquareSupport_cardFactors_eq_three
#print axioms forcedSlotCarrySelection_of_tailSelection
#print axioms sunflowerForcedCarrySupply_of_forcedSlotCarrySelection
#print axioms sunflowerForcedCarrySupply_of_orthogonalPetalBouquet
#print axioms irrational_erdosSupportSeries_of_orthogonalPetalBouquet
#print axioms card_filter_dvd_progression_le_reduced
#print axioms gcd_dvd_offset_sub_of_dvd_progression
#print axioms gcd_le_offset_sub_of_dvd_progression
#print axioms supportCoeff_prime_power_layer
#print axioms supportCoeffInt_prime_power_layer
#print axioms supportCoeffInt_prime_power_layer_fixture

end Erdos249257.SupportSunflowerDichotomy
